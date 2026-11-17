-- Prove2me | Definitions.Def_ExactAmpDich_Supplement_Codes
-- name    : ExactAmpDich_Supplement_Codes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:19:06.549205+00:00
-- url     : https://prove2.me/theorems/6571c102-3fca-42e1-8720-24f98767ba22
-- title:
--   Exact codes of algebraic matrices, libraries, bases and presentations of the full relation ideal
-- statement:
--   Exact inputs for the effectivity clauses of the paper. An algebraic number is coded by the published **exact code** of `BlockOrthoCSP_Decide_Codes`: a nonzero integer polynomial together with a closed rational box; the code is *valid* when the box contains exactly one root, and it *denotes* that root.
--
--   1. A **matrix code** of a $2^k\times 2^k$ matrix $M$ is the list of the $4^k$ codes of its entries, the entry $(y,x)$ at position $\mathrm{idx}(y)\,2^k+\mathrm{idx}(x)$ with $\mathrm{idx}(x)=\sum_i x_i2^i$; a $2\times2$ code lists the entries $(0,0),(0,1),(1,0),(1,1)$.
--   2. A **library code** of $G=(U_1,\dots,U_t)$ lists, for each gate, its number of qubits $k_j$ and a matrix code of $U_j$. A library with a code is algebraic, and a valid code determines the library.
--   3. A **basis code** lists exact codes of the elements of a finite list of algebraic numbers, e.g. a $\mathbb Q$-basis of a number field $K\subseteq\mathbb C$.
--   4. A **presentation** of a complex library consists of the gate sizes $k_j$, the coordinate layout (which real or imaginary part of which entry each variable $X_i$ carries), and a finite list of rational polynomials. It *presents* $(G,e)$ when the sizes and layout are those of $G$ and of the variable order $e$, and the polynomials generate the **full** relation ideal $I=\{p\in\mathbb Q[X]:p(\alpha)=0\}$ of (35).
--
--   Every effectivity statement of the mission quantifies over all valid codes of its input, never over a chosen one.
--
--   **Formalization Note** Codes are lists and pairs of integers and naturals, so Mathlib's `Primcodable` instances apply and `Computable` makes sense for maps between them.
-- source:
--   Liu–Meng, A Dichotomy for Exact Quantum Circuit Amplitudes, STOC 2027 submission (held manuscript, sha256 40ad9c68…), App. A.1, p.18 (PDF p.19); App. F.4, p.50 (PDF p.51) ('decidable from the exact algebraic gate matrices'); App. G.1, pp.51–52 (PDF pp.52–53) and Theorem G.1, p.52 (presentations)

import Mathlib
import Definitions.Def_ExactAmpDich_Coord
import Definitions.Def_BlockOrthoCSP_Decide_Codes

set_option autoImplicit false

namespace ExactAmpDich.Supplement

open QAlgorithms BlockOrthoCSP.Decide

/-- The position `bitsIndex x = Σᵢ xᵢ 2ⁱ` of a bit string in the listing of `{0,1}^k` used by all
exact matrix codes below. -/
def bitsIndex {k : ℕ} (x : Qubits k) : ℕ := ∑ i : Fin k, if x i then 2 ^ (i : ℕ) else 0

/-- Exact code of a `2^k × 2^k` algebraic matrix: the list of the `4^k` exact codes
(`BlockOrthoCSP.Decide.AlgCode`: integer polynomial and isolating rational box) of its entries,
entry `(y, x)` at position `bitsIndex y · 2^k + bitsIndex x`. Liu–Meng, *A Dichotomy for Exact
Quantum Circuit Amplitudes*, STOC 2027 submission (held manuscript, sha256 40ad9c68…), App. F.4,
p.50 (PDF p.51): "decidable from the exact algebraic gate matrices"; App. A.1, p.18. -/
abbrev MatCode : Type := List AlgCode

/-- `cd` is a valid exact code of the matrix `M`: it has `4^k` entries and the entry at the
position of `(y, x)` is a valid code (it isolates exactly one root) of `M y x`. A matrix with a
code has algebraic entries, and a valid code determines its matrix. -/
def MatCode.Denotes (k : ℕ) (cd : MatCode) (M : Matrix (Qubits k) (Qubits k) ℂ) : Prop :=
  cd.length = 4 ^ k ∧ ∀ y x, ∃ a, (cd[bitsIndex y * 2 ^ k + bitsIndex x]? = some a) ∧ a.Valid ∧
    a.Denotes (M y x)

/-- Position of the entry `(i, j)` of a `2 × 2` matrix in its code. -/
def idx2 (i j : Bool) : ℕ := 2 * (if i then 1 else 0) + (if j then 1 else 0)

/-- Exact code of a `2 × 2` algebraic matrix: four entry codes, in the order
`(0,0), (0,1), (1,0), (1,1)`. -/
abbrev Mat2Code : Type := List AlgCode

/-- `cd` is a valid exact code of the `2 × 2` matrix `M`. -/
def Mat2Code.Denotes (cd : Mat2Code) (M : Matrix Bool Bool ℂ) : Prop :=
  cd.length = 4 ∧ ∀ i j, ∃ a, (cd[idx2 i j]? = some a) ∧ a.Valid ∧ a.Denotes (M i j)

/-- Exact code of a library: for each gate, in library order, its number of qubits `k_j` and the
exact code of its matrix. -/
abbrev LibCode : Type := List (ℕ × MatCode)

/-- `cd` is a valid exact code of the library `L`. Every library with a code is algebraic; every
algebraic library has (many) codes, and every effectivity statement of this mission quantifies
over all of them. -/
def LibCode.Denotes (cd : LibCode) (L : Library) : Prop :=
  cd.length = L.t ∧ ∀ j : Fin L.t, ∃ e, cd[j.val]? = some e ∧ e.1 = L.k j ∧
    MatCode.Denotes (L.k j) e.2 (L.U j)

/-- Exact code of a finite list of algebraic numbers (e.g. a `ℚ`-basis of a number field
`K ⊆ ℂ`). -/
abbrev BasisCode : Type := List AlgCode

/-- `cd` is a valid exact code of the list `v`. -/
def BasisCode.Denotes {d : ℕ} (cd : BasisCode) (v : Fin d → ℂ) : Prop :=
  cd.length = d ∧ ∀ i : Fin d, ∃ a, (cd[i.val]? = some a) ∧ a.Valid ∧ a.Denotes (v i)

/-- Code of a coordinate position `(j, y, x, re/im)` of a library. -/
def coordCode (L : Library) (p : L.Coord) : ℕ × ℕ × ℕ × Bool :=
  (p.1.val, bitsIndex p.2.1, bitsIndex p.2.2.1, p.2.2.2)

/-- Code of a rational polynomial in `s` variables: a list of terms, each a rational coefficient
`num / (den + 1)` (`BlockOrthoCSP.Decide.ratOf`) and an exponent list. -/
abbrev RatPolyCode : Type := List ((ℤ × ℕ) × List ℕ)

/-- Decoding of a rational polynomial code in the variables `X₀, …, X_{s-1}` (missing exponents
are `0`). -/
noncomputable def RatPolyCode.decode (s : ℕ) (g : RatPolyCode) : MvPolynomial (Fin s) ℚ :=
  (g.map fun m => MvPolynomial.C (ratOf m.1) *
    ∏ i : Fin s, MvPolynomial.X i ^ (m.2.getD i.val 0)).sum

/-- A **presentation** of a complex library (Liu–Meng, Theorem G.1, p.52, PDF p.53: "a finite
rational generating set promised to equal the full ideal I, together with the positions of the
coordinate variables in the unitary gate matrices"): the gate sizes `k_j`, the coordinate layout
(position `i` holds the code of the coordinate carried by the variable `X_i`), and the list of
rational generators. -/
abbrev PresCode : Type := List ℕ × List (ℕ × ℕ × ℕ × Bool) × List RatPolyCode

/-- `pc` presents the library `L` with variable order `e`: the gate sizes and the layout are those
of `L` and `e`, every exponent list has length `s`, and the generators span the **full** relation
ideal `I = relIdeal L e` (35). -/
def PresCode.Denotes (pc : PresCode) (L : Library) {s : ℕ} (e : L.Coord ≃ Fin s) : Prop :=
  pc.1 = List.ofFn L.k ∧ pc.2.1 = List.ofFn (fun i => coordCode L (e.symm i)) ∧
    (∀ g ∈ pc.2.2, ∀ m ∈ g, m.2.length = s) ∧
    Ideal.span {p | ∃ g ∈ pc.2.2, RatPolyCode.decode s g = p} = relIdeal L e

end ExactAmpDich.Supplement


