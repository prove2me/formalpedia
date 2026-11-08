-- Prove2me | Definitions.Def_Holant3Dich_AlgPres
-- name    : Holant3Dich_AlgPres
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:49:04.499936+00:00
-- url     : https://prove2.me/theorems/d9c63f46-079c-44f2-b641-b0eb80820d2e
-- title:
--   Finite presentations of algebraic numbers, signatures, matrices and polynomials
-- statement:
--   Inputs for the decidability statements.
--
--   1. An **algebraic number** is presented by the rational coefficients $[c_0,\dots,c_m]$ of $p(X)=c_0+c_1X+\cdots+c_mX^m$ and a closed rational box $[r_0,r_1]\times[s_0,s_1]\subseteq\mathbb C$. The presentation is **valid** if $p\neq0$ and $p$ has exactly one complex root in the box; it presents that root.
--   2. A **domain-3 signature** is presented by its arity $n$ and its $3^n$ values in lexicographic order of the inputs ($\mathsf B<\mathsf G<\mathsf R$), each presented as in 1 (p.11: "A signature $F_v$ is listed by its values lexicographically as a table").
--   3. A $d\times d$ **matrix** is presented by its $d^2$ entries in row-major order, and a **polynomial** in the $d^2$ entries by a list of terms (exponent list, presented coefficient).
--
--   The presentations are built from lists and products of rationals and natural numbers, so computability of functions on them is Mathlib's `Computable`.
--
--   **Formalization Note** The paper does not fix an input format for algebraic numbers; this is the standard one (a defining polynomial with an isolating box). Invalid presentations decode to $0$; the decidability statements make no claim about them. A verification file proves that $(X^2+1,\ [0,0]\times[\tfrac12,2])$ is valid and presents $i$.
-- source:
--   Cai, Ihm, Group Action and Spin Representation Lead to a Holant* Complexity Dichotomy on Domain Size 3, STOC 2027 submission, arXiv:2610.04750 (held manuscript sha256 b608db44…), Theorem 9.11 p.91; §4.5.3 p.47; §2.1 p.11

import Mathlib
import Definitions.Def_Holant3Dich_Sig

set_option autoImplicit false

namespace Holant3Dich

/-- A **presentation of an algebraic number**: a list of rational coefficients
`[c₀, c₁, …, c_m]` of the polynomial `c₀ + c₁X + ⋯ + c_mX^m`, and a closed rational box
`[re₀, re₁] × [im₀, im₁]` in `ℂ`. Cai–Ihm, *Group Action and Spin Representation Lead to a Holant\*
Complexity Dichotomy on Domain Size 3*, STOC 2027 submission, arXiv:2610.04750 (held manuscript
sha256 b608db44…), Theorem 9.11, p.91: "Furthermore, the dichotomy is decidable."; §4.5.3, p.47.

**Formalization Note.** The paper does not fix an input format for algebraic numbers; this is the
standard one (a defining polynomial and an isolating box). It is a product of `List ℚ` and `ℚ`'s,
so it has a `Primcodable` instance and `Computable` deciders on it make sense. -/
abbrev AlgPres := List ℚ × (ℚ × ℚ) × (ℚ × ℚ)

/-- The polynomial `c₀ + c₁X + ⋯` of a presentation. -/
noncomputable def AlgPres.poly (p : AlgPres) : Polynomial ℚ :=
  ∑ i : Fin p.1.length, Polynomial.C (p.1.get i) * Polynomial.X ^ (i : ℕ)

/-- `z` lies in the closed box of the presentation. -/
def AlgPres.InBox (p : AlgPres) (z : ℂ) : Prop :=
  (p.2.1.1 : ℝ) ≤ z.re ∧ z.re ≤ (p.2.1.2 : ℝ) ∧ (p.2.2.1 : ℝ) ≤ z.im ∧ z.im ≤ (p.2.2.2 : ℝ)

/-- A presentation is **valid** when its polynomial is nonzero and has exactly one complex root in
its box. -/
def AlgPres.Valid (p : AlgPres) : Prop :=
  p.poly ≠ 0 ∧ ∃! z : ℂ, Polynomial.aeval z p.poly = 0 ∧ p.InBox z

/-- The algebraic number presented: the unique root in the box (`0` for an invalid
presentation). -/
noncomputable def AlgPres.val (p : AlgPres) : ℂ :=
  open Classical in if h : p.Valid then Classical.choose h.2.exists else 0

/-- The lexicographic index of an input `x ∈ {B, G, R}^n` (B < G < R), the first coordinate
most significant. -/
def lexIndex {n : ℕ} (x : Fin n → Fin 3) : ℕ := ∑ i : Fin n, (x i).val * 3 ^ (n - 1 - i.val)

/-- A **presented domain-3 signature**: its arity `n` and its `3ⁿ` values in lexicographic order
of the inputs, each an `AlgPres`. Cai–Ihm, §2.1, p.11: "A signature Fv is listed by its values
lexicographically as a table". -/
abbrev SigPres := ℕ × List AlgPres

/-- A presented signature is valid when it lists `3ⁿ` valid values. -/
def SigPres.Valid (s : SigPres) : Prop := s.2.length = 3 ^ s.1 ∧ ∀ p ∈ s.2, p.Valid

/-- The signature presented. -/
noncomputable def SigPres.decode (s : SigPres) : Sig 3 :=
  ⟨s.1, fun x => (s.2.map AlgPres.val).getD (lexIndex x) 0⟩

/-- The set of signatures presented by a list. -/
def decodeSet (l : List SigPres) : Set (Sig 3) := {F | ∃ s ∈ l, F = s.decode}

/-- A **presented `d × d` matrix**: its `d²` entries in row-major order, each an `AlgPres`. -/
abbrev MatPres := List AlgPres

/-- The matrix presented (entry `(i, j)` at index `i·d + j`). -/
noncomputable def decodeMat (d : ℕ) (m : MatPres) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => (m.map AlgPres.val).getD (i.val * d + j.val) 0

/-- A **presented polynomial** in the `d²` entries of a `d × d` matrix: a list of terms, each an
exponent list (exponent of the entry with row-major index `k` at position `k`, missing exponents
`0`) and an `AlgPres` coefficient. -/
abbrev PolyPres := List (List ℕ × AlgPres)

/-- The value of a presented polynomial at a `d × d` matrix `M`. -/
noncomputable def PolyPres.eval {d : ℕ} (P : PolyPres) (M : Matrix (Fin d) (Fin d) ℂ) : ℂ :=
  (P.map fun t => t.2.val * ∏ i : Fin d, ∏ j : Fin d, M i j ^ t.1.getD (i.val * d + j.val) 0).sum

/-- A presented polynomial is valid when all its coefficients are. -/
def PolyPres.Valid (P : PolyPres) : Prop := ∀ t ∈ P, t.2.Valid

end Holant3Dich


