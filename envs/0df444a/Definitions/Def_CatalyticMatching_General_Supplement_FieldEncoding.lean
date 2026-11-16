-- Prove2me | Definitions.Def_CatalyticMatching_General_Supplement_FieldEncoding
-- name    : CatalyticMatching_General_Supplement_FieldEncoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:06:15.714322+00:00
-- url     : https://prove2.me/theorems/b271605e-8fce-41c7-b241-25e3f5e250d7
-- title:
--   Explicit bit encodings of ℚ, of finite fields, of mixed matrices and of matrix lists
-- statement:
--   All complexity bounds are measured in the total binary input length (p.10). A **presented field** is a field together with a header string and a self-delimiting encoding of elements. Two standard presentations are used.
--
--   1. $\mathbb Q$: header $0$; a rational is a sign bit, its framed numerator magnitude and framed positive denominator in lowest terms (the base mission's encoding).
--   2. A finite field $\mathbb F_p[t]/(f)$ with $p$ prime and $f$ monic irreducible over $\mathbb F_p$ of degree $k$: header $1$ followed by framed $p$, framed $k$ and the $k$ lower coefficients of $f$; an element is written by its $k$ coordinates in the basis $1,t,\dots,t^{k-1}$, each a framed binary residue. This field has $p^k$ elements.
--
--   A word $w$ is framed as $1^{|w|}0w$ and naturals are written in binary. A mixed matrix is written as framed $r$, framed $c$ and its $rc$ entries in row-major order, each $1$ for an indeterminate or $0$ followed by the scalar. An assignment lists the values of the variables in row-major order of their positions. A list of $n\times n$ matrices is framed $n$, framed $m$ and the $m$ matrices row-major.
--
--   The predicate "standard field of size at least $\beta$" holds for $\mathbb Q$ (any $\beta$) and for $\mathbb F_p[t]/(f)$ when $\beta\le p^{k}$.
--
--   These encodings describe input and output strings only; arithmetic and rank are not free operations of the machine model.
-- source:
--   Srijan Chakraborty, Samir Datta, Aryan Kusre, Partha Mukhopadhyay, Amit Sinhababu, Maximum Matching and Related Problems in Catalytic Logspace, STOC 2027 submission #479 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/479.pdf, §2 final paragraph, printed/PDF p.10; §4 preamble, p.22; §5, pp.26–28

import Definitions.Def_CatalyticMatching_General_Encoding

namespace CatalyticMatching.General.Supplement

/-- A field together with an explicit bit presentation: a header describing the field
and a self-delimiting encoding of its elements. Only the two standard presentations
below are ever used as inputs. -/
structure Presented where
  F : Type
  [inst : Field F]
  header : Bits
  enc : F → Bits

attribute [instance] Presented.inst

/-- ℚ with reduced framed binary rationals (the published `ratBits`); header bit 0. -/
def ratPresented : Presented where
  F := ℚ
  header := [false]
  enc := ratBits

/-- Description of 𝔽_p[t]/(f) for a monic f: framed binary p, framed degree k, and the
k lower coefficients of f, each a framed binary residue in [0,p). -/
def ffDescBits {p : ℕ} (f : Polynomial (ZMod p)) : Bits :=
  frame (natBits p) ++ frame (natBits f.natDegree) ++
    (List.range f.natDegree).flatMap (fun i => frame (natBits (f.coeff i).val))

/-- An element of 𝔽_p[t]/(f) is written by its k coordinates in the power basis
1, t, …, t^{k-1}, each a framed binary residue in [0,p). -/
noncomputable def ffElemBits {p : ℕ} (f : Polynomial (ZMod p)) (hm : f.Monic)
    (z : AdjoinRoot f) : Bits :=
  (List.finRange (AdjoinRoot.powerBasis' hm).dim).flatMap
    (fun i => frame (natBits (((AdjoinRoot.powerBasis' hm).basis.repr z) i).val))

/-- The standard explicit representation of a finite field: p prime, f monic irreducible
over 𝔽_p, field 𝔽_p[t]/(f) of size p^{deg f}; header bit 1 followed by the description. -/
noncomputable def ffPresented (p : ℕ) [Fact p.Prime] (f : Polynomial (ZMod p))
    [Fact (Irreducible f)] (hm : f.Monic) : Presented where
  F := AdjoinRoot f
  header := true :: ffDescBits f
  enc := ffElemBits f hm

/-- The source's computational field setting (p.10, §4 p.22, §5 pp.26--28): ℚ, or any
finite field in standard representation with at least β elements. -/
inductive StandardField : Presented → ℝ → Prop
  | rat (β : ℝ) : StandardField ratPresented β
  | finite (p : ℕ) [Fact p.Prime] (f : Polynomial (ZMod p)) [Fact (Irreducible f)]
      (hm : f.Monic) (β : ℝ) (hβ : β ≤ (p : ℝ) ^ f.natDegree) :
      StandardField (ffPresented p f hm) β

/-- Row-major positions of an r×c array; empty if r = 0 or c = 0. -/
def gridPairs (r c : ℕ) : List (Fin r × Fin c) :=
  (List.finRange r).flatMap (fun i => (List.finRange c).map (fun j => (i, j)))

/-- An entry of a mixed matrix: 1 for an indeterminate, 0 followed by the scalar. -/
def entryBits {F : Type} (enc : F → Bits) : Option F → Bits
  | none => [true]
  | some s => false :: enc s

/-- Framed dimensions r, c, then all r·c entries row-major. -/
def mixedBits {F : Type} (enc : F → Bits) {r c : ℕ} (A : Fin r → Fin c → Option F) : Bits :=
  frame (natBits r) ++ frame (natBits c) ++
    (gridPairs r c).flatMap (fun ij => entryBits enc (A ij.1 ij.2))

/-- The value of every variable, in row-major order of its position. -/
noncomputable def assignBits {F : Type} (enc : F → Bits) {r c : ℕ}
    (A : Fin r → Fin c → Option F) (a : {p : Fin r × Fin c // A p.1 p.2 = none} → F) : Bits := by
  classical
  exact (gridPairs r c).flatMap (fun ij =>
    if h : A ij.1 ij.2 = none then enc (a ⟨ij, h⟩) else [])

/-- All n² entries of a square matrix, row-major (n is known from the input). -/
def sqMatrixBits {F : Type} (enc : F → Bits) {n : ℕ} (B : Matrix (Fin n) (Fin n) F) : Bits :=
  (gridPairs n n).flatMap (fun ij => enc (B ij.1 ij.2))

/-- An instance of Edmonds' problem: framed n, framed m, then A₁,…,A_m. -/
def generatorsBits {F : Type} (enc : F → Bits) {n m : ℕ}
    (A : Fin m → Matrix (Fin n) (Fin n) F) : Bits :=
  frame (natBits n) ++ frame (natBits m) ++
    (List.finRange m).flatMap (fun i => sqMatrixBits enc (A i))

end CatalyticMatching.General.Supplement


