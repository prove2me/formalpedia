-- Prove2me | Definitions.Def_ConsModCount_Balance
-- name    : ConsModCount_Balance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:28:14.886431+00:00
-- url     : https://prove2.me/theorems/aa80152e-fa64-48bc-be75-4cab4ee9990c
-- title:
--   Block-rank-one matrices, witness-count matrices, strong balance and $Q_C$
-- statement:
--   Let $M$ be a nonnegative matrix with finite row and column index sets. Its positive support is **rectangular** if
--
--   $$\operatorname{supp}(M)=\bigcup_{i=1}^{s}A_i\times B_i$$
--
--   with nonempty pairwise disjoint $A_i$ and nonempty pairwise disjoint $B_i$ ($s=0$ allowed). $M$ is **block-rank-one** if moreover the restriction of $M$ to each block $A_i\times B_i$ has rank one; the zero matrix qualifies.
--
--   For $R\subseteq D^{k}$ and a grouping of its coordinates into $x\in D^r$, $y\in D^s$, $z\in D^t$ with $r,s\ge1$, $t\ge0$, the **witness-count matrix** is $M_R(a,b)=|\{c\in D^t:(a,b,c)\in R\}|$. $H$ is **strongly balanced** if $M_R$ is block-rank-one over the integers for every $R\in\mathrm{pp}(H)$ and every choice and ordering of the three groups; entries are not reduced modulo a prime.
--
--   For a three-element $C=\{c_0,c_1,d\}\subseteq D$ with chosen singleton fibre $\{d\}$, put $q(c_0)=q(c_1)=0$, $q(d)=1$ and
--
--   $$Q_C=\{(z_1,z_2,z_3,z_4)\in C^4:\ q(z_1)\oplus q(z_2)\oplus q(z_3)\oplus q(z_4)=0\}.$$
--
--   Strong balance is the tractability criterion at primes $p\ge7$, and $Q_C$ is its obstruction.
--
--   **Formalization Note** A positive block has rank one exactly when its $2\times2$ minors vanish; the definition states the minors. A grouping is an equivalence $\mathrm{Fin}\,k\simeq\mathrm{Fin}\,r\oplus\mathrm{Fin}\,s\oplus\mathrm{Fin}\,t$. $Q_C$ is written as "an even number of coordinates equal $d$".
-- source:
--   Xie, Conservative Modular Counting at Every Odd Prime, STOC 2027 submission (manuscript sha256 c673b4cc58550963462480168a22eca7184c16aebf1faa02497d68c5a46d876a), §10, pp.12–13 (PDF pp.13–14): block-rank-one, rectangular, witness-count matrix, strongly balanced; §1, p.1 (PDF p.2) and §11, p.16 (PDF p.17): Q_C

import Mathlib
import Definitions.Def_ConsModCount_PP

set_option autoImplicit false

namespace ConsModCount

/-- The positive support of a nonnegative matrix `M` is **rectangular**: it is a disjoint union
`⋃_{i=1}^{s} A_i × B_i` with the nonempty `A_i` pairwise disjoint and the nonempty `B_i` pairwise
disjoint (`s = 0` allowed: the zero matrix). Xie, §10, pp.12–13 (PDF pp.13–14): "A relation with
support of this form, without the rank requirement, is called rectangular." -/
def RectangularSupport {R α β : Type} [Zero R] [LT R] (M : α → β → R) : Prop :=
  ∃ (s : ℕ) (A : Fin s → Set α) (B : Fin s → Set β),
    (∀ i, (A i).Nonempty) ∧ (∀ i, (B i).Nonempty) ∧
    Pairwise (fun i j => Disjoint (A i) (A j)) ∧ Pairwise (fun i j => Disjoint (B i) (B j)) ∧
    ∀ a b, 0 < M a b ↔ ∃ i, a ∈ A i ∧ b ∈ B i

/-- A nonnegative matrix `M` is **block-rank-one**: its positive support is a disjoint union
`⋃_{i=1}^{s} A_i × B_i` as in `RectangularSupport`, and the restriction of `M` to each block
`A_i × B_i` has rank one. Xie, §10, pp.12–13 (PDF pp.13–14). The zero matrix is included (`s = 0`).

**Formalization Note.** Every entry of a block is positive, so the block has rank one (over the
fraction field, e.g. `ℚ` for integer matrices or `ℝ` for real ones) exactly when all its `2 × 2`
minors vanish; the definition states the minors. -/
def BlockRankOne {R α β : Type} [Zero R] [LT R] [Mul R] (M : α → β → R) : Prop :=
  ∃ (s : ℕ) (A : Fin s → Set α) (B : Fin s → Set β),
    (∀ i, (A i).Nonempty) ∧ (∀ i, (B i).Nonempty) ∧
    Pairwise (fun i j => Disjoint (A i) (A j)) ∧ Pairwise (fun i j => Disjoint (B i) (B j)) ∧
    (∀ a b, 0 < M a b ↔ ∃ i, a ∈ A i ∧ b ∈ B i) ∧
    ∀ i, ∀ a ∈ A i, ∀ a' ∈ A i, ∀ b ∈ B i, ∀ b' ∈ B i, M a b * M a' b' = M a b' * M a' b

/-- The tuple of `D^k` whose coordinates, grouped by `e : Fin k ≃ Fin r ⊕ Fin s ⊕ Fin t` into
three groups, are `a ∈ D^r`, `b ∈ D^s` and `c ∈ D^t`. -/
def groupTuple {D : Type} {k r s t : ℕ} (e : Fin k ≃ Fin r ⊕ Fin s ⊕ Fin t)
    (a : Fin r → D) (b : Fin s → D) (c : Fin t → D) : Fin k → D :=
  fun j => Sum.elim a (Sum.elim b c) (e j)

/-- The **witness-count matrix** of `R ⊆ D^k` for the coordinate grouping `e` into `(x, y, z)`:
`M_R(a, b) = |{c ∈ D^t : (a, b, c) ∈ R}|` for `a ∈ D^r`, `b ∈ D^s`. Xie, §10, p.13 (PDF p.14). -/
noncomputable def witnessMatrix {D : Type} {k r s t : ℕ} (R : Set (Fin k → D))
    (e : Fin k ≃ Fin r ⊕ Fin s ⊕ Fin t) (a : Fin r → D) (b : Fin s → D) : ℕ :=
  Nat.card {c : Fin t → D // groupTuple e a b c ∈ R}

/-- `H` is **strongly balanced**: for every `R ∈ pp(H)` of any arity `k` and every choice and
ordering of three coordinate groups `x, y, z` with `x, y` nonempty and `z` possibly empty, the
witness-count matrix `M_R` is block-rank-one over the integers. Xie, §10, p.13 (PDF p.14): "This
is an integer condition. Reducing the entries modulo a prime is not part of its definition."

**Formalization Note.** A grouping is an equivalence `Fin k ≃ Fin r ⊕ Fin s ⊕ Fin t` with
`r, s ≥ 1`, `t ≥ 0`; ranging over all of them is "any choice and ordering of the three coordinate
groups". -/
def StronglyBalanced {D : Type} [Fintype D] (H : Template D) : Prop :=
  ∀ (k : ℕ) (R : Set (Fin k → D)), PPDefinable H R →
    ∀ (r s t : ℕ) (e : Fin k ≃ Fin r ⊕ Fin s ⊕ Fin t), 1 ≤ r → 1 ≤ s →
      BlockRankOne (witnessMatrix R e)

/-- The four-ary **three-state parity relation** `Q_C` for a three-element `C = {c₀, c₁, d} ⊆ D`
with doubled fibre `C \ {d}`: with `q(c₀) = q(c₁) = 0`, `q(d) = 1`,
`Q_C = {(z₁, z₂, z₃, z₄) ∈ C⁴ : q(z₁) ⊕ q(z₂) ⊕ q(z₃) ⊕ q(z₄) = 0}`. Xie, p.1 (PDF p.2) and §11,
p.16 (PDF p.17).

**Formalization Note.** The parity of `q(z₁) + ⋯ + q(z₄)` is the parity of the number of
coordinates equal to `d`. The relation is meaningful for `C.card = 3` and `d ∈ C`; every statement
using it assumes both. -/
def Q {D : Type} [DecidableEq D] (C : Finset D) (d : D) : Set (Fin 4 → D) :=
  {z | (∀ j, z j ∈ C) ∧ Even (Finset.univ.filter (fun j => z j = d)).card}

end ConsModCount


