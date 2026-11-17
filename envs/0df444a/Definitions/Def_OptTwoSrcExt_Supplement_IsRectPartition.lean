-- Prove2me | Definitions.Def_OptTwoSrcExt_Supplement_IsRectPartition
-- name    : OptTwoSrcExt_Supplement_IsRectPartition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:36:30.745291+00:00
-- url     : https://prove2.me/theorems/2a9d912a-d348-436d-9cfc-6a52be217383
-- title:
--   Product-rectangle partitions, leaf masses, entropy loss and distance from uniform on the output affine hull
-- statement:
--   Let $X$ be uniform on a nonempty finite set $A_0$ and $Y$ uniform on a nonempty finite set $B_0$, independent, and let $F(x,y)\in\mathbb F_2^D$.
--
--   1. A **finite partition of $A_0\times B_0$ into product rectangles** is a finite family of nonempty rectangles $A'\times B'\subseteq A_0\times B_0$ (the **leaves**) such that every point of $A_0\times B_0$ lies in exactly one leaf.
--   2. The **mass** of a leaf is $\Pr[(X,Y)\in A'\times B']=|A'||B'|/(|A_0||B_0|)$.
--   3. Conditioned on a leaf, $X$ is uniform on $A'$ and $Y$ uniform on $B'$; the sources **lose at most $L$ bits of min-entropy** on the leaf if $\log_2(|A_0|/|A'|)\le L$ and $\log_2(|B_0|/|B'|)\le L$.
--   4. The **exact affine hull** of the leaf is the $\mathbb F_2$-affine span $W$ of $F(A'\times B')$, and the distance of the conditional output from uniform on it is
--   $$\tfrac12\sum_{z\in\mathbb F_2^D}\Big|\Pr\big[F(X,Y)=z\mid (X,Y)\in A'\times B'\big]-\frac{\mathbf 1_W(z)}{|W|}\Big| .$$
--
--   These are the objects of the regularization theorems (Theorems 2.30 and 5.5).
--
--   **Formalization Note** The partition is not required to be computable. Logarithms are base 2.
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), Theorem 2.30, p.27 (PDF p.29); Theorem 5.5, p.103 (PDF p.105); Definition 2.7, p.15 (PDF p.17)

import Mathlib

namespace OptTwoSrcExt.Supplement

/-- **Finite partition of `A₀ × B₀` into product rectangles (leaves).**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Theorem 2.30, printed p.27 (PDF p.29): "there is a finite
partition into raw product rectangles"; Theorem 5.5, printed p.103 (PDF p.105): "a finite
deterministic product-rectangle partition".

`IsRectPartition A₀ B₀ Al Bl`: the leaves `Al i × Bl i` (`i` in a finite index type) are nonempty
product rectangles inside `A₀ × B₀`, and every point of `A₀ × B₀` lies in exactly one leaf.

**Formalization Note.** The partition is not required to be computable (the paper: "The partition is
proof-only and need not be computed"). -/
def IsRectPartition {α β ι : Type*} (A₀ : Finset α) (B₀ : Finset β) (Al : ι → Finset α)
    (Bl : ι → Finset β) : Prop :=
  (∀ i, (Al i).Nonempty ∧ (Bl i).Nonempty ∧ Al i ⊆ A₀ ∧ Bl i ⊆ B₀) ∧
    ∀ x ∈ A₀, ∀ y ∈ B₀, ∃! i, x ∈ Al i ∧ y ∈ Bl i

/-- **The exact affine hull of the output on a rectangle**: the `𝔽₂`-affine span of
`F(A' × B') ⊆ 𝔽₂^D`, as a set. -/
def outHull {α β : Type*} {D : ℕ} (F : α → β → (Fin D → ZMod 2)) (A' : Finset α)
    (B' : Finset β) : Set (Fin D → ZMod 2) :=
  (affineSpan (ZMod 2) {z | ∃ x ∈ A', ∃ y ∈ B', F x y = z} : Set (Fin D → ZMod 2))

/-- **Distance of the conditional output on a leaf from uniform on its exact affine hull.**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Theorem 2.30, printed p.27 (PDF p.29): "On every leaf, the
conditional output is within 2^{D/2−H−1} of uniform on its exact affine hull"; Theorem 5.5 (i),
printed p.103 (PDF p.105); statistical distance ∆(P, Q) = ½ Σ_z |P(z) − Q(z)| (Definition 2.7).

For independent flat `X` (uniform on `A₀`) and `Y` (uniform on `B₀`), conditioning on the leaf
`A' × B'` makes `(X, Y)` uniform on `A' × B'`, so the conditional output law is
`P(z) = |{(x, y) ∈ A' × B' : F(x, y) = z}| / (|A'| |B'|)`. `leafHullDist F A' B'` is
`½ Σ_z |P(z) − 1_W(z)/|W||`, `W = outHull F A' B'`. -/
noncomputable def leafHullDist {α β : Type*} {D : ℕ} (F : α → β → (Fin D → ZMod 2))
    (A' : Finset α) (B' : Finset β) : ℝ := by
  classical
  exact (1 / 2 : ℝ) * ∑ z : Fin D → ZMod 2,
    |(((A' ×ˢ B').filter fun p => F p.1 p.2 = z).card : ℝ) / ((A'.card : ℝ) * B'.card) -
      (if z ∈ outHull F A' B' then 1 / ((outHull F A' B').ncard : ℝ) else 0)|

/-- **Mass of a leaf** `Pr[(X, Y) ∈ A' × B'] = |A'| |B'| / (|A₀| |B₀|)` for independent flat
`X` uniform on `A₀`, `Y` uniform on `B₀`. -/
noncomputable def leafMass {α β : Type*} (A₀ : Finset α) (B₀ : Finset β) (A' : Finset α)
    (B' : Finset β) : ℝ :=
  ((A'.card : ℝ) * B'.card) / ((A₀.card : ℝ) * B₀.card)

/-- **Both sources lose at most `L` bits of min-entropy on the leaf `A' × B'`**:
`log₂(|A₀|/|A'|) ≤ L` and `log₂(|B₀|/|B'|) ≤ L`. Conditioned on the leaf, the flat source `X`
(uniform on `A₀`, min-entropy `log₂|A₀|`) becomes uniform on `A'` (min-entropy `log₂|A'|`), and
likewise for `Y`. -/
def LosesAtMost {α β : Type*} (A₀ : Finset α) (B₀ : Finset β) (A' : Finset α) (B' : Finset β)
    (L : ℝ) : Prop :=
  Real.logb 2 ((A₀.card : ℝ) / A'.card) ≤ L ∧ Real.logb 2 ((B₀.card : ℝ) / B'.card) ≤ L

end OptTwoSrcExt.Supplement


