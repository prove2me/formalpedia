-- Prove2me | Definitions.Def_AdaDiscRL_HierPartition
-- name    : AdaDiscRL_HierPartition
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:25:59.813378+00:00
-- url     : https://prove2.me/theorems/9e04142a-2d13-4614-9439-2db5f4d41a75
-- title:
--   Hierarchical partition of $\mathcal S\times\mathcal A$
-- statement:
--   A **hierarchical partition** of $\mathcal S\times\mathcal A$ is a family of regions $\mathcal P_\ell$ for levels $\ell=0,\dots,L_{\max}$ such that
--
--   1. every region is a product $B=\mathcal S(B)\times\mathcal A(B)$;
--   2. $\mathcal P_0=\{\mathcal S\times\mathcal A\}$;
--   3. each level consists of disjoint regions covering $\mathcal S\times\mathcal A$;
--   4. $\mathrm{diam}(B)=2^{-\ell}$ for $B\in\mathcal P_\ell$ (diameter in $\mathcal D$);
--   5. centers $(\tilde x(B),\tilde a(B))\in B$ of distinct regions of one level are at distance at least $2^{-\ell}$;
--   6. each $B\in\mathcal P_\ell$, $\ell\ge1$, lies strictly inside a parent region of level $\ell-1$; the children of a region are the regions whose parent it is;
--   7. the state cells $\mathcal S(\mathcal P_\ell)=\{\mathcal S(B):B\in\mathcal P_\ell\}$ form a partition of $\mathcal S$, $\tilde x(B)$ depends only on $\mathcal S(B)$, and each state cell of level $\ell<L_{\max}$ has exactly $2^{d_{\mathcal S}}$ sub-cells at level $\ell+1$;
--   8. regions are measurable.
--
--   The canonical example is the dyadic partition of $[0,1]^{d_{\mathcal S}}\times[0,1]^{d_{\mathcal A}}$ under the $\ell_\infty$ metric. AdaMB and AdaQL maintain an adaptive sub-tree of such a partition.
--
--   **Formalization Note** Regions are indexed by a type of nodes. Definition 3.1 prints $\mathrm{diam}(B)\le2^{-\ell}$; the exact value $2^{-\ell}$ (p.36, p.39, p.53), the center and state-cell clauses (p.15, p.17) and the $2^{d_{\mathcal S}}$ sub-cells (p.19) are stated elsewhere in the source and are part of the structure here. The diameter is a supremum (half-open dyadic cells do not attain it). Helper definitions: `region`, `diam`, `cellsAt` ($\mathcal S(\mathcal P_\ell)$), `IsAncestorOrSelf`.
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, Definition 3.1, p.14; additions from p.15, p.17, p.19, p.36 (Table 2), p.39, p.53

import Mathlib

namespace AdaDiscRL

/-- Diameter of a region `B ⊆ S × A` in the metric `D` (arXiv:2110.15843v3, p.10:
"`diam(B) = max{D((x,a),(y,b)) | (x,a),(y,b) ∈ B}`"), taken as a supremum (the regions of the
paper's own example, half-open dyadic cubes, do not attain it). -/
noncomputable def diamD {S A : Type*} (D : S × A → S × A → ℝ) (B : Set (S × A)) : ℝ :=
  sSup {t | ∃ p ∈ B, ∃ q ∈ B, t = D p q}

/-- **Hierarchical partition of `S × A`** (arXiv:2110.15843v3, Definition 3.1, p.14), with levels
`ℓ = 0, …, Lmax`. Regions are indexed by a type `ι` of nodes; node `B` has level `level B`, region
`sCell B ×ˢ aCell B` (= `S(B) × A(B)`), center `center B = (x̃(B), ã(B))`, and (for `level B ≥ 1`)
parent `parent B`.

Definition 3.1's clauses: regions are products; `P_0 = {S × A}`; each level covers `S × A` and
consists of disjoint regions; `diam(B) ≤ 2^{−ℓ}` (here `= 2^{−ℓ}`, see below); centers of distinct
regions of one level are at `D`-distance `≥ 2^{−ℓ}`; each region of level `ℓ ≥ 1` lies strictly
inside its parent of level `ℓ − 1`.

**Formalization Note.** Additions, each stated in the source (reading R1):
* `diam(B) = 2^{−ℓ(B)}` exactly (p.36 Table 2, "`ℓ(B)` … equivalent to `log₂(D(S×A)/D(B))`",
  "dyadic cubes of `S` of diameter `2^{−ℓ}`"; p.39 "using `diam(B_ℓ) = 2^{−ℓ}`"; p.53); in
  particular `S × A` has diameter `1` (p.10).
* centers lie in their regions (p.15, "Center(B)") and `x̃(B)` depends only on `S(B)`
  (`sCenter`, p.17 writes `x̃(A)` for a state cell `A`);
* the state cells of one level form a partition of `S` (p.15, Eq. (5) and `S(P_ℓ)`; p.19), and
  each state cell of level `ℓ < Lmax` has exactly `2^{d_S}` sub-cells at level `ℓ + 1` (p.19:
  "each element of `S(P_{ℓ(B^{par})})` has `2^{d_S}` children");
* the children of a node (a finite set) are the nodes whose parent it is (p.13, line 12);
* regions are measurable (needed for the transition and action laws to see them). -/
structure HierPartition (S A ι : Type*) [MeasurableSpace S] [MeasurableSpace A]
    (D : S × A → S × A → ℝ) (dS Lmax : ℕ) where
  level : ι → ℕ
  sCell : ι → Set S
  aCell : ι → Set A
  center : ι → S × A
  sCenter : Set S → S
  root : ι
  parent : ι → ι
  children : ι → Finset ι
  level_le : ∀ B, level B ≤ Lmax
  level_root : level root = 0
  eq_root : ∀ B, level B = 0 → B = root
  sCell_root : sCell root = Set.univ
  aCell_root : aCell root = Set.univ
  cover : ∀ ℓ ≤ Lmax, ∀ p : S × A, ∃ B, level B = ℓ ∧ p ∈ sCell B ×ˢ aCell B
  disjoint : ∀ B B', level B = level B' → B ≠ B' →
    Disjoint (sCell B ×ˢ aCell B) (sCell B' ×ˢ aCell B')
  diam_eq : ∀ B, diamD D (sCell B ×ˢ aCell B) = (2 : ℝ) ^ (-(level B : ℤ))
  center_mem : ∀ B, center B ∈ sCell B ×ˢ aCell B
  center_sep : ∀ B B', level B = level B' → B ≠ B' →
    (2 : ℝ) ^ (-(level B : ℤ)) ≤ D (center B) (center B')
  parent_level : ∀ B, 1 ≤ level B → level (parent B) + 1 = level B
  parent_ssubset : ∀ B, 1 ≤ level B →
    sCell B ×ˢ aCell B ⊂ sCell (parent B) ×ˢ aCell (parent B)
  mem_children : ∀ B C, C ∈ children B ↔ (1 ≤ level C ∧ parent C = B)
  sCell_eq_or_disjoint : ∀ B B', level B = level B' →
    sCell B = sCell B' ∨ Disjoint (sCell B) (sCell B')
  sCenter_spec : ∀ B, (center B).1 = sCenter (sCell B)
  sCell_children_card : ∀ B, level B < Lmax →
    {X : Set S | ∃ C, level C = level B + 1 ∧ sCell C = X ∧ X ⊆ sCell B}.ncard = 2 ^ dS
  measurableSet_sCell : ∀ B, MeasurableSet (sCell B)
  measurableSet_aCell : ∀ B, MeasurableSet (aCell B)

namespace HierPartition

variable {S A ι : Type*} [MeasurableSpace S] [MeasurableSpace A]
  {D : S × A → S × A → ℝ} {dS Lmax : ℕ}

/-- The region `B = S(B) × A(B)` of a node. -/
def region (P : HierPartition S A ι D dS Lmax) (B : ι) : Set (S × A) :=
  P.sCell B ×ˢ P.aCell B

/-- `diam(B)`, the `D`-diameter of the region of node `B`. -/
noncomputable def diam (P : HierPartition S A ι D dS Lmax) (B : ι) : ℝ :=
  diamD D (P.region B)

/-- The state partition at level `ℓ`, `S(P_ℓ) = {S(B) | B ∈ P_ℓ}` (Eq. (5), p.15). -/
def cellsAt (P : HierPartition S A ι D dS Lmax) (ℓ : ℕ) : Set (Set S) :=
  {X | ∃ B, P.level B = ℓ ∧ P.sCell B = X}

/-- `A` is an ancestor of `B` or `B` itself (iterated parents). -/
def IsAncestorOrSelf (P : HierPartition S A ι D dS Lmax) (A B : ι) : Prop :=
  ∃ m : ℕ, m ≤ P.level B ∧ P.parent^[m] B = A

end HierPartition

end AdaDiscRL


