-- Prove2me | Definitions.Def_SetOptLattice_Existence_Supplement_WellPosedness
-- name    : SetOptLattice_Existence_Supplement_WellPosedness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:57:11.831902+00:00
-- url     : https://prove2.me/theorems/79ae8cb0-0e81-4893-b477-661e6f8c3a02
-- title:
--   Definitions 4.8–4.9 — minimizing nets and ordinary/plus well-posedness
-- statement:
--   Let $X$ be the real separated topological linear space of §4, $(Z,\preceq)$ a preordered set, $\Psi$ a family of monotone maps $Z\to\mathbb R\cup\{\pm\infty\}$, and $f:X\to\mathcal P(Z,\Psi)$. A net $M_i\subseteq X$ is $\Psi$-minimizing if
--   $$\forall\varepsilon>0,\quad\text{eventually}_i\quad M_i\in\operatorname{Sol}(f,\varepsilon,\Psi).$$
--   The function $f$ is $(0,\Psi)$-well-posed if an exact solution exists and every $\Psi$-minimizing net has a Hausdorff-convergent subnet with limit in $\operatorname{Sol}(f,0,\Psi)$. The $(0+,\Psi)$ notion changes only the existence and limit family to $\operatorname{Sol}(f,0+,\Psi)$, retaining the same minimizing nets.
--
--   Well-posedness is defined by Definition 4.9, independently of the conditions in Theorem 4.12. It imposes no compactness, uniqueness, metric, or chosen rate. The limit may depend on the net. The paper writes "for all $i>i_\varepsilon$"; this is read as the usual tail $i\ge i_\varepsilon$, i.e. eventually along the net. Nontrivial filters on the set-valued carrier represent arbitrary directed nets; the explicit net predicate uses the image of its tail filter. The existence conjunct prevents vacuous truth when there are no exact solutions.
-- source:
--   Crespi, Hamel, Rocca, Schrage, arXiv:1812.03300v1, p. 26, Definitions 4.8 and 4.9

import Mathlib
import Definitions.Def_SetOptLattice_Existence_Supplement_SolutionFamilies
import Definitions.Def_SetOptLattice_Existence_Supplement_HausdorffNets

namespace SetOptLattice.Existence.Supplement

open Set Filter Topology

/-- Definition 4.8, p. 26 in image-tail-filter form. -/
def IsMinimizingFilter {X Z : Type*} (Ψ : Set (Z → EReal)) (f : X → Set Z)
    (F : Filter (Set X)) : Prop :=
  ∀ ε : ℝ, 0 < ε → Sol Ψ f ε ∈ F

/-- Definition 4.8 for any nonempty directed index type, with no convergence rate.
The nonempty/directed assumptions belong to a net's caller, not this eventual predicate. -/
def IsMinimizingNet {X Z ι : Type*} [Preorder ι]
    (Ψ : Set (Z → EReal)) (f : X → Set Z) (M : ι → Set X) : Prop :=
  IsMinimizingFilter Ψ f (Filter.map M Filter.atTop)

/-- Definition 4.9: existence AND subnet convergence for every minimizing net.
Quantifying nontrivial filters on the fixed set-valued carrier represents all nets,
including arbitrarily large directed index sets. It imposes no uniqueness of limit. -/
def IsWellPosed {X Z : Type*} [TopologicalSpace X] [AddZeroClass X]
    (Ψ : Set (Z → EReal)) (f : X → Set Z) : Prop :=
  (Sol Ψ f 0).Nonempty ∧
    ∀ F : Filter (Set X), F.NeBot → IsMinimizingFilter Ψ f F →
      HasHausdorffSubnetIn F (Sol Ψ f 0)

/-- The second notion in Definition 4.9: only the target solution family changes.
This is included to record the whole definition, and is not the target of Theorem 4.12. -/
def IsPlusWellPosed {X Z : Type*} [TopologicalSpace X] [AddZeroClass X]
    (Ψ : Set (Z → EReal)) (f : X → Set Z) : Prop :=
  (SolPlus Ψ f 0).Nonempty ∧
    ∀ F : Filter (Set X), F.NeBot → IsMinimizingFilter Ψ f F →
      HasHausdorffSubnetIn F (SolPlus Ψ f 0)

end SetOptLattice.Existence.Supplement


