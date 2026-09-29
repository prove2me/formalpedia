-- Prove2me | Definitions.Def_AlgebraicGeometry_TwoGluedCurvesNodeUnitModule
-- name    : AlgebraicGeometry_TwoGluedCurvesNodeUnitModule
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/abf2c50c-bbff-5507-87d8-e5ea2c4c942f
-- title:
--   Node-unit modules on two curves glued along node sections
-- statement:
--   Throughout, $\kappa$ is a field, $x\colon X\to\operatorname{Spec}\kappa$ is a $\kappa$-scheme, $c_1\colon C_1\to\operatorname{Spec}\kappa$ and $c_2\colon C_2\to\operatorname{Spec}\kappa$ are $\kappa$-schemes equipped with morphisms over $\kappa$, $i_1\colon C_1\to X$ and $i_2\colon C_2\to X$ (elements of the project's `SchemeHomOver`, i.e. morphisms together with a proof of commutation over $\operatorname{Spec}\kappa$), together with families $p_1,p_2$ indexed by a type $\iota$ of sections of $c_1$, resp. $c_2$, over $\operatorname{Spec}\kappa$, and a $\kappa$-scheme $h\colon T\to\operatorname{Spec}\kappa$.
--
--   `nodeSectionFst` and `nodeSectionSnd` are the sections $T\to C_1\times_\kappa T$ and $T\to C_2\times_\kappa T$ obtained from $p_1 j$, $p_2 j$ by the project's `rigSection`, namely the morphism with components $h$ followed by the given $\kappa$-point and $\mathrm{id}_T$. For an open $W$ of $X\times_\kappa T$, `nodeLocus` is the open subset of $T$ on which both $j$-th node sections land in the preimage of $W$ under the base-changed maps $\mathrm{curveChange}$, i.e. $i_1\times\mathrm{id}_T$ and $i_2\times\mathrm{id}_T$. Given units $u_j\in\Gamma(T,\mathcal O_T)^\times$, `NodeCondition` asserts, for sections $f$ over $(i_1\times\mathrm{id}_T)^{-1}W$ and $g$ over $(i_2\times\mathrm{id}_T)^{-1}W$, the equality $\sigma^{1*}_j f = u_j\cdot\sigma^{2*}_j g$ of sections over that node locus, all three terms being restricted there.
--
--   `IsNodeUnitModule u M`, for $M$ a sheaf of modules on $X\times_\kappa T$, is the predicate: there exist morphisms $j_1\colon M\to (i_1\times\mathrm{id}_T)_*\mathcal O$ and $j_2\colon M\to (i_2\times\mathrm{id}_T)_*\mathcal O$ into the pushforwards of the unit sheaves of modules such that, for every open $W$, the map $m\mapsto (j_1 m,\,j_2 m)$ on sections over $W$ is injective with image exactly the pairs satisfying the node condition at every $j\in\iota$. It is thus a condition on a presentation of $M$ as the fibre product of the two component structure sheaves along the prescribed gluing units, not a construction of such an $M$.
--
--   **Relation to Mathlib.** Built on Mathlib's `Scheme.Modules`, `SheafOfModules.unit` and `Scheme.Modules.pushforward`; Mathlib has no notion of modules glued across nodes with prescribed gluing units, so the predicates here are the project's own, as are the auxiliary `rigSection` and `curveChange` they use.
--
--   **Where it is used.** These definitions belong to the project's development of relative Picard functors, where line bundles on a curve obtained by gluing two components at finitely many $\kappa$-rational points are described by gluing units attached to the nodes; such descriptions control the multiplicative part of the Picard scheme of a nodal curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_TwoGluedCurvesNodeUnitModule.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

namespace AlgebraicGeometry.TwoGluedCurves

variable {κ : Type u} [Field κ]
  {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (.of κ))
  {c₁ : C₁ ⟶ Spec (.of κ)} {c₂ : C₂ ⟶ Spec (.of κ)}
  (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x)
  {ι : Type v} (p₁ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₁) (p₂ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₂)
  {T : Scheme.{u}} (h : T ⟶ Spec (.of κ))

def nodeSectionFst (j : ι) : T ⟶ pullback c₁ h :=
  rigSection c₁ h (p₁ j)

def nodeSectionSnd (j : ι) : T ⟶ pullback c₂ h :=
  rigSection c₂ h (p₂ j)

def nodeLocus (j : ι) (W : (pullback x h).Opens) : T.Opens :=
  (nodeSectionFst p₁ h j) ⁻¹ᵁ ((curveChange i₁.1 i₁.2 h) ⁻¹ᵁ W) ⊓
    (nodeSectionSnd p₂ h j) ⁻¹ᵁ ((curveChange i₂.1 i₂.2 h) ⁻¹ᵁ W)

def NodeCondition (u : ι → Γ(T, ⊤)ˣ) (W : (pullback x h).Opens) (j : ι)
    (f : Γ(pullback c₁ h, (curveChange i₁.1 i₁.2 h) ⁻¹ᵁ W))
    (g : Γ(pullback c₂ h, (curveChange i₂.1 i₂.2 h) ⁻¹ᵁ W)) : Prop :=
  (nodeSectionFst p₁ h j).appLE ((curveChange i₁.1 i₁.2 h) ⁻¹ᵁ W)
      (nodeLocus x i₁ i₂ p₁ p₂ h j W) inf_le_left f =
    T.presheaf.map (homOfLE le_top).op (u j : Γ(T, ⊤)) *
      (nodeSectionSnd p₂ h j).appLE ((curveChange i₂.1 i₂.2 h) ⁻¹ᵁ W)
        (nodeLocus x i₁ i₂ p₁ p₂ h j W) inf_le_right g

def IsNodeUnitModule (u : ι → Γ(T, ⊤)ˣ) (M : (pullback x h).Modules) : Prop :=
  ∃ (j₁ : M ⟶ (Scheme.Modules.pushforward (curveChange i₁.1 i₁.2 h)).obj
      (SheafOfModules.unit (pullback c₁ h).ringCatSheaf))
    (j₂ : M ⟶ (Scheme.Modules.pushforward (curveChange i₂.1 i₂.2 h)).obj
      (SheafOfModules.unit (pullback c₂ h).ringCatSheaf)),
    ∀ W : (pullback x h).Opens,
      Function.Injective (fun m : Γ(M, W) => (j₁.app W m, j₂.app W m)) ∧
      Set.range (fun m : Γ(M, W) => (j₁.app W m, j₂.app W m)) =
        {fg | ∀ j : ι, NodeCondition x i₁ i₂ p₁ p₂ h u W j fg.1 fg.2}

end AlgebraicGeometry.TwoGluedCurves

end


