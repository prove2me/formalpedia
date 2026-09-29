-- Prove2me | Definitions.Def_AlgebraicGeometry_TwoGluedProjectiveLinesNodeUnitModule
-- name    : AlgebraicGeometry_TwoGluedProjectiveLinesNodeUnitModule
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/2297c2a3-e5b3-5fbb-9a9c-da485a70b2fa
-- title:
--   Node-unit modules on two glued rational curves
-- statement:
--   Throughout, $\kappa$ is an algebraically closed field, $x : X \to \operatorname{Spec}\kappa$ a $\kappa$-scheme, and $M_1, M_2$ are objects of `CurveModel κ (RatFunc κ)`: smooth proper integral curves over $\kappa$ equipped with an identification of their function field with $\kappa(t)$ under which closed points correspond bijectively to the places of $\kappa(t)/\kappa$. They are mapped into $X$ by $i_1, i_2$, compatibly with the structure morphisms ($i_1$ followed by $x$ equals $M_1.\mathrm{toBase}$, and likewise for $i_2$); $a, b : \mathrm{Fin}\,s \to \kappa^{\times}$ record the gluing parameters, and $h : T \to \operatorname{Spec}\kappa$ is a further base.
--
--   For $c \in \kappa$, `pointAt M c` is the section of $M.\mathrm{toBase}$ corresponding, under the bijection `pointEquivPlace` between $\kappa$-points and places, to the place of $\kappa(t)$ cut out by $t - c$. `nodeSectionFst` and `nodeSectionSnd` are the resulting constant sections $T \to M_1.C \times_\kappa T$ and $T \to M_2.C \times_\kappa T$ at the points $a_i$ and $b_i$ (given by `rigSection`: first component $T \to \operatorname{Spec}\kappa \to M_j.C$, second the identity of $T$). For an open $W$ of $X \times_\kappa T$, `nodeLocus i W` is the open subset of $T$ on which both node sections land in the preimage of $W$ under the respective morphisms $i_j \times \mathrm{id}_T$ (`curveChange`), namely the intersection of the two preimages.
--
--   Given units $u_i \in \Gamma(T,\mathcal O_T)^{\times}$, sections $f$ over $(i_1\times \mathrm{id}_T)^{-1}W$ and $g$ over $(i_2\times \mathrm{id}_T)^{-1}W$, `NodeCondition` asserts the equality, on `nodeLocus i W`, of the pullback of $f$ along the $i$-th first node section with $u_i$ (restricted from $\Gamma(T,\top)$) times the pullback of $g$ along the $i$-th second node section. Finally, `IsNodeUnitModule u M`, for a sheaf of modules $M$ on $X \times_\kappa T$, asserts the existence of maps $j_1, j_2$ from $M$ to the pushforwards along $i_1\times\mathrm{id}_T$ and $i_2\times\mathrm{id}_T$ of the respective unit (structure-sheaf) modules such that, for every open $W$, the map $m \mapsto (j_1 m, j_2 m)$ on $\Gamma(M,W)$ is injective and its image is exactly the set of pairs satisfying `NodeCondition` for all $i$. Thus the predicate characterises $M$ as the sheaf of pairs of functions on the two components agreeing at each node up to the unit $u_i$; it is a condition on a given $M$, stated section-wise, with no invertibility of $M$ demanded.
--
--   **Relation to Mathlib.** Mathlib has no notion of modules presented by gluing data along nodes; this is the project's own predicate, phrased using Mathlib's `SheafOfModules.unit`, `Scheme.Modules.pushforward` and scheme-theoretic pullbacks, together with the project's `CurveModel`, `rigSection` and `curveChange`.
--
--   **Where it is used.** These definitions describe line bundles and structure sheaves on a curve obtained by gluing two projective lines transversally at $s$ nodes, as a sheaf of pairs of functions on the components congruent at the nodes up to units. They support the computations with the relative Picard functor and with Néron models of Jacobians of curves with such degenerate fibres.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_TwoGluedProjectiveLinesNodeUnitModule.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
  NeronModelInfra

namespace AlgebraicGeometry.TwoGluedProjectiveLines

variable {κ : Type u} [Field κ] [IsAlgClosed κ]
  {X : Scheme.{u}} (x : X ⟶ Spec (.of κ))
  (M₁ M₂ : CurveModel κ (RatFunc κ)) (i₁ : M₁.C ⟶ X) (i₂ : M₂.C ⟶ X)
  (hi₁ : i₁ ≫ x = M₁.toBase) (hi₂ : i₂ ≫ x = M₂.toBase)
  {s : ℕ} (a b : Fin s → κˣ)
  {T : Scheme.{u}} (h : T ⟶ Spec (.of κ))

def pointAt (M : CurveModel κ (RatFunc κ)) (c : κ) : SchemeHomOver (𝟙 (Spec (.of κ))) M.toBase :=
  M.pointEquivPlace.symm (RationalFunctionField.placeOfPoint κ c)

def nodeSectionFst (i : Fin s) : T ⟶ pullback M₁.toBase h :=
  rigSection M₁.toBase h (pointAt M₁ (a i : κ))

def nodeSectionSnd (i : Fin s) : T ⟶ pullback M₂.toBase h :=
  rigSection M₂.toBase h (pointAt M₂ (b i : κ))

def nodeLocus (i : Fin s) (W : (pullback x h).Opens) : T.Opens :=
  (nodeSectionFst M₁ a h i) ⁻¹ᵁ ((curveChange i₁ hi₁ h) ⁻¹ᵁ W) ⊓
    (nodeSectionSnd M₂ b h i) ⁻¹ᵁ ((curveChange i₂ hi₂ h) ⁻¹ᵁ W)

def NodeCondition (u : Fin s → Γ(T, ⊤)ˣ) (W : (pullback x h).Opens) (i : Fin s)
    (f : Γ(pullback M₁.toBase h, (curveChange i₁ hi₁ h) ⁻¹ᵁ W))
    (g : Γ(pullback M₂.toBase h, (curveChange i₂ hi₂ h) ⁻¹ᵁ W)) : Prop :=
  (nodeSectionFst M₁ a h i).appLE ((curveChange i₁ hi₁ h) ⁻¹ᵁ W)
      (nodeLocus x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h i W) inf_le_left f =
    T.presheaf.map (homOfLE le_top).op (u i : Γ(T, ⊤)) *
      (nodeSectionSnd M₂ b h i).appLE ((curveChange i₂ hi₂ h) ⁻¹ᵁ W)
        (nodeLocus x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h i W) inf_le_right g

def IsNodeUnitModule (u : Fin s → Γ(T, ⊤)ˣ) (M : (pullback x h).Modules) : Prop :=
  ∃ (j₁ : M ⟶ (Scheme.Modules.pushforward (curveChange i₁ hi₁ h)).obj
      (SheafOfModules.unit (pullback M₁.toBase h).ringCatSheaf))
    (j₂ : M ⟶ (Scheme.Modules.pushforward (curveChange i₂ hi₂ h)).obj
      (SheafOfModules.unit (pullback M₂.toBase h).ringCatSheaf)),
    ∀ W : (pullback x h).Opens,
      Function.Injective (fun m : Γ(M, W) => (j₁.app W m, j₂.app W m)) ∧
      Set.range (fun m : Γ(M, W) => (j₁.app W m, j₂.app W m)) =
        {fg | ∀ i : Fin s, NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u W i fg.1 fg.2}

end AlgebraicGeometry.TwoGluedProjectiveLines

end


