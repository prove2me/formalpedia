-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_SurjOfCover
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_SurjOfCover
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:26.580205+00:00
-- url     : https://prove2.me/theorems/e6a4db4d-6e23-4080-accf-fa24528102cc
-- title:
--   Surj Of Cover
-- statement:
--   Definitions and structural lemmas for Surj Of Cover, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/SurjOfCover.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
namespace GluingInclusion
variable {G B : Scheme.{0}} (q : G ⟶ B) {X : Type} [AddCommMonoid X] {W : B.Opens}
  (φ : ∀ V : B.Opens, V ≤ W → (Multiplicative X →* Γ(G, q ⁻¹ᵁ V)))
abbrev cm (V : B.Opens) (h : V ≤ W) : AddMonoidAlgebra Γ(B, V) X →+* Γ(G, q ⁻¹ᵁ V) :=
  AddMonoidAlgebra.liftNCRingHom (q.app V).hom (φ V h) (fun _ _ => Commute.all _ _)
variable (hnat : ∀ (V₁ V₂ : B.Opens) (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W) (h : V₁ ≤ V₂)
    (x : Multiplicative X),
    φ V₁ h₁ x = (G.presheaf.map (homOfLE (q.preimage_mono h)).op).hom (φ V₂ h₂ x))
end GluingInclusion
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf


