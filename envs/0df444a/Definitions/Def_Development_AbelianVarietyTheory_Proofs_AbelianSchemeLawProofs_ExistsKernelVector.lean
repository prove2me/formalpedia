-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKernelVector
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKernelVector
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:56.377028+00:00
-- url     : https://prove2.me/theorems/7381d50e-4bc8-44ec-a405-5cb774386727
-- title:
--   Exists Kernel Vector
-- statement:
--   Definitions and structural lemmas for Exists Kernel Vector, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsKernelVector.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
namespace GlobalTheory.AbLaw.Seesaw
variable {X X' Y : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']
section
variable {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X} (P : Perf f M)
def loc (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R')) (v : Fin P.a → R') (i : P.I) : Γ(X', π ⁻¹ᵁ P.W i) :=
  ∑ k, cst f' (π ⁻¹ᵁ P.W i) (v k) * (π.app (P.W i)).hom (P.u k i)
def loc₀ (v : Fin P.a → R) (i : P.I) : Γ(X, P.W i) := ∑ k, cst f (P.W i) (v k) * P.u k i
variable {g : R →+* R'} {π : X' ⟶ X} {f' : X' ⟶ Spec (CommRingCat.of R')}
  (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
include h
end
end GlobalTheory.AbLaw.Seesaw


