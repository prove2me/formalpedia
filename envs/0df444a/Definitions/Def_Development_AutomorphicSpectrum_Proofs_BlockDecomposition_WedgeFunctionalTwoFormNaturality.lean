-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeFunctionalTwoFormNaturality
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeFunctionalTwoFormNaturality
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T22:15:14.472306+00:00
-- url     : https://prove2.me/theorems/54e40462-98ae-4088-8931-5339f052fe49
-- title:
--   Wedge Functional Two Form Naturality
-- statement:
--   Definitions and structural lemmas for Wedge Functional Two Form Naturality, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeFunctionalTwoFormNaturality.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
namespace GlobalTheory.CompanionTheory.HodgeTwoForm
section Generic
variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {n : ℕ}
def L2 (L : Fin n → Module.Dual A M) (i j : Fin n) : ⋀[A]^2 M →ₗ[A] A :=
  exteriorPower.pairingDual A M 2 (exteriorPower.ιMulti A 2 ![L i, L j])
def wb : M →ₗ[A] M →ₗ[A] ⋀[A]^2 M :=
  LinearMap.mk₂ A (fun a b ↦ exteriorPower.ιMulti A 2 ![a, b])
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply, add_mul]))
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply]))
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply, mul_add]))
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply]))
end Generic
section Forms
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
def wedgeAt (T : C) : Glob1 F [⋀^Fin 2]→ₗ[R] Om R (F.obj T) 2 where
  toMultilinearMap := ((exteriorPower.ιMulti (F.obj T) 2 (M := Ω[F.obj T⁄R])).toMultilinearMap.restrictScalars
    R).compLinearMap fun _ ↦ evForm F T
  map_eq_zero_of_eq' v i j hv hij :=
    (exteriorPower.ιMulti (F.obj T) 2 (M := Ω[F.obj T⁄R])).map_eq_zero_of_eq _
      (congrArg (evForm F T) hv) hij
def nu : ⋀[R]^2 (Glob1 F) →ₗ[R] W0 F 2 :=
  LinearMap.pi fun T ↦ exteriorPower.alternatingMapLinearEquiv (wedgeAt F T)
variable {F}
def Lf (hP : Par F) (l : Module.Dual R (Glob1 F)) (T : C) : Module.Dual (F.obj T) Ω[F.obj T⁄R] :=
  (hP T).lift (Algebra.linearMap R (F.obj T) ∘ₗ l)
end Forms
end GlobalTheory.CompanionTheory.HodgeTwoForm


