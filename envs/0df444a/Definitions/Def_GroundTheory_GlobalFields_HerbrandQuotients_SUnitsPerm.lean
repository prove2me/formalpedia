-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
-- name    : GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:39:43.679393+00:00
-- url     : https://prove2.me/theorems/41fa1680-b1cd-4f97-b30b-cf80aece31ce
-- title:
--   SUnits Perm
-- statement:
--   Definitions and structural lemmas for SUnits Perm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/SUnitsPerm.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_LatticeBridge
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Galois
import Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_coeff_permOfFun
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_normHom_apply
import Theorems.Thm_GroundTheory_Global_piRep_apply
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
import Theorems.Thm_P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.SemiLocal.tensorHomeomorph_apply
attribute [local simp] GroundTheory.Global.coeff_permOfFun
attribute [local simp] GroundTheory.Global.cycSub_apply
attribute [local simp] GroundTheory.Global.normHom_apply
attribute [local simp] GroundTheory.Global.piRep_apply
attribute [local simp] GroundTheory.GroupCoh.restrictEnd_apply
attribute [local simp] P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7


set_option autoImplicit false
namespace GroundTheory.Global
open MulAction NumberField IsDedekindDomain
open scoped Pointwise
noncomputable section
section FunPerm
variable (k G X : Type*) [CommRing k] [Group G] [MulAction G X]
def funPermRep : Representation k G (X → k) where
  toFun g := LinearMap.funLeft k k (fun x => g⁻¹ • x)
  map_one' := by
    ext f x
    simp [LinearMap.funLeft_apply]
  map_mul' g h := by
    ext f x
    simp [LinearMap.funLeft_apply, mul_smul]
variable {k G X}
@[simp]
theorem funPermRep_apply (g : G) (f : X → k) (x : X) : funPermRep k G X g f x = f (g⁻¹ • x) :=
  rfl
def funEquivMonoidAlgebra [Finite X] : (X → ℤ) ≃+ MonoidAlgebra ℤ X where
  toFun := permOfFun
  invFun f x := f.coeff x
  left_inv F := funext fun x => coeff_permOfFun F x
  right_inv f := by
    ext x
    exact coeff_permOfFun _ x
  map_add' F F' := by
    ext x
    simp
end FunPerm
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
section Infinite
end Infinite
section Finite
def placeBelow (w : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum (𝓞 K) :=
  ⟨w.asIdeal.under (𝓞 K), inferInstance, Ideal.under_ne_bot (𝓞 K) w.ne_bot⟩
instance (w : HeightOneSpectrum (𝓞 L)) :
    w.asIdeal.LiesOver (placeBelow (K := K) w).asIdeal :=
  ⟨rfl⟩
variable (S : Set (HeightOneSpectrum (𝓞 L)))
@[reducible] def stableMulAction (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) : MulAction (L ≃ₐ[K] L) S where
  smul g w := ⟨g • w.1, hS g w.1 w.2⟩
  one_smul w := Subtype.ext (one_smul _ w.1)
  mul_smul g h w := Subtype.ext (mul_smul g h w.1)
end Finite
end
end GroundTheory.Global


