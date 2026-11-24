-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
-- name    : GroundTheory_PAdicHodge_TiltAlgebra
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T11:39:55.297051+00:00
-- url     : https://prove2.me/theorems/40f76e8a-55b9-460a-9889-ea0ab653c721
-- title:
--   Tilt Algebra
-- statement:
--   Definitions and structural lemmas for Tilt Algebra, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltAlgebra.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltMap
import Theorems.Thm_GroundTheory_PAdicHodge_norm_tiltMap
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.PAdicHodge
section Functor
variable {K L M : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField L] [IsUltrametricDist L] [NontriviallyNormedField M] [IsUltrametricDist M]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField L p]
  [IsPerfectoidField M p]
omit [IsUltrametricDist K] [IsUltrametricDist L] [IsUltrametricDist M] in
theorem norm_comp_eq {φ : K →+* L} (hφ : ∀ x, ‖φ x‖ = ‖x‖) {ψ : L →+* M}
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (x : K) : ‖(ψ.comp φ) x‖ = ‖x‖ := by
  rw [RingHom.comp_apply, hψ, hφ]
variable (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (ψ : L →+* M) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
theorem preTiltMap_comp :
    preTiltMap p (ψ.comp φ) (norm_comp_eq hφ hψ) =
      (preTiltMap p ψ hψ).comp (preTiltMap p φ hφ) := by
  refine RingHom.ext fun x => Perfection.ext fun n => ?_
  rw [RingHom.comp_apply, coeff_preTiltMap, coeff_preTiltMap, coeff_preTiltMap]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (Perfection.coeff (ModP (normInteger K) p) p n x)
  rw [← ha, modPMap_mk, modPMap_mk, modPMap_mk]
  rfl
theorem tiltMap_comp :
    tiltMap p (ψ.comp φ) (norm_comp_eq hφ hψ) = (tiltMap p ψ hψ).comp (tiltMap p φ hφ) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (PreTilt (normInteger K) p)) ?_
  ext a
  simp only [RingHom.comp_apply, tiltMap_algebraMap]
  rw [preTiltMap_comp φ hφ ψ hψ]
  rfl
end Functor
section Density
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]
end Density
section Algebra
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p
instance tiltAlgebra : Algebra K♭ C♭ :=
  (tiltMap p (algebraMap K C) (norm_algebraMap' C)).toAlgebra
theorem algebraMap_tilt_eq :
    algebraMap K♭ C♭ = tiltMap p (algebraMap K C) (norm_algebraMap' C) :=
  rfl
theorem norm_algebraMap_tilt (x : K♭) : ‖algebraMap K♭ C♭ x‖ = ‖x‖ :=
  norm_tiltMap _ _ x
instance tiltNormedAlgebra : NormedAlgebra K♭ C♭ where
  norm_smul_le r x := by
    rw [Algebra.smul_def, norm_mul, norm_algebraMap_tilt]
end Algebra
section IntermediateField
variable {K C : Type*} [NontriviallyNormedField K] [NormedField C] [NormedAlgebra K C]
instance (F : IntermediateField K C) : NontriviallyNormedField F where
  __ := (inferInstance : NormedField F)
  non_trivial := by
    obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm K
    refine ⟨algebraMap K F c, ?_⟩
    change 1 < ‖((algebraMap K F c : F) : C)‖
    rw [IntermediateField.coe_algebraMap_apply, norm_algebraMap']
    exact hc
end IntermediateField
section TiltIntermediate
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p
variable (F : IntermediateField K C) [IsPerfectoidField F p]
local notation "F♭" => Tilt F NormedField.valuation (normInteger F) normInteger_integers p
omit [IsUltrametricDist K] [IsUltrametricDist C] in
theorem norm_val (x : F) : ‖(F.val : F →+* C) x‖ = ‖x‖ := rfl
variable (p) in

def tiltInclusion : F♭ →+* C♭ :=
  tiltMap p (F.val : F →+* C) (norm_val F)
theorem algebraMap_tilt_eq_comp :
    algebraMap K♭ C♭ = (tiltInclusion p F).comp
      (tiltMap p (algebraMap K F) (norm_algebraMap' F)) := by
  rw [algebraMap_tilt_eq, tiltInclusion, ← tiltMap_comp]
  rfl
variable (p) in

def tiltIntermediateField : IntermediateField K♭ C♭ where
  carrier := (tiltInclusion p F).fieldRange
  mul_mem' ha hb := Subfield.mul_mem _ ha hb
  add_mem' ha hb := Subfield.add_mem _ ha hb
  inv_mem' _ hx := Subfield.inv_mem _ hx
  algebraMap_mem' x := by
    rw [algebraMap_tilt_eq_comp F]
    exact ⟨_, rfl⟩
end TiltIntermediate
end GroundTheory.PAdicHodge


