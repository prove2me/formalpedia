-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdModelTransc
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdModelTransc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:24.939715+00:00
-- url     : https://prove2.me/theorems/d62cca6f-7a59-4dd3-9baa-97bfb9c4121a
-- title:
--   PDual Std Model Transc
-- statement:
--   Definitions and structural lemmas for PDual Std Model Transc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdModelTransc.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial
noncomputable section
namespace StandardDualModelTranscendence
variable {L : Type} [Field L]
def scaleHom (a : L) :
    MvPolynomial Unit (MvPolynomial Unit L) →+* MvPolynomial Unit (MvPolynomial Unit L) :=
  eval₂Hom ((C : MvPolynomial Unit L →+* MvPolynomial Unit (MvPolynomial Unit L)).comp
      (aeval fun _ : Unit => C a * X ()).toRingHom) fun _ => C (C a⁻¹) * X ()
theorem scaleHom_CC (a c : L) : scaleHom a (C (C c)) = C (C c) := by simp [scaleHom]
theorem scaleHom_S (a : L) : scaleHom a (C (X ())) = C (C a) * C (X ()) := by simp [scaleHom]
theorem scaleHom_alt (a : L) : scaleHom a (X ()) = C (C a⁻¹) * X () := by simp [scaleHom]
theorem scaleHom_comp {a : L} (ha : a ≠ 0) : (scaleHom a⁻¹).comp (scaleHom a) = RingHom.id _ := by
  have hC : ((scaleHom a⁻¹).comp (scaleHom a)).comp C =
      (C : MvPolynomial Unit L →+* MvPolynomial Unit (MvPolynomial Unit L)) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun v => ?_)
    · simp only [RingHom.comp_apply, scaleHom_CC]
    · cases v
      simp only [RingHom.comp_apply, scaleHom_S, map_mul, scaleHom_CC]
      rw [← mul_assoc, ← map_mul, ← map_mul, ← C_mul, mul_inv_cancel₀ ha, C_1, one_mul]
  refine MvPolynomial.ringHom_ext (fun p => ?_) (fun u => ?_)
  · exact RingHom.congr_fun hC p
  · cases u
    simp only [RingHom.comp_apply, scaleHom_alt, map_mul, scaleHom_CC, RingHom.id_apply]
    rw [← mul_assoc, ← map_mul, ← map_mul, inv_inv, inv_mul_cancel₀ ha, map_one, map_one, one_mul]
theorem scaleHom_injective {a : L} (ha : a ≠ 0) : Function.Injective (scaleHom a) :=
  Function.LeftInverse.injective (g := scaleHom a⁻¹) fun p => RingHom.congr_fun (scaleHom_comp ha) p
def scale {a : L} (ha : a ≠ 0) :
    FractionRing (MvPolynomial Unit (MvPolynomial Unit L)) →+*
      FractionRing (MvPolynomial Unit (MvPolynomial Unit L)) :=
  IsFractionRing.lift (A := MvPolynomial Unit (MvPolynomial Unit L))
    (g := (algebraMap _ (FractionRing (MvPolynomial Unit (MvPolynomial Unit L)))).comp (scaleHom a))
    ((IsFractionRing.injective _ _).comp (scaleHom_injective ha))
variable {K : Type} [Field K] {i : ℕ}
variable [NumberField K] {F : HermLattice K i} {T : Type} (b : Module.Basis T ℤ (dualLattice F))
end StandardDualModelTranscendence
end
end GroundTheory.Heights₂.Heights


