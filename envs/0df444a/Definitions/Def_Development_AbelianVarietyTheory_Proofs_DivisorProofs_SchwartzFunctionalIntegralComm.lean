-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzFunctionalIntegralComm
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzFunctionalIntegralComm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:34.055427+00:00
-- url     : https://prove2.me/theorems/a6d02bb0-2694-470c-9d17-040d37f07a46
-- title:
--   Schwartz Functional Integral Comm
-- statement:
--   Definitions and structural lemmas for Schwartz Functional Integral Comm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzFunctionalIntegralComm.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap BoundedContinuousFunction
noncomputable section
namespace GlobalTheory.SchwartzIntegral
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
def weightedDeriv (k m : ℕ) (f : 𝓢(E, ℂ)) : E →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin m => E) ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => (‖x‖ ^ k : ℝ) • iteratedFDeriv ℝ m f x)
    ((continuous_norm.pow k).smul ((f.smooth ⊤).continuous_iteratedFDeriv (by exact_mod_cast le_top)))
    (SchwartzMap.seminorm ℂ k m f) (fun x => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact f.le_seminorm ℂ k m x)
theorem weightedDeriv_apply (k m : ℕ) (f : 𝓢(E, ℂ)) (x : E) :
    weightedDeriv k m f x = (‖x‖ ^ k : ℝ) • iteratedFDeriv ℝ m f x := rfl
theorem norm_weightedDeriv_le (k m : ℕ) (f : 𝓢(E, ℂ)) :
    ‖weightedDeriv k m f‖ ≤ SchwartzMap.seminorm ℂ k m f :=
  (BoundedContinuousFunction.norm_le (apply_nonneg _ _)).mpr fun x => by
    rw [weightedDeriv_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact f.le_seminorm ℂ k m x
def weightedDerivCLM (k m : ℕ) :
    𝓢(E, ℂ) →L[ℂ] (E →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin m => E) ℂ) :=
  SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (weightedDeriv k m)
    (fun f g => by
      ext x : 1
      simp only [weightedDeriv_apply, BoundedContinuousFunction.coe_add, Pi.add_apply, SchwartzMap.add_apply]
      rw [show ⇑(f + g) = ⇑f + ⇑g from rfl, iteratedFDeriv_add_apply ((f.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt
        ((g.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt, smul_add])
    (fun a f => by
      ext x : 1
      simp only [weightedDeriv_apply, BoundedContinuousFunction.coe_smul, Pi.smul_apply,
        RingHom.id_apply]
      rw [show ⇑(a • f) = a • ⇑f from rfl,
        iteratedFDeriv_const_smul_apply ((f.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt, smul_comm])
    ⟨{(k, m)}, 1, zero_le_one, fun f => by
      simpa [Finset.sup_singleton, SchwartzMap.schwartzSeminormFamily_apply] using norm_weightedDeriv_le k m f⟩
section Param
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
  [BorelSpace W] {ν : Measure W}
abbrev Target (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (s : Finset (ℕ × ℕ)) : Type :=
  (i : s) → (E →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin i.1.2 => E) ℂ)
def embed (s : Finset (ℕ × ℕ)) : 𝓢(E, ℂ) →L[ℂ] Target E s :=
  ContinuousLinearMap.pi fun i => weightedDerivCLM i.1.1 i.1.2
end Param
end GlobalTheory.SchwartzIntegral


