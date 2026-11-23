-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IwasawaDecompositionAdelicSL2
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IwasawaDecompositionAdelicSL2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:49.08255+00:00
-- url     : https://prove2.me/theorems/9e7aefdd-611c-4d7a-97da-1ac1374c9023
-- title:
--   Iwasawa Decomposition Adelic SL2
-- statement:
--   Definitions and structural lemmas for Iwasawa Decomposition Adelic SL2, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/IwasawaDecompositionAdelicSL2.lean

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.Iwasawa
variable {F : Type} [Field F] [NumberField F]
def IntAt (b : F) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  algebraMap F (A F) b v ∈ v.adicCompletionIntegers F
open Classical in

def idem (b : F) : A F :=
  ⟨fun v => if IntAt b v then 1 else 0, Filter.Eventually.of_forall fun v => by
    by_cases h : IntAt b v
    · simpa [h] using (v.adicCompletionIntegers F).one_mem
    · simpa [h] using (v.adicCompletionIntegers F).zero_mem⟩
open Classical in

def scale (b : F) : A F :=
  ⟨fun v => if IntAt b v then 1 else (algebraMap F (A F) b v)⁻¹,
    Filter.Eventually.of_forall fun v => by
      by_cases h : IntAt b v
      · simpa [h] using (v.adicCompletionIntegers F).one_mem
      · simpa [h] using ((v.adicCompletionIntegers F).mem_or_inv_mem _).resolve_left h⟩
open Classical in

def scaleInv (b : F) : A F :=
  ⟨fun v => if IntAt b v then 1 else algebraMap F (A F) b v, by
    filter_upwards [(algebraMap F (A F) b).2] with v hv
    have h : IntAt b v := hv
    simpa [h] using (v.adicCompletionIntegers F).one_mem⟩
theorem mul_at (x y : A F) (v : HeightOneSpectrum (𝓞 F)) : (x * y) v = x v * y v := rfl
theorem add_at (x y : A F) (v : HeightOneSpectrum (𝓞 F)) : (x + y) v = x v + y v := rfl
theorem sub_at (x y : A F) (v : HeightOneSpectrum (𝓞 F)) : (x - y) v = x v - y v := rfl
theorem one_at (v : HeightOneSpectrum (𝓞 F)) : (1 : A F) v = 1 := rfl
theorem idem_int {b : F} {v : HeightOneSpectrum (𝓞 F)} (h : IntAt b v) : idem b v = 1 :=
  if_pos h
theorem idem_not {b : F} {v : HeightOneSpectrum (𝓞 F)} (h : ¬ IntAt b v) : idem b v = 0 :=
  if_neg h
theorem scale_int {b : F} {v : HeightOneSpectrum (𝓞 F)} (h : IntAt b v) : scale b v = 1 :=
  if_pos h
theorem scale_not {b : F} {v : HeightOneSpectrum (𝓞 F)} (h : ¬ IntAt b v) :
    scale b v = (algebraMap F (A F) b v)⁻¹ :=
  if_neg h
theorem scaleInv_int {b : F} {v : HeightOneSpectrum (𝓞 F)} (h : IntAt b v) : scaleInv b v = 1 :=
  if_pos h
theorem scaleInv_not {b : F} {v : HeightOneSpectrum (𝓞 F)} (h : ¬ IntAt b v) :
    scaleInv b v = algebraMap F (A F) b v :=
  if_neg h
theorem ne_zero_of_not_int {b : F} {v : HeightOneSpectrum (𝓞 F)} (h : ¬ IntAt b v) :
    algebraMap F (A F) b v ≠ 0 := fun h0 =>
  h (by unfold IntAt; rw [h0]; exact (v.adicCompletionIntegers F).zero_mem)
theorem scale_mul_scaleInv (b : F) : scale b * scaleInv b = 1 := by
  refine FiniteAdeleRing.ext F fun v => ?_
  rw [mul_at, one_at]
  by_cases h : IntAt b v
  · rw [scale_int h, scaleInv_int h, one_mul]
  · rw [scale_not h, scaleInv_not h, inv_mul_cancel₀ (ne_zero_of_not_int h)]
theorem scale_combo (b : F) :
    scale b * idem b + (1 - idem b) * (scale b * algebraMap F (A F) b) = 1 := by
  refine FiniteAdeleRing.ext F fun v => ?_
  rw [add_at, mul_at, mul_at, mul_at, sub_at, one_at]
  by_cases h : IntAt b v
  · rw [scale_int h, idem_int h]; ring
  · rw [scale_not h, idem_not h, inv_mul_cancel₀ (ne_zero_of_not_int h)]; ring
def scaleUnit (b : F) : (A F)ˣ :=
  ⟨scale b, scaleInv b, scale_mul_scaleInv b, by rw [mul_comm]; exact scale_mul_scaleInv b⟩
def kMat (b : F) : SL(2, A F) :=
  ⟨!![idem b - 1, idem b; -scale b, -(scale b * algebraMap F (A F) b)], by
    rw [Matrix.det_fin_two_of]
    linear_combination scale_combo b⟩
end GlobalTheory.CompanionTheory.SW.Iwasawa


