-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_TensInduction
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_TensInduction
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T21:43:14.854728+00:00
-- url     : https://prove2.me/theorems/5ca5fed5-7edc-48c5-8da6-5f65838d7d5f
-- title:
--   Tens Induction
-- statement:
--   Definitions and structural lemmas for Tens Induction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FrobeniusReciprocity/TensInduction.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvariantFunctionalEqHaarMultipleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchwartzBruhatProdSpanTensorsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PartialIntegralMemSchwartzBruhatStatement
import Theorems.Thm_GlobalTheory_T_partial_integral_mem_schwartzBruhat
import Theorems.Thm_PositivityTheory_PfBern_Frob_mem_SB_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Set MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil
namespace PositivityTheory.PfBern.Frob
section Tens
variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] [T2Space A] [T2Space B]
theorem tens_mem (a : SB A) (b : SB B) :
    (fun q : A × B => (a : A → ℂ) q.1 * (b : B → ℂ) q.2) ∈ SB (A × B) := by
  have ha := mem_SB_iff.1 a.2
  have hb := mem_SB_iff.1 b.2
  refine mem_SB_iff.2 ⟨?_, ?_⟩
  · exact (ha.1.comp_continuous continuous_fst).mul (hb.1.comp_continuous continuous_snd)
  · refine HasCompactSupport.intro (IsCompact.prod ha.2 hb.2) ?_
    intro q hq
    rw [Set.mem_prod, not_and_or] at hq
    rcases hq with h | h
    · simp [image_eq_zero_of_notMem_tsupport h]
    · simp [image_eq_zero_of_notMem_tsupport h]
def tens (a : SB A) (b : SB B) : SB (A × B) :=
  ⟨_, tens_mem a b⟩
@[simp]
theorem tens_apply (a : SB A) (b : SB B) (q : A × B) :
    ((tens a b : SB (A × B)) : A × B → ℂ) q = (a : A → ℂ) q.1 * (b : B → ℂ) q.2 :=
  rfl
def tensL (b : SB B) : SB A →ₗ[ℂ] SB (A × B) where
  toFun a := tens a b
  map_add' a a' := Subtype.ext (funext fun q => by
    show ((a : A → ℂ) q.1 + (a' : A → ℂ) q.1) * (b : B → ℂ) q.2 = _
    rw [add_mul]; rfl)
  map_smul' c a := Subtype.ext (funext fun q => by
    show (c * (a : A → ℂ) q.1) * (b : B → ℂ) q.2 = c * ((a : A → ℂ) q.1 * (b : B → ℂ) q.2)
    rw [mul_assoc])
@[simp]
theorem tensL_apply (a : SB A) (b : SB B) : tensL b a = tens a b :=
  rfl
def tensR (a : SB A) : SB B →ₗ[ℂ] SB (A × B) where
  toFun b := tens a b
  map_add' b b' := Subtype.ext (funext fun q => by
    show (a : A → ℂ) q.1 * ((b : B → ℂ) q.2 + (b' : B → ℂ) q.2) = _
    rw [mul_add]; rfl)
  map_smul' c b := Subtype.ext (funext fun q => by
    show (a : A → ℂ) q.1 * (c * (b : B → ℂ) q.2) = c * ((a : A → ℂ) q.1 * (b : B → ℂ) q.2)
    ring)
@[simp]
theorem tensR_apply (a : SB A) (b : SB B) : tensR a b = tens a b :=
  rfl
end Tens
section Prod
variable {A B : Type} [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A]
  [TotallyDisconnectedSpace A] [TopologicalSpace B] [T2Space B] [LocallyCompactSpace B]
  [TotallyDisconnectedSpace B]
end Prod
section Fint
variable {A B : Type} [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A]
  [TotallyDisconnectedSpace A] [TopologicalSpace B] [T2Space B] [LocallyCompactSpace B]
  [TotallyDisconnectedSpace B] [MeasurableSpace B] [BorelSpace B]
  (μ : Measure B) [IsFiniteMeasureOnCompacts μ]
theorem fib_integrable (F : SB (A × B)) (a : A) {w : B → ℂ} (hw : Continuous w) :
    Integrable (fun b => (F : A × B → ℂ) (a, b) * w b) μ := by
  have hF := mem_SB_iff.1 F.2
  refine Continuous.integrable_of_hasCompactSupport
    ((hF.1.continuous.comp (Continuous.prodMk_right a)).mul hw) ?_
  refine HasCompactSupport.mul_right (f' := w) ?_
  refine HasCompactSupport.intro (IsCompact.image hF.2 continuous_snd) ?_
  intro b hb
  by_contra h
  exact hb ⟨(a, b), subset_tsupport _ h, rfl⟩
def intB (w : B → ℂ) (hw : Continuous w) : SB (A × B) →ₗ[ℂ] SB A where
  toFun F := ⟨fun a => ∫ b, (F : A × B → ℂ) (a, b) * w b ∂μ, GlobalTheory.T.partial_integral_mem_schwartzBruhat A B μ w hw F⟩
  map_add' F F' := Subtype.ext (funext fun a => by
    show ∫ b, ((F : A × B → ℂ) (a, b) + (F' : A × B → ℂ) (a, b)) * w b ∂μ =
      (∫ b, (F : A × B → ℂ) (a, b) * w b ∂μ) + ∫ b, (F' : A × B → ℂ) (a, b) * w b ∂μ
    simp only [add_mul]
    exact integral_add (fib_integrable μ F a hw) (fib_integrable μ F' a hw))
  map_smul' c F := Subtype.ext (funext fun a => by
    show ∫ b, (c * (F : A × B → ℂ) (a, b)) * w b ∂μ = c * ∫ b, (F : A × B → ℂ) (a, b) * w b ∂μ
    simp only [mul_assoc]
    exact integral_const_mul c _)
end Fint
section Factor
variable {A : Type} [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A]
  [TotallyDisconnectedSpace A]
  {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [T2Space K]
  [LocallyCompactSpace K] [TotallyDisconnectedSpace K] [MeasurableSpace K] [BorelSpace K]
  (μ : Measure K) [μ.IsHaarMeasure]
def rtr (k : K) : SB (A × K) →ₗ[ℂ] SB (A × K) :=
  pullHomeo ((Homeomorph.refl A).prodCongr (Homeomorph.mulRight k))
end Factor
end PositivityTheory.PfBern.Frob


