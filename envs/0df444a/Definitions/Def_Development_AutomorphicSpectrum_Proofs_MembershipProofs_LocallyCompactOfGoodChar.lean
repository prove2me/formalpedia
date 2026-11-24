-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_LocallyCompactOfGoodChar
-- name    : Development_AutomorphicSpectrum_Proofs_MembershipProofs_LocallyCompactOfGoodChar
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T14:25:33.97773+00:00
-- url     : https://prove2.me/theorems/cd59eb57-8773-4f1c-b368-0a856412f4cf
-- title:
--   Locally Compact Of Good Char
-- statement:
--   Definitions and structural lemmas for Locally Compact Of Good Char, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/LocallyCompactOfGoodChar.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_GoodCharIsLocallyConstant
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Implements_comp
import Theorems.Thm_GlobalTheory_CompanionTheory_SchrLaw_schr_law

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.WeilM GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.SchrLaw
namespace GlobalTheory.CompanionTheory.SchrModel
variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
theorem locallyCompact_of_goodChar [T2Space R] {ψ : AddChar R ℂ} {O : Subring R} {u : Rˣ} (h : GoodChar ψ O u) :
    LocallyCompactSpace R := by
  exact h.compact.locallyCompactSpace_of_mem_nhds_of_addGroup (h.isOpen.mem_nhds O.zero_mem)
omit [CommRing R] [IsTopologicalRing R] in

theorem integrable_pair {κ : Type} (μ : @Measure (κ → R) (borel _))
    (hμ : @IsFiniteMeasureOnCompacts _ (borel _) _ μ) (φ φ' : SB (κ → R)) :
    @Integrable _ _ _ _ (borel _) (fun x => (starRingEnd ℂ) ((φ : (κ → R) → ℂ) x) * (φ' : (κ → R) → ℂ) x) μ := by
  haveI := hμ
  have hφ : IsLocallyConstant (φ : (κ → R) → ℂ) ∧ HasCompactSupport (φ : (κ → R) → ℂ) := φ.2
  have hφ' : IsLocallyConstant (φ' : (κ → R) → ℂ) ∧ HasCompactSupport (φ' : (κ → R) → ℂ) := φ'.2
  have hcont : Continuous (fun x => (starRingEnd ℂ) ((φ : (κ → R) → ℂ) x) * (φ' : (κ → R) → ℂ) x) :=
    (Complex.continuous_conj.comp hφ.1.continuous).mul hφ'.1.continuous
  have hsupp : HasCompactSupport
      (fun x => (starRingEnd ℂ) ((φ : (κ → R) → ℂ) x) * (φ' : (κ → R) → ℂ) x) :=
    HasCompactSupport.mul_left (f := fun x => (starRingEnd ℂ) ((φ : (κ → R) → ℂ) x)) hφ'.2
  letI : MeasurableSpace (κ → R) := borel _
  haveI : BorelSpace (κ → R) := ⟨rfl⟩
  exact Continuous.integrable_of_hasCompactSupport hcont hsupp
omit [CommRing R] [IsTopologicalRing R] in

def form {κ : Type} (μ : @Measure (κ → R) (borel _)) (hμ : @IsFiniteMeasureOnCompacts _ (borel _) _ μ) :
    SB (κ → R) →ₗ⋆[ℂ] SB (κ → R) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun φ φ' => pair μ φ φ')
    (fun φ₁ φ₂ φ' => by
      unfold pair
      rw [← integral_add (integrable_pair μ hμ φ₁ φ') (integrable_pair μ hμ φ₂ φ')]
      congr 1
      funext x
      simp [add_mul])
    (fun a φ φ' => by
      unfold pair
      rw [smul_eq_mul, ← integral_const_mul]
      congr 1
      funext x
      simp [mul_assoc])
    (fun φ φ₁ φ₂ => by
      unfold pair
      rw [← integral_add (integrable_pair μ hμ φ φ₁) (integrable_pair μ hμ φ φ₂)]
      congr 1
      funext x
      simp [mul_add])
    (fun a φ φ' => by
      unfold pair
      rw [smul_eq_mul, ← integral_const_mul]
      congr 1
      funext x
      simp [mul_left_comm])
omit [CommRing R] [IsTopologicalRing R] in

theorem pair_conj {κ : Type} (μ : @Measure (κ → R) (borel _)) (φ φ' : (κ → R) → ℂ) :
    (starRingEnd ℂ) (pair μ φ φ') = pair μ φ' φ := by
  show (starRingEnd ℂ) (∫ x, (starRingEnd ℂ) (φ x) * φ' x ∂μ) = ∫ x, (starRingEnd ℂ) (φ' x) * φ x ∂μ
  rw [← @integral_conj (κ → R) (borel _) μ ℂ _ _]
  congr 1
  funext x
  rw [map_mul, Complex.conj_conj, mul_comm]
omit [IsTopologicalRing R] in

theorem pair_pos {κ : Type} (μ : @Measure (κ → R) (borel _))
    (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) (φ : SB (κ → R)) (hφ : φ ≠ 0) :
    0 < (pair μ (φ : (κ → R) → ℂ) φ).re := by
  haveI := hμ
  have hφl : IsLocallyConstant (φ : (κ → R) → ℂ) ∧ HasCompactSupport (φ : (κ → R) → ℂ) := φ.2
  have hcont : Continuous (φ : (κ → R) → ℂ) := hφl.1.continuous
  have hint := integrable_pair μ
    (@Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts _ _ _ (borel _) μ hμ) φ φ
  have hg : ∀ z : ℂ, ((starRingEnd ℂ) z * z).re = Complex.normSq z := by
    intro z
    rw [Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hre : (pair μ (φ : (κ → R) → ℂ) φ).re =
      ∫ x, ((starRingEnd ℂ) ((φ : (κ → R) → ℂ) x) * (φ : (κ → R) → ℂ) x).re ∂μ :=
    (@integral_re (κ → R) (borel _) μ ℂ _ _ hint).symm
  rw [hre]
  obtain ⟨x0, hx0⟩ : ∃ x, (φ : (κ → R) → ℂ) x ≠ 0 := by
    by_contra hc
    apply hφ
    apply Subtype.ext
    funext x
    by_contra hx
    exact hc ⟨x, hx⟩
  refine (MeasureTheory.integral_pos_iff_support_of_nonneg ?_ ?_).mpr ?_
  · intro x
    show (0 : ℝ) ≤ ((starRingEnd ℂ) ((φ : (κ → R) → ℂ) x) * (φ : (κ → R) → ℂ) x).re
    rw [hg]
    exact Complex.normSq_nonneg _
  · exact hint.re
  · have hU : IsOpen ((φ : (κ → R) → ℂ) ⁻¹' {0}ᶜ) := hcont.isOpen_preimage _ isOpen_compl_singleton
    have hsub : (φ : (κ → R) → ℂ) ⁻¹' {0}ᶜ ⊆
        Function.support fun x => ((starRingEnd ℂ) ((φ : (κ → R) → ℂ) x) * (φ : (κ → R) → ℂ) x).re := by
      intro x hx
      rw [Function.mem_support, hg]
      exact (Complex.normSq_pos.mpr hx).ne'
    exact lt_of_lt_of_le (hU.measure_pos μ ⟨x0, hx0⟩) (measure_mono hsub)
variable [T2Space R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R} {κ : Type} [Fintype κ]
def sys {ψ : AddChar R ℂ} {O : Subring R} {u : Rˣ} (h : GoodChar ψ O u) (d : Darboux B κ)
    (μ : @Measure (κ → R) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    GlobalTheory.CompanionTheory.FinHeis.Sys W (SB (κ → R)) :=
  haveI := locallyCompact_of_goodChar h
  { c := fun w w' => ψ (⅟(2 : R) * B w w')
    rho := fun w =>
      { toFun := fun φ => ⟨d.rho ψ w φ, (schr_law ψ O u d μ w w φ φ h hμ).2.2.1 φ.2⟩
        map_add' := fun φ φ' => Subtype.ext (funext fun x => by simp [Darboux.rho, schr, mul_add])
        map_smul' := fun a φ => Subtype.ext (funext fun x => by simp [Darboux.rho, schr, mul_left_comm]) }
    B := form μ (@Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts _ _ _ (borel _) μ hμ)
    c_add_left := fun x x' y => by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      simp only [d.form, map_add, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
      ring
    c_add_right := fun x y y' => by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      simp only [d.form, map_add, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
      ring
    c_self := fun x => by simp [d.form]
    c_norm := fun x y => h.norm_one _
    rho_zero := fun φ => Subtype.ext (schr_law ψ O u d μ 0 0 φ φ h hμ).2.1
    rho_rho := fun w w' φ => Subtype.ext (schr_law ψ O u d μ w w' φ φ h hμ).1
    B_conj := fun φ φ' => pair_conj μ φ φ'
    B_pos := fun φ hφ => pair_pos μ hμ φ hφ
    B_rho := fun w φ φ' => (schr_law ψ O u d μ w w φ φ' h hμ).2.2.2 }
end GlobalTheory.CompanionTheory.SchrModel


