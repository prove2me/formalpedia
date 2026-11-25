-- Prove2me | solution 1 for Arxiv0810_5751.sage_estep_cond_mean
-- status  : ACCEPTED   (prove)
-- author  : @ytako6706
-- created : 2026-11-25T07:09:24.63654+00:00
-- url     : https://prove2.me/submissions/8dec014a-98e2-4905-bab0-38f923d97000

import Mathlib
import Definitions.Def_Arxiv0810_5751_Basic

open MeasureTheory Matrix ProbabilityTheory Complex
open scoped ComplexOrder
open Arxiv0810_5751

/-- Real part of the Hermitian pairing recovers a real-linear functional. -/
lemma re_pairing_eq {M : ℕ} (L : (Fin M → ℂ) →L[ℝ] ℝ) (z : Fin M → ℂ) :
    (star (fun j => ((L (Pi.single j 1) : ℝ) : ℂ) + I * ((L (Pi.single j I) : ℝ) : ℂ))
      ⬝ᵥ z).re = L z := by
  have hz : z = ∑ j, ((z j).re • (Pi.single j (1 : ℂ) : Fin M → ℂ) +
      (z j).im • (Pi.single j I : Fin M → ℂ)) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib, Finset.sum_ite_eq]
  conv_rhs => rw [hz]
  simp only [map_sum, map_add, map_smul, smul_eq_mul, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

lemma circ_integrable {M : ℕ} (ν : Measure (Fin M → ℂ)) [IsProbabilityMeasure ν]
    (C : Matrix (Fin M) (Fin M) ℂ) (hC : C.PosDef) (h : IsCircGaussian ν C) :
    Integrable id ν := by
  have hG : IsGaussian ν := by
    refine isGaussian_of_map_eq_gaussianReal fun L => ?_
    set w : Fin M → ℂ := fun j => ((L (Pi.single j 1) : ℝ) : ℂ) + I * ((L (Pi.single j I) : ℝ) : ℂ)
      with hw
    have hq := hC.posSemidef.dotProduct_mulVec_nonneg w
    set q := star w ⬝ᵥ (C *ᵥ w) with hqdef
    have hqre : q = ((q.re : ℝ) : ℂ) := by
      have := (Complex.nonneg_iff.mp hq).2
      exact Complex.ext rfl (by simp [this.symm])
    have hq0 : 0 ≤ q.re := (Complex.nonneg_iff.mp hq).1
    set v : NNReal := ⟨q.re / 2, by positivity⟩ with hv
    refine ⟨0, v, ?_⟩
    have : IsProbabilityMeasure (ν.map L) :=
      Measure.isProbabilityMeasure_map L.continuous.measurable.aemeasurable
    apply Measure.ext_of_charFun
    funext t
    rw [charFun_gaussianReal, charFun_apply_real,
      integral_map L.continuous.measurable.aemeasurable (by fun_prop)]
    have h1 := h ((t : ℂ) • w)
    have hpair : ∀ z, (star ((t : ℂ) • w) ⬝ᵥ z).re = t * L z := by
      intro z
      rw [star_smul, smul_dotProduct, ← re_pairing_eq L z]
      simp [Complex.conj_ofReal]
      try (left; rfl)
    simp_rw [hpair] at h1
    have hlhs : (fun x => cexp (↑t * ↑(L x) * I)) = fun x => cexp (I * ↑(t * L x)) := by
      funext x; push_cast; ring_nf
    rw [hlhs, h1]
    congr 1
    rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, ← hqdef]
    simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
    have hvq : ((v : ℝ) : ℂ) = q / 2 := by
      have hv' : (v : ℝ) = q.re / 2 := rfl
      rw [hv', Complex.ofReal_div, ← hqre]
      norm_num
    rw [hvq]
    push_cast
    ring
  exact IsGaussian.integrable_id

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {K M : ℕ} (P : Fin K → ℕ) (s : ∀ i : Fin K, (Fin (P i) → ℂ) → Fin M → ℂ)
    (θk : ∀ i : Fin K, Fin (P i) → ℂ)
    (Pcov : Matrix (Fin M) (Fin M) ℂ) (hPcov : Pcov.PosDef)
    (n : Ω → Fin M → ℂ) (hn : Measurable n) (hlaw : IsCircGaussian (μ.map n) Pcov) (i : Fin K) :
    μ[fun ω => s i (θk i) + n ω |
        MeasurableSpace.comap
          (fun ω => (s i (θk i) + n ω) + ∑ l ∈ Finset.univ.erase i, s l (θk l)) inferInstance] =ᵐ[μ]
      (fun ω => s i (θk i) +
        (((s i (θk i) + n ω) + ∑ l ∈ Finset.univ.erase i, s l (θk l)) - ∑ l, s l (θk l))) ∧
    ∀ ω, s i (θk i) +
        (((s i (θk i) + n ω) + ∑ l ∈ Finset.univ.erase i, s l (θk l)) - ∑ l, s l (θk l)) =
      ((s i (θk i) + n ω) + ∑ l ∈ Finset.univ.erase i, s l (θk l)) -
        ∑ l ∈ Finset.univ.erase i, s l (θk l) := by
  set a := s i (θk i) with ha
  set R := ∑ l ∈ Finset.univ.erase i, s l (θk l) with hR
  have hsum : ∑ l, s l (θk l) = a + R := by
    rw [ha, hR, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have halg : ∀ ω, a + (((a + n ω) + R) - ∑ l, s l (θk l)) = a + n ω := by
    intro ω; rw [hsum]; abel
  refine ⟨?_, fun ω => by rw [halg ω]; abel⟩
  set y : Ω → Fin M → ℂ := fun ω => (a + n ω) + R with hy
  have hym : Measurable y := (measurable_const.add hn).add measurable_const
  have hle : MeasurableSpace.comap y inferInstance ≤ (inferInstance : MeasurableSpace Ω) :=
    hym.comap_le
  have : IsProbabilityMeasure (μ.map n) := Measure.isProbabilityMeasure_map hn.aemeasurable
  have hint_n : Integrable n μ := by
    have h1 := circ_integrable (μ.map n) Pcov hPcov hlaw
    exact (integrable_map_measure h1.aestronglyMeasurable hn.aemeasurable).mp h1
  have hint : Integrable (fun ω => a + n ω) μ := (integrable_const a).add hint_n
  have hsm : StronglyMeasurable[MeasurableSpace.comap y inferInstance] (fun ω => a + n ω) := by
    have hm : Measurable[MeasurableSpace.comap y inferInstance] (fun ω => a + n ω) := by
      have : (fun ω => a + n ω) = (fun v => v - R) ∘ y := by
        funext ω; simp [hy]
      rw [this]
      exact (measurable_id.sub_const R).comp (Measurable.of_comap_le le_rfl)
    exact hm.stronglyMeasurable
  have hce := condExp_of_stronglyMeasurable hle hsm hint
  rw [hce]
  exact Filter.Eventually.of_forall (fun ω => (halg ω).symm)
