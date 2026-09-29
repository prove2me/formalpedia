-- Prove2me | solution 1 for AutomorphicForm.continuous_whittakerCoefficient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/916fcf92-52eb-55fc-ab11-d2638573d8d4

import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_continuous_whittakerCoefficient

set_option autoImplicit false

open MeasureTheory Filter Topology NumberField NumberField.AdelicBox NumberField.AdelicHaar AutomorphicForm
open scoped ProbabilityTheory

namespace Ws37ContW

theorem continuous_unipotentGL2 (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (fun x : A => (unipotentGL2 x : GL (Fin 2) A)) := by
  have hmat : ∀ s : A → A, Continuous s → Continuous (fun x : A => (!![1, s x; 0, 1] : Matrix (Fin 2) (Fin 2) A)) := by
    intro s hs
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [hs, continuous_const]
  rw [Units.continuous_iff]
  constructor
  · have h__af := hmat id continuous_id
    simp [unipotentGL2_coe] at h__af
    exact h__af
  · have hinv : ∀ x : A, ((unipotentGL2 x : GL (Fin 2) A)⁻¹ : GL (Fin 2) A) = unipotentGL2 (-x) := by
      intro x
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← unipotentGL2_add, neg_add_cancel, unipotentGL2_zero]
    simp only [hinv]
    simpa [unipotentGL2_coe] using hmat Neg.neg continuous_neg

end Ws37ContW

open Ws37ContW

theorem solution
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : Continuous ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ) (α : F) :
    Continuous (fun g : AdelicGL2 (𝓞 F) F =>
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g) := by
  letI := adeleBorel (𝓞 F) F
  haveI := borelSpace_adeleBorel (𝓞 F) F
  set G : AdelicGL2 (𝓞 F) F → AdeleRing (𝓞 F) F → ℂ := fun g x =>
    φ (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)) with hG
  have hW : (fun g : AdelicGL2 (𝓞 F) F => whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g)
      = fun g => (((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹).toReal • ∫ x in adelicBox F, G g x ∂(adelicAddHaar (𝓞 F) F) := by
    funext g
    unfold whittakerCoefficient
    dsimp only [productionPinsOf]
    exact integral_smul_measure _ _
  rw [hW]
  refine Continuous.fun_smul continuous_const ?_
  set μ : Measure (AdeleRing (𝓞 F) F) := adelicAddHaar (𝓞 F) F with hμ
  set B : Set (AdeleRing (𝓞 F) F) := adelicBox F with hB

  have hGc : Continuous (fun p : AdeleRing (𝓞 F) F × AdelicGL2 (𝓞 F) F => G p.2 p.1) := by
    have h1 : Continuous (fun p : AdeleRing (𝓞 F) F × AdelicGL2 (𝓞 F) F => (unipotentGL2 p.1 : AdelicGL2 (𝓞 F) F) * p.2) :=
      ((continuous_unipotentGL2 _).comp continuous_fst).mul continuous_snd
    have h2 : Continuous (fun p : AdeleRing (𝓞 F) F × AdelicGL2 (𝓞 F) F =>
        ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * p.1))) :=
      hψ.comp ((continuous_const.mul continuous_fst).neg)
    exact (hφ.comp h1).mul h2
  obtain ⟨C, hCc, hBC⟩ := exists_isCompact_adelicBox_subset F
  have hBfin : μ B < ⊤ := adelicAddHaar_adelicBox_lt_top F
  have hBmeas : MeasurableSet B := measurableSet_adelicBox F

  have hint : ∀ g, IntegrableOn (G g) B μ := by
    intro g
    have hc : Continuous (fun x => G g x) := by
      rw [hG]
      exact (hφ.comp (((continuous_unipotentGL2 (AdeleRing (𝓞 F) F))).mul continuous_const)).mul
        (hψ.comp ((continuous_const.mul continuous_id).neg))
    obtain ⟨M, hM⟩ := hCc.exists_bound_of_continuousOn (f := fun x => G g x) hc.continuousOn
    exact Measure.integrableOn_of_bounded hBfin.ne hc.aestronglyMeasurable
      (ae_restrict_of_forall_mem hBmeas fun x hx => hM x (hBC hx))
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  set ε' : ℝ := ε / (μ.real B + 1) with hε'
  have hm0 : 0 ≤ μ.real B := measureReal_nonneg
  have hε'0 : 0 < ε' := div_pos hε (by linarith)

  set O : Set (AdeleRing (𝓞 F) F × AdelicGL2 (𝓞 F) F) := {p | dist (G p.2 p.1) (G g₀ p.1) < ε'} with hO
  have hOopen : IsOpen O :=
    isOpen_lt (continuous_dist.comp (hGc.prodMk (hGc.comp (continuous_fst.prodMk continuous_const)))) continuous_const
  have hsub : C ×ˢ ({g₀} : Set (AdelicGL2 (𝓞 F) F)) ⊆ O := by
    rintro ⟨x, g⟩ ⟨-, hg⟩
    rw [Set.mem_singleton_iff] at hg
    subst hg
    show dist (G g x) (G g x) < ε'
    rw [dist_self]; exact hε'0
  obtain ⟨u, v, hu, hv, hCu, hg₀v, huv⟩ := generalized_tube_lemma hCc isCompact_singleton hOopen hsub
  have hg₀ : g₀ ∈ v := hg₀v (Set.mem_singleton g₀)
  filter_upwards [hv.mem_nhds hg₀] with g hg
  rw [dist_eq_norm, ← integral_sub (hint g) (hint g₀)]
  have hpt : ∀ x ∈ B, ‖G g x - G g₀ x‖ ≤ ε' := by
    intro x hx
    have hxO : (x, g) ∈ O := huv ⟨hCu (hBC hx), hg⟩
    have : dist (G g x) (G g₀ x) < ε' := hxO
    rw [dist_eq_norm] at this
    exact this.le
  calc ‖∫ x in B, G g x - G g₀ x ∂μ‖ ≤ ε' * μ.real B := norm_setIntegral_le_of_norm_le_const hBfin hpt
    _ < ε := by
      rw [hε', div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith

end S_AutomorphicForm_continuous_whittakerCoefficient
end P2MW
export P2MW.S_AutomorphicForm_continuous_whittakerCoefficient (solution)
