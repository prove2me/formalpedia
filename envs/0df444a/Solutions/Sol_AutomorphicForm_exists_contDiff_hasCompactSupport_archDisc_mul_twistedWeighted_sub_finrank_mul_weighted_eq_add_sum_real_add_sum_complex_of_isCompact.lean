-- Prove2me | solution 1 for AutomorphicForm.exists_contDiff_hasCompactSupport_archDisc_mul_twistedWeighted_sub_finrank_mul_weighted_eq_add_sum_real_add_sum_complex_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/7d94e5fc-4ea2-5f05-9c76-99ad2cb76c11

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_archDisc_mul_weighted_eq_neg_two_mul_sum_log_mul_orbital_add_sum_real_add_sum_complex
import Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_archDisc_mul_twistedWeighted_eq_neg_two_mul_finrank_mul_sum_log_mul_twistedOrbital_add_sum_real_add_sum_complex
import Theorems.Thm_AutomorphicForm_exists_isOrbitalIntegralOn_and_exists_isTwistedOrbitalIntegralOn_and_eq_of_areMatchingArch_diagUnits2
import Theorems.Thm_AutomorphicForm_exists_isSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_of_hasCompactSupport
import Theorems.Thm_AutomorphicForm_WindowedSiegel_sum_mult_mul_log_topNormSq_mul_rowNormSq_div_eq_neg_log_archHeight_sub_log_archHeight_weyl_mul
import Theorems.Thm_AutomorphicForm_neg_log_archHeight_archIdentGL_sub_log_archHeight_adelicWeyl_mul_eq_sum_mult_mul_log
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_archDisc_mul_twistedWeighted_sub_finrank_mul_weighted_eq_add_sum_real_add_sum_complex_of_isCompact
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped Classical

namespace R2pReduce

theorem tsupport_sub_const_mul_subset {X : Type*} [TopologicalSpace X] (f g : X → ℂ) (c : ℂ) {p : X}
    (hp : p ∈ tsupport (fun x => f x - c * g x)) : p ∈ tsupport f ∨ p ∈ tsupport g := by
  by_contra h
  rw [not_or] at h
  obtain ⟨hf, hg⟩ := h
  rw [notMem_tsupport_iff_eventuallyEq] at hf hg
  have : (fun x => f x - c * g x) =ᶠ[nhds p] 0 := by
    filter_upwards [hf, hg] with x hx hy
    simp only [Pi.zero_apply] at hx hy ⊢
    rw [hx, hy, mul_zero, sub_zero]
  exact (notMem_tsupport_iff_eventuallyEq.mpr this) hp

end R2pReduce

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : AutomorphicForm.IsArchTestFactor L φa)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfa : AutomorphicForm.IsArchTestFactor K fa)
    (hmatch : AutomorphicForm.AreMatchingArch K L σ φa fa)
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    (τ₀ : Measure (InfiniteAdeleRing K × InfiniteAdeleRing K)) :
    ∃ (B : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ)
      (C E : NumberField.InfinitePlace K → (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) B ∧ (∀ w, ContDiff ℝ (⊤ : ℕ∞) (C w)) ∧ (∀ w, ContDiff ℝ (⊤ : ℕ∞) (E w)) ∧
      HasCompactSupport B ∧ (∀ w, HasCompactSupport (C w)) ∧ (∀ w, HasCompactSupport (E w)) ∧
      (∀ p : Fin 2 → NumberField.mixedEmbedding.mixedSpace K, (B p ≠ 0 ∨ ∃ w, C w p ≠ 0 ∨ E w p ≠ 0) →
        IsUnit ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0)) ∧ IsUnit ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1))) ∧
      (∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport B ∪ ⋃ w, (tsupport (C w) ∪ tsupport (E w)),
            ∃ q ∈ Ca, p = ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (q.1 : InfiniteAdeleRing K),
              NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (q.2 : InfiniteAdeleRing K)]) ∧
      ∀ (a t : (InfiniteAdeleRing K)ˣ), AutomorphicForm.IsRegularSemisimple (diagUnits2 a (a * t)) →
      ∀ (τ : Measure (Subgroup.centralizer ({diagUnits2 a (a * t)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))),
        τ.IsHaarMeasure →
        Measure.map
            (fun x : Subgroup.centralizer ({diagUnits2 a (a * t)} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
              ((((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0,
                ((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) :
                InfiniteAdeleRing K × InfiniteAdeleRing K))
            τ = τ₀ →
      ∀ J : ℂ, AutomorphicForm.IsWeightedOrbitalIntegralOn (InfiniteAdeleRing K) (AutomorphicForm.archHaarK K)
          (fun x : GL (Fin 2) (InfiniteAdeleRing K) =>
            (∑ w : NumberField.InfinitePlace K, (w.mult : ℝ) *
            Real.log
              (AutomorphicForm.WindowedSiegel.topNormSq
                  ((NumberField.AdelicLevel.archComponent K w x : GL (Fin 2) w.Completion) :
                    Matrix (Fin 2) (Fin 2) w.Completion) *
                AutomorphicForm.WindowedSiegel.rowNormSq
                  ((NumberField.AdelicLevel.archComponent K w x : GL (Fin 2) w.Completion) :
                    Matrix (Fin 2) (Fin 2) w.Completion) /
                ‖((NumberField.AdelicLevel.archComponent K w x : GL (Fin 2) w.Completion) :
                    Matrix (Fin 2) (Fin 2) w.Completion).det‖ ^ 2)))
          (diagUnits2 a (a * t)) τ fa J →

        (∀ α β : (L ⊗[K] InfiniteAdeleRing K)ˣ,
          AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (diagUnits2 α β) =
            AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 a (a * t)) →
          ∀ (τ' : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (diagUnits2 α β))),
            τ'.IsHaarMeasure →
            AutomorphicForm.Coupled K L (InfiniteAdeleRing K) σ (diagUnits2 a (a * t)) (diagUnits2 α β) 1 τ τ' →
          ∀ J' : ℂ, AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ
              (AutomorphicForm.archHaarL K L)
              (fun x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
            (∑ w : NumberField.InfinitePlace L, (w.mult : ℝ) *
            Real.log
              (AutomorphicForm.WindowedSiegel.topNormSq
                  ((NumberField.AdelicLevel.archComponent L w (AutomorphicForm.archIdentGL K L x) : GL (Fin 2) w.Completion) :
                    Matrix (Fin 2) (Fin 2) w.Completion) *
                AutomorphicForm.WindowedSiegel.rowNormSq
                  ((NumberField.AdelicLevel.archComponent L w (AutomorphicForm.archIdentGL K L x) : GL (Fin 2) w.Completion) :
                    Matrix (Fin 2) (Fin 2) w.Completion) /
                ‖((NumberField.AdelicLevel.archComponent L w (AutomorphicForm.archIdentGL K L x) : GL (Fin 2) w.Completion) :
                    Matrix (Fin 2) (Fin 2) w.Completion).det‖ ^ 2)))
              (diagUnits2 α β) τ' (φa ∘ AutomorphicForm.archIdentGL K L) J' →
            ((∏ w : NumberField.InfinitePlace K,
              (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ /
                  Real.sqrt ‖NumberField.AdelicLevel.archEval K w (t : InfiniteAdeleRing K)‖) ^ w.mult : ℝ) : ℂ) *
                (J' - (Module.finrank K L : ℂ) * J) =
              B ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] +
            ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsReal),
              ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) :
                ℂ) * C w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] +
            ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsComplex),
              ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 *
                  Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ :
                  ℝ) : ℂ) *
                E w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)]) ∧

        ((¬ ∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (diagUnits2 a (a * t)) δ) →
            ((∏ w : NumberField.InfinitePlace K,
              (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ /
                  Real.sqrt ‖NumberField.AdelicLevel.archEval K w (t : InfiniteAdeleRing K)‖) ^ w.mult : ℝ) : ℂ) *
                (0 - (Module.finrank K L : ℂ) * J) =
              B ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] +
            ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsReal),
              ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) :
                ℂ) * C w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] +
            ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsComplex),
              ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 *
                  Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ :
                  ℝ) : ℂ) *
                E w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)]) := by
  classical
  obtain ⟨B₁, C₁, E₁, hB₁, hC₁, hE₁, hB₁c, hC₁c, hE₁c, hU₁, hCa₁, h₁⟩ :=
    AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_archDisc_mul_weighted_eq_neg_two_mul_sum_log_mul_orbital_add_sum_real_add_sum_complex
      K fa hfa τ₀
  obtain ⟨B₂, C₂, E₂, hB₂, hC₂, hE₂, hB₂c, hC₂c, hE₂c, hU₂, hCa₂, hV₂, h₂⟩ :=
    AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_archDisc_mul_twistedWeighted_eq_neg_two_mul_finrank_mul_sum_log_mul_twistedOrbital_add_sum_real_add_sum_complex
      K L σ hgen hdeg φa hφa τ₀
  refine ⟨fun p => B₂ p - (Module.finrank K L : ℂ) * B₁ p,
    fun w p => C₂ w p - (Module.finrank K L : ℂ) * C₁ w p,
    fun w p => E₂ w p - (Module.finrank K L : ℂ) * E₁ w p,
    hB₂.sub (contDiff_const.mul hB₁), fun w => (hC₂ w).sub (contDiff_const.mul (hC₁ w)),
    fun w => (hE₂ w).sub (contDiff_const.mul (hE₁ w)),
    hB₂c.sub (hB₁c.mul_left), fun w => (hC₂c w).sub ((hC₁c w).mul_left), fun w => (hE₂c w).sub ((hE₁c w).mul_left),
    ?_, ?_, ?_⟩
  ·
    intro p hp
    by_cases hq : B₁ p ≠ 0 ∨ ∃ w, C₁ w p ≠ 0 ∨ E₁ w p ≠ 0
    · exact hU₁ p hq
    · apply hU₂ p
      push Not at hq
      obtain ⟨hq1, hq2⟩ := hq
      rcases hp with h | ⟨w, h | h⟩
      · left; intro h0; apply h; beta_reduce; rw [h0, hq1]; simp
      · right; exact ⟨w, Or.inl fun h0 => h (by beta_reduce; rw [h0, (hq2 w).1]; simp)⟩
      · right; exact ⟨w, Or.inr fun h0 => h (by beta_reduce; rw [h0, (hq2 w).2]; simp)⟩
  ·
    obtain ⟨Ca₁, hCa₁c, hCa₁⟩ := hCa₁
    obtain ⟨Ca₂, hCa₂c, hCa₂⟩ := hCa₂
    refine ⟨Ca₂ ∪ Ca₁, hCa₂c.union hCa₁c, fun p hp => ?_⟩
    have key : p ∈ (tsupport B₂ ∪ ⋃ w, (tsupport (C₂ w) ∪ tsupport (E₂ w))) ∨
        p ∈ (tsupport B₁ ∪ ⋃ w, (tsupport (C₁ w) ∪ tsupport (E₁ w))) := by
      rcases hp with hB | hCE
      · rcases R2pReduce.tsupport_sub_const_mul_subset _ _ _ hB with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)
      · obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hCE
        rcases hw with hC | hE
        · rcases R2pReduce.tsupport_sub_const_mul_subset _ _ _ hC with h | h
          · exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨w, Or.inl h⟩))
          · exact Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨w, Or.inl h⟩))
        · rcases R2pReduce.tsupport_sub_const_mul_subset _ _ _ hE with h | h
          · exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨w, Or.inr h⟩))
          · exact Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨w, Or.inr h⟩))
    rcases key with h | h
    · obtain ⟨q, hq, hpq⟩ := hCa₂ p h
      exact ⟨q, Or.inl hq, hpq⟩
    · obtain ⟨q, hq, hpq⟩ := hCa₁ p h
      exact ⟨q, Or.inr hq, hpq⟩
  intro a t hreg τ hτ hmap J hJ
  rw [AutomorphicForm.WindowedSiegel.sum_mult_mul_log_topNormSq_mul_rowNormSq_div_eq_neg_log_archHeight_sub_log_archHeight_weyl_mul K] at hJ

  have hCsum : ∀ (X Y : NumberField.InfinitePlace K → ℂ),
      (∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsReal), ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) * (X w - (Module.finrank K L : ℂ) * Y w)) =
        (∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsReal), ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) * X w) - (Module.finrank K L : ℂ) * ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsReal), ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) * Y w := by
    intro X Y
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun w _ => by ring
  have hEsum : ∀ (X Y : NumberField.InfinitePlace K → ℂ),
      (∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsComplex), ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 *
                  Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) * (X w - (Module.finrank K L : ℂ) * Y w)) =
        (∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsComplex), ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 *
                  Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) * X w) - (Module.finrank K L : ℂ) * ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsComplex), ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 *
                  Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) * Y w := by
    intro X Y
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun w _ => by ring
  refine ⟨fun α β hN τ' hτ' hcoup J' hJ' => ?_, fun hnn => ?_⟩
  ·
    obtain ⟨⟨I, hI⟩, ⟨I', hI'⟩, hmI⟩ :=
      AutomorphicForm.exists_isOrbitalIntegralOn_and_exists_isTwistedOrbitalIntegralOn_and_eq_of_areMatchingArch_diagUnits2
        K L σ hgen hdeg φa hφa fa hfa hmatch a t hreg α β hN τ hτ τ' hτ' hcoup
    have hW' : (fun x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
            (∑ w : NumberField.InfinitePlace L, (w.mult : ℝ) *
            Real.log
              (AutomorphicForm.WindowedSiegel.topNormSq
                  ((NumberField.AdelicLevel.archComponent L w (AutomorphicForm.archIdentGL K L x) : GL (Fin 2) w.Completion) :
                    Matrix (Fin 2) (Fin 2) w.Completion) *
                AutomorphicForm.WindowedSiegel.rowNormSq
                  ((NumberField.AdelicLevel.archComponent L w (AutomorphicForm.archIdentGL K L x) : GL (Fin 2) w.Completion) :
                    Matrix (Fin 2) (Fin 2) w.Completion) /
                ‖((NumberField.AdelicLevel.archComponent L w (AutomorphicForm.archIdentGL K L x) : GL (Fin 2) w.Completion) :
                    Matrix (Fin 2) (Fin 2) w.Completion).det‖ ^ 2))) = (fun y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
            -Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
              - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
                  (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) *
                    AutomorphicForm.archIdentGL K L y))) :=
      funext fun y => (AutomorphicForm.neg_log_archHeight_archIdentGL_sub_log_archHeight_adelicWeyl_mul_eq_sum_mult_mul_log K L y).symm
    rw [hW'] at hJ'
    have e1 := h₁ a t hreg τ hτ hmap J I hJ hI
    have e2 := h₂ a t hreg τ hτ hmap α β hN τ' hτ' hcoup J' I' hJ' hI'
    rw [hmI I I' hI hI'] at e2
    beta_reduce
    rw [hCsum, hEsum]
    linear_combination e2 - (Module.finrank K L : ℂ) * e1
  ·
    haveI := hτ
    obtain ⟨s, hs, -⟩ :=
      AutomorphicForm.exists_isSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_of_hasCompactSupport
        K (diagUnits2 a (a * t)) hreg τ fa hfa.2
    set I : ℂ := ∫ x, fa (x⁻¹ * diagUnits2 a (a * t) * x) * (s x : ℂ) ∂(AutomorphicForm.archHaarK K) with hIdef
    have hI : AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) (AutomorphicForm.archHaarK K)
        (diagUnits2 a (a * t)) τ fa I := ⟨s, hs, hIdef⟩
    have hI0 : I = 0 := hmatch.2 (diagUnits2 a (a * t)) hreg hnn τ hτ I hI
    have e1 := h₁ a t hreg τ hτ hmap J I hJ hI
    rw [hI0] at e1
    obtain ⟨hB0, hCE0⟩ := hV₂ a t hnn
    beta_reduce
    rw [hCsum, hEsum, hB0, Finset.sum_eq_zero (fun w _ => by rw [(hCE0 w).1, mul_zero]),
      Finset.sum_eq_zero (s := Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsComplex)) (fun w _ => by rw [(hCE0 w).2, mul_zero])]
    linear_combination (-(Module.finrank K L : ℂ)) * e1

end S_AutomorphicForm_exists_contDiff_hasCompactSupport_archDisc_mul_twistedWeighted_sub_finrank_mul_weighted_eq_add_sum_real_add_sum_complex_of_isCompact
end P2MW
export P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_archDisc_mul_twistedWeighted_sub_finrank_mul_weighted_eq_add_sum_real_add_sum_complex_of_isCompact (solution)
