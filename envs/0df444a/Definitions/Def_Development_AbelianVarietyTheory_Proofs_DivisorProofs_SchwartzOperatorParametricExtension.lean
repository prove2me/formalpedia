-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzOperatorParametricExtension
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzOperatorParametricExtension
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T22:20:22.755327+00:00
-- url     : https://prove2.me/theorems/cc6d4ca4-7e95-406d-9d74-569bd3679e3c
-- title:
--   Schwartz Operator Parametric Extension
-- statement:
--   Definitions and structural lemmas for Schwartz Operator Parametric Extension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzOperatorParametricExtension.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthProdMkConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSliceSeminormLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasFderivAtSchwartzOperatorFirstStatement
import Theorems.Thm_GlobalTheory_SchwartzFstOp_dSndCLM_apply
import Theorems.Thm_GlobalTheory_T_has_fderiv_at_schwartz_operator_first
import Theorems.Thm_GlobalTheory_T_schwartz_slice_seminorm_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped SchwartzMap ContDiff
namespace GlobalTheory.SchwartzFstOp
section Bounds
variable {X Y F G : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
theorem continuous_finset_sup_schwartz (s : Finset (ℕ × ℕ)) :
    Continuous ⇑(s.sup (schwartzSeminormFamily ℂ Y G)) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sup_empty]; exact continuous_const
  | insert i s _ ih =>
    rw [Finset.sup_insert]
    exact (((schwartz_withSeminorms ℂ Y G).continuous_seminorm i).max ih).congr
      fun x => (Seminorm.sup_apply _ _ _).symm
theorem exists_sup_bound (A : 𝓢(X, F) →L[ℂ] 𝓢(Y, G)) (s : Finset (ℕ × ℕ)) :
    ∃ (t : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ f, (s.sup (schwartzSeminormFamily ℂ Y G)) (A f) ≤
      C * (t.sup (schwartzSeminormFamily ℂ X F)) f := by
  obtain ⟨t, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ X F)
    ((s.sup (schwartzSeminormFamily ℂ Y G)).comp A.toLinearMap)
    ((continuous_finset_sup_schwartz s).comp A.continuous)
  exact ⟨t, C, C.2, fun f => by simpa [Seminorm.comp_apply, Seminorm.smul_apply, NNReal.smul_def] using hC f⟩
theorem sup_apply_mono {s t : Finset (ℕ × ℕ)} (h : s ⊆ t) (f : 𝓢(X, F)) :
    (s.sup (schwartzSeminormFamily ℂ X F)) f ≤ (t.sup (schwartzSeminormFamily ℂ X F)) f :=
  Seminorm.le_def.1 (Finset.sup_mono h) f
end Bounds
variable {V W V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
theorem slice_sup_le (f : 𝓢(V × V', ℂ)) (x' : V') (s : Finset (ℕ × ℕ)) (k : ℕ) :
    ‖x'‖ ^ k * (s.sup (schwartzSeminormFamily ℂ V ℂ)) (sliceCLM x' f) ≤
      ((s.image fun m : ℕ × ℕ => ((m.1 + k, m.2) : ℕ × ℕ)).sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f := by
  set c : ℝ := ‖x'‖ ^ k with hc
  have c0 : 0 ≤ c := by positivity
  set R := ((s.image fun m : ℕ × ℕ => ((m.1 + k, m.2) : ℕ × ℕ)).sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f
  have h1 : ∀ m ∈ s, c * schwartzSeminormFamily ℂ V ℂ m (sliceCLM x' f) ≤ R := by
    intro m hm
    have a1 : ‖x'‖ ^ k * SchwartzMap.seminorm ℂ m.1 m.2 (sliceCLM x' f) ≤
        SchwartzMap.seminorm ℂ (m.1 + k) m.2 f := GlobalTheory.T.schwartz_slice_seminorm_le f x' m.1 k m.2
    have a2 : schwartzSeminormFamily ℂ (V × V') ℂ ((m.1 + k, m.2) : ℕ × ℕ) f ≤ R :=
      Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ (V × V') ℂ)
        (Finset.mem_image_of_mem (fun m : ℕ × ℕ => ((m.1 + k, m.2) : ℕ × ℕ)) hm)
    exact a1.trans a2
  rcases c0.eq_or_lt with h | h
  · rw [← h, zero_mul]; exact apply_nonneg _ _
  · rw [← le_div_iff₀' h]
    refine Seminorm.finset_sup_apply_le (div_nonneg (apply_nonneg _ _) c0) fun m hm => ?_
    rw [le_div_iff₀' h]
    exact h1 m hm
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem base_bound (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (k : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : 𝓢(V × V', ℂ)) (p : W × V'),
      ‖p‖ ^ k * ‖opFst T f p‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f := by
  obtain ⟨s₁, C₁, hC₁, h₁⟩ := exists_sup_bound T {(k, 0)}
  obtain ⟨s₂, C₂, hC₂, h₂⟩ := exists_sup_bound T {(0, 0)}
  set t₁ := s₁.image fun m : ℕ × ℕ => ((m.1 + 0, m.2) : ℕ × ℕ)
  set t₂ := s₂.image fun m : ℕ × ℕ => ((m.1 + k, m.2) : ℕ × ℕ)
  refine ⟨t₁ ∪ t₂, C₁ + C₂, by positivity, fun f p => ?_⟩
  obtain ⟨y, x'⟩ := p
  set h := sliceCLM x' f
  have e1 : ‖y‖ ^ k * ‖T h y‖ ≤ C₁ * (s₁.sup (schwartzSeminormFamily ℂ V ℂ)) h := by
    refine (SchwartzMap.norm_pow_mul_le_seminorm ℂ (T h) k y).trans ?_
    have := h₁ h
    simpa [schwartzSeminormFamily] using this
  have e2 : ‖T h y‖ ≤ C₂ * (s₂.sup (schwartzSeminormFamily ℂ V ℂ)) h := by
    have a := SchwartzMap.norm_pow_mul_le_seminorm ℂ (T h) 0 y
    simp only [pow_zero, one_mul] at a
    refine a.trans ?_
    have := h₂ h
    simpa [schwartzSeminormFamily] using this
  have f1 : (s₁.sup (schwartzSeminormFamily ℂ V ℂ)) h ≤
      ((t₁ ∪ t₂).sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f := by
    have := slice_sup_le f x' s₁ 0
    rw [pow_zero, one_mul] at this
    exact this.trans (sup_apply_mono Finset.subset_union_left f)
  have f2 : ‖x'‖ ^ k * (s₂.sup (schwartzSeminormFamily ℂ V ℂ)) h ≤
      ((t₁ ∪ t₂).sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f :=
    (slice_sup_le f x' s₂ k).trans (sup_apply_mono Finset.subset_union_right f)
  have hp : ‖(y, x')‖ ^ k ≤ ‖y‖ ^ k + ‖x'‖ ^ k := by
    rw [Prod.norm_mk]
    rcases le_total ‖y‖ ‖x'‖ with hl | hl
    · rw [max_eq_right hl]; linarith [pow_nonneg (norm_nonneg y) k]
    · rw [max_eq_left hl]; linarith [pow_nonneg (norm_nonneg x') k]
  set S := ((t₁ ∪ t₂).sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f
  change ‖(y, x')‖ ^ k * ‖T h y‖ ≤ (C₁ + C₂) * S
  calc ‖(y, x')‖ ^ k * ‖T h y‖ ≤ (‖y‖ ^ k + ‖x'‖ ^ k) * ‖T h y‖ := by gcongr
    _ = ‖y‖ ^ k * ‖T h y‖ + ‖x'‖ ^ k * ‖T h y‖ := by ring
    _ ≤ C₁ * (s₁.sup (schwartzSeminormFamily ℂ V ℂ)) h +
          ‖x'‖ ^ k * (C₂ * (s₂.sup (schwartzSeminormFamily ℂ V ℂ)) h) := by gcongr
    _ = C₁ * (s₁.sup (schwartzSeminormFamily ℂ V ℂ)) h +
          C₂ * (‖x'‖ ^ k * (s₂.sup (schwartzSeminormFamily ℂ V ℂ)) h) := by ring
    _ ≤ C₁ * S + C₂ * S := by gcongr
    _ = (C₁ + C₂) * S := by ring
variable [FiniteDimensional ℝ V']
theorem differentiable_opFst (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) :
    Differentiable ℝ (opFst T f) := fun p => (GlobalTheory.T.has_fderiv_at_schwartz_operator_first T f p.1 p.2).differentiableAt
variable (W V' E) in

def compFst : (W →L[ℝ] E) →L[ℝ] (W × V' →L[ℝ] E) :=
  (ContinuousLinearMap.compL ℝ (W × V') W E).flip (ContinuousLinearMap.fst ℝ W V')
variable (W V' E) in

def coordSnd (i : Fin (Module.finrank ℝ V')) : E →L[ℝ] (W × V' →L[ℝ] E) :=
  ContinuousLinearMap.smulRightL ℝ (W × V') E
    ((LinearMap.toContinuousLinearMap ((Module.finBasis ℝ V').coord i)).comp (ContinuousLinearMap.snd ℝ W V'))
theorem fderiv_opFst (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) :
    fderiv ℝ (opFst T f) = fun p =>
      compFst W V' E (opFst ((SchwartzMap.fderivCLM ℂ W E).comp T) f p) +
        ∑ i, coordSnd W V' E i (opFst T (lineSnd (Module.finBasis ℝ V' i) f) p) := by
  funext p
  rw [(GlobalTheory.T.has_fderiv_at_schwartz_operator_first T f p.1 p.2).fderiv]
  refine ContinuousLinearMap.ext fun q => ?_
  have hv : q.2 = ∑ i, (Module.finBasis ℝ V').repr q.2 i • Module.finBasis ℝ V' i :=
    ((Module.finBasis ℝ V').sum_repr q.2).symm
  simp [compFst, coordSnd]
  congr 1
  conv_lhs => rw [hv]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, dSndCLM_apply]
theorem finiteRing_sq_sub_mul_sq_eq_of_card (n : ℕ) : ∀ (E' : Type) [NormedAddCommGroup E'] [NormedSpace ℂ E']
    (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E')),
    (∀ f : 𝓢(V × V', ℂ), ContDiff ℝ n (opFst T f)) ∧
    ∀ k : ℕ, ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : 𝓢(V × V', ℂ)) (p : W × V'),
      ‖p‖ ^ k * ‖iteratedFDeriv ℝ n (opFst T f) p‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f := by
  induction n with
  | zero =>
    intro E' _ _ T
    refine ⟨fun f => contDiff_zero.2 (differentiable_opFst T f).continuous, fun k => ?_⟩
    obtain ⟨s, C, hC, h⟩ := base_bound (V' := V') T k
    exact ⟨s, C, hC, fun f p => by rw [norm_iteratedFDeriv_zero]; exact h f p⟩
  | succ n ih =>
    intro E' _ _ T
    set b := Module.finBasis ℝ V'
    set T₁ := (SchwartzMap.fderivCLM ℂ W E').comp T
    obtain ⟨c₁, b₁⟩ := ih _ T₁
    obtain ⟨c₂, b₂⟩ := ih E' T
    have hA : ∀ f : 𝓢(V × V', ℂ), ContDiff ℝ n (fun p => compFst W V' E' (opFst T₁ f p)) :=
      fun f => (compFst W V' E').contDiff.comp (c₁ f)
    have hB : ∀ (f : 𝓢(V × V', ℂ)) (i : Fin (Module.finrank ℝ V')),
        ContDiff ℝ n (fun p => coordSnd W V' E' i (opFst T (lineSnd (b i) f) p)) :=
      fun f i => (coordSnd W V' E' i).contDiff.comp (c₂ _)
    have hG : ∀ f : 𝓢(V × V', ℂ), ContDiff ℝ n (fderiv ℝ (opFst T f)) := fun f => by
      rw [fderiv_opFst]
      exact (hA f).add (ContDiff.sum fun i _ => hB f i)
    refine ⟨fun f => ?_, fun k => ?_⟩
    · rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
      exact ⟨differentiable_opFst T f, by simp, hG f⟩
    · obtain ⟨s₁, C₁, hC₁, h₁⟩ := b₁ k
      obtain ⟨s₂, C₂, hC₂, h₂⟩ := b₂ k
      choose t Ct hCt ht using fun i : Fin (Module.finrank ℝ V') =>
        exists_sup_bound (lineSnd (b i) : 𝓢(V × V', ℂ) →L[ℂ] 𝓢(V × V', ℂ)) s₂
      refine ⟨s₁ ∪ Finset.univ.biUnion t,
        ‖compFst W V' E'‖ * C₁ + ∑ i, ‖coordSnd W V' E' i‖ * (C₂ * Ct i), ?_, fun f p => ?_⟩
      · exact add_nonneg (mul_nonneg (norm_nonneg _) hC₁)
          (Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (mul_nonneg hC₂ (hCt i)))
      set S := ((s₁ ∪ Finset.univ.biUnion t).sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f
      rw [← norm_iteratedFDeriv_fderiv, fderiv_opFst]
      have e : iteratedFDeriv ℝ n (fun p => compFst W V' E' (opFst T₁ f p) +
            ∑ i, coordSnd W V' E' i (opFst T (lineSnd (b i) f) p)) p =
          iteratedFDeriv ℝ n (fun p => compFst W V' E' (opFst T₁ f p)) p +
            ∑ i, iteratedFDeriv ℝ n (fun p => coordSnd W V' E' i (opFst T (lineSnd (b i) f) p)) p := by
        rw [show (fun p => compFst W V' E' (opFst T₁ f p) +
            ∑ i, coordSnd W V' E' i (opFst T (lineSnd (b i) f) p)) =
            (fun p => compFst W V' E' (opFst T₁ f p)) +
            (fun p => ∑ i, coordSnd W V' E' i (opFst T (lineSnd (b i) f) p)) from rfl]
        rw [iteratedFDeriv_add_apply (f := fun p => compFst W V' E' (opFst T₁ f p))
          (g := fun p => ∑ i, coordSnd W V' E' i (opFst T (lineSnd (b i) f) p))
          (hA f).contDiffAt (ContDiff.sum fun i _ => hB f i).contDiffAt,
          iteratedFDeriv_fun_sum_apply fun i _ => (hB f i).contDiffAt]
      rw [e]
      have kA : ‖p‖ ^ k * ‖iteratedFDeriv ℝ n (fun p => compFst W V' E' (opFst T₁ f p)) p‖ ≤
          ‖compFst W V' E'‖ * C₁ * S := by
        have a := (compFst W V' E').norm_iteratedFDeriv_comp_left (c₁ f).contDiffAt (x := p) le_rfl
        have a2 := h₁ f p
        have a3 := sup_apply_mono (Finset.subset_union_left (s₁ := s₁) (s₂ := Finset.univ.biUnion t)) f
        calc _ ≤ ‖p‖ ^ k * (‖compFst W V' E'‖ * ‖iteratedFDeriv ℝ n (opFst T₁ f) p‖) := by
              gcongr; exact a
          _ = ‖compFst W V' E'‖ * (‖p‖ ^ k * ‖iteratedFDeriv ℝ n (opFst T₁ f) p‖) := by ring
          _ ≤ ‖compFst W V' E'‖ * (C₁ * S) :=
              mul_le_mul_of_nonneg_left (a2.trans (mul_le_mul_of_nonneg_left a3 hC₁)) (norm_nonneg _)
          _ = _ := by ring
      have kB : ∀ i, ‖p‖ ^ k *
          ‖iteratedFDeriv ℝ n (fun p => coordSnd W V' E' i (opFst T (lineSnd (b i) f) p)) p‖ ≤
          ‖coordSnd W V' E' i‖ * (C₂ * Ct i) * S := by
        intro i
        have a := (coordSnd W V' E' i).norm_iteratedFDeriv_comp_left (c₂ (lineSnd (b i) f)).contDiffAt
          (x := p) le_rfl
        have a2 := h₂ (lineSnd (b i) f) p
        have a3 := ht i f
        have a4 : ((t i).sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f ≤ S :=
          sup_apply_mono (Finset.subset_union_right.trans' (Finset.subset_biUnion_of_mem t (Finset.mem_univ i))) f
        calc _ ≤ ‖p‖ ^ k * (‖coordSnd W V' E' i‖ *
                ‖iteratedFDeriv ℝ n (opFst T (lineSnd (b i) f)) p‖) := by
              gcongr; exact a
          _ = ‖coordSnd W V' E' i‖ * (‖p‖ ^ k * ‖iteratedFDeriv ℝ n (opFst T (lineSnd (b i) f)) p‖) := by ring
          _ ≤ ‖coordSnd W V' E' i‖ * (C₂ * (Ct i * S)) :=
              mul_le_mul_of_nonneg_left (a2.trans (mul_le_mul_of_nonneg_left
                (a3.trans (mul_le_mul_of_nonneg_left a4 (hCt i))) hC₂)) (norm_nonneg _)
          _ = _ := by ring
      calc ‖p‖ ^ k * ‖iteratedFDeriv ℝ n (fun p => compFst W V' E' (opFst T₁ f p)) p +
            ∑ i, iteratedFDeriv ℝ n (fun p => coordSnd W V' E' i (opFst T (lineSnd (b i) f) p)) p‖
          ≤ ‖p‖ ^ k * ‖iteratedFDeriv ℝ n (fun p => compFst W V' E' (opFst T₁ f p)) p‖ +
            ∑ i, ‖p‖ ^ k *
              ‖iteratedFDeriv ℝ n (fun p => coordSnd W V' E' i (opFst T (lineSnd (b i) f) p)) p‖ := by
            rw [← Finset.mul_sum, ← mul_add]
            gcongr
            exact (norm_add_le _ _).trans (by gcongr; exact norm_sum_le _ _)
        _ ≤ ‖compFst W V' E'‖ * C₁ * S + ∑ i, ‖coordSnd W V' E' i‖ * (C₂ * Ct i) * S := by
            exact add_le_add kA (Finset.sum_le_sum fun i _ => kB i)
        _ = _ := by rw [← Finset.sum_mul, ← add_mul]
def tensorId (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, ℂ)) : 𝓢(V × V', ℂ) →L[ℂ] 𝓢(W × V', ℂ) :=
  SchwartzMap.mkCLM (σ := RingHom.id ℂ) (fun f p => opFst T f p)
    (fun f g p => by simp [opFst, map_add])
    (fun a f p => by simp [opFst, map_smul])
    (fun f => contDiff_infty.2 fun n => (finiteRing_sq_sub_mul_sq_eq_of_card n ℂ T).1 f)
    (fun m => (finiteRing_sq_sub_mul_sq_eq_of_card m.2 ℂ T).2 m.1)
end GlobalTheory.SchwartzFstOp


