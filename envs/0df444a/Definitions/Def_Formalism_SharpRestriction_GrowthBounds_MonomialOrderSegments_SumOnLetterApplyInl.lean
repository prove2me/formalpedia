-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SumOnLetterApplyInl
-- name    : Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SumOnLetterApplyInl
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T02:27:46.289734+00:00
-- url     : https://prove2.me/theorems/b3f6414e-ea8f-4178-a935-6f7933688bd6
-- title:
--   Sum On Letter Apply Inl
-- statement:
--   Definitions and structural lemmas for Sum On Letter Apply Inl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SumOnLetterApplyInl.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Theorems.Thm_Formalism_MainNotions_PlaneGram_CostOK_prod
import Theorems.Thm_Formalism_MainNotions_PlaneGram_Slope_prod
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_digitPart_appL
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_opS_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_bin_onLetter
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_add
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_appL
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_ddiv_sub_appL
import Theorems.Thm_Formalism_MainNotions_PlaneGram_coeff_ddiv
import Theorems.Thm_Formalism_MainNotions_PlaneGram_ddiv_add
import Theorems.Thm_Formalism_MainNotions_PlaneGram_divE_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eIn_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_letE_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_onLetter_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_nonneg_of_vec
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_ddiv_letter
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_mono
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_mul_left_nonneg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_outside_linear
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_smul
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_sum
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_zero
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_mul
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_natCast
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_ddiv_monomial__64d37c5132b7
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_der__2d3ff284a7e8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.PlaneGram.divE_apply
attribute [local simp] Formalism.MainNotions.PlaneGram.letE_apply


set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
theorem cge_ddiv (v : AddValuation K (WithTop ℚ)) {σ : Type} (M : σ →₀ ℕ) {a : ℝ}
    {F : MvPolynomial σ K} (hF : cge v a F) : cge v a (ddiv M F) := by
  intro β
  rw [coeff_ddiv]
  have h1 : vge v 0 ((β + M).prod fun x k => (k.choose (M x) : K)) := by
    unfold Finsupp.prod
    rw [← Nat.cast_prod]
    exact vge_natCast v _
  have := vge_mul v (hF (β + M)) h1
  rwa [add_zero] at this
namespace TwistData
variable [CharZero K] (D : TwistData K) (v : AddValuation K (WithTop ℚ)) (p : ℕ)
def ChOK (θ : (j : Fin D.J) → Fin (D.nch j) → ℝ) (a : ℝ) (G : MvPolynomial (D.OL × Fin D.r) K) : Prop :=
  ∃ G0 E : MvPolynomial (D.OL × Fin D.r) K, G = G0 + E ∧ cge v a G0 ∧ cge v (a + D.c) E ∧
    ∀ (ρ : D.Tau → Fin D.r → ℕ) (j : Fin D.J) (i : Fin (D.nch j)),
      vala D.msg (D.chainSet j i) (θ j i) (D.digitPart p ρ G0)
variable {D v p}
variable (D p)
def CostA (n : ℕ) (f : D.EA → K) : Prop :=
  ∀ ρ : D.Tau → Fin D.r → ℕ, CostV D.msg Set.univ n (fun ζ => f (D.emb p ρ ζ))
variable {D p}
theorem vala_opS [NeZero D.r] (hV2 : V2 K) (t : D.Tau) (S : Finset D.ML) (μ κ1 : Fin D.r →₀ ℕ) (c1 : K)
    {θ : ℝ} {Q : MvPolynomial (D.ML × Fin D.r) K} (hQ : vala D.msg S θ Q) :
    vala D.msg S (θ - absE κ1) (D.opS t μ κ1 c1 Q) := by
  classical
  rw [opS_apply]
  refine vala_smul c1 (vala_mul_left_nonneg ?_ (vala_ddiv_letter hV2 (D.mw t) κ1 hQ))
  refine valS_nonneg_of_vec D.msg S _ fun α hα i a hne => ?_
  have := support_monomial_subset hα
  rw [Finset.mem_singleton] at this
  rw [this, onLetter_apply] at hne
  by_cases hi : i = D.mw t
  · rw [hi]; rfl
  · rw [if_neg hi] at hne; exact absurd rfl hne
theorem vala_opS_out (t : D.Tau) (S : Finset D.ML) (hS : D.mw t ∉ S) (μ κ1 : Fin D.r →₀ ℕ) (c1 : K)
    {θ : ℝ} {Q : MvPolynomial (D.ML × Fin D.r) K} (hQ : vala D.msg S θ Q) :
    vala D.msg S θ (D.opS t μ κ1 c1 Q) := by
  classical
  have hform : ∀ α : D.EM, D.opS t μ κ1 c1 (monomial α 1) =
      monomial (onLetter (D.mw t) μ + (α - onLetter (D.mw t) κ1))
        (c1 * bin κ1 (letE α (D.mw t))) := by
    intro α
    rw [opS_apply, ddiv_monomial', monomial_mul, smul_monomial, bin_onLetter]
    simp
  refine vala_outside_linear (D.opS t μ κ1 c1) (fun i => i = D.mw t)
    (fun i hi h => hS (h ▸ hi)) ?_ ?_ hQ
  · intro α
    rw [hform, hform, monomial_mul, one_mul]
    have e1 : onLetter (D.mw t) μ + (α - onLetter (D.mw t) κ1) =
        eIn (fun i => i = D.mw t) α + (onLetter (D.mw t) μ +
          (eOut (fun i => i = D.mw t) α - onLetter (D.mw t) κ1)) := by
      ext ⟨i, a⟩
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, onLetter_apply, eIn_apply, eOut_apply]
      by_cases hi : i = D.mw t
      · simp [hi]
      · simp [hi]
    have e2 : letE (eOut (fun i => i = D.mw t) α) (D.mw t) = letE α (D.mw t) := by
      ext a
      simp [eOut_apply]
    rw [e1, e2]
  · intro α
    rw [hform]
    refine valS_nonneg_of_vec D.msg S _ fun β hβ i a hne => ?_
    have := support_monomial_subset hβ
    rw [Finset.mem_singleton] at this
    by_cases hi : i = D.mw t
    · rw [hi]; rfl
    · exfalso
      apply hne
      rw [this]
      simp [onLetter_apply, eOut_apply, hi]
theorem mw_not_mem_chainSet (D : TwistData K) (t : D.Tau) (j : Fin D.J) (i : Fin (D.nch j))
    (h : t.1 ≠ D.aux₃ j) : D.mw t ∉ D.chainSet j i := by
  classical
  intro hm
  unfold chainSet wSet at hm
  rcases Finset.mem_union.mp hm with h1 | h1
  · obtain ⟨b, -, hb⟩ := Finset.mem_image.mp h1
    simp [mb, mw] at hb
  · obtain ⟨m, -, hm'⟩ := Finset.mem_image.mp h1
    apply h
    have : (D.aux₃ j, m) = t := by simpa [mw] using hm'
    rw [← this]
theorem ChOK.ddiv [NeZero D.r] (hV2 : V2 K) (hDER : DER K v p) (hD : DVRHyp v p) (hc : 1 ≤ D.c)
    {θ : (j : Fin D.J) → Fin (D.nch j) → ℝ} {a : ℝ}
    {G : MvPolynomial (D.OL × Fin D.r) K} (h : D.ChOK v p θ a G) (t : D.Tau) (M : Fin D.r →₀ ℕ) :
    D.ChOK v p (fun j i => θ j i - (if t.1 = D.aux₃ j then (absE M : ℝ) / (D.P p t : ℝ) + D.c else 0)) a
      (Formalism.MainNotions.PlaneGram.ddiv (onLetter (Sum.inr t) M) G) := by
  classical
  obtain ⟨G0, E, h1, h2, h3, h4⟩ := h
  obtain ⟨I, hI, cls, cf, ρ', δ, κ, hcf, hκ, hder⟩ := der' v p hDER hD D.r (D.g t) M D.c hc
  have hP : 0 < D.P p t := pow_pos hD.prime.pos _
  refine ⟨appL (Sum.inr t) (D.P p t) cls cf ρ' δ κ G0,
    (Formalism.MainNotions.PlaneGram.ddiv (onLetter (Sum.inr t) M) G0 - appL (Sum.inr t) (D.P p t) cls cf ρ' δ κ G0) +
      Formalism.MainNotions.PlaneGram.ddiv (onLetter (Sum.inr t) M) E, ?_, ?_, ?_, ?_⟩
  · rw [h1, ddiv_add]; abel
  · exact cge_appL v _ _ cls cf ρ' δ κ hcf h2
  · exact cge_add v (cge_ddiv_sub_appL v _ (D.P p t) M cls cf ρ' δ κ D.c hder h2) (cge_ddiv v _ h3)
  · intro ρ'' j i
    rw [D.digitPart_appL p t hP]
    refine vala_sum _ _ fun s _ => ?_
    show vala D.msg (D.chainSet j i)
      (θ j i - (if t.1 = D.aux₃ j then (absE M : ℝ) / (D.P p t : ℝ) + D.c else 0)) _
    by_cases hB : (fun a => ρ' s a % D.P p t) = ρ'' t
    · rw [if_pos hB]
      by_cases hj : t.1 = D.aux₃ j
      · rw [if_pos hj]
        refine vala_mono ?_ (vala_opS hV2 t _ _ (κ s) (cf s) (h4 (Function.update ρ'' t (cls s)) j i))
        have := hκ s
        have e : ((D.P p t : ℕ) : ℝ) = (p : ℝ) ^ D.g t := by unfold P; push_cast; rfl
        rw [e]
        linarith
      · rw [if_neg hj, sub_zero]
        exact vala_opS_out t _ (D.mw_not_mem_chainSet t j i hj) _ (κ s) (cf s)
          (h4 (Function.update ρ'' t (cls s)) j i)
    · rw [if_neg hB]
      exact vala_zero _
end TwistData
end Formalism.MainNotions.PlaneGram


