-- Prove2me | solution 1 for ALAVI.eq_47
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T19:58:14.271093+00:00
-- url     : https://prove2.me/submissions/fc9873de-4857-4a26-9b62-3c7900a0a5bc

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_CalamaiMore_Convergence_proj
import Definitions.Def_ALAVI_Standing
import Definitions.Def_ALAVI_Params
import Definitions.Def_ALAVI_IsALAVIRun

namespace Aux_ALAVI47

theorem proj_spec {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (K : Set F) (hne : K.Nonempty) (hcl : IsClosed K)
    (hconv : Convex ℝ K) (x : F) :
    CalamaiMore.Convergence.proj K x ∈ K ∧
      ∀ w ∈ K, inner ℝ (x - CalamaiMore.Convergence.proj K x)
        (w - CalamaiMore.Convergence.proj K x) ≤ 0 := by
  haveI : Nonempty K := hne.to_subtype
  have hbdd : BddBelow (Set.range fun w : K => ‖x - (w : F)‖) :=
    ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
  obtain ⟨v, hvK, hv⟩ := exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hconv x
  have hex : ∃ z ∈ K, ∀ w ∈ K, ‖z - x‖ ≤ ‖w - x‖ := by
    refine ⟨v, hvK, fun w hw => ?_⟩
    rw [norm_sub_rev v x, norm_sub_rev w x, hv]
    exact ciInf_le hbdd ⟨w, hw⟩
  unfold CalamaiMore.Convergence.proj CalamaiMore.Convergence.nearestPoint
  rw [dif_pos hex]
  have hz := Classical.choose_spec hex
  refine ⟨hz.1, ?_⟩
  rw [← norm_eq_iInf_iff_real_inner_le_zero hconv hz.1]
  apply le_antisymm
  · apply le_ciInf
    intro w
    rw [norm_sub_rev x, norm_sub_rev x]
    exact hz.2 w w.2
  · exact ciInf_le hbdd ⟨_, hz.1⟩

end Aux_ALAVI47

open ALAVI in
theorem solution {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (U : Set E) (C : ProperCone ℝ F) (G : E → E) (J : E → EReal) (Θ : E → F) (L τ η α γ : ℝ) (v u : ℕ → E) (p q : ℕ → F)
    (hA : Standing U C G J Θ L τ) (hP : Params η α γ L τ)
    (hrun : IsALAVIRun U C G J Θ η α γ v u p q)
    (k : ℕ) (hk : 2 ≤ k) (b : F) (hb : b ∈ ProperCone.innerDual (C : Set F)) :
    inner ℝ (b - p k) (Θ (u k)) ≤ 1 / γ * inner ℝ (b - p k) (p k - p (k - 1)) ∧
      1 / γ * inner ℝ (b - p k) (p k - p (k - 1)) =
        1 / (2 * γ) * (‖b - p (k - 1)‖ ^ 2 - ‖b - p k‖ ^ 2 - ‖p (k - 1) - p k‖ ^ 2) := by
  have hγ : 0 < γ := hP.2.2.1
  set K : ProperCone ℝ F := ProperCone.innerDual (C : Set F) with hKdef
  have hstep := (hrun (k - 1) (by omega)).2.2.2
  have hk' : k - 1 + 1 = k := by omega
  rw [hk'] at hstep
  have hspec := (Aux_ALAVI47.proj_spec (K : Set F) K.nonempty K.isClosed K.convex
    (p (k - 1) + γ • Θ (u k))).2 b hb
  rw [← hstep] at hspec
  have hz : p (k - 1) + γ • Θ (u k) - p k = -(p k - p (k - 1)) + γ • Θ (u k) := by abel
  rw [hz, inner_add_left, inner_neg_left, real_inner_smul_left,
    real_inner_comm (b - p k) (p k - p (k - 1)), real_inner_comm (b - p k) (Θ (u k))] at hspec
  constructor
  · rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hγ]
    linarith
  · have hb' : b - p (k - 1) = (b - p k) + (p k - p (k - 1)) := by abel
    have h1 : ‖b - p (k - 1)‖ ^ 2 =
        ‖b - p k‖ ^ 2 + 2 * inner ℝ (b - p k) (p k - p (k - 1)) + ‖p k - p (k - 1)‖ ^ 2 := by
      rw [hb']
      exact norm_add_sq_real _ _
    have h2 : ‖p (k - 1) - p k‖ = ‖p k - p (k - 1)‖ := norm_sub_rev _ _
    rw [h1, h2]
    ring
