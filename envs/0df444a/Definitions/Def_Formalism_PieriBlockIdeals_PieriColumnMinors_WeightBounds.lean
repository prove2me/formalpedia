-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightBounds
-- name    : Formalism_PieriBlockIdeals_PieriColumnMinors_WeightBounds
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T23:20:33.028085+00:00
-- url     : https://prove2.me/theorems/4286bd25-7898-4314-ade1-bf71d3f4288f
-- title:
--   Weight Bounds
-- statement:
--   Definitions and structural lemmas for Weight Bounds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WeightBounds.lean

import Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionRealSettingAlt
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
namespace Formalism.CohomologicalDescent.ShortWeightBounds
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem weight_on_block_eq_bot_add (P : Par) (hP : P.Hyp) {ι : Type} (W : Wts ι) (hW : W.Ok P) (τ : ι) (a : ℕ)
    (h1 : kc P + W.j τ ≤ a) (h2 : a < kc P + W.j τ + P.t) :
    W.U P τ a = W.bot P τ + ((kc P + W.j τ + P.t - 1 - a : ℕ) : ℤ) := by
  have ht := hP.t_ge
  have e1 := hW.block τ a h1 h2
  have e2 := hW.block τ (kc P + W.j τ + P.t - 1) (by omega) (by omega)
  unfold Wts.bot Wts.U UN
  rw [e1, e2]
  omega
theorem top_eq_bot_add_t_sub_one (P : Par) (hP : P.Hyp) {ι : Type} (W : Wts ι) (hW : W.Ok P) (τ : ι) :
    W.top P τ = W.bot P τ + (P.t : ℤ) - 1 := by
  have ht := hP.t_ge
  have e := weight_on_block_eq_bot_add P hP W hW τ (kc P + W.j τ) le_rfl (by omega)
  unfold Wts.top
  rw [e]
  omega
theorem rank_fits_block_and_t_ge_six (P : Par) (hP : P.Hyp) {ι : Type} (W : Wts ι) (hW : W.Ok P) (τ : ι) :
    kc P + W.j τ + P.t ≤ P.Nr ∧ 6 ≤ P.t := by
  have h1 := hW.what₂ τ
  have h2 := hP.t_ge
  have h3 := hP.m_pos
  have h4 := hP.m_le
  omega
theorem weights_have_positive_shape (P : Par) (hP : P.Hyp) {ι : Type} (W : Wts ι) (hW : W.Ok P) (τ : ι) :
    P.Shape (W.Uset P τ) (W.bot P τ) (W.c τ) (W.e τ) 1 := by
  have hr := rank_fits_block_and_t_ge_six P hP W hW τ
  refine ⟨Or.inl rfl, ?_, ?_⟩
  · have := hW.centre τ
    push_cast
    linarith
  · intro u hu hnot
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
    have ha' : a < P.Nr := Finset.mem_range.mp ha
    push_cast
    rw [one_mul]
    by_cases h1 : a < kc P
    · left
      have h2 := hW.cloud τ a h1
      have h3 := hW.window τ
      have h4 : (W.xm τ : ℝ) ≤ (W.U P τ a : ℝ) := by exact_mod_cast h2.1
      have h5 : (W.U P τ a : ℝ) ≤ (W.xp τ : ℝ) := by exact_mod_cast h2.2
      constructor <;> linarith [h3.1, h3.2.2]
    · right
      by_cases hb : kc P + W.j τ ≤ a ∧ a < kc P + W.j τ + P.t
      · exfalso
        apply hnot
        have e := weight_on_block_eq_bot_add P hP W hW τ a hb.1 hb.2
        rw [Finset.mem_Icc, e]
        constructor <;> omega
      · refine hW.low τ a ha' ?_
        by_cases h3 : a < kc P + W.j τ
        · exact Or.inl ⟨by omega, h3⟩
        · right
          by_contra h4
          exact hb ⟨by omega, by omega⟩
theorem shape_reflect (P : Par) (U : Finset ℤ) (bot H : ℤ) (c e : ℝ) (h : P.Shape U bot c e 1) :
    P.Shape (U.image (fun u => H - u)) (H - (bot + (P.t : ℤ) - 1)) ((H : ℝ) - c) e (-1) := by
  obtain ⟨-, h2, h3⟩ := h
  refine ⟨Or.inr rfl, ?_, ?_⟩
  · push_cast at h2 ⊢
    linarith
  · intro u' hu' hnot
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hu'
    have hn : u ∉ Finset.Icc bot (bot + (P.t : ℤ) - 1) := by
      intro hm
      apply hnot
      rw [Finset.mem_Icc] at hm ⊢
      constructor <;> omega
    have h4 := h3 u hu hn
    have e1 : (((-1 : ℤ) : ℝ)) * (((H - u : ℤ) : ℝ) - ((H : ℝ) - c)) = ((1 : ℤ) : ℝ) * ((u : ℝ) - c) := by
      push_cast; ring
    rw [e1]
    exact h4
theorem thick_or_top_or_thin (P : Par) {ι : Type} (W : Wts ι) (hW : W.Ok P) (τ : ι) :
    P.Thick (W.e τ) ∨ P.Top (W.e τ) ∨ P.Thin (W.e τ) := by
  by_cases h : τ ∈ W.T2
  · exact Or.inl (hW.thick τ h).1
  · rcases hW.other τ h with h1 | h1
    · exact Or.inr (Or.inl h1.1)
    · exact Or.inr (Or.inr h1.1)
def placesOfParameters (P : Par) (hP : P.Hyp) {ι : Type} (W : Wts ι) (hW : W.Ok P) (J : ℕ → ℕ) :
    Places (W.sizeData₂ P J) P where
  U := W.Uset P
  bot := W.bot P
  c := W.c
  e := W.e
  σ := fun _ => 1
  UF := W.UsetF P
  botF := W.botF P
  cF := fun τ l => if W.cj l τ then ((h0 P : ℤ) : ℝ) - W.c (W.fr l τ) else W.c (W.fr l τ)
  eF := fun τ l => W.e (W.fr l τ)
  σF := fun τ l => if W.cj l τ then -1 else 1
  shape := fun τ => weights_have_positive_shape P hP W hW τ
  kind := fun τ => thick_or_top_or_thin P W hW τ
  shapeF := by
    intro τ l
    cases h : W.cj l τ
    · simp only [Wts.UsetF, Wts.botF, h, Bool.false_eq_true, if_false]
      exact weights_have_positive_shape P hP W hW _
    · simp only [Wts.UsetF, Wts.botF, h, if_true]
      rw [top_eq_bot_add_t_sub_one P hP W hW]
      exact shape_reflect P _ _ _ _ _ (weights_have_positive_shape P hP W hW _)
  kindF := fun τ l => thick_or_top_or_thin P W hW _
  mw_eq := fun _ _ => rfl
  mwF_eq := fun _ _ => rfl
end Formalism.CohomologicalDescent.ShortWeightBounds


