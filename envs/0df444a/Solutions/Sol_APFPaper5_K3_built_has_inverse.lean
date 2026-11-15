-- Prove2me | solution 1 for APFPaper5.K3.built_has_inverse
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T08:01:08.534293+00:00
-- url     : https://prove2.me/submissions/561f2906-0248-4437-aebd-af9ed01912e2

import Theorems.Thm_APFPaper5_K3_relativeTurn_one_zero
/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K3_completeness_without_flip
title: If the rate flip is not admitted, every admitted map of two held components is built from turns and recombinations
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K3_HeldMaps. Author's ruling of 2026-11-13: route C.
consumes_inputs: none. CONDITIONAL INSTANCE in a supplied model. Carries hroot as in
 Thm_APFPaper5_K3_generator_completeness.
statement: (commonTurn_comp, relativeTurn_comp, mix_comp, commonTurn_one_zero, mix_one_zero) turns compose
 by adding, and the turn by nothing is the identity.
 (built_has_inverse) a map built from turns and recombinations is undone by one.
 (generator_completeness_of_no_flip) let the admitted maps contain the built maps, be closed under doing one
 after another, and each be additive, homogeneous, leave the total cost unchanged and the common turn
 unseen. If the rate flip is not admitted, every admitted map is built from turns and recombinations.
not_claimed: that the rate flip is not admitted (see Thm_APFPaper5_K4_completeness_from_composition for one
 route); any K.
-/
import Definitions.Def_APFPaper5_K3_HeldMaps
import Theorems.Thm_APFPaper5_K3_euler_core
import Theorems.Thm_APFPaper5_K3_expand_of_commutes
import Theorems.Thm_APFPaper5_K3_commuting_is_combination_of_built
import Theorems.Thm_APFPaper5_K3_generator_completeness
import Theorems.Thm_APFPaper5_K3_built_iff
import Theorems.Thm_APFPaper5_K3_admitted_is_built_or_flipped
import Theorems.Thm_APFPaper5_K3_admitted_iff
import Theorems.Thm_APFPaper5_K3_generator_completeness_of_halves
import Theorems.Thm_APFPaper5_K3_rateFlip_has_no_admitted_half
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
namespace APFPaper5.K3

theorem commonTurn_comp (c s c' s' : ℝ) (h : Held2) :
    commonTurn c s (commonTurn c' s' h) = commonTurn (c * c' - s * s') (c * s' + s * c') h := by
  apply Held2.ext <;> dsimp only [commonTurn] <;> ring

theorem commonTurn_one_zero (h : Held2) : commonTurn 1 0 h = h := by
  apply Held2.ext <;> dsimp only [commonTurn] <;> ring

theorem relativeTurn_comp (c s c' s' : ℝ) (h : Held2) :
    relativeTurn c s (relativeTurn c' s' h) = relativeTurn (c * c' - s * s') (c * s' + s * c') h := by
  apply Held2.ext <;> dsimp only [relativeTurn] <;> ring

theorem mix_comp (c s c' s' : ℝ) (h : Held2) :
    mix c s (mix c' s' h) = mix (c * c' - s * s') (c * s' + s * c') h := by
  apply Held2.ext <;> dsimp only [mix] <;> ring

theorem mix_one_zero (h : Held2) : mix 1 0 h = h := by
  apply Held2.ext <;> dsimp only [mix] <;> ring

theorem built_has_inverse (U : Held2 → Held2) (hU : BuiltFromTurns U) :
    ∃ V : Held2 → Held2, BuiltFromTurns V ∧ (∀ h : Held2, U (V h) = h) ∧ ∀ h : Held2, V (U h) = h := by
  induction hU with
  | common c s hcs =>
    have e1 : c * c - s * -s = 1 := by linear_combination hcs
    have e2 : c * -s + s * c = 0 := by ring
    have e3 : c * c - -s * s = 1 := by linear_combination hcs
    have e4 : c * s + -s * c = 0 := by ring
    exact ⟨commonTurn c (-s), BuiltFromTurns.common c (-s) (by linear_combination hcs),
      fun h => by rw [commonTurn_comp, e1, e2, commonTurn_one_zero],
      fun h => by rw [commonTurn_comp, e3, e4, commonTurn_one_zero]⟩
  | relative c s hcs =>
    have e1 : c * c - s * -s = 1 := by linear_combination hcs
    have e2 : c * -s + s * c = 0 := by ring
    have e3 : c * c - -s * s = 1 := by linear_combination hcs
    have e4 : c * s + -s * c = 0 := by ring
    exact ⟨relativeTurn c (-s), BuiltFromTurns.relative c (-s) (by linear_combination hcs),
      fun h => by rw [relativeTurn_comp, e1, e2, relativeTurn_one_zero],
      fun h => by rw [relativeTurn_comp, e3, e4, relativeTurn_one_zero]⟩
  | recombine c s hcs =>
    have e1 : c * c - s * -s = 1 := by linear_combination hcs
    have e2 : c * -s + s * c = 0 := by ring
    have e3 : c * c - -s * s = 1 := by linear_combination hcs
    have e4 : c * s + -s * c = 0 := by ring
    exact ⟨mix c (-s), BuiltFromTurns.recombine c (-s) (by linear_combination hcs),
      fun h => by rw [mix_comp, e1, e2, mix_one_zero],
      fun h => by rw [mix_comp, e3, e4, mix_one_zero]⟩
  | @comp S T _ _ ihS ihT =>
    obtain ⟨S', bS, l1, r1⟩ := ihS
    obtain ⟨T', bT, l2, r2⟩ := ihT
    refine ⟨fun h => T' (S' h), BuiltFromTurns.comp bT bS, fun h => ?_, fun h => ?_⟩
    · show S (T (T' (S' h))) = h
      rw [l2, l1]
    · show T' (S' (S (T h))) = h
      rw [r1, r2]

theorem generator_completeness_of_no_flip
    (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, 0 ≤ r ∧ r * r = t) (Adm : Set (Held2 → Held2))
    (hbuilt : ∀ U : Held2 → Held2, BuiltFromTurns U → U ∈ Adm)
    (hcomp : ∀ S ∈ Adm, ∀ T ∈ Adm, (fun h => S (T h)) ∈ Adm)
    (hadm : ∀ T ∈ Adm, AdditiveHomogeneous T ∧ PreservesTotalCost T ∧ CommonTurnUnseenAfter T)
    (hflip : rateFlip ∉ Adm) : ∀ T ∈ Adm, BuiltFromTurns T := by
  intro T hT
  obtain ⟨hlin, hcost, hun⟩ := hadm T hT
  rcases admitted_is_built_or_flipped hroot T hlin hcost hun with hb | hb
  · exact hb
  · exfalso
    obtain ⟨V, bV, l, _⟩ := built_has_inverse _ hb
    have hmem := hcomp T hT V (hbuilt V bV)
    have e : (fun h => T (V h)) = rateFlip := by
      funext h
      have k : rateFlip (T (V h)) = h := l h
      have k' := congrArg rateFlip k
      rw [rateFlip_rateFlip] at k'
      exact k'
    rw [e] at hmem
    exact hflip hmem

end APFPaper5.K3


theorem solution :
∀ (U : APFPaper5.K3.Held2 → APFPaper5.K3.Held2) (hU : APFPaper5.K3.BuiltFromTurns U),
  @Exists.{1} (APFPaper5.K3.Held2 → APFPaper5.K3.Held2) fun (V : APFPaper5.K3.Held2 → APFPaper5.K3.Held2) =>
    And (APFPaper5.K3.BuiltFromTurns V)
      (And (∀ (h : APFPaper5.K3.Held2), @Eq.{1} APFPaper5.K3.Held2 (U (V h)) h)
        (∀ (h : APFPaper5.K3.Held2), @Eq.{1} APFPaper5.K3.Held2 (V (U h)) h)) := by
  exact @APFPaper5.K3.built_has_inverse
