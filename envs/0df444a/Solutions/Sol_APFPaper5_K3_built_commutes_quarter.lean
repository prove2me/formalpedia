-- Prove2me | solution 1 for APFPaper5.K3.built_commutes_quarter
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:31:23.258414+00:00
-- url     : https://prove2.me/submissions/fab72f83-66cf-421b-8958-e306e216bf08

import Theorems.Thm_APFPaper5_K3_plainAfterTurn_commonTurn
import Theorems.Thm_APFPaper5_K3_relative_commutes_common
/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K3_built_from_turns
title: Maps built from turns and recombinations commute with the quarter turn; a one-plane turn and the rate flip are not among them
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K3_HeldMaps.
consumes_inputs: none. CONDITIONAL INSTANCE in a supplied model.
statement: (built_commutes_common, built_commutes_quarter, built_additiveHomogeneous,
 built_preserves_totalCost, built_unseen) a map built from common turns, turns of one component and
 recombinations commutes with every common turn, is additive and homogeneous, leaves the total cost
 unchanged, and leaves the common turn unseen.
 (onePlaneQuarter_*) the one-plane quarter turn is additive, homogeneous and leaves the total cost unchanged,
 but after it the common turn is seen. So it is not built from turns and recombinations.
 (rateFlip_*) the rate flip is additive, homogeneous, leaves the total cost unchanged and leaves the common
 turn unseen, but it is not built from turns and recombinations.
 (rateFlip_comp_commutes) following a map that anticommutes with the quarter turn by the rate flip gives a
 map that commutes with it.
reading: leaving cost unchanged does not confine the admitted maps to those built from turns and
 recombinations. Keeping the common turn unseen removes the one-plane turn. It does not remove the rate flip.
not_claimed: which maps are admitted at an interface; any K.
-/
import Definitions.Def_APFPaper5_K3_HeldMaps
import Theorems.Thm_APFPaper5_K3_records_of_plainAfterTurn_eq
import Theorems.Thm_APFPaper5_K3_plainAfterTurn_eq_iff_records
import Theorems.Thm_APFPaper5_K3_pair_dichotomy
import Theorems.Thm_APFPaper5_K3_unseen_dichotomy
import Theorems.Thm_APFPaper5_K3_unseen_of_anticommutes
import Theorems.Thm_APFPaper5_K3_unseen_iff
import Theorems.Thm_APFPaper5_K3_square_commutes_quarter
import Theorems.Thm_APFPaper5_K3_unseen_of_fixed_by_records
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace APFPaper5.K3

theorem common_commutes_common (c s c' s' : ℝ) (h : Held2) :
    commonTurn c' s' (commonTurn c s h) = commonTurn c s (commonTurn c' s' h) := by
  apply Held2.ext <;> dsimp only [commonTurn] <;> ring

theorem mix_commutes_common (c s c' s' : ℝ) (h : Held2) :
    mix c' s' (commonTurn c s h) = commonTurn c s (mix c' s' h) := by
  apply Held2.ext <;> dsimp only [commonTurn, mix] <;> ring

theorem built_commutes_common (T : Held2 → Held2) (hT : BuiltFromTurns T) (c s : ℝ) (h : Held2) :
    T (commonTurn c s h) = commonTurn c s (T h) := by
  induction hT generalizing h with
  | common c' s' _ => exact common_commutes_common c s c' s' h
  | relative c' s' _ => exact relative_commutes_common c s c' s' h
  | recombine c' s' _ => exact mix_commutes_common c s c' s' h
  | @comp S T _ _ ihS ihT =>
    show S (T (commonTurn c s h)) = commonTurn c s (S (T h))
    rw [ihT h, ihS]

theorem built_commutes_quarter (T : Held2 → Held2) (hT : BuiltFromTurns T) : CommutesWithQuarter T :=
  fun h => built_commutes_common T hT 0 1 h

theorem commonTurn_additiveHomogeneous (c s : ℝ) : AdditiveHomogeneous (commonTurn c s) :=
  ⟨fun x y => by apply Held2.ext <;> dsimp only [commonTurn, add2] <;> ring,
   fun r x => by apply Held2.ext <;> dsimp only [commonTurn, smul2] <;> ring⟩

theorem relativeTurn_additiveHomogeneous (c s : ℝ) : AdditiveHomogeneous (relativeTurn c s) :=
  ⟨fun x y => by apply Held2.ext <;> dsimp only [relativeTurn, add2] <;> ring,
   fun r x => by apply Held2.ext <;> dsimp only [relativeTurn, smul2] <;> ring⟩

theorem mix_additiveHomogeneous (c s : ℝ) : AdditiveHomogeneous (mix c s) :=
  ⟨fun x y => by apply Held2.ext <;> dsimp only [mix, add2] <;> ring,
   fun r x => by apply Held2.ext <;> dsimp only [mix, smul2] <;> ring⟩

theorem comp_additiveHomogeneous (S T : Held2 → Held2) (hS : AdditiveHomogeneous S)
    (hT : AdditiveHomogeneous T) : AdditiveHomogeneous (fun h => S (T h)) :=
  ⟨fun x y => by show S (T (add2 x y)) = add2 (S (T x)) (S (T y)); rw [hT.1, hS.1],
   fun r x => by show S (T (smul2 r x)) = smul2 r (S (T x)); rw [hT.2, hS.2]⟩

theorem built_additiveHomogeneous (T : Held2 → Held2) (hT : BuiltFromTurns T) :
    AdditiveHomogeneous T := by
  induction hT with
  | common c s _ => exact commonTurn_additiveHomogeneous c s
  | relative c s _ => exact relativeTurn_additiveHomogeneous c s
  | recombine c s _ => exact mix_additiveHomogeneous c s
  | comp _ _ ihS ihT => exact comp_additiveHomogeneous _ _ ihS ihT

theorem commonTurn_totalCost (c s : ℝ) (hcs : c * c + s * s = 1) (h : Held2) :
    totalCost (commonTurn c s h) = totalCost h := by
  dsimp only [totalCost, recA, recB, commonTurn]
  linear_combination (h.a1 * h.a1 + h.a2 * h.a2 + h.b1 * h.b1 + h.b2 * h.b2) * hcs

theorem relativeTurn_totalCost (c s : ℝ) (hcs : c * c + s * s = 1) (h : Held2) :
    totalCost (relativeTurn c s h) = totalCost h := by
  dsimp only [totalCost, recA, recB, relativeTurn]
  linear_combination (h.b1 * h.b1 + h.b2 * h.b2) * hcs

theorem mix_totalCost (c s : ℝ) (hcs : c * c + s * s = 1) (h : Held2) :
    totalCost (mix c s h) = totalCost h := by
  dsimp only [totalCost, recA, recB, mix]
  linear_combination (h.a1 * h.a1 + h.a2 * h.a2 + h.b1 * h.b1 + h.b2 * h.b2) * hcs

theorem built_preserves_totalCost (T : Held2 → Held2) (hT : BuiltFromTurns T) :
    PreservesTotalCost T := by
  induction hT with
  | common c s hcs => exact commonTurn_totalCost c s hcs
  | relative c s hcs => exact relativeTurn_totalCost c s hcs
  | recombine c s hcs => exact mix_totalCost c s hcs
  | comp _ _ ihS ihT => exact fun h => (ihS _).trans (ihT h)

theorem built_unseen (T : Held2 → Held2) (hT : BuiltFromTurns T) : CommonTurnUnseenAfter T := by
  intro c s hcs h
  rw [built_commutes_common T hT c s h, plainAfterTurn_commonTurn c s hcs]

theorem onePlaneQuarter_additiveHomogeneous : AdditiveHomogeneous onePlaneQuarter :=
  ⟨fun x y => Held2.ext (by dsimp only [onePlaneQuarter, add2]; ring) rfl rfl rfl,
   fun r x => Held2.ext (by dsimp only [onePlaneQuarter, smul2]; ring) rfl rfl rfl⟩

theorem onePlaneQuarter_preserves_totalCost : PreservesTotalCost onePlaneQuarter := by
  intro h
  dsimp only [totalCost, recA, recB, onePlaneQuarter]
  ring

theorem onePlaneQuarter_makes_common_turn_seen : ¬ CommonTurnUnseenAfter onePlaneQuarter := by
  intro hun
  have hA := (records_of_plainAfterTurn_eq _ _ (hun 0 1 (by norm_num) ⟨1, 0, 0, 0⟩)).1
  dsimp only [recA, onePlaneQuarter, commonTurn] at hA
  norm_num at hA

theorem onePlaneQuarter_not_built : ¬ BuiltFromTurns onePlaneQuarter :=
  fun hT => onePlaneQuarter_makes_common_turn_seen (built_unseen _ hT)

theorem rateFlip_additiveHomogeneous : AdditiveHomogeneous rateFlip :=
  ⟨fun x y => by apply Held2.ext <;> dsimp only [rateFlip, add2] <;> ring,
   fun r x => by apply Held2.ext <;> dsimp only [rateFlip, smul2] <;> ring⟩

theorem rateFlip_preserves_totalCost : PreservesTotalCost rateFlip := by
  intro h
  dsimp only [totalCost, recA, recB, rateFlip]
  ring

theorem rateFlip_anticommutesWithQuarter : AnticommutesWithQuarter rateFlip := by
  intro h
  apply Held2.ext <;> dsimp only [commonTurn, rateFlip, neg2] <;> ring

theorem rateFlip_unseen : CommonTurnUnseenAfter rateFlip :=
  unseen_of_anticommutes rateFlip rateFlip_additiveHomogeneous rateFlip_anticommutesWithQuarter

theorem rateFlip_not_built : ¬ BuiltFromTurns rateFlip := by
  intro hT
  have h2 := congrArg Held2.a2 (built_commutes_quarter _ hT ⟨1, 0, 0, 0⟩)
  dsimp only [commonTurn, rateFlip] at h2
  norm_num at h2

theorem rateFlip_comp_commutes (T : Held2 → Held2) (ha : AnticommutesWithQuarter T) :
    CommutesWithQuarter (fun h => rateFlip (T h)) := by
  intro h
  show rateFlip (T (commonTurn 0 1 h)) = commonTurn 0 1 (rateFlip (T h))
  rw [ha h]
  apply Held2.ext <;> dsimp only [commonTurn, rateFlip, neg2] <;> ring

theorem rateFlip_rateFlip (h : Held2) : rateFlip (rateFlip h) = h := by
  apply Held2.ext <;> dsimp only [rateFlip] <;> ring

end APFPaper5.K3


theorem solution :
∀ (T : APFPaper5.K3.Held2 → APFPaper5.K3.Held2) (hT : APFPaper5.K3.BuiltFromTurns T), APFPaper5.K3.CommutesWithQuarter T := by
  exact @APFPaper5.K3.built_commutes_quarter
