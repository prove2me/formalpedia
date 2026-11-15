-- Prove2me | solution 1 for APFB01.recorded_map_is_built_or_flipped
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T08:01:09.8962+00:00
-- url     : https://prove2.me/submissions/33813ea6-09b8-4fe2-a1aa-e1ab29b1814c

import Theorems.Thm_APFB01_fact_agrees_of_same_profile
import Theorems.Thm_APFPaper5_K3_plainAfterTurn_commonTurn
/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFB01_admitted_maps
title: If what is recorded after a map is a physical fact, the common turn is unseen after it, and the map is built from turns and recombinations or is such a map followed by the rate flip
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: FOUNDATION_INPUTS B01 ("Physical facts are fixed by that structure"). As Def_APFPaper5_K3_HeldMaps.
consumes_inputs: B01, in the sense that the hypothesis hfact is one of its descent statements, taken at the
 model's continuation profile. CONDITIONAL INSTANCE in a supplied model. Carries hroot as in
 Thm_APFPaper5_K3_generator_completeness.
statement: (APFB01.common_turn_unseen_after_of_descends) if, for every value, "the continuation profile after
 T has this value" descends to the quotient by continuation profile, the common turn is unseen after T.
 (APFB01.recorded_map_is_built_or_flipped) if moreover T is additive, homogeneous and leaves the total cost
 unchanged, T is built from turns and recombinations or is such a map followed by the rate flip.
not_claimed: that what is recorded after a given map at an interface is a physical fact; that the model's
 continuation profile is the original one; any K.
-/
import Definitions.Def_APF_B01_DeclaredInput
import Definitions.Def_APFPaper5_K3_HeldMaps
import Theorems.Thm_APFB01_unseen_turn_changes_no_fact
import Theorems.Thm_APFPaper5_K3_euler_core
import Theorems.Thm_APFPaper5_K3_expand_of_commutes
import Theorems.Thm_APFPaper5_K3_commuting_is_combination_of_built
import Theorems.Thm_APFPaper5_K3_generator_completeness
import Theorems.Thm_APFPaper5_K3_built_iff
import Theorems.Thm_APFPaper5_K3_admitted_is_built_or_flipped
import Theorems.Thm_APFPaper5_K3_admitted_iff
import Theorems.Thm_APFPaper5_K3_generator_completeness_of_halves
import Theorems.Thm_APFPaper5_K3_rateFlip_has_no_admitted_half

set_option autoImplicit false

open APFPaper5.K3 in
theorem APFB01.common_turn_unseen_after_of_descends (T : Held2 → Held2)
    (hfact : ∀ P : ℝ × ℝ × (ℝ × ℝ × ℝ) → Prop,
      APFB01.Descends plainAfterTurn (fun h : Held2 => plainAfterTurn (T h) = P)) :
    CommonTurnUnseenAfter T := by
  intro c s hcs h
  exact (APFB01.fact_agrees_of_same_profile plainAfterTurn _ (hfact (plainAfterTurn (T h)))
    (commonTurn c s h) h (plainAfterTurn_commonTurn c s hcs h)).mpr rfl

open APFPaper5.K3 in
theorem APFB01.recorded_map_is_built_or_flipped
    (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, 0 ≤ r ∧ r * r = t) (T : Held2 → Held2)
    (hlin : AdditiveHomogeneous T) (hcost : PreservesTotalCost T)
    (hfact : ∀ P : ℝ × ℝ × (ℝ × ℝ × ℝ) → Prop,
      APFB01.Descends plainAfterTurn (fun h : Held2 => plainAfterTurn (T h) = P)) :
    BuiltFromTurns T ∨ BuiltFromTurns (fun h => rateFlip (T h)) :=
  APFPaper5.K3.admitted_is_built_or_flipped hroot T hlin hcost
    (APFB01.common_turn_unseen_after_of_descends T hfact)


theorem solution :
∀
  (hroot :
    ∀ (t : Real),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) t →
        @Exists.{1} Real fun (r : Real) =>
          And
            (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r)
            (@Eq.{1} Real (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) r r) t))
  (T : APFPaper5.K3.Held2 → APFPaper5.K3.Held2) (hlin : APFPaper5.K3.AdditiveHomogeneous T)
  (hcost : APFPaper5.K3.PreservesTotalCost T)
  (hfact :
    ∀ (P : Prod.{0, 0} Real (Prod.{0, 0} Real (Prod.{0, 0} Real (Prod.{0, 0} Real Real))) → Prop),
      @APFB01.Descends.{0, 0} APFPaper5.K3.Held2
        (Prod.{0, 0} Real (Prod.{0, 0} Real (Prod.{0, 0} Real (Prod.{0, 0} Real Real)))) APFPaper5.K3.plainAfterTurn
        fun (h : APFPaper5.K3.Held2) =>
        @Eq.{1} ((x : Prod.{0, 0} Real (Prod.{0, 0} Real (Prod.{0, 0} Real (Prod.{0, 0} Real Real)))) → Prop)
          (APFPaper5.K3.plainAfterTurn (T h)) P),
  Or (APFPaper5.K3.BuiltFromTurns T)
    (APFPaper5.K3.BuiltFromTurns fun (h : APFPaper5.K3.Held2) => APFPaper5.K3.rateFlip (T h)) := by
  exact @APFB01.recorded_map_is_built_or_flipped
