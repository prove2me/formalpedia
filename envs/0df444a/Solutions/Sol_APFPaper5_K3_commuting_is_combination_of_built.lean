-- Prove2me | solution 1 for APFPaper5.K3.commuting_is_combination_of_built
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:50:23.705348+00:00
-- url     : https://prove2.me/submissions/b8630422-efef-49de-8803-3175f4b02eb3

import Theorems.Thm_APFPaper5_K3_plainAfterTurn_commonTurn
import Theorems.Thm_APFPaper5_K3_rateFlip_reverses_turn
/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K3_generator_completeness
title: On two held components, every additive homogeneous map that leaves the total cost unchanged and the common turn unseen is built from turns and recombinations, or is such a map followed by the rate flip
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K3_HeldMaps. Paper 5 Supplement v7.33:2004-2012 carries generator completeness as
 consumed, not derived.
consumes_inputs: none. CONDITIONAL INSTANCE in a supplied model. One pure-mathematics hypothesis is carried
 in the open: hroot, that every nonnegative real is a square. It is a theorem of Mathlib (Real.sqrt) that
 the session build does not reach; the box discharges it in one line.
statement: (exists_polar) every pair of reals is a real multiple of a unit pair.
 (commuting_is_combination_of_built) an additive homogeneous map that commutes with the quarter turn is a
 real combination of eight maps built from turns and recombinations. No cost condition and no hroot.
 (commuting_cost_preserving_decomposes) an additive homogeneous map that leaves the total cost unchanged and
 commutes with the quarter turn is a common turn after a turn of one component after a recombination after a
 turn of one component.
 (generator_completeness, built_iff) so it is built from turns and recombinations, and the maps so built are
 exactly these.
 (admitted_is_built_or_flipped, admitted_iff) an additive homogeneous map that leaves the total cost
 unchanged and the common turn unseen is built from turns and recombinations, or is such a map followed by
 the rate flip; and conversely.
 (square_is_built) the square of such a map is built from turns and recombinations.
 (generator_completeness_of_halves) if every admitted map is additive, homogeneous, leaves the total cost
 unchanged and the common turn unseen, and every admitted map is an admitted map done twice, then every
 admitted map is built from turns and recombinations.
 (rateFlip_has_no_admitted_half) the rate flip is no such map done twice.
reading: on this carrier generator completeness is a theorem for the maps that commute with the quarter turn.
 What stands between the admitted maps and the built ones is the rate flip alone.
not_claimed: that an interface is this carrier; that admitted maps there are additive, homogeneous and leave
 the total cost unchanged; that the rate flip is excluded; generator completeness of the Supplement's
 represented algebra; any K.
-/
import Definitions.Def_APFPaper5_K3_HeldMaps
import Definitions.Def_APFPaper5_K3_TwoPoint
import Theorems.Thm_APFPaper5_K3_built_commutes_common
import Theorems.Thm_APFPaper5_K3_built_commutes_quarter
import Theorems.Thm_APFPaper5_K3_comp_additiveHomogeneous
import Theorems.Thm_APFPaper5_K3_built_additiveHomogeneous
import Theorems.Thm_APFPaper5_K3_built_preserves_totalCost
import Theorems.Thm_APFPaper5_K3_built_unseen
import Theorems.Thm_APFPaper5_K3_onePlaneQuarter_not_built
import Theorems.Thm_APFPaper5_K3_rateFlip_additiveHomogeneous
import Theorems.Thm_APFPaper5_K3_rateFlip_preserves_totalCost
import Theorems.Thm_APFPaper5_K3_rateFlip_not_built
import Theorems.Thm_APFPaper5_K3_rateFlip_comp_commutes
import Theorems.Thm_APFPaper5_K3_rateFlip_rateFlip
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
namespace APFPaper5.K3

theorem exists_polar (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, 0 ≤ r ∧ r * r = t) (x y : ℝ) :
    ∃ r c s : ℝ, c * c + s * s = 1 ∧ x = r * c ∧ y = r * s := by
  obtain ⟨r, _, hr⟩ := hroot (x * x + y * y) (add_nonneg (mul_self_nonneg x) (mul_self_nonneg y))
  by_cases hz : r = 0
  · have h0 : x * x + y * y = 0 := by rw [← hr, hz]; ring
    obtain ⟨hx, hy⟩ := mul_self_add_mul_self_eq_zero.mp h0
    exact ⟨0, 1, 0, by norm_num, by rw [hx]; ring, by rw [hy]; ring⟩
  · refine ⟨r, x / r, y / r, ?_, ?_, ?_⟩
    · rw [div_mul_div_comm, div_mul_div_comm, ← add_div, ← hr]
      exact div_self (mul_ne_zero hz hz)
    · field_simp
    · field_simp

theorem euler_core (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, 0 ≤ r ∧ r * r = t)
    (p1 p2 p3 p4 q1 q2 q3 q4 : ℝ)
    (hN1 : p1 * p1 + p2 * p2 + p3 * p3 + p4 * p4 = 1)
    (hN2 : q1 * q1 + q2 * q2 + q3 * q3 + q4 * q4 = 1)
    (hO1 : p1 * q1 + p2 * q2 + p3 * q3 + p4 * q4 = 0)
    (hO2 : p2 * q1 - p1 * q2 + p4 * q3 - p3 * q4 = 0) :
    ∃ c0 s0 c1 s1 c2 s2 c3 s3 : ℝ, c0 * c0 + s0 * s0 = 1 ∧ c1 * c1 + s1 * s1 = 1 ∧
      c2 * c2 + s2 * s2 = 1 ∧ c3 * c3 + s3 * s3 = 1 ∧
      ∀ h : Held2,
        (⟨h.a1 * p1 - h.a2 * p2 + h.b1 * q1 - h.b2 * q2, h.a1 * p2 + h.a2 * p1 + h.b1 * q2 + h.b2 * q1,
          h.a1 * p3 - h.a2 * p4 + h.b1 * q3 - h.b2 * q4,
          h.a1 * p4 + h.a2 * p3 + h.b1 * q4 + h.b2 * q3⟩ : Held2) =
        commonTurn c0 s0 (relativeTurn c1 s1 (mix c2 s2 (relativeTurn c3 s3 h))) := by
  obtain ⟨L1, hL1⟩ : ∃ L1 : ℝ, L1 = (p1 * q3 - p2 * q4) - (p3 * q1 - p4 * q2) := ⟨_, rfl⟩
  obtain ⟨L2, hL2⟩ : ∃ L2 : ℝ, L2 = (p1 * q4 + p2 * q3) - (p3 * q2 + p4 * q1) := ⟨_, rfl⟩
  have hL : L1 * L1 + L2 * L2 = 1 := by
    rw [hL1, hL2]
    linear_combination (q1 * q1 + q2 * q2 + q3 * q3 + q4 * q4) * hN1 + hN2 -
      (p1 * q1 + p2 * q2 + p3 * q3 + p4 * q4) * hO1 - (p2 * q1 - p1 * q2 + p4 * q3 - p3 * q4) * hO2
  have hq1 : q1 = -(L1 * p3 + L2 * p4) := by
    rw [hL1, hL2]
    linear_combination (-q1) * hN1 + p1 * hO1 + p2 * hO2
  have hq2 : q2 = -(L2 * p3 - L1 * p4) := by
    rw [hL1, hL2]
    linear_combination (-q2) * hN1 + p2 * hO1 - p1 * hO2
  have hq3 : q3 = L1 * p1 + L2 * p2 := by
    rw [hL1, hL2]
    linear_combination (-q3) * hN1 + p3 * hO1 + p4 * hO2
  have hq4 : q4 = L2 * p1 - L1 * p2 := by
    rw [hL1, hL2]
    linear_combination (-q4) * hN1 + p4 * hO1 - p3 * hO2
  clear hL1 hL2 hN2 hO1 hO2
  obtain ⟨r1, ca, sa, hua, hp1, hp2⟩ := exists_polar hroot p1 p2
  obtain ⟨r2, cb, sb, hub, hp3, hp4⟩ := exists_polar hroot p3 p4
  subst hp1 hp2 hp3 hp4
  refine ⟨ca, sa, cb * ca + sb * sa, sb * ca - cb * sa, r1, r2,
    L1 * (ca * cb - sa * sb) + L2 * (ca * sb + sa * cb),
    L2 * (ca * cb - sa * sb) - L1 * (ca * sb + sa * cb), hua, ?_, ?_, ?_, ?_⟩
  · linear_combination (cb * cb + sb * sb) * hua + hub
  · linear_combination hN1 - r1 * r1 * hua - r2 * r2 * hub
  · linear_combination ((ca * cb - sa * sb) * (ca * cb - sa * sb) +
      (ca * sb + sa * cb) * (ca * sb + sa * cb)) * hL + (cb * cb + sb * sb) * hua + hub
  · intro h
    apply Held2.ext
    · dsimp only [commonTurn, relativeTurn, mix]
      linear_combination h.b1 * hq1 - h.b2 * hq2 +
        (r2 * ((L1 * cb + L2 * sb) * h.b1 - (L2 * cb - L1 * sb) * h.b2)) * hua
    · dsimp only [commonTurn, relativeTurn, mix]
      linear_combination h.b1 * hq2 + h.b2 * hq1 +
        (r2 * ((L1 * cb + L2 * sb) * h.b2 + (L2 * cb - L1 * sb) * h.b1)) * hua
    · dsimp only [commonTurn, relativeTurn, mix]
      linear_combination h.b1 * hq3 - h.b2 * hq4 -
        (r2 * (cb * h.a1 - sb * h.a2) +
          r1 * ((ca * L1 + sa * L2) * h.b1 - (ca * L2 - sa * L1) * h.b2) * (cb * cb + sb * sb)) * hua -
        r1 * ((ca * L1 + sa * L2) * h.b1 - (ca * L2 - sa * L1) * h.b2) * hub
    · dsimp only [commonTurn, relativeTurn, mix]
      linear_combination h.b1 * hq4 + h.b2 * hq3 -
        (r2 * (cb * h.a2 + sb * h.a1) +
          r1 * ((ca * L1 + sa * L2) * h.b2 + (ca * L2 - sa * L1) * h.b1) * (cb * cb + sb * sb)) * hua -
        r1 * ((ca * L1 + sa * L2) * h.b2 + (ca * L2 - sa * L1) * h.b1) * hub

theorem expand_of_commutes (T : Held2 → Held2) (hlin : AdditiveHomogeneous T)
    (hJ : CommutesWithQuarter T) (h : Held2) :
    T h = add2 (add2 (smul2 h.a1 (T ⟨1, 0, 0, 0⟩)) (smul2 h.a2 (commonTurn 0 1 (T ⟨1, 0, 0, 0⟩))))
      (add2 (smul2 h.b1 (T ⟨0, 0, 1, 0⟩)) (smul2 h.b2 (commonTurn 0 1 (T ⟨0, 0, 1, 0⟩)))) := by
  have hh : h = add2 (add2 (smul2 h.a1 ⟨1, 0, 0, 0⟩) (smul2 h.a2 (commonTurn 0 1 ⟨1, 0, 0, 0⟩)))
      (add2 (smul2 h.b1 ⟨0, 0, 1, 0⟩) (smul2 h.b2 (commonTurn 0 1 ⟨0, 0, 1, 0⟩))) := by
    apply Held2.ext <;> dsimp only [add2, smul2, commonTurn] <;> ring
  have e := congrArg T hh
  rw [hlin.1, hlin.1, hlin.1, hlin.2, hlin.2, hlin.2, hlin.2, hJ ⟨1, 0, 0, 0⟩,
    hJ ⟨0, 0, 1, 0⟩] at e
  exact e

theorem commuting_is_combination_of_built (T : Held2 → Held2) (hlin : AdditiveHomogeneous T)
    (hJ : CommutesWithQuarter T) :
    ∃ x1 x2 x3 x4 x5 x6 x7 x8 : ℝ, ∀ h : Held2, T h =
      add2
        (add2 (add2 (smul2 x1 h) (smul2 x2 (commonTurn 0 1 h)))
          (add2 (smul2 x3 (relativeTurn (-1) 0 h))
            (smul2 x4 (commonTurn 0 1 (relativeTurn (-1) 0 h)))))
        (add2 (add2 (smul2 x5 (mix 0 1 h)) (smul2 x6 (commonTurn 0 1 (mix 0 1 h))))
          (add2 (smul2 x7 (mix 0 1 (relativeTurn (-1) 0 h)))
            (smul2 x8 (commonTurn 0 1 (mix 0 1 (relativeTurn (-1) 0 h)))))) := by
  have hexp := expand_of_commutes T hlin hJ
  generalize T ⟨1, 0, 0, 0⟩ = u at hexp
  generalize T ⟨0, 0, 1, 0⟩ = v at hexp
  obtain ⟨p1, p2, p3, p4⟩ := u
  obtain ⟨q1, q2, q3, q4⟩ := v
  refine ⟨(p1 + q3) / 2, (p2 + q4) / 2, (p1 - q3) / 2, (p2 - q4) / 2, (p3 - q1) / 2, (p4 - q2) / 2,
    (p3 + q1) / 2, (p4 + q2) / 2, fun h => ?_⟩
  rw [hexp h]
  apply Held2.ext <;> dsimp only [add2, smul2, commonTurn, relativeTurn, mix] <;> ring

theorem commuting_cost_preserving_decomposes
    (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, 0 ≤ r ∧ r * r = t) (T : Held2 → Held2)
    (hlin : AdditiveHomogeneous T) (hcost : PreservesTotalCost T) (hJ : CommutesWithQuarter T) :
    ∃ c0 s0 c1 s1 c2 s2 c3 s3 : ℝ, c0 * c0 + s0 * s0 = 1 ∧ c1 * c1 + s1 * s1 = 1 ∧
      c2 * c2 + s2 * s2 = 1 ∧ c3 * c3 + s3 * s3 = 1 ∧
      ∀ h : Held2, T h = commonTurn c0 s0 (relativeTurn c1 s1 (mix c2 s2 (relativeTurn c3 s3 h))) := by
  have hexp := expand_of_commutes T hlin hJ
  have k1 := hcost ⟨1, 0, 0, 0⟩
  have k2 := hcost ⟨0, 0, 1, 0⟩
  have k3 := hcost ⟨1, 0, 1, 0⟩
  have k4 := hcost ⟨1, 0, 0, 1⟩
  rw [hexp] at k3 k4
  generalize T ⟨1, 0, 0, 0⟩ = u at hexp k1 k3 k4
  generalize T ⟨0, 0, 1, 0⟩ = v at hexp k2 k3 k4
  obtain ⟨p1, p2, p3, p4⟩ := u
  obtain ⟨q1, q2, q3, q4⟩ := v
  dsimp only [totalCost, recA, recB, add2, smul2, commonTurn] at k1 k2 k3 k4
  have hN1 : p1 * p1 + p2 * p2 + p3 * p3 + p4 * p4 = 1 := by linear_combination k1
  have hN2 : q1 * q1 + q2 * q2 + q3 * q3 + q4 * q4 = 1 := by linear_combination k2
  have hO1 : p1 * q1 + p2 * q2 + p3 * q3 + p4 * q4 = 0 := by
    linear_combination (1 / 2) * k3 - (1 / 2) * hN1 - (1 / 2) * hN2
  have hO2 : p2 * q1 - p1 * q2 + p4 * q3 - p3 * q4 = 0 := by
    linear_combination (1 / 2) * k4 - (1 / 2) * hN1 - (1 / 2) * hN2
  obtain ⟨c0, s0, c1, s1, c2, s2, c3, s3, h0, h1, h2, h3, hall⟩ :=
    euler_core hroot p1 p2 p3 p4 q1 q2 q3 q4 hN1 hN2 hO1 hO2
  refine ⟨c0, s0, c1, s1, c2, s2, c3, s3, h0, h1, h2, h3, fun h => ?_⟩
  rw [← hall h, hexp h]
  apply Held2.ext <;> dsimp only [add2, smul2, commonTurn] <;> ring

theorem generator_completeness (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, 0 ≤ r ∧ r * r = t)
    (T : Held2 → Held2) (hlin : AdditiveHomogeneous T) (hcost : PreservesTotalCost T)
    (hJ : CommutesWithQuarter T) : BuiltFromTurns T := by
  obtain ⟨c0, s0, c1, s1, c2, s2, c3, s3, h0, h1, h2, h3, hall⟩ :=
    commuting_cost_preserving_decomposes hroot T hlin hcost hJ
  have hb : BuiltFromTurns
      (fun h => commonTurn c0 s0 (relativeTurn c1 s1 (mix c2 s2 (relativeTurn c3 s3 h)))) :=
    BuiltFromTurns.comp (BuiltFromTurns.common c0 s0 h0)
      (BuiltFromTurns.comp (BuiltFromTurns.relative c1 s1 h1)
        (BuiltFromTurns.comp (BuiltFromTurns.recombine c2 s2 h2) (BuiltFromTurns.relative c3 s3 h3)))
  have e : T = fun h => commonTurn c0 s0 (relativeTurn c1 s1 (mix c2 s2 (relativeTurn c3 s3 h))) :=
    funext hall
  rw [e]
  exact hb

theorem built_iff (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, 0 ≤ r ∧ r * r = t) (T : Held2 → Held2) :
    BuiltFromTurns T ↔ AdditiveHomogeneous T ∧ PreservesTotalCost T ∧ CommutesWithQuarter T :=
  ⟨fun hT => ⟨built_additiveHomogeneous T hT, built_preserves_totalCost T hT,
      built_commutes_quarter T hT⟩,
    fun ⟨hlin, hcost, hJ⟩ => generator_completeness hroot T hlin hcost hJ⟩

theorem admitted_is_built_or_flipped (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, 0 ≤ r ∧ r * r = t)
    (T : Held2 → Held2) (hlin : AdditiveHomogeneous T) (hcost : PreservesTotalCost T)
    (hun : CommonTurnUnseenAfter T) :
    BuiltFromTurns T ∨ BuiltFromTurns (fun h => rateFlip (T h)) := by
  rcases unseen_dichotomy T hlin hun with hc | ha
  · exact Or.inl (generator_completeness hroot T hlin hcost hc)
  · exact Or.inr (generator_completeness hroot _
      (comp_additiveHomogeneous rateFlip T rateFlip_additiveHomogeneous hlin)
      (fun h => (rateFlip_preserves_totalCost (T h)).trans (hcost h))
      (rateFlip_comp_commutes T ha))

theorem flipped_is_admitted (T : Held2 → Held2) (hU : BuiltFromTurns (fun h => rateFlip (T h))) :
    AdditiveHomogeneous T ∧ PreservesTotalCost T ∧ CommonTurnUnseenAfter T := by
  have eT : T = fun h => rateFlip ((fun k => rateFlip (T k)) h) :=
    funext fun h => (rateFlip_rateFlip (T h)).symm
  have hlin : AdditiveHomogeneous T := by
    rw [eT]
    exact comp_additiveHomogeneous rateFlip _ rateFlip_additiveHomogeneous
      (built_additiveHomogeneous _ hU)
  refine ⟨hlin, ?_, ?_⟩
  · intro h
    have k := built_preserves_totalCost _ hU h
    rw [← k]
    exact (rateFlip_preserves_totalCost (T h)).symm
  · intro c s hcs h
    have k := built_commutes_common _ hU c s h
    have k' : T (commonTurn c s h) = commonTurn c (-s) (T h) := by
      have j := congrArg rateFlip k
      rw [rateFlip_rateFlip, rateFlip_reverses_turn, rateFlip_rateFlip] at j
      exact j
    rw [k', plainAfterTurn_commonTurn c (-s) (by linear_combination hcs)]

theorem admitted_iff (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, 0 ≤ r ∧ r * r = t) (T : Held2 → Held2) :
    (AdditiveHomogeneous T ∧ PreservesTotalCost T ∧ CommonTurnUnseenAfter T) ↔
      (BuiltFromTurns T ∨ BuiltFromTurns (fun h => rateFlip (T h))) :=
  ⟨fun ⟨hlin, hcost, hun⟩ => admitted_is_built_or_flipped hroot T hlin hcost hun,
    fun hb => hb.elim
      (fun hT => ⟨built_additiveHomogeneous T hT, built_preserves_totalCost T hT, built_unseen T hT⟩)
      (flipped_is_admitted T)⟩

theorem square_is_built (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, 0 ≤ r ∧ r * r = t)
    (S : Held2 → Held2) (hlin : AdditiveHomogeneous S) (hcost : PreservesTotalCost S)
    (hun : CommonTurnUnseenAfter S) : BuiltFromTurns (fun h => S (S h)) :=
  generator_completeness hroot _ (comp_additiveHomogeneous S S hlin hlin)
    (fun h => (hcost (S h)).trans (hcost h)) (square_commutes_quarter S hlin hun)

theorem generator_completeness_of_halves
    (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, 0 ≤ r ∧ r * r = t) (Adm : Set (Held2 → Held2))
    (hadm : ∀ T ∈ Adm, AdditiveHomogeneous T ∧ PreservesTotalCost T ∧ CommonTurnUnseenAfter T)
    (hhalf : TurnsHaveHalves Adm) : ∀ T ∈ Adm, BuiltFromTurns T := by
  intro T hT
  obtain ⟨H, hH, hsq⟩ := hhalf T hT
  obtain ⟨hlin, hcost, hun⟩ := hadm H hH
  have e : T = fun h => H (H h) := funext fun h => (hsq h).symm
  rw [e]
  exact square_is_built hroot H hlin hcost hun

theorem rateFlip_has_no_admitted_half :
    ¬ ∃ S : Held2 → Held2, AdditiveHomogeneous S ∧ CommonTurnUnseenAfter S ∧
      ∀ h : Held2, S (S h) = rateFlip h := by
  rintro ⟨S, hlin, hun, hsq⟩
  have k := square_commutes_quarter S hlin hun ⟨1, 0, 0, 0⟩
  have k' : rateFlip (commonTurn 0 1 ⟨1, 0, 0, 0⟩) = commonTurn 0 1 (rateFlip ⟨1, 0, 0, 0⟩) := by
    rw [← hsq (commonTurn 0 1 ⟨1, 0, 0, 0⟩), ← hsq ⟨1, 0, 0, 0⟩]
    exact k
  have h2 := congrArg Held2.a2 k'
  dsimp only [commonTurn, rateFlip] at h2
  norm_num at h2

end APFPaper5.K3


theorem solution :
∀ (T : APFPaper5.K3.Held2 → APFPaper5.K3.Held2) (hlin : APFPaper5.K3.AdditiveHomogeneous T)
  (hJ : APFPaper5.K3.CommutesWithQuarter T),
  @Exists.{1} Real fun (x1 : Real) =>
    @Exists.{1} Real fun (x2 : Real) =>
      @Exists.{1} Real fun (x3 : Real) =>
        @Exists.{1} Real fun (x4 : Real) =>
          @Exists.{1} Real fun (x5 : Real) =>
            @Exists.{1} Real fun (x6 : Real) =>
              @Exists.{1} Real fun (x7 : Real) =>
                @Exists.{1} Real fun (x8 : Real) =>
                  ∀ (h : APFPaper5.K3.Held2),
                    @Eq.{1} APFPaper5.K3.Held2 (T h)
                      (APFPaper5.K3.add2
                        (APFPaper5.K3.add2
                          (APFPaper5.K3.add2 (APFPaper5.K3.smul2 x1 h)
                            (APFPaper5.K3.smul2 x2
                              (APFPaper5.K3.commonTurn
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) h)))
                          (APFPaper5.K3.add2
                            (APFPaper5.K3.smul2 x3
                              (APFPaper5.K3.relativeTurn
                                (@Neg.neg.{0} Real Real.instNeg
                                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) h))
                            (APFPaper5.K3.smul2 x4
                              (APFPaper5.K3.commonTurn
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                (APFPaper5.K3.relativeTurn
                                  (@Neg.neg.{0} Real Real.instNeg
                                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) h)))))
                        (APFPaper5.K3.add2
                          (APFPaper5.K3.add2
                            (APFPaper5.K3.smul2 x5
                              (APFPaper5.K3.mix
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) h))
                            (APFPaper5.K3.smul2 x6
                              (APFPaper5.K3.commonTurn
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                (APFPaper5.K3.mix
                                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) h))))
                          (APFPaper5.K3.add2
                            (APFPaper5.K3.smul2 x7
                              (APFPaper5.K3.mix
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                (APFPaper5.K3.relativeTurn
                                  (@Neg.neg.{0} Real Real.instNeg
                                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) h)))
                            (APFPaper5.K3.smul2 x8
                              (APFPaper5.K3.commonTurn
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                (APFPaper5.K3.mix
                                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                  (APFPaper5.K3.relativeTurn
                                    (@Neg.neg.{0} Real Real.instNeg
                                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) h))))))) := by
  exact @APFPaper5.K3.commuting_is_combination_of_built
