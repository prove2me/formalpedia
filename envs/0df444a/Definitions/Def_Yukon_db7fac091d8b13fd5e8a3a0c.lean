-- Prove2me | Definitions.Def_Yukon_db7fac091d8b13fd5e8a3a0c
-- name    : Yukon_db7fac091d8b13fd5e8a3a0c
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T06:01:31.28043+00:00
-- url     : https://prove2.me/theorems/32d0caa9-7856-487d-9f59-3f88f0c15f0b
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberPhaseCore6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberPhaseCore6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberPhaseCore6814.lean
--
--   yukon-proof-operation:foundation-direct-a5014101ffd1b2ae424be7ca624f6b5f1be7ff6e17b4e164979b7498a782d9fb
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiOWY1MzI1YjY4ODEwYTkxYTRiNTI1YmIyZWM1M2ExMGY0YTNkODQxZWFhNTMwNzFjZWI5N2UzNTY3OWMzMmQ0OSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWE1MDE0MTAxZmZkMWIyYWU0MjRiZTdjYTYyNGY2YjVmMWJlN2ZmNmUxN2I0ZTE2NDk3OWI3NDk4YTc4MmQ5ZmIiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9kYjdmYWMwOTFkOGIxM2ZkNWU4YTNhMGMiLCJ2IjoyfQ]

import Definitions.Def_Yukon_542fee5622a1d28a6009acd1

import Definitions.Def_Yukon_dfd305be17d46cecd47c7820










































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.Lower80889.PhaseRows
open RCN095 LocatorFactorAggregate LocatorArbitraryPowerAvoidance
open LocatorPhase6800Oracle (Potential BaseRow BaseSegment evalBaseSegments rawFlag rawFlag_total rawFlag_middle rawFlag_all)
open Lower80889.Oracle
open LocatorPhase6800Audit (powerBandBudget_mono_fuel)
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem routeable_raw_mono_z
    (s : SourceNumbers) {r v z₁ z₂ : ℕ}
    (hz : z₁ ≤ z₂) (hcap : r + v + z₂ ≤ s.totalCap)
    (hroute : s.Routeable (rawFlag r v z₁)) :
    s.Routeable (rawFlag r v z₂) := by
  rcases hroute with ⟨hr, ht, hy, hs, hband⟩
  have hr' : 1 ≤ r := by simpa only [rawFlag_all] using hr
  have htotal : r + v + z₁ ≤ r + v + z₂ := by omega
  have hpos : 0 < r + v + z₁ := by omega
  have hdiv : s.totalCap / (r + v + z₂) ≤
      s.totalCap / (r + v + z₁) :=
    Nat.div_le_div_left htotal hpos
  have hfuel : s.fuel (rawFlag r v z₂) ≤
      s.fuel (rawFlag r v z₁) := by
    unfold SourceNumbers.fuel
    simp only [rawFlag_total, rawFlag_middle, rawFlag_all]
    exact min_le_min hdiv (le_refl _)
  have hbox : s.totalCap - (r + v + z₂) ≤
      s.totalCap - (r + v + z₁) := Nat.sub_le_sub_left htotal _
  have hsameFuel :
      powerBandBudget 50185 (r + v + z₂) (r + v) r
          (s.totalCap - (r + v + z₂)) (s.middleCap - (r + v))
          (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) ≤
        powerBandBudget 50185 (r + v + z₁) (r + v) r
          (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
          (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) := by
    exact powerBandBudget_mono 50185
      (r + v + z₂) (r + v) r
      (s.totalCap - (r + v + z₂)) (s.middleCap - (r + v))
      (s.slopeCap - r)
      (r + v + z₁) (r + v) r
      (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
      (s.slopeCap - r) (s.fuel (rawFlag r v z₂))
      hbox (le_refl _) (le_refl _) htotal (le_refl _) (le_refl _)
  have hmoreFuel :
      powerBandBudget 50185 (r + v + z₁) (r + v) r
          (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
          (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) ≤
        powerBandBudget 50185 (r + v + z₁) (r + v) r
          (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
          (s.slopeCap - r) (s.fuel (rawFlag r v z₁)) :=
    powerBandBudget_mono_fuel 50185 (r + v + z₁) (r + v) r
      (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
      (s.slopeCap - r) hfuel
  refine ⟨hr, ?_, ?_, ?_, ?_⟩
  · simpa only [rawFlag_total] using hcap
  · simpa only [rawFlag_middle] using hy
  · simpa only [rawFlag_all] using hs
  · rcases hband with hband | hthin
    · left
      unfold SourceNumbers.band at hband ⊢
      simp only [rawFlag_total, rawFlag_middle, rawFlag_all] at hband ⊢
      exact (hsameFuel.trans hmoreFuel).trans_lt hband
    · right
      have hsameFuelT :
          powerBandBudgetThin 131071 (s.contactCap (rawFlag r v z₂)) 50185
              (contactDec (rawFlag r v z₂)) (r + v + z₂) (r + v) r
              (s.totalCap - (r + v + z₂)) (s.middleCap - (r + v))
              (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) ≤
            powerBandBudgetThin 131071 (s.contactCap (rawFlag r v z₁)) 50185
              (contactDec (rawFlag r v z₁)) (r + v + z₁) (r + v) r
              (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
              (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) := by
        have hcap : s.contactCap (rawFlag r v z₂) = s.contactCap (rawFlag r v z₁) := by
          simp only [SourceNumbers.contactCap, contactDec, rawFlag_middle, rawFlag_all]
        have hdec : contactDec (rawFlag r v z₂) = contactDec (rawFlag r v z₁) := by
          simp only [contactDec, rawFlag_middle, rawFlag_all]
        rw [hcap, hdec]
        exact powerBandBudgetThin_mono 131071 50185 (s.fuel (rawFlag r v z₂))
          (s.contactCap (rawFlag r v z₁)) (contactDec (rawFlag r v z₁))
          (r + v + z₂) (r + v) r
          (s.totalCap - (r + v + z₂)) (s.middleCap - (r + v)) (s.slopeCap - r)
          (s.contactCap (rawFlag r v z₁)) (contactDec (rawFlag r v z₁))
          (r + v + z₁) (r + v) r
          (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v)) (s.slopeCap - r)
          le_rfl le_rfl hbox le_rfl le_rfl htotal le_rfl le_rfl
      have hmoreFuelT :
          powerBandBudgetThin 131071 (s.contactCap (rawFlag r v z₁)) 50185
              (contactDec (rawFlag r v z₁)) (r + v + z₁) (r + v) r
              (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
              (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) ≤
            powerBandBudgetThin 131071 (s.contactCap (rawFlag r v z₁)) 50185
              (contactDec (rawFlag r v z₁)) (r + v + z₁) (r + v) r
              (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
              (s.slopeCap - r) (s.fuel (rawFlag r v z₁)) :=
        powerBandBudgetThin_mono_fuel 131071 (s.contactCap (rawFlag r v z₁)) 50185
          (contactDec (rawFlag r v z₁)) (r + v + z₁) (r + v) r
          (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v)) (s.slopeCap - r) hfuel
      unfold SourceNumbers.bandThin at hthin ⊢
      simp only [rawFlag_total, rawFlag_middle, rawFlag_all] at hthin ⊢
      exact (hsameFuelT.trans hmoreFuelT).trans_lt hthin


def phasePotential : ℕ → Potential
  | 0 => Lower80889.SourceSound.Phase00.potential
  | 1 => Lower80889.SourceSound.Phase01.potential
  | 2 => Lower80889.SourceSound.Phase02.potential
  | 3 => Lower80889.SourceSound.Phase03.potential
  | 4 => Lower80889.SourceSound.Phase04.potential
  | 5 => Lower80889.SourceSound.Phase05.potential
  | 6 => Lower80889.SourceSound.Phase06.potential
  | 7 => Lower80889.SourceSound.Phase03.potential
  | 8 => Lower80889.SourceSound.Phase04.potential
  | _ => Lower80889.SourceSound.Phase05.potential

def thresholdAt (q : Array ℕ) (j : ℕ) : ℕ := (q[j]?).getD 10715
def cachedPrefixAt (q : Array ℕ) (j : ℕ) : ℕ := (q[j]?).getD 0
structure PhaseRowContext where
  R : ℕ
  V : ℕ
  base : BaseRow
  threshold : Array ℕ
  here : Array ℕ
  parent : Array ℕ

def baseAt (c : PhaseRowContext) (z : ℕ) : ℕ := c.base.evalAt z

def parentCharge (c : PhaseRowContext) (phase z : ℕ) : ℕ :=
  (phasePotential phase).eval (rawFlag c.R c.V z) + cachedPrefixAt c.parent phase

def hereCharge (c : PhaseRowContext) (phase z : ℕ) : ℕ :=
  (phasePotential phase).eval (rawFlag c.R c.V z) + cachedPrefixAt c.here phase

/-- Source `0` is the base line; source `j+1` is the parent charge of phase
`j`. -/
def sourceLine (c : PhaseRowContext) : ℕ → ℕ → ℕ
  | 0, z => baseAt c z
  | j + 1, z => parentCharge c j z

/-- The cap just before `phase`. -/
def capBefore (c : PhaseRowContext) : ℕ → ℕ → ℕ
  | 0, z => baseAt c z
  | j + 1, z =>
      if thresholdAt c.threshold j ≤ z then
        min (capBefore c j z) (parentCharge c j z)
      else capBefore c j z

def SourceActive (c : PhaseRowContext) : ℕ → ℕ → Prop
  | 0, _ => True
  | j + 1, z => thresholdAt c.threshold j ≤ z

instance  _root_.ProximityPrize.SubmissionLower.Lower80889.PhaseRows.instDecidableSourceActive (c : PhaseRowContext) (w z : ℕ) : Decidable (SourceActive c w z) := by
  cases w <;> simp only [SourceActive] <;> infer_instance

theorem sourceActive_mono (c : PhaseRowContext) (w lo z : ℕ)
    (h : SourceActive c w lo) (hz : lo ≤ z) : SourceActive c w z := by
  cases w with
  | zero => trivial
  | succ j =>
      change thresholdAt c.threshold j ≤ lo at h
      change thresholdAt c.threshold j ≤ z
      exact h.trans hz

theorem capBefore_step_le (c : PhaseRowContext) (phase z : ℕ) :
    capBefore c (phase + 1) z ≤ capBefore c phase z := by
  simp only [capBefore]
  split
  · exact min_le_left _ _
  · exact le_rfl

theorem capBefore_le_sourceLine (c : PhaseRowContext) (phase witness z : ℕ)
    (hw : witness ≤ phase) (ha : SourceActive c witness z) :
    capBefore c phase z ≤ sourceLine c witness z := by
  induction phase with
  | zero =>
      have : witness = 0 := by omega
      subst witness
      exact le_rfl
  | succ phase ih =>
      by_cases hprev : witness ≤ phase
      · exact (capBefore_step_le c phase z).trans (ih hprev)
      · have heq : witness = phase + 1 := by omega
        subst witness
        simp only [SourceActive] at ha
        simp only [capBefore, sourceLine, if_pos ha]
        exact min_le_right _ _

/-! ## Affine cells -/

open SecondJetRowIntervals

theorem potential_raw_affine (q : Potential) (R V lo z : ℕ) (hlo : lo ≤ z) :
    q.eval (rawFlag R V z) =
      q.eval (rawFlag R V lo) + q.totalCoeff * (z - lo) := by
  have hz : z = lo + (z - lo) := by omega
  rw [hz]
  simp only [Potential.eval, rawFlag_total, rawFlag_middle, rawFlag_all]
  have hsub : lo + (z - lo) - lo = z - lo := by omega
  rw [hsub]
  ring


def SourceCell (c : PhaseRowContext) : ℕ → ℕ → ℕ → Prop
  | 0, lo, hi => BaseCell c.base lo hi
  | _+1, _, _ => True
instance  _root_.ProximityPrize.SubmissionLower.Lower80889.PhaseRows.instDecidableSourceCell (c : PhaseRowContext) (w lo hi : ℕ) : Decidable (SourceCell c w lo hi) := by
  cases w <;> simp only [SourceCell] <;> infer_instance

def sourceSlope (c : PhaseRowContext) : ℕ → ℕ → ℕ
  | 0, lo => baseSlopeAt c.base lo
  | j+1, _ => (phasePotential j).totalCoeff

theorem parentCharge_affine (c : PhaseRowContext) (phase lo z : ℕ) (hz : lo ≤ z) :
    parentCharge c phase z = parentCharge c phase lo + (phasePotential phase).totalCoeff*(z-lo) := by
  unfold parentCharge
  rw [potential_raw_affine _ _ _ lo z hz]
  omega

theorem hereCharge_affine (c : PhaseRowContext) (phase lo hi z : ℕ)
    (_hp : phase < 10) (hlo : lo ≤ z) (_hhi : z ≤ hi) :
    hereCharge c phase z = hereCharge c phase lo + (phasePotential phase).totalCoeff*(z-lo) := by
  unfold hereCharge
  rw [potential_raw_affine _ _ _ lo z hlo]
  omega

theorem sourceLine_affine (c : PhaseRowContext) (w lo hi z : ℕ)
    (_hw : w ≤ 10) (hc : SourceCell c w lo hi) (hlo : lo ≤ z) (hhi : z ≤ hi) :
    sourceLine c w z = sourceLine c w lo + sourceSlope c w lo*(z-lo) := by
  cases w with
  | zero => exact baseAt_affine c.base lo hi z hc hlo hhi
  | succ j => exact parentCharge_affine c j lo z hlo

theorem affine_le_between (a A m M d finish : ℕ) (hd : d ≤ finish)
    (hstart : a ≤ A) (hend : a+m*finish ≤ A+M*finish) : a+m*d ≤ A+M*d := by
  by_cases hm : m ≤ M
  · exact Nat.add_le_add hstart (Nat.mul_le_mul_right d hm)
  · have hMm : M ≤ m := (Nat.lt_of_not_ge hm).le
    have hdecomp : M+(m-M)=m := Nat.add_sub_of_le hMm
    have hdeltaFinish : a+(m-M)*finish ≤ A := by
      rw [← hdecomp, Nat.add_mul] at hend
      omega
    have hdelta := Nat.mul_le_mul_left (m-M) hd
    rw [← hdecomp, Nat.add_mul]
    omega


def RunValid (c : PhaseRowContext) (phase start : ℕ) (run : PhaseRun) : Prop :=
  let hi := run.stop - 1
  start < run.stop ∧ run.witness ≤ phase ∧
    SourceActive c run.witness start ∧
    SourceCell c run.witness start hi ∧
    sourceLine c run.witness start ≤ hereCharge c phase start ∧
    sourceLine c run.witness hi ≤ hereCharge c phase hi

instance  _root_.ProximityPrize.SubmissionLower.Lower80889.PhaseRows.instDecidableRunValid (c : PhaseRowContext) (phase start : ℕ) (run : PhaseRun) :
    Decidable (RunValid c phase start run) := by
  unfold RunValid
  infer_instance

theorem RunValid.sound (c : PhaseRowContext) (phase start : ℕ) (run : PhaseRun)
    (hp : phase < 10) (h : RunValid c phase start run)
    (z : ℕ) (hlo : start ≤ z) (hhi : z < run.stop) :
    capBefore c phase z ≤ hereCharge c phase z := by
  change start < run.stop ∧ run.witness ≤ phase ∧
    SourceActive c run.witness start ∧
    SourceCell c run.witness start (run.stop - 1) ∧
    sourceLine c run.witness start ≤ hereCharge c phase start ∧
    sourceLine c run.witness (run.stop - 1) ≤
      hereCharge c phase (run.stop - 1) at h
  rcases h with ⟨hstart, hw, hactive, hsource, hleft, hright⟩
  let hi := run.stop - 1
  have hzhi : z ≤ hi := by dsimp only [hi]; omega
  have hsthi : start ≤ hi := by dsimp only [hi]; omega
  have hs := sourceLine_affine c run.witness start hi z (by omega)
    hsource hlo hzhi
  have ht := hereCharge_affine c phase start hi z hp hlo hzhi
  have hsEnd := sourceLine_affine c run.witness start hi hi (by omega)
    hsource hsthi le_rfl
  have htEnd := hereCharge_affine c phase start hi hi hp
    hsthi le_rfl
  have hline : sourceLine c run.witness z ≤ hereCharge c phase z := by
    rw [hs, ht]
    apply affine_le_between
      (sourceLine c run.witness start) (hereCharge c phase start)
      (sourceSlope c run.witness start) ((phasePotential phase).totalCoeff)
      (z - start) (hi - start)
    · exact Nat.sub_le_sub_right hzhi start
    · exact hleft
    · rw [← hsEnd, ← htEnd]
      exact hright
  apply (capBefore_le_sourceLine c phase run.witness z hw ?_).trans hline
  exact sourceActive_mono c run.witness start z hactive hlo

def RunsValid (c : PhaseRowContext) (phase finish : ℕ) :
    ℕ → List PhaseRun → Prop
  | start, [] => start = finish
  | start, run :: runs =>
      run.stop ≤ finish ∧ RunValid c phase start run ∧
        RunsValid c phase finish run.stop runs

instance  _root_.ProximityPrize.SubmissionLower.Lower80889.PhaseRows.instDecidableRunsValid (c : PhaseRowContext) (phase finish start : ℕ)
    (runs : List PhaseRun) : Decidable (RunsValid c phase finish start runs) := by
  induction runs generalizing start with
  | nil => simp only [RunsValid]; infer_instance
  | cons run runs ih => simp only [RunsValid]; infer_instance

theorem RunsValid.sound (c : PhaseRowContext) (phase finish start : ℕ)
    (runs : List PhaseRun) (hp : phase < 10)
    (h : RunsValid c phase finish start runs)
    (z : ℕ) (hlo : start ≤ z) (hhi : z < finish) :
    capBefore c phase z ≤ hereCharge c phase z := by
  induction runs generalizing start with
  | nil =>
      simp only [RunsValid] at h
      omega
  | cons run runs ih =>
      simp only [RunsValid] at h
      by_cases hz : z < run.stop
      · exact RunValid.sound c phase start run hp h.2.1 z hlo hz
      · exact ih run.stop h.2.2 (by omega)

def phaseFinish (c : PhaseRowContext) (phase : ℕ) : ℕ :=
  min (thresholdAt c.threshold phase) (10715 - (c.R + c.V))

def RowRunsValid (c : PhaseRowContext) (runs : Array (List PhaseRun)) : Prop :=
  ∀ j ∈ List.range 10, RunsValid c j (phaseFinish c j) 0 ((runs[j]?).getD [])

instance  _root_.ProximityPrize.SubmissionLower.Lower80889.PhaseRows.instDecidableRowRunsValid (c : PhaseRowContext) (runs : Array (List PhaseRun)) :
    Decidable (RowRunsValid c runs) := by
  unfold RowRunsValid
  infer_instance

theorem phaseTerminal_of_runs (c : PhaseRowContext) (phase : ℕ)
    (runs : List PhaseRun) (hp : phase < 10)
    (h : RunsValid c phase (phaseFinish c phase) 0 runs)
    (z : ℕ) (hz : z < 10715 - (c.R + c.V)) :
    thresholdAt c.threshold phase ≤ z ∨
      capBefore c phase z ≤ hereCharge c phase z := by
  by_cases ht : thresholdAt c.threshold phase ≤ z
  · exact Or.inl ht
  · apply Or.inr
    apply RunsValid.sound c phase (phaseFinish c phase) 0 runs hp h z
    · omega
    · unfold phaseFinish
      exact lt_min (Nat.lt_of_not_ge ht) hz


end ProximityPrize.SubmissionLower.Lower80889.PhaseRows

namespace ProximityPrize.SubmissionLower.Lower80889.ThresholdFast

open scoped BigOperators
open LocatorLowQuotient

set_option autoImplicit false
set_option maxRecDepth 100000

theorem term_eq (B x : ℕ) :
    (x + 1) * (B + x) - (x + 1) * x / 2 =
      (x + 1) * B + (x + 1).choose 2 := by
  rw [Nat.choose_two_right]
  simp only [Nat.add_sub_cancel]
  have hdvd : 2 ∣ (x + 1) * x := by
    simpa [Nat.mul_comm, Nat.add_comm] using
      (even_iff_two_dvd.mp (Nat.even_mul_succ_self x))
  have hhalf := Nat.div_mul_cancel hdvd
  rw [Nat.mul_add]
  omega

theorem kernelSumRange_succ_all : ∀ n : ℕ,
    kernelSumRange (fun x => x + 1) n = (n + 1).choose 2
  | 0 => by decide
  | n + 1 => by
      rw [LocatorLowQuotient.kernelSumRange_succ, kernelSumRange_succ_all]
      simpa [Nat.choose_one_right, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using (Nat.choose_succ_succ (n + 1) 1).symm

theorem kernelSumRange_succ (U : ℕ) :
    kernelSumRange (fun x => x + 1) (U + 1) = (U + 2).choose 2 := by
  simpa only [Nat.add_assoc] using kernelSumRange_succ_all (U + 1)

theorem kernelSumRange_choose_two_all : ∀ n : ℕ,
    kernelSumRange (fun x => (x + 1).choose 2) n = (n + 1).choose 3
  | 0 => by decide
  | n + 1 => by
      rw [LocatorLowQuotient.kernelSumRange_succ, kernelSumRange_choose_two_all]
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Nat.choose_succ_succ (n + 1) 2).symm

theorem kernelSumRange_choose_two (U : ℕ) :
    kernelSumRange (fun x => (x + 1).choose 2) (U + 1) =
      (U + 2).choose 3 := by
  simpa only [Nat.add_assoc] using kernelSumRange_choose_two_all (U + 1)

theorem kernelSumRange_uncapped (B U : ℕ) :
    kernelSumRange (fun x =>
      (x + 1) * (B + x) - (x + 1) * x / 2) (U + 1) =
      B * (U + 2).choose 2 + (U + 2).choose 3 := by
  rw [kernelSumRange_eq]
  simp_rw [term_eq]
  rw [Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  rw [← kernelSumRange_eq, kernelSumRange_succ]
  rw [← kernelSumRange_eq, kernelSumRange_choose_two]
  simp only [Nat.mul_comm]

def cappedTerm (B S x : ℕ) : ℕ :=
  let M := min S x
  (M + 1) * (B + x) - (M + 1) * M / 2

theorem min_sub_min_eq (T YS x : ℕ) (hx : x ≤ min T YS) :
    min (T - (min T YS - x)) (YS - (min T YS - x)) = x := by
  rcases le_total T YS with h | h
  · simp only [Nat.min_eq_left h] at hx ⊢
    omega
  · simp only [Nat.min_eq_right h] at hx ⊢
    omega

theorem channelCount_eq_cappedKernel (T YS S : ℕ) :
    channelCount T YS S =
      kernelSumRange
        (cappedTerm (T + 1 - min T YS) S) (min T YS + 1) := by
  unfold channelCount
  rw [kernelSumRange_eq, ← Finset.sum_range_reflect]
  rw [kernelSumRange_eq]
  refine Finset.sum_congr rfl ?_
  intro x hx
  have hx' : x ≤ min T YS := by
    have := Finset.mem_range.mp hx
    omega
  have hU : min T YS ≤ T := Nat.min_le_left _ _
  simp only [Nat.add_sub_cancel, cappedTerm]
  rw [min_sub_min_eq T YS x hx']
  have harg : T + 1 - (min T YS - x) =
      (T + 1 - min T YS) + x := by omega
  rw [harg]

def fastChannelCount (T YS S : ℕ) : ℕ :=
  let U := min T YS
  let B := T + 1 - U
  let k := min S U
  let n := U - k
  let C := (S + 1) * (B + S + 1) - (S + 1) * S / 2
  B * (k + 2).choose 2 + (k + 2).choose 3 +
    n * C + (S + 1) * (n * (n - 1) / 2)

theorem tail_term_eq (B S t : ℕ) :
    cappedTerm B S (S + 1 + t) =
      ((S + 1) * (B + S + 1) - (S + 1) * S / 2) +
        (S + 1) * t := by
  unfold cappedTerm
  rw [Nat.min_eq_left (by omega)]
  change (S + 1) * (B + (S + 1 + t)) - (S + 1) * S / 2 =
    ((S + 1) * (B + S + 1) - (S + 1) * S / 2) + (S + 1) * t
  rw [show B + (S + 1 + t) = (B + S + 1) + t by omega,
    Nat.mul_add]
  have hS : S ≤ B + S + 1 := by omega
  have hq : (S + 1) * S / 2 ≤ (S + 1) * (B + S + 1) :=
    (Nat.div_le_self ((S + 1) * S) 2).trans
      (Nat.mul_le_mul_left (S + 1) hS)
  exact Nat.sub_add_comm
    (n := (S + 1) * (B + S + 1)) (m := (S + 1) * t)
    (k := (S + 1) * S / 2) hq

theorem kernelSumRange_capped_prefix (B S k : ℕ) (hk : k ≤ S) :
    kernelSumRange (cappedTerm B S) (k + 1) =
      B * (k + 2).choose 2 + (k + 2).choose 3 := by
  calc
    kernelSumRange (cappedTerm B S) (k + 1) =
        kernelSumRange (fun x =>
          (x + 1) * (B + x) - (x + 1) * x / 2) (k + 1) := by
      rw [kernelSumRange_eq, kernelSumRange_eq]
      refine Finset.sum_congr rfl ?_
      intro x hx
      have hxk : x ≤ k := by
        have := Finset.mem_range.mp hx
        omega
      simp only [cappedTerm, Nat.min_eq_right (hxk.trans hk)]
    _ = B * (k + 2).choose 2 + (k + 2).choose 3 :=
      kernelSumRange_uncapped B k

theorem sum_Ico_capped_tail (B S U : ℕ) (hSU : S < U) :
    (∑ x ∈ Finset.Ico (S + 1) (U + 1), cappedTerm B S x) =
      (U - S) *
          ((S + 1) * (B + S + 1) - (S + 1) * S / 2) +
        (S + 1) * ((U - S) * (U - S - 1) / 2) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hsub : U + 1 - (S + 1) = U - S := by omega
  rw [hsub]
  simp_rw [tail_term_eq]
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul,
    Finset.sum_range_id]

theorem kernelSumRange_capped_closed (B S U : ℕ) :
    kernelSumRange (cappedTerm B S) (U + 1) =
      let k := min S U
      let n := U - k
      B * (k + 2).choose 2 + (k + 2).choose 3 +
        n * ((S + 1) * (B + S + 1) - (S + 1) * S / 2) +
          (S + 1) * (n * (n - 1) / 2) := by
  by_cases hSU : S < U
  · simp only [Nat.min_eq_left hSU.le]
    rw [kernelSumRange_eq]
    rw [← Finset.sum_range_add_sum_Ico (cappedTerm B S)
      (show S + 1 ≤ U + 1 by omega)]
    rw [← kernelSumRange_eq, kernelSumRange_capped_prefix B S S le_rfl,
      sum_Ico_capped_tail B S U hSU]
    simp only [Nat.add_assoc]
  · have hUS : U ≤ S := Nat.le_of_not_gt hSU
    simp only [Nat.min_eq_right hUS, Nat.sub_self, zero_mul,
      Nat.zero_sub, Nat.add_zero]
    exact kernelSumRange_capped_prefix B S U hUS

theorem channelCount_eq_fast (T YS S : ℕ) :
    channelCount T YS S = fastChannelCount T YS S := by
  rw [channelCount_eq_cappedKernel]
  rw [kernelSumRange_capped_closed]
  rfl

/-! ## Constant-time executable form -/

theorem choose_three_right (n : ℕ) :
    n.choose 3 = n * (n - 1) * (n - 2) / 6 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  simp [Nat.descFactorial, Nat.factorial]
  congr 1
  ring

def evalChooseTwo (n : ℕ) : ℕ := n * (n - 1) / 2
def evalChooseThree (n : ℕ) : ℕ := n * (n - 1) * (n - 2) / 6

/-- A constant-time executable version of `channelCount`. -/
def evalChannelCount (T YS S : ℕ) : ℕ :=
  let U := min T YS
  let B := T + 1 - U
  let k := min S U
  let n := U - k
  let C := (S + 1) * (B + S + 1) - (S + 1) * S / 2
  B * evalChooseTwo (k + 2) + evalChooseThree (k + 2) +
    n * C + (S + 1) * (n * (n - 1) / 2)

theorem fastChannelCount_eq_eval (T YS S : ℕ) :
    fastChannelCount T YS S = evalChannelCount T YS S := by
  simp only [fastChannelCount, evalChannelCount, evalChooseTwo,
    evalChooseThree, Nat.choose_two_right, choose_three_right]

theorem channelCount_eq_eval (T YS S : ℕ) :
    channelCount T YS S = evalChannelCount T YS S :=
  (channelCount_eq_fast T YS S).trans (fastChannelCount_eq_eval T YS S)

open LocatorArbitraryPowerAvoidance Lower80889.Oracle
open LocatorPhase6800Oracle (rawFlag)
open RCN095 LocatorFactorAggregate

/-- Executable power-band budget with the expensive range sum replaced by
the proved constant-time channel-count formula. -/
def evalPowerBandBudget
    (delta dT dY dS T YS S : ℕ) : ℕ → ℕ
  | 0 => 0
  | fuel + 1 =>
      delta * evalChannelCount T YS S +
        evalPowerBandBudget delta dT dY dS
          (T - dT) (YS - dY) (S - dS) fuel

theorem evalPowerBandBudget_eq
    (delta dT dY dS T YS S fuel : ℕ) :
    evalPowerBandBudget delta dT dY dS T YS S fuel =
      powerBandBudget delta dT dY dS T YS S fuel := by
  induction fuel generalizing T YS S with
  | zero => rfl
  | succ fuel ih =>
      simp only [evalPowerBandBudget, powerBandBudget]
      rw [← channelCount_eq_eval, ih]

def evalBand (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  evalPowerBandBudget 50185 (total p) (middle p) p.all
    (s.totalCap - total p) (s.middleCap - middle p)
    (s.slopeCap - p.all) (s.fuel p)

theorem evalBand_eq (s : SourceNumbers) (p : FlagDegree) :
    evalBand s p = s.band p := by
  unfold evalBand SourceNumbers.band
  exact evalPowerBandBudget_eq _ _ _ _ _ _ _ _

/-- Executable thin budget (lever S1): the same recursion with the constant-time
channel count; `thinTop` is already a single division. -/
def evalPowerBandBudgetThin
    (w Dh delta dc dT dY dS T YS S : ℕ) : ℕ → ℕ
  | 0 => 0
  | fuel + 1 =>
      delta * evalChannelCount T (min YS (thinTop w Dh S)) S +
        evalPowerBandBudgetThin w (Dh - delta - dc) delta dc dT dY dS
          (T - dT) (YS - dY) (S - dS) fuel

theorem evalPowerBandBudgetThin_eq
    (w Dh delta dc dT dY dS T YS S fuel : ℕ) :
    evalPowerBandBudgetThin w Dh delta dc dT dY dS T YS S fuel =
      powerBandBudgetThin w Dh delta dc dT dY dS T YS S fuel := by
  induction fuel generalizing Dh T YS S with
  | zero => rfl
  | succ fuel ih =>
      simp only [evalPowerBandBudgetThin, powerBandBudgetThin]
      rw [← channelCount_eq_eval, ih]

def evalBandThin (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  evalPowerBandBudgetThin 131071 (s.contactCap p) 50185 (contactDec p)
    (total p) (middle p) p.all
    (s.totalCap - total p) (s.middleCap - middle p)
    (s.slopeCap - p.all) (s.fuel p)

theorem evalBandThin_eq (s : SourceNumbers) (p : FlagDegree) :
    evalBandThin s p = s.bandThin p := by
  unfold evalBandThin SourceNumbers.bandThin
  exact evalPowerBandBudgetThin_eq _ _ _ _ _ _ _ _ _ _ _

def FastRouteable (s : SourceNumbers) (p : FlagDegree) : Prop :=
  1 ≤ p.all ∧ total p ≤ s.totalCap ∧ middle p ≤ s.middleCap ∧
    p.all ≤ s.slopeCap ∧ (evalBandThin s p < s.gap ∨ evalBand s p < s.gap)

instance  _root_.ProximityPrize.SubmissionLower.Lower80889.ThresholdFast.instDecidableFastRouteable (s : SourceNumbers) (p : FlagDegree) :
    Decidable (FastRouteable s p) := by
  unfold FastRouteable
  infer_instance

theorem fastRouteable_iff (s : SourceNumbers) (p : FlagDegree) :
    FastRouteable s p ↔ s.Routeable p := by
  unfold FastRouteable SourceNumbers.Routeable
  rw [evalBand_eq, evalBandThin_eq, or_comm]

def FastSourceThresholdSufficient
    (s : SourceNumbers) (r v threshold : ℕ) : Prop :=
  10714 - (r + v) < threshold ∨ FastRouteable s (rawFlag r v threshold)

instance  _root_.ProximityPrize.SubmissionLower.Lower80889.ThresholdFast.instDecidableFastSourceThresholdSufficient (s : SourceNumbers) (r v threshold : ℕ) :
    Decidable (FastSourceThresholdSufficient s r v threshold) := by
  unfold FastSourceThresholdSufficient
  infer_instance


theorem sufficient_route (s : SourceNumbers) (r v threshold z : ℕ)
    (hs : 10714 ≤ s.totalCap) (hz : r+v+z ≤ 10714) (ht : threshold ≤ z)
    (hc : FastSourceThresholdSufficient s r v threshold) :
    s.Routeable (rawFlag r v z) := by
  rcases hc with hbad | hroute
  · omega
  · exact Lower80889.PhaseRows.routeable_raw_mono_z s ht (hz.trans hs)
      ((fastRouteable_iff _ _).mp hroute)
end ProximityPrize.SubmissionLower.Lower80889.ThresholdFast


