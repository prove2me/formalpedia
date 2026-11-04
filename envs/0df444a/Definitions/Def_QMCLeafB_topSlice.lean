-- Prove2me | Definitions.Def_QMCLeafB_topSlice
-- name    : QMCLeafB_topSlice
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T00:48:24.015562+00:00
-- url     : https://prove2.me/theorems/21b8544d-0ded-478b-84ae-5a7092cd1409
-- title:
--   QMCLeafB topSlice
-- statement:
--   # leaf B phase 14 — `topslice-range` (swarm `smw1a99tp`, member m4, direction d8)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_brick_verdict_sound
import Definitions.Def_QMCLeafB_fuelwire_m4
import Definitions.Def_QMCLeafB_RStInit
import Definitions.Def_QMCLeafB_round_program_m3
/-
# leaf B phase 14 — `topslice-range` (swarm `smw1a99tp`, member m4, direction d8)

**A hypothesis in the closing chain is false as stated, and this file fixes the range.**

`VerdictSound.soundEpsOnBracket_of_runData_interior` (`Check_brick_verdict_sound`, §5) asks for the
top slice

    htop : ∀ G t, -(Rq G/40000) ≤ t → t ≤ 0 → o G t = true

for **every** order `G.n`.  Its own proof, however, uses `htop` only after `G.n ≤ 1` has been
discharged by `soundAt_of_le_one` — so the `n ≤ 1` part of the hypothesis is never needed, and at
`n = 1` it is in fact **false** for m3's `RoundProgram` loop:

* `betaOf (1, 0) = 2/(1-1) = 0` and `alphInv 1 = (1+1)/(1-1) = 0` in `ℚ`, so the cut branch's
  scaling is `0 • stepY` and the round sends `stX` to the zero code (`snapY_n_one`);
* the zero code in dimension one has `dvR = |0 - 1| = 1 ≠ 0`, so `oracleR` answers *cut* again
  (`oracleR_of_dvR_ne`), forever;
* hence every flag is `false` (`stOks_iterate_n_one`) and `verdict` — `decide (0 < #true)` — is
  `false` at every `T ≥ 1`.

So the chain must ask `htop` only for `2 ≤ G.n`, which is what the weakened stroke below does.

Contents: `soundEpsOnBracket_of_runData_interior_hn` (same as the shelf's interior stroke, `htop`
restricted to `2 ≤ G.n`), `solution_of_runParts_interior_halve_hn` (m4's fuel assembly at that range),
and the `n = 1` obstruction lemmas.

No `sorry`, no `axiom`; audits at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section
namespace QMCLeafB.TopSliceRange

open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open QMCLeafB.RoundProgram

local instance instRequestCodingTopSlice : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 1.  The weakened interior stroke -/

/-- **`SoundεOnBracket` with the top slice required only at `2 ≤ G.n`.**  Same proof as
`VerdictSound.soundEpsOnBracket_of_runData_interior`, with the `n ≤ 1` case discharged by
`soundAt_of_le_one` *before* `htop` is used. -/
theorem soundEpsOnBracket_of_runData_interior_hn
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 → o G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.VerdictSound.RunData o G t) :
    QMCLeafB.FinishLine.SoundεOnBracket o := by
  rw [QMCLeafB.VerdictSound.soundEpsOnBracket_iff o]
  intro G t hlo hhi
  by_cases hn : G.n ≤ 1
  · exact QMCLeafB.VerdictSound.soundAt_of_le_one o hn t hlo hhi
  have hn2 : 2 ≤ G.n := by omega
  by_cases hcut : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)
  · exact QMCLeafB.VerdictSound.soundAt_of_runData o G t hn2 (hd G t hn2 hlo hcut)
  · have htop' : -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) :=
      not_lt.mp hcut
    refine ⟨fun _ => QMCLeafB.VerdictSound.exists_trace_le_of_neg_eps_le G t htop', ?_⟩
    intro hb
    exact absurd (hb ▸ htop G t hn2 htop' hhi) (by simp)

/-- **`SolutionStatement` from the interior run brick at m2's family, `htop` only at `2 ≤ G.n`.**  The
fuel, the halving inequality, the budget target, `hspec` and the size ledger's role are all
discharged as in `FuelWire.solution_of_runParts_interior_halve`. -/
theorem solution_of_runParts_interior_halve_hn
    {σ : Type} [Coding σ]
    (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (init : QMCLeafB.FuelWire.Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hinit : OAI.MetricKMedian.Binary.Automatic.Poly init)
    (hr : OAI.MetricKMedian.Binary.Automatic.Poly round)
    (hv : OAI.MetricKMedian.Binary.Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (horbit : ∀ a : σ × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (round^[j] a.1, a.2.drop j)).length
        ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hinitTape : ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init round verdict
        (fun G' _ => (QMCLeafB.FuelWire.paramsHalve G').K
          * (QMCLeafB.FuelWire.paramsHalve G').m) G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict
          (fun G' _ => (QMCLeafB.FuelWire.paramsHalve G').K
            * (QMCLeafB.FuelWire.paramsHalve G').m)) G t
        (QMCLeafB.FuelWire.paramsHalve G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.LoopRestate.solution_of_loop_bounded init
    (QMCLeafB.FuelWire.fuelOfProd k
      (fun G => QMCLeafB.FuelWire.Kbc (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G)
      (fun G => QMCLeafB.HalvePerG.mHalve (G.n * G.n)))
    round verdict hinit
    (QMCLeafB.FuelWire.poly_fuelOfProd k _ _ QMCLeafB.FuelWire.poly_Kbc_mHalve_mul)
    hr hv sizes horbit
    (QMCLeafB.FinalStroke.loopBit init round verdict
      (fun G' _ => (QMCLeafB.FuelWire.paramsHalve G').K
        * (QMCLeafB.FuelWire.paramsHalve G').m))
    (fun p => QMCLeafB.FinalStroke.hspec_of_tape_free init _ round verdict
      (fun G' _ => (QMCLeafB.FuelWire.paramsHalve G').K
        * (QMCLeafB.FuelWire.paramsHalve G').m) hinitTape
      (fun q => QMCLeafB.FuelWire.fuelOfProd_length k _ _
        (QMCLeafB.FuelWire.Kbc_mHalve_le_seed k hk) q) p)
    (soundEpsOnBracket_of_runData_interior_hn
      (QMCLeafB.FinalStroke.loopBit init round verdict
        (fun G' _ => (QMCLeafB.FuelWire.paramsHalve G').K
          * (QMCLeafB.FuelWire.paramsHalve G').m)) htop
      (fun G t hn hlo hlt => (hd G t hn hlo hlt).toRunData))


/-! ## 2.  The order-one obstruction (mechanized) -/

theorem alphInv_one : alphInv 1 = 0 := by
  unfold alphInv; norm_num

theorem smulRaw_zero_mem {N : ℕ} {l : List ℚ} {x : ℚ}
    (hx : x ∈ QMCLeafB.MatQUpdate.smulRaw ((N, l), (0 : ℚ))) : x = 0 := by
  simp only [QMCLeafB.MatQUpdate.smulRaw, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨i, -, j, -, rfl⟩ := hx
  ring

theorem smulRaw_zero_length_one {N : ℕ} {l : List ℚ} (h : (l.take N).length = 1) :
    (QMCLeafB.MatQUpdate.smulRaw ((N, l), (0 : ℚ))).length = 1 := by
  unfold QMCLeafB.MatQUpdate.smulRaw
  rw [h]
  simp

theorem clipRat_zero (mu : ℚ) : clipRat mu 0 = 0 := by
  unfold clipRat
  by_cases h : |(0 : ℚ)| ≤ mu
  · simp [h]
  · simp [h]

theorem nrmQ_zero (mu : ℚ) (d : ℕ) : nrmQ mu d (0 : ℚ) = 0 := by
  unfold nrmQ
  rw [clipRat_zero, QMCLeafB.RoundPolySnap.snapDiv_zero]

theorem nrmRow_map_zero (mu : ℚ) (d : ℕ) (l : List ℚ) (hz : ∀ x ∈ l, x = 0) :
    nrmRow mu d l = l.map (fun _ => 0) := by
  unfold nrmRow
  refine List.map_congr_left ?_
  intro x hx
  rw [hz x hx]
  show nrmQ mu d 0 = 0
  exact nrmQ_zero mu d

theorem stepY_length (s : RSt) (hX : (stX s).length = stN s * stN s) :
    (stepY s).length = stN s * stN s := by
  unfold stepY QMCLeafB.MatQUpdate.Step.stepFun
  exact QMCLeafB.MatQUpdate.updFun_length (stN s) (stX s) _ _ hX

theorem snapY_eq_zero (s : RSt) (hN : stN s = 1) (hX : (stX s).length = 1) :
    snapY s = [0] := by
  have hstep : (stepY s).length = 1 := by
    have h := stepY_length s (by rw [hN, hX])
    rw [hN] at h
    simpa using h
  have htake : ((stepY s).take (stN s)).length = 1 := by
    rw [hN]; simp [hstep]
  have hscale : scaleY s = QMCLeafB.MatQUpdate.smulRaw ((stN s, stepY s), (0 : ℚ)) := by
    unfold scaleY
    rw [hN, alphInv_one]
  have hmem : ∀ x ∈ scaleY s, x = 0 := by
    intro x hx
    rw [hscale] at hx
    exact smulRaw_zero_mem hx
  have hlen : (scaleY s).length = 1 := by
    rw [hscale]
    exact smulRaw_zero_length_one htake
  have hrep : scaleY s = [0] := by
    cases hs : scaleY s with
    | nil => rw [hs] at hlen; simp at hlen
    | cons x xs =>
        cases xs with
        | nil => simpa [hs] using hmem x (by rw [hs]; simp)
        | cons y ys => rw [hs] at hlen; simp at hlen
  unfold snapY
  rw [nrmRow_map_zero _ _ _ hmem, hrep]
  rfl



/-! ## 2.  The zero code in dimension one fails the diagonal test -/

theorem dvR_eq_one (s : RSt) (hN : stN s = 1) (hX : stX s = [0]) : dvR s = 1 := by
  unfold dvR diagSumV idxs entV absq
  rw [hN, hX]
  simp

theorem dvR_eq_abs_entry (s : RSt) (hN : stN s = 1) (hX : (stX s).length = 1) :
    dvR s = |(stX s).getD 0 0 - 1| := by
  unfold dvR diagSumV idxs entV
  rw [hN]
  have htake : (stX s).take 1 = stX s := by rw [← hX]; exact List.take_length
  rw [htake, hX, List.range_one]
  simp [absq_eq]

theorem dvR_init0_ne (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) (hG : p.1.1.n = 1) :
    dvR (QMCLeafB.RStInit.init0 p) ≠ 0 := by
  have hN : stN (QMCLeafB.RStInit.init0 p) = 1 := by
    rw [QMCLeafB.RStInit.stN_init0]; exact hG
  obtain ⟨hlen, hent⟩ := QMCLeafB.RStInit.stX_correct p
  rw [hN] at hlen hent
  have hlen1 : (stX (QMCLeafB.RStInit.init0 p)).length = 1 := by simpa using hlen
  rw [dvR_eq_abs_entry _ hN hlen1]
  have he : (stX (QMCLeafB.RStInit.init0 p)).getD 0 0 = (QMCLeafB.InitVerdict.MOf 1)⁻¹ := by
    have h := hent (0 : Fin (1 * 1)) (0 : Fin (1 * 1))
    rw [QMCLeafB.InitVerdict.initShapeOf_apply] at h
    simp only [Fin.zero_eta, if_true] at h
    simpa [MatQ.entry] using h
  rw [he]
  have hM : QMCLeafB.InitVerdict.MOf 1 = 4 := by
    unfold QMCLeafB.InitVerdict.MOf QMCLeafB.InitVerdict.dqV
    norm_num
  rw [hM]
  norm_num

theorem oracleR_isCut (s : RSt) (h : dvR s ≠ 0) : (oracleR s).1 = true := by
  unfold oracleR
  rw [if_neg h]

/-! ## 3.  The orbit from `init0` at order one stays on the zero code -/

local notation "rnd" => QMCLeafB.RoundProgram.round

theorem stN_rnd (s : RSt) : stN (rnd s) = stN s := by
  unfold QMCLeafB.RoundProgram.round
  by_cases h : (oracleR s).1 <;> simp [h, QMCLeafB.RoundProgram.roundCut,
    QMCLeafB.RoundProgram.roundOk]

theorem stX_rnd_of_cut (s : RSt) (h : (oracleR s).1 = true) : stX (rnd s) = snapY s := by
  unfold QMCLeafB.RoundProgram.round
  rw [if_pos h]
  rfl

theorem orbit_zero (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ))
    (hG : p.1.1.n = 1) (T : ℕ) :
    stN (rnd^[T + 1] (QMCLeafB.RStInit.init0 p)) = 1 ∧
      stX (rnd^[T + 1] (QMCLeafB.RStInit.init0 p)) = [0] := by
  induction T with
  | zero =>
      have hN : stN (QMCLeafB.RStInit.init0 p) = 1 := by
        rw [QMCLeafB.RStInit.stN_init0]; exact hG
      have hlen : (stX (QMCLeafB.RStInit.init0 p)).length = 1 := by
        have hcor := QMCLeafB.RStInit.stX_correct p
        rw [hN] at hcor
        simpa using hcor.1
      have hcut : (oracleR (QMCLeafB.RStInit.init0 p)).1 = true :=
        oracleR_isCut _ (dvR_init0_ne p hG)
      have h1 : rnd^[0 + 1] (QMCLeafB.RStInit.init0 p)
          = rnd (QMCLeafB.RStInit.init0 p) := by
        rw [show 0 + 1 = 1 from rfl, Function.iterate_one]
      refine ⟨?_, ?_⟩
      · rw [h1, stN_rnd]; exact hN
      · rw [h1, stX_rnd_of_cut _ hcut]
        exact snapY_eq_zero _ hN hlen
  | succ T ih =>
      obtain ⟨ihN, ihX⟩ := ih
      set s := rnd^[T + 1] (QMCLeafB.RStInit.init0 p) with hs
      have hlen : (stX s).length = 1 := by rw [ihX]; rfl
      have hcut : (oracleR s).1 = true :=
        oracleR_isCut _ (by rw [dvR_eq_one _ ihN ihX]; norm_num)
      have hstep : rnd^[T + 1 + 1] (QMCLeafB.RStInit.init0 p) = rnd s := by
        rw [hs, show T + 1 + 1 = (T + 1) + 1 from rfl, Function.iterate_succ_apply']
      refine ⟨?_, ?_⟩
      · rw [hstep, stN_rnd]; exact ihN
      · rw [hstep, stX_rnd_of_cut _ hcut]
        exact snapY_eq_zero _ ihN hlen


/-! ## 4.  Every round is a cut, so the loop's verdict bit is `false` at every count -/

theorem oracleR_orbit_cut (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ))
    (hG : p.1.1.n = 1) (k : ℕ) : (oracleR (rnd^[k] (QMCLeafB.RStInit.init0 p))).1 = true := by
  cases k with
  | zero =>
      rw [Function.iterate_zero]
      exact oracleR_isCut _ (dvR_init0_ne p hG)
  | succ j =>
      obtain ⟨hN, hX⟩ := orbit_zero p hG j
      refine oracleR_isCut _ ?_
      rw [dvR_eq_one _ hN hX]
      norm_num

theorem stOks_orbit (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ))
    (hG : p.1.1.n = 1) (T : ℕ) :
    stOks (rnd^[T] (QMCLeafB.RStInit.init0 p)) = List.replicate T false := by
  rw [QMCLeafB.RStInit.stOks_iterate]
  have hnil : stOks (QMCLeafB.RStInit.init0 p) = [] := rfl
  rw [hnil, List.nil_append]
  have hmap : (List.range T).map
      (fun k => !((oracleR (rnd^[k] (QMCLeafB.RStInit.init0 p))).1))
      = (List.range T).map (fun _ => false) := by
    refine List.map_congr_left ?_
    intro k _
    rw [oracleR_orbit_cut p hG k]
    rfl
  rw [hmap]
  simp

theorem verdict_orbit_false (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ))
    (hG : p.1.1.n = 1) (T : ℕ) (hT : 1 ≤ T) :
    QMCLeafB.RoundProgram.verdict (rnd^[T] (QMCLeafB.RStInit.init0 p)) = false := by
  unfold QMCLeafB.RoundProgram.verdict
  rw [stOks_orbit p hG T]
  have h0 : (List.replicate T false).filter id = [] := by
    rw [List.filter_replicate]
    simp
  rw [h0]
  rfl

/-- **The verdict bit of the RSt loop at order one is `false` at every round count.** -/
theorem loopBit_false_n_one (G : QuantumMaxCutEnergy.Input) (hG : G.n = 1) (t : ℚ)
    (T : ℕ) (hT : 1 ≤ T) :
    QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 rnd QMCLeafB.RoundProgram.verdict
      (fun _ _ => T) G t = false := by
  unfold QMCLeafB.FinalStroke.loopBit
  exact verdict_orbit_false _ (by simpa using hG) T hT

/-- **The top-slice hypothesis of the interior stroke is false as stated**: at `t = 0`, order one,
the loop's bit is `false`. -/
theorem htop_interior_false
    (G : QuantumMaxCutEnergy.Input) (hG : G.n = 1) (T : ℕ) (hT : 1 ≤ T) :
    ¬ (∀ (G' : QuantumMaxCutEnergy.Input) (t : ℚ),
        -(((QMCLeafB.EngineRuntime.Rq G' / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
        QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 rnd QMCLeafB.RoundProgram.verdict
          (fun _ _ => T) G' t = true) := by
  intro h
  have hRq := QMCLeafB.EngineRuntime.Rq_nonneg G
  have h0 : -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ ((0 : ℚ) : ℝ) := by
    have hq : (0 : ℚ) ≤ QMCLeafB.EngineRuntime.Rq G / 40000 :=
      div_nonneg hRq (by norm_num)
    have hq' : (0 : ℝ) ≤ ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ) := by
      exact_mod_cast hq
    rw [Rat.cast_zero]
    linarith
  have hf := h G 0 h0 (le_refl (0 : ℚ))
  rw [loopBit_false_n_one G hG 0 T hT] at hf
  exact Bool.false_ne_true hf


end QMCLeafB.TopSliceRange


/-! ## Axiom audit -/


#print axioms QMCLeafB.TopSliceRange.soundEpsOnBracket_of_runData_interior_hn
#print axioms QMCLeafB.TopSliceRange.solution_of_runParts_interior_halve_hn

#print axioms QMCLeafB.TopSliceRange.snapY_eq_zero
#print axioms QMCLeafB.TopSliceRange.dvR_eq_one
#print axioms QMCLeafB.TopSliceRange.dvR_init0_ne
#print axioms QMCLeafB.TopSliceRange.orbit_zero
#print axioms QMCLeafB.TopSliceRange.stOks_orbit
#print axioms QMCLeafB.TopSliceRange.verdict_orbit_false
#print axioms QMCLeafB.TopSliceRange.loopBit_false_n_one
#print axioms QMCLeafB.TopSliceRange.htop_interior_false


