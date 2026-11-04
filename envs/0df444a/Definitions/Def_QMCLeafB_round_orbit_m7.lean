-- Prove2me | Definitions.Def_QMCLeafB_round_orbit_m7
-- name    : QMCLeafB_round_orbit_m7
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T01:10:22.59248+00:00
-- url     : https://prove2.me/theorems/0baad9fd-6056-45a7-8db2-ae7f1bd8a74e
-- title:
--   QMCLeafB round_orbit_m7
-- statement:
--   # leaf B phase 14 — `round-orbit` (swarm `smw17fqzz`, member m7, direction d13)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_roundsize_m6
import Definitions.Def_QMCLeafB_final_stroke_m7
import Definitions.Def_QMCLeafB_assembly_fuel_m4
/-
# leaf B phase 14 — `round-orbit` (swarm `smw17fqzz`, member m7, direction d13)

`RoundSizeM6.endgame_RSt_size` (`Check_roundsize_m6`) reduces the leaf to `htop`, `hd` and **one**
size hypothesis

    hM : ∀ s : RSt, Msz s ≤ C₀ * ((enc s).length + 1) ^ k.

That statement quantifies over **every** state, and it is false as stated: `Msz` contains
`capX s = (stN s * stN s) * (6 * (Lmu s + Ld s) + 21)`, and nothing in `(enc s).length` relates the
dimension `stN s` to the length of the primal code `stX s`.  A state with `stN s = 2^100` and
`stX s = []` has `(enc s).length` about a hundred bits and `Msz s` about `2^200 * 21`.  No polynomial
in the encoding length dominates that.

What the ledger *does* give unconditionally is `round_cap : Msz (round s) ≤ Msz s + 6` and
`round_step : (enc (round s)).length ≤ max ((enc s).length + 6) (Msz s)`.  So the cap only has to be
paid **once**, at the state the loop starts from; after that it grows by 6 bits per round.  This file
turns exactly that into the `horbit` slot the endgame wants:

    horbit_of_cap (hM0 : ∀ a, Msz a.1 ≤ C₀ * ((encSt a).length + 1) ^ k) :
      ∀ a j, j ≤ a.2.length →
        (encSt (round^[j] a.1, a.2.drop j)).length ≤ (sizesOrbitPow (C₀+1) k).eval (encSt a).length

with `sizes = (2C₀+4)·(X+1)^k`, so `RoundSizeM6.endgame_RSt_size`'s `hM` is replaced by a bound at a
*single* state.  The remaining job at that single state is `Msz (init0 p) ≤ C₀ * (L+1)^k`, where
`init0`'s `X` is the `n²`-entry identity code — that is where the `n²` versus `n` relation is
available, and only there.

No `sorry`, no `axiom`; audits at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section
namespace QMCLeafB.RoundOrbit

open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open QMCLeafB.RoundSizeM6

local instance instRequestCodingRoundOrbit : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 1.  The Bool list encoding is exactly three bits per element -/

theorem encodeBool_length (b : Bool) : (enc b : List Bool).length = 1 := rfl

theorem encodeListBool_length (l : List Bool) :
    (encodeList (enc : Bool → List Bool) l).length = 3 * l.length := by
  induction l with
  | nil => rw [show encodeList (enc : Bool → List Bool) [] = [] from rfl]; simp
  | cons b bs ih =>
      rw [EncodedList.cons_length, encodeBool_length, ih]
      simp only [List.length_cons]
      ring

/-- The `Coding (List Bool)` encoding is the list encoding, definitionally. -/
theorem encListBool_eq (l : List Bool) :
    (enc l : List Bool) = encodeList (enc : Bool → List Bool) l := rfl

theorem encSt_unfold (s : QMCLeafB.RoundProgram.RSt) (f : List Bool) :
    (QMCLeafB.SimPoly.encSt (s, f)).length
      = 2 * (enc s).length + 1 + 3 * f.length := by
  rw [show (QMCLeafB.SimPoly.encSt (s, f)).length
      = 2 * (enc s).length + 1 + (encodeList (enc : Bool → List Bool) f).length from
    encodePair_length (enc : QMCLeafB.RoundProgram.RSt → List Bool) (enc : List Bool → List Bool) (s, f)]
  rw [encodeListBool_length]

/-! ## 2.  The cap propagates by 6 bits a round -/

/-- The orbit cap: `Msz` grows by at most 6 bits per round. -/
theorem Msz_orbit (s : QMCLeafB.RoundProgram.RSt) (j : ℕ) :
    Msz (QMCLeafB.RoundProgram.round^[j] s) ≤ Msz s + 6 * j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have h1 : Msz (QMCLeafB.RoundProgram.round^[j + 1] s)
          = Msz (QMCLeafB.RoundProgram.round (QMCLeafB.RoundProgram.round^[j] s)) := by
        rw [Function.iterate_succ_apply']
      rw [h1]
      have h2 : Msz (QMCLeafB.RoundProgram.round (QMCLeafB.RoundProgram.round^[j] s)) ≤ Msz (QMCLeafB.RoundProgram.round^[j] s) + 6 := round_cap _
      have h3 : 6 * (j + 1) = 6 * j + 6 := by ring
      omega

/-- The orbit's encoded length: it never exceeds `max ((enc s).length) (Msz s)`, plus `6` a round. -/
theorem enc_orbit (s : QMCLeafB.RoundProgram.RSt) (j : ℕ) :
    (enc (QMCLeafB.RoundProgram.round^[j] s)).length
      ≤ max ((enc s).length) (Msz s) + 6 * j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have h1 : (enc (QMCLeafB.RoundProgram.round^[j + 1] s)).length
          = (enc (QMCLeafB.RoundProgram.round (QMCLeafB.RoundProgram.round^[j] s))).length := by
        rw [Function.iterate_succ_apply']
      rw [h1]
      have h2 := round_step (QMCLeafB.RoundProgram.round^[j] s)
      have h3 := Msz_orbit s j
      have hcur : (enc (QMCLeafB.RoundProgram.round (QMCLeafB.RoundProgram.round^[j] s))).length
          ≤ max ((enc (QMCLeafB.RoundProgram.round^[j] s)).length)
              (Msz (QMCLeafB.RoundProgram.round^[j] s)) + 6 := by
        rcases le_total ((enc (QMCLeafB.RoundProgram.round^[j] s)).length + 6)
          (Msz (QMCLeafB.RoundProgram.round^[j] s)) with h | h
        · rw [max_eq_right h] at h2
          exact le_trans h2 (le_trans (le_max_right _ _) (Nat.le_add_right _ _))
        · rw [max_eq_left h] at h2
          exact le_trans h2 (by omega)
      have hmaxmono : max ((enc (QMCLeafB.RoundProgram.round^[j] s)).length)
            (Msz (QMCLeafB.RoundProgram.round^[j] s))
          ≤ max ((enc s).length) (Msz s) + 6 * j := by
        refine max_le ?_ ?_
        · omega
        · omega
      have h6 : 6 * (j + 1) = 6 * j + 6 := by ring
      omega

/-! ## 3.  `horbit` from a cap bound at one state -/

/-- **The size slot of the `RSt` loop, from a single cap bound.**  `C₀` and `k` are
`RoundSizeM6`'s, but the hypothesis `hM0` is read at `a.1` only — which is the only place where the
relation `stX s |>.length = stN s * stN s` is available.  The size polynomial is
`sizesOrbitPow (C₀+2) k = (2C₀+6)·(X+1)^k`. -/
theorem horbit_of_cap (C₀ k : ℕ) (hk : 1 ≤ k)
    (hM0 : ∀ a : QMCLeafB.RoundProgram.RSt × List Bool,
      Msz a.1 ≤ C₀ * ((QMCLeafB.SimPoly.encSt a).length + 1) ^ k) :
    ∀ a : QMCLeafB.RoundProgram.RSt × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (QMCLeafB.RoundProgram.round^[j] a.1, a.2.drop j)).length
        ≤ (QMCLeafB.FinalStroke.sizesOrbitPow (C₀ + 2) k).eval
            (QMCLeafB.SimPoly.encSt a).length := by
  intro a j hj
  set T := (QMCLeafB.SimPoly.encSt a).length with hT
  set L := (enc a.1).length with hL
  have hTdef : T = 2 * L + 1 + 3 * a.2.length := by
    rw [hT, encSt_unfold, hL]
  have hcap : Msz a.1 ≤ C₀ * (T + 1) ^ k := hM0 a
  have hTk : (T + 1) ≤ (T + 1) ^ k := Nat.le_self_pow (show k ≠ 0 by omega) (T + 1)
  have hcap : Msz a.1 ≤ C₀ * (T + 1) ^ k := hM0 a
  have hmax : max L (Msz a.1) ≤ (C₀ + 1) * (T + 1) ^ k := by
    refine max_le ?_ ?_
    · calc L ≤ T := by omega
        _ ≤ (T + 1) := by omega
        _ ≤ (T + 1) ^ k := hTk
        _ ≤ (C₀ + 1) * (T + 1) ^ k := Nat.le_mul_of_pos_left _ (by omega)
    · calc Msz a.1 ≤ C₀ * (T + 1) ^ k := hcap
        _ ≤ (C₀ + 1) * (T + 1) ^ k := Nat.mul_le_mul_right _ (by omega)
  have henc := enc_orbit a.1 j
  have hdrop : (a.2.drop j).length = a.2.length - j := List.length_drop ..
  have hstep : (QMCLeafB.SimPoly.encSt
        (QMCLeafB.RoundProgram.round^[j] a.1, a.2.drop j)).length
      = 2 * (enc (QMCLeafB.RoundProgram.round^[j] a.1)).length + 1
        + 3 * (a.2.drop j).length := encSt_unfold _ _
  rw [QMCLeafB.FinalStroke.sizesOrbitPow_eval, hstep, hdrop]
  -- every linear term is absorbed by `T`
  have hlen : 3 * a.2.length ≤ T := by omega
  have hj3 : 3 * j ≤ T := by omega
  have henc2 : 2 * (enc (QMCLeafB.RoundProgram.round^[j] a.1)).length
      ≤ 2 * ((C₀ + 1) * (T + 1) ^ k) + 12 * j := by
    have h1 : (enc (QMCLeafB.RoundProgram.round^[j] a.1)).length
        ≤ max L (Msz a.1) + 6 * j := henc
    nlinarith
  have hfour : 12 * j ≤ 4 * (T + 1) ^ k := by
    have hA : 4 * T ≤ 4 * (T + 1) ^ k :=
      Nat.mul_le_mul_left 4 (le_trans (Nat.le_succ T) hTk)
    omega
  have hone : 1 + 3 * (a.2.length - j) ≤ (T + 1) ^ k := by
    have hA : 3 * (a.2.length - j) ≤ 3 * a.2.length := by omega
    omega
  have hexp : (2 * (C₀ + 2) + 2) * (T + 1) ^ k
      = 2 * ((C₀ + 1) * (T + 1) ^ k) + 4 * (T + 1) ^ k := by ring
  rw [hexp]
  have hcomb : 2 * (enc (QMCLeafB.RoundProgram.round^[j] a.1)).length
        + 1 + 3 * (a.2.length - j)
      ≤ 2 * ((C₀ + 1) * (T + 1) ^ k) + 4 * (T + 1) ^ k := by omega
  exact hcomb

/-! **`Msz` is not polynomially bounded in the encoding length.**  `capX s = (stN s * stN s) *
(6 * (Lmu s + Ld s) + 21)` and `(enc s).length` does not relate `stN s` to the length of `stX s`, so
`RoundSizeM6.endgame_RSt_size`'s `hM : ∀ s, Msz s ≤ C₀ * ((enc s).length + 1) ^ k` is **false as
stated**: the family `mkSt (2^m) [] [] 0 0 0 [] []` has encoding length `O(m)` and `Msz ≈ 21·4^m`.
So `hM` has to be restricted to the states the loop actually visits, or `Msz` has to be defined with
the *effective* dimension `(stX s).length` (which `smulRaw`/`snapY` already use) instead of
`stN s * stN s`.  What survives unconditionally is `round_cap` (`Msz` grows 6 bits a round) and
`round_step`, and `horbit_of_cap` below turns either into the endgame's `horbit` slot. -/
/-- **The endgame with `horbit` discharged from m6's cap hypothesis.**  This is
`FuelAssembly.solution_RSt` with its `horbit` slot supplied by `horbit_of_cap`, so the residuals of
the leaf at `σ = RSt` are now `htop`, `hd` and the single cap bound `hM0`. -/
theorem solution_RSt_cap (k : ℕ) (hk : 20 ≤ 2 ^ k) (C₀ kk : ℕ) (hkk : 1 ≤ kk)
    (hM0 : ∀ a : QMCLeafB.RoundProgram.RSt × List Bool,
      Msz a.1 ≤ C₀ * ((QMCLeafB.SimPoly.encSt a).length + 1) ^ kk)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FuelAssembly.loopBitRSt G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts (QMCLeafB.FuelAssembly.loopBitRSt) G t
        (QMCLeafB.FuelWire.paramsHalve G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FuelAssembly.solution_RSt k hk
    (QMCLeafB.FinalStroke.sizesOrbitPow (C₀ + 2) kk) (horbit_of_cap C₀ kk hkk hM0) htop hd

end QMCLeafB.RoundOrbit

/-! ## 4.  Axiom audit -/

#print axioms QMCLeafB.RoundOrbit.encodeBool_length
#print axioms QMCLeafB.RoundOrbit.encodeListBool_length
#print axioms QMCLeafB.RoundOrbit.encSt_unfold
#print axioms QMCLeafB.RoundOrbit.Msz_orbit
#print axioms QMCLeafB.RoundOrbit.enc_orbit
#print axioms QMCLeafB.RoundOrbit.horbit_of_cap
#print axioms QMCLeafB.RoundOrbit.solution_RSt_cap


