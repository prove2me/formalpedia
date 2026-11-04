-- Prove2me | Definitions.Def_QMCLeafB_conformance_m8
-- name    : QMCLeafB_conformance_m8
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T02:17:59.086952+00:00
-- url     : https://prove2.me/theorems/bef1d191-3364-4b6c-85bc-9115ef85f80a
-- title:
--   QMCLeafB conformance_m8
-- statement:
--   # leaf B phase 16 — `conformance` (swarm `smw1ez4a9`, member m8, direction d2)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_brick_finish_line
import Definitions.Def_QMCLeafB_brick_verdict_sound
import Definitions.Def_QMCLeafB_sim_loop_m6
import Definitions.Def_QMCLeafB_LoopRestate
import Definitions.Def_QMCLeafB_ClosingBracket
import Definitions.Def_QMCLeafB_final_stroke_m7
import Definitions.Def_QMCLeafB_final_reunion_m7
import Definitions.Def_QMCLeafB_guard
import Definitions.Def_QMCLeafB_capguard_m3
import Definitions.Def_QMCLeafB_roundT_m7
import Definitions.Def_QMCLeafB_integration_m6
import Definitions.Def_QMCLeafB_round_orbit_m7
import Definitions.Def_QMCLeafB_centre_m5
import Definitions.Def_QMCLeafB_runparts_m5
import Definitions.Def_QMCLeafB_runparts_dilate_m5
import Definitions.Def_QMCLeafB_halve_perG_m2
import Definitions.Def_QMCLeafB_fuelwire_m4
import Definitions.Def_QMCLeafB_unionShallow
import Definitions.Def_QMCLeafB_ledgerG_m3
import Definitions.Def_QMCLeafB_loopclose_m2
import Definitions.Def_QMCLeafB_initdq_m1
import Definitions.Def_QMCLeafB_roundGU_endgame_m7
/-
# leaf B phase 16 — `conformance` (swarm `smw1ez4a9`, member m8, direction d2)

Cross-brick conformance glue and audit for the final mile.  What is here, in order:

* **§1** `massV_init0`/`epsOf_init0`: the flat-code bridge `∑|A| = ∑ᵢⱼ|wMatQ| = Rq`, i.e. the
  campaign slack read back at `init0` (`epsOf = Rq/40000`) — needed by every `t + εw` test.
* **§2** `roundGT` = guard ∘ slack round, its `Poly` proof, its orbit (`roundGT_iterate_eq_roundT`,
  guard inert), the flag ledger (`stOks_roundGT`, `verdict_iterate_eq_anyOk_GT`).
* **§3** `LedgerGT`: the branch-wise one-step ledger (ok branch unconditional, cut branch at
  normalised states only — off the normalised set the cut rebuilds `X` from `n`, which is `log n`
  bits, so no polynomial cap absorbs it), with `ledgerG_of_ledgerGT` and `ledgerGT_of_ledgerGT`.
* **§4** `htop` at the guarded slack round, and (further down) at an arbitrary init (§10).
* **§5/§5b** the assembly contract over `IntegrateM6.solution_of_bricks`, at `roundGT`, `roundT` and
  any round.
* **§6** the statement lock: the `d9f601e5` sentence written out, both directions by `exact`.
* **§7** supply audit: the routing's named supplies, type-locked (`example`/`#check`).
* **§8** m5's shallow stroke composed with the bricks (`endgame_shallow_at_roundGT`).
* **§9** `ledgerGT_MszG` from m3's `LedgerG`, and the leaf from two hypotheses.
* **§10** `htop` at an arbitrary init (brick 1's interface).
* **§11** the flag stream: `okGT_eq_false`/`okGT_eq_true` and `hverdict_GT`.
* **§12** the leaf from brick 4 alone at m2's `4·Kbc` count.
* **§13** `verdictT`: the alternative verdict slot (plan flags ∨ top test), which keeps `hmem`.
* **§14** `epsOf` at brick 1's own `InitDq.init0` (the sixth init fact), and the leaf from `hd`.
* **§15** **the final wiring**: `endgame_leaf_final`/`solution_final` — the `d9f601e5` sentence from
  brick 4's `RunParts` at the SHELF round, via m7's `roundGU` endgame, at brick 1's real init.

Every theorem is axiom-audited below (`[propext, Classical.choice, Quot.sound]`); no `sorry`, no
`axiom`, no `native_decide`, no `unsafe`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped BigOperators
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.ConformanceM8

open QuantumMaxCutEnergy
open QMCNumericRuntime
open QMCLeafB.RoundProgram

local instance instRequestCodingM8 :
    Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 1.  The campaign's slack, read back at `init0` -/

/-- **`MatQ.mk` commutes with a pointwise map.** -/
theorem map_mk (n : ℕ) (f : ℕ → ℕ → ℚ) (g : ℚ → ℚ) :
    (MatQ.mk n f).map g = MatQ.mk n (fun i j => g (f i j)) := by
  unfold MatQ.mk
  rw [List.map_flatMap]
  congr 1
  funext i
  rw [List.map_map]
  rfl

/-- **The sum of a row-major code is the double sum.** -/
theorem mk_sum (n : ℕ) (f : ℕ → ℕ → ℚ) :
    (MatQ.mk n f).sum = ∑ i : Fin n, ∑ j : Fin n, f i j := by
  rw [MatQ.mk, MatQ.sum_flatMap_range]
  exact Finset.sum_congr rfl fun i _ => MatQ.list_sum_range (fun j => f (i : ℕ) j) n

/-- **The state's ℓ¹ mass at `init0` is the graph's total weight `Rq G`.** -/
theorem massV_init0 (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    QMCLeafB.RoundT.massV (QMCLeafB.RStInit.init0 p) = QMCLeafB.EngineRuntime.Rq p.1.1 := by
  obtain ⟨⟨G, coins⟩, t⟩ := p
  set es := parseEdges (QuantumMaxCutEnergy.encodeRequest (G, coins)) with hes
  have hA : stA (QMCLeafB.RStInit.init0 ((G, coins), t)) = MatQ.mk G.n (QMCLeafB.RStInit.wVal es) := by
    rw [QMCLeafB.RStInit.stA_init0, QMCLeafB.RStInit.wProg_eq,
      QMCNumericRuntime.inputWidth_request]
  have hpt : ∀ (i j : Fin G.n), QMCLeafB.RoundProgram.absq (QMCLeafB.RStInit.wVal es i j)
      = |QMCLeafB.RStInit.wMatQ G i j| := by
    intro i j
    rw [QMCLeafB.RoundProgram.absq_eq]
    congr 1
    have h1 := (QMCLeafB.RStInit.wProg_correct G coins).2 i j
    rw [QMCLeafB.RStInit.wProg_eq, QMCNumericRuntime.inputWidth_request,
      MatQ.entry_mk _ _ i.isLt j.isLt] at h1
    exact h1
  unfold QMCLeafB.RoundT.massV
  rw [hA, map_mk, mk_sum]
  calc ∑ i : Fin G.n, ∑ j : Fin G.n, QMCLeafB.RoundProgram.absq (QMCLeafB.RStInit.wVal es i j)
      = ∑ i : Fin G.n, ∑ j : Fin G.n, |QMCLeafB.RStInit.wMatQ G i j| :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hpt i j
    _ = QMCLeafB.EngineRuntime.Rq G := QMCLeafB.RStInit.abs_sum_wMatQ G

/-- **The slack at `init0` is `Rq G / 40000`** — the leaf's own `εw`. -/
theorem epsOf_init0 (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    QMCLeafB.RoundT.epsOf (QMCLeafB.RStInit.init0 p)
      = QMCLeafB.EngineRuntime.Rq p.1.1 / 40000 := by
  unfold QMCLeafB.RoundT.epsOf
  rw [massV_init0]
  ring

/-! ## 2.  The guarded slack round `roundGT` -/

/-- **The round the leaf actually runs**: m1's normalisation guard outside m7's slack round. -/
noncomputable def roundGT (s : RSt) : RSt :=
  if (stX s).length = stN s * stN s then QMCLeafB.RoundT.roundT s
  else QMCLeafB.RoundProgram.roundOk s

theorem roundGT_of_normalised (s : RSt) (h : (stX s).length = stN s * stN s) :
    roundGT s = QMCLeafB.RoundT.roundT s := by
  unfold roundGT
  rw [if_pos h]

theorem roundGT_of_abnormal (s : RSt) (h : ¬ ((stX s).length = stN s * stN s)) :
    roundGT s = QMCLeafB.RoundProgram.roundOk s := by
  unfold roundGT
  rw [if_neg h]

/-- `roundT` keeps the state's order. -/
theorem stN_roundT (s : RSt) : stN (QMCLeafB.RoundT.roundT s) = stN s := by
  unfold QMCLeafB.RoundT.roundT
  split_ifs with h
  · rfl
  · exact QMCLeafB.RStInit.stN_round s

/-- `roundT` keeps a normalised state normalised. -/
theorem roundT_normalised (s : RSt) (h : (stX s).length = stN s * stN s) :
    (stX (QMCLeafB.RoundT.roundT s)).length
      = stN (QMCLeafB.RoundT.roundT s) * stN (QMCLeafB.RoundT.roundT s) := by
  unfold QMCLeafB.RoundT.roundT
  split_ifs with hc
  · rw [QMCLeafB.GuardedRound.stN_roundOk, QMCLeafB.GuardedRound.stX_roundOk]
    exact h
  · have h1 := QMCLeafB.GuardedRound.roundG_normalised s h
    rwa [QMCLeafB.GuardedRound.roundG_of_normalised s h] at h1

/-- The guard is inert along the run of `roundGT` from a normalised start. -/
theorem roundGT_iterate_normalised {init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → RSt}
    (hnorm : ∀ p, (stX (init p)).length = stN (init p) * stN (init p))
    (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) (j : ℕ) :
    (stX (roundGT^[j] (init p))).length
      = stN (roundGT^[j] (init p)) * stN (roundGT^[j] (init p)) := by
  induction j with
  | zero => simpa using hnorm p
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      unfold roundGT
      split_ifs with h
      · exact roundT_normalised _ h
      · rw [QMCLeafB.GuardedRound.stN_roundOk, QMCLeafB.GuardedRound.stX_roundOk]
        exact ih

/-- **`roundGT` is `roundT` on the whole orbit from a normalised start.** -/
theorem roundGT_iterate_eq_roundT {init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → RSt}
    (hnorm : ∀ p, (stX (init p)).length = stN (init p) * stN (init p))
    (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) (j : ℕ) :
    roundGT^[j] (init p) = QMCLeafB.RoundT.roundT^[j] (init p) := by
  induction j with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      refine roundGT_of_normalised _ ?_
      have hk := roundGT_iterate_normalised hnorm p k
      rw [ih] at hk
      exact hk

/-- **`roundGT` is a `Poly` program.** -/
theorem poly_roundGT : Automatic.Poly roundGT := by
  have hlen : Automatic.Poly (fun s : RSt => (stX s).length) :=
    Automatic.Poly.comp (f := (List.length : List ℚ → ℕ)) (g := stX)
      (Automatic.Poly.list_length (α := ℚ)) QMCLeafB.RoundProgram.poly_stX
  have hnn : Automatic.Poly (fun s : RSt => stN s * stN s) :=
    Automatic.Poly.comp (f := fun x : ℕ × ℕ => x.1 * x.2)
      (g := fun s : RSt => (stN s, stN s)) Automatic.Poly.nat_mul
      (Automatic.Poly.pair QMCLeafB.RoundProgram.poly_stN QMCLeafB.RoundProgram.poly_stN)
  have hp : Automatic.Poly (fun s : RSt => decide ((stX s).length = stN s * stN s)) :=
    Automatic.Poly.nat_eq_comp hlen hnn
  have h := Automatic.Poly.ite_prop
    (p := fun s : RSt => (stX s).length = stN s * stN s) hp
    QMCLeafB.RoundT.poly_roundT QMCLeafB.RoundProgram.poly_roundOk
  exact QMCLeafB.FinishLine.poly_of_pointwise h (fun s => rfl)

/-- **The flag `roundGT` appends.**  On a normalised state it is the slack test's answer (`ok` when
the point is feasible at the campaign's own slack `t + εw`), otherwise it is the freeze's `ok`. -/
noncomputable def okGT (s : RSt) : Bool :=
  if (stX s).length = stN s * stN s then
    (if fvR s ≤ stT s + QMCLeafB.RoundT.epsOf s then true else !((oracleR s).1))
  else true

theorem stOks_roundT (s : RSt) :
    stOks (QMCLeafB.RoundT.roundT s) = stOks s ++
      [if fvR s ≤ stT s + QMCLeafB.RoundT.epsOf s then true else !((oracleR s).1)] := by
  by_cases hc : fvR s ≤ stT s + QMCLeafB.RoundT.epsOf s
  · rw [QMCLeafB.RoundT.roundT, if_pos hc, if_pos hc]
    rfl
  · rw [QMCLeafB.RoundT.roundT, if_neg hc, if_neg hc]
    exact QMCLeafB.RStInit.stOks_round s

theorem stOks_roundGT (s : RSt) : stOks (roundGT s) = stOks s ++ [okGT s] := by
  by_cases h : (stX s).length = stN s * stN s
  · rw [roundGT_of_normalised s h, okGT, if_pos h, stOks_roundT]
  · rw [roundGT_of_abnormal s h, okGT, if_neg h]
    rfl

theorem stOks_iterate_GT (s : RSt) (T : ℕ) :
    stOks (roundGT^[T] s) = stOks s ++ (List.range T).map (fun k => okGT (roundGT^[k] s)) := by
  induction T generalizing s with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', stOks_roundGT, ih, List.range_succ, List.map_append,
        List.map_cons, List.map_nil, List.append_assoc]

/-- **`hverdict` at the guarded slack loop**: the loop's bit is the run's `anyOk`. -/
theorem verdict_iterate_eq_anyOk_GT (s : RSt) (hs : stOks s = []) (T : ℕ) :
    QMCLeafB.RoundProgram.verdict (roundGT^[T] s)
      = QMCLeafB.SimLoop.anyOk (fun k => okGT (roundGT^[k] s)) T := by
  unfold QMCLeafB.RoundProgram.verdict
  rw [stOks_iterate_GT, hs, List.nil_append]
  exact QMCLeafB.RStInit.decide_pos_filter_map_range _ T

/-- The loop bit of `roundGT` is the loop bit of `roundT` on any normalised start. -/
theorem loopBit_GT_eq_roundT {init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → RSt}
    (hnorm : ∀ p, (stX (init p)).length = stN (init p) * stN (init p))
    (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ) (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.FinalStroke.loopBit init roundGT QMCLeafB.RoundProgram.verdict T0 G t
      = QMCLeafB.FinalStroke.loopBit init QMCLeafB.RoundT.roundT
          QMCLeafB.RoundProgram.verdict T0 G t := by
  unfold QMCLeafB.FinalStroke.loopBit
  rw [roundGT_iterate_eq_roundT hnorm]

/-! ## 3.  The branch-wise ledger, and its two readings

Brick 2's `CapGuard.LedgerG` is stated at `roundG`; the assembly runs `roundGT`.  On a normalised
state `roundGT` is either `roundOk` (slack branch) or literally `round` (else branch), and on an
abnormal state it is `roundOk`.  So the *branch-wise* form below is what both rounds follow from,
and it is the interface brick 2 should prove. -/

/-- **The branch-wise one-step ledger.**  Three pieces, in exactly the strength the guarded slack
round needs:

* the `ok` branch (`roundOk`) — unconditional: it freezes the state and appends one flag;
* the `cut` branch (`round`) — only at a **normalised** state (`|X| = n·n`), which is the only place
  the cut branch can be reached on the orbit: off the normalised set the guard freezes the state.
  (The cut branch at an *abnormal* state rebuilds `X` from `n`, and `n` is `log n` bits, so no
  polynomial cap can absorb that jump: the normalised restriction is not a convenience, it is the
  exact strength in which the ledger is true.);
* the polynomial cap on `M`. -/
def LedgerGT (M : RSt → ℕ) (c : ℕ) : Prop :=
  (∀ s, M (QMCLeafB.RoundProgram.roundOk s) ≤ M s + c) ∧
  (∀ s, (enc (QMCLeafB.RoundProgram.roundOk s)).length ≤ max ((enc s).length + c) (M s)) ∧
  (∀ s, (stX s).length = stN s * stN s → M (QMCLeafB.RoundProgram.round s) ≤ M s + c) ∧
  (∀ s, (stX s).length = stN s * stN s →
    (enc (QMCLeafB.RoundProgram.round s)).length ≤ max ((enc s).length + c) (M s)) ∧
  (∃ C₀ k, ∀ s, M s ≤ C₀ * ((enc s).length + 1) ^ k)

/-- **The branch-wise ledger gives m3's `LedgerG` at the guarded round.** -/
theorem ledgerG_of_ledgerGT {M : RSt → ℕ} {c : ℕ} (h : LedgerGT M c) :
    QMCLeafB.CapGuard.LedgerG M c := by
  obtain ⟨hOi, hOs, hCi, hCs, hcap⟩ := h
  refine ⟨?_, ?_, hcap⟩
  · intro s
    by_cases hg : (stX s).length = stN s * stN s
    · rw [QMCLeafB.GuardedRound.roundG_of_normalised s hg]
      exact hCi s hg
    · rw [QMCLeafB.GuardedRound.roundG_of_abnormal s hg]
      exact hOi s
  · intro s
    by_cases hg : (stX s).length = stN s * stN s
    · rw [QMCLeafB.GuardedRound.roundG_of_normalised s hg]
      exact hCs s hg
    · rw [QMCLeafB.GuardedRound.roundG_of_abnormal s hg]
      exact hOs s

/-- **The branch-wise ledger at the guarded slack round.** -/
theorem ledgerGT_of_ledgerGT {M : RSt → ℕ} {c : ℕ} (h : LedgerGT M c) :
    (∀ s, M (roundGT s) ≤ M s + c) ∧
    (∀ s, (enc (roundGT s)).length ≤ max ((enc s).length + c) (M s)) := by
  obtain ⟨hOi, hOs, hCi, hCs, hcap⟩ := h
  constructor
  · intro s
    by_cases hg : (stX s).length = stN s * stN s
    · rw [roundGT_of_normalised s hg]
      unfold QMCLeafB.RoundT.roundT
      split_ifs with hs
      · exact hOi s
      · exact hCi s hg
    · rw [roundGT_of_abnormal s hg]
      exact hOi s
  · intro s
    by_cases hg : (stX s).length = stN s * stN s
    · rw [roundGT_of_normalised s hg]
      unfold QMCLeafB.RoundT.roundT
      split_ifs with hs
      · exact hOs s
      · exact hCs s hg
    · rw [roundGT_of_abnormal s hg]
      exact hOs s

/-! ## 4.  `htop` at the guarded slack round -/

/-- **The top slice is decided by the first round.**  On `-Rq G/40000 ≤ t ≤ 0` the initial point has
`fvR = 0` and slack `Rq G/40000`, so `roundT`'s first round reports `ok` and every later round keeps
the flag; the guard is inert because `init0` is normalised.  Hence the loop's bit is `true` at any
positive count. -/
theorem htop_roundGT (K : QuantumMaxCutEnergy.Input → ℕ) (hK : ∀ G, 1 ≤ K G)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hlo : -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ)) (hhi : t ≤ 0) :
    QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 roundGT
      QMCLeafB.RoundProgram.verdict (fun G' _ => K G') G t = true := by
  unfold QMCLeafB.FinalStroke.loopBit
  rw [roundGT_iterate_eq_roundT QMCLeafB.RStInit.init_normalised]
  refine QMCLeafB.RoundT.htop_roundT G t (hK G) ?_
  have h1 : QMCLeafB.RoundT.epsOf
      (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))
      = QMCLeafB.EngineRuntime.Rq G / 40000 := epsOf_init0 _
  have hloR : -((QMCLeafB.EngineRuntime.Rq G : ℝ) / 40000) ≤ (t : ℝ) := by
    have h := hlo
    push_cast at h
    linarith
  have h2 : (0 : ℚ) ≤ t + QMCLeafB.EngineRuntime.Rq G / 40000 := by
    have hcast : ((t + QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ)
        = (t : ℝ) + (QMCLeafB.EngineRuntime.Rq G : ℝ) / 40000 := by
      push_cast
      ring
    have hpos : (0 : ℝ) ≤ ((t + QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ) := by
      rw [hcast]
      linarith
    exact_mod_cast hpos
  rw [h1]
  exact h2
/-! ## 5.  The assembly contract

`IntegrateM6.solution_of_bricks` is the phase-14 assembly, and — unlike
`Conformance.solution_union` and `RoundOrbit.solution_RSt_cap`, whose `hd` slot is keyed to
`FuelWire.paramsHalve` and therefore to `dq = 1` (uninhabited at the campaign's rounding budget,
m5's obstruction) — it mentions **no** `dq`, `rmax`, `m` or `K`: the numeric half rides inside
`VerdictSound.RunData`.  So it is the correct assembly for the phase-16 parameter family
(`dqShallow`), and everything below is the same theorem with its slots named. -/

/-- **The leaf from the phase-16 residuals.**  `SolutionStatement` from:

* `init` (brick 1, at `dqShallow`) with `Poly` and tape-freeness;
* the fuel wire `(fuel p).length = K p.1.1` (brick 1/4) with `Poly fuel`;
* the branch-wise one-step ledger `LedgerGT M c` (brick 2) and the cap `M ≤ C₀(enc+1)^k`;
* `htop` (brick 3) — discharged by `htop_roundGT` at `init0`;
* `hd` (brick 4) — `RunData` on the strict interior at the same `K`.

`round` is `roundGT` and `verdict` is `RoundProgram.verdict`; both are programs. -/
theorem endgame_of_phase16
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → RSt)
    (hinit : Automatic.Poly init)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (hfuel : Automatic.Poly fuel)
    (K : QuantumMaxCutEnergy.Input → ℕ)
    (hinitTape : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = K p.1.1)
    (M : RSt → ℕ) (C₀ c k : ℕ) (hk : 1 ≤ k)
    (hled : LedgerGT M c)
    (hcap : ∀ s, M s ≤ C₀ * ((enc s).length + 1) ^ k)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init roundGT QMCLeafB.RoundProgram.verdict
        (fun G' _ => K G') G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.VerdictSound.RunData
        (QMCLeafB.FinalStroke.loopBit init roundGT QMCLeafB.RoundProgram.verdict
          (fun G' _ => K G')) G t) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.IntegrateM6.solution_of_bricks init fuel roundGT QMCLeafB.RoundProgram.verdict
    hinit hfuel poly_roundGT QMCLeafB.RoundProgram.poly_verdict
    M C₀ c k hk (ledgerGT_of_ledgerGT hled).1 (ledgerGT_of_ledgerGT hled).2 hcap
    K hinitTape hfuelLen htop hd

/-- **The same, with `init0` and `htop` already discharged.**  The leaf's remaining content is
exactly: the fuel wire, the branch-wise ledger with its cap, and the interior `RunData` bundle. -/
theorem endgame_phase16_at_init0
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (hfuel : Automatic.Poly fuel)
    (K : QuantumMaxCutEnergy.Input → ℕ) (hK : ∀ G, 1 ≤ K G)
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = K p.1.1)
    (M : RSt → ℕ) (C₀ c k : ℕ) (hk : 1 ≤ k)
    (hled : LedgerGT M c)
    (hcap : ∀ s, M s ≤ C₀ * ((enc s).length + 1) ^ k)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.VerdictSound.RunData
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 roundGT
          QMCLeafB.RoundProgram.verdict (fun G' _ => K G')) G t) :
    QMCLeafB.FinishLine.SolutionStatement :=
  endgame_of_phase16 QMCLeafB.RStInit.init0 QMCLeafB.RStInit.poly_init0 fuel hfuel K
    QMCLeafB.RStInit.init0_tape hfuelLen M C₀ c k hk hled hcap
    (htop_roundGT K hK) hd

/-! ## 6.  The statement lock

The verbatim `d9f601e5` sentence (token for token the one in `QMCLeafB.FinishLine`), and the leaf as
a function of the §5 contract: the coordinator's repackaging step is the last line. -/

/-- **`QuantumMaxCutEnergy.agm_classical_sdp_lower_value_tm2`** (theorem id
`d9f601e5-8c68-4369-a27d-701e73e686b8`), written out verbatim. -/
theorem statement_lock_of_solutionStatement
    (h : QMCLeafB.FinishLine.SolutionStatement) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue
          (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  h

/-- The reverse direction, so the lock is an equivalence of statements. -/
theorem solutionStatement_of_lock
    (h : ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue
          (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000) :
    QMCLeafB.FinishLine.SolutionStatement :=
  h

/-- **The leaf, in the exact `d9f601e5` type**, from the phase-16 residuals. -/
theorem solution_of_phase16
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → RSt)
    (hinit : Automatic.Poly init)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (hfuel : Automatic.Poly fuel)
    (K : QuantumMaxCutEnergy.Input → ℕ)
    (hinitTape : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = K p.1.1)
    (M : RSt → ℕ) (C₀ c k : ℕ) (hk : 1 ≤ k)
    (hled : LedgerGT M c)
    (hcap : ∀ s, M s ≤ C₀ * ((enc s).length + 1) ^ k)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init roundGT QMCLeafB.RoundProgram.verdict
        (fun G' _ => K G') G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.VerdictSound.RunData
        (QMCLeafB.FinalStroke.loopBit init roundGT QMCLeafB.RoundProgram.verdict
          (fun G' _ => K G')) G t) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue
          (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  statement_lock_of_solutionStatement
    (endgame_of_phase16 init hinit fuel hfuel K hinitTape hfuelLen M C₀ c k hk hled hcap htop hd)


/-! ## 5b.  The assembly at an arbitrary round, and at `roundT`

The `hd`/ledger bricks may settle on either the guarded round (`roundGT`), the unguarded slack round
(`roundT`) or a variant; the assembly below is the same theorem for *any* round, so the coordinator
drops in whichever the bricks deliver. -/

/-- **The leaf from a one-step ledger at an arbitrary round.** -/
theorem endgame_general
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → RSt)
    (hinit : Automatic.Poly init)
    (round : RSt → RSt) (hround : Automatic.Poly round)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (hfuel : Automatic.Poly fuel)
    (K : QuantumMaxCutEnergy.Input → ℕ)
    (hinitTape : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = K p.1.1)
    (M : RSt → ℕ) (C₀ c k : ℕ) (hk : 1 ≤ k)
    (hMinv : ∀ s, M (round s) ≤ M s + c)
    (hstep : ∀ s, (enc (round s)).length ≤ max ((enc s).length + c) (M s))
    (hcap : ∀ s, M s ≤ C₀ * ((enc s).length + 1) ^ k)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init round QMCLeafB.RoundProgram.verdict
        (fun G' _ => K G') G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.VerdictSound.RunData
        (QMCLeafB.FinalStroke.loopBit init round QMCLeafB.RoundProgram.verdict
          (fun G' _ => K G')) G t) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.IntegrateM6.solution_of_bricks init fuel round QMCLeafB.RoundProgram.verdict
    hinit hfuel hround QMCLeafB.RoundProgram.poly_verdict
    M C₀ c k hk hMinv hstep hcap K hinitTape hfuelLen htop hd

/-- **`htop` at the unguarded slack round.** -/
theorem htop_roundT_at (K : QuantumMaxCutEnergy.Input → ℕ) (hK : ∀ G, 1 ≤ K G)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hlo : -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ)) (hhi : t ≤ 0) :
    QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundT.roundT
      QMCLeafB.RoundProgram.verdict (fun G' _ => K G') G t = true := by
  unfold QMCLeafB.FinalStroke.loopBit
  refine QMCLeafB.RoundT.htop_roundT G t (hK G) ?_
  have h1 : QMCLeafB.RoundT.epsOf
      (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))
      = QMCLeafB.EngineRuntime.Rq G / 40000 := epsOf_init0 _
  have hloR : -((QMCLeafB.EngineRuntime.Rq G : ℝ) / 40000) ≤ (t : ℝ) := by
    have h := hlo
    push_cast at h
    linarith
  have h2 : (0 : ℚ) ≤ t + QMCLeafB.EngineRuntime.Rq G / 40000 := by
    have hcast : ((t + QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ)
        = (t : ℝ) + (QMCLeafB.EngineRuntime.Rq G : ℝ) / 40000 := by
      push_cast
      ring
    have hpos : (0 : ℝ) ≤ ((t + QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ) := by
      rw [hcast]
      linarith
    exact_mod_cast hpos
  rw [h1]
  exact h2

/-! ## 7.  Supply audit — the routing's named supplies, type-locked

Every entry below is a routing supply stated to exist on the shelf.  An `example` with the expected
type fails to compile if a supply disappears or its statement drifts, so this section is the
machine-checked half of the conformance report (the empty slots of the leaf are named in
`results/…` and on the board, not here). -/

#check @QMCLeafB.BrickRQ.Rq_poly
example : Automatic.Poly QMCLeafB.RStInit.init0 := QMCLeafB.RStInit.poly_init0
example (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    (stX (QMCLeafB.RStInit.init0 p)).length
      = stN (QMCLeafB.RStInit.init0 p) * stN (QMCLeafB.RStInit.init0 p) :=
  QMCLeafB.RStInit.init_normalised p
example : Automatic.Poly QMCLeafB.RoundProgram.round := QMCLeafB.RoundProgram.poly_round
example : Automatic.Poly QMCLeafB.RoundProgram.verdict := QMCLeafB.RoundProgram.poly_verdict
example : Automatic.Poly QMCLeafB.GuardedRound.roundG := QMCLeafB.GuardedRound.poly_roundG
example : Automatic.Poly QMCLeafB.RoundT.roundT := QMCLeafB.RoundT.poly_roundT
example : Automatic.Poly roundGT := poly_roundGT
example (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.RoundProgram.fvR
      (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)) = 0 :=
  QMCLeafB.HtopInit.fvR_init0 G t
#check @QMCLeafB.CentreTrack.hdrift_of_dyadic
#check @QMCLeafB.RunPartsShallow.runParts_shallow_bracket
#check @QMCLeafB.RunPartsDilate.runParts_of_dilated
#check @QMCLeafB.HalvePerG.budgetRounds_le_monomial
#check @QMCLeafB.HalvePerG.hhalve_perG
#check @QMCLeafB.FuelWire.fuelOf_length
#check @QMCLeafB.FuelWire.poly_fuelOf
#check @QMCLeafB.VerdictSound.solution_of_loop_via_runData
#check @QMCLeafB.LoopRestate.solution_of_loop_bounded
#check @QMCLeafB.IntegrateM6.orbit_envelope
#check @QMCLeafB.CapGuard.LedgerG
#check @QMCLeafB.SimLoop.anyOk
#check @QMCLeafB.VerdictSound.RunData
#check @QMCLeafB.FinalStroke.RunParams
#check @QMCLeafB.FinalStroke.RunParts
#check @QMCLeafB.ClosingBracket.runData_hbudget_close
#check @QMCLeafB.SimLoop.simulate_refuted_sound
#check @QMCLeafB.SizesProfile.poly_runPivN
#check @QMCLeafB.LedgerSnap.state_encode_length
#check @QMCLeafB.SimPoly.solution_of_loop
#check @QMCLeafB.FinishLine.solution_of_bracket_program
#check @QMCLeafB.FinishLine.SoundεOnBracket


/-! ## 8.  Conformance of m5's shallow stroke with the bricks

`UnionShallow.solution_union_shallow` (brick 5) is the campaign's stroke: `SolutionStatement` at
`paramsShallowK` with `htop` only at `2 ≤ G.n` and `RunParts` at the shallow family.  §5/§5b above
were written against `IntegrateM6.solution_of_bricks`, so this section *checks that the bricks meet
brick 5's slots*: the round is `roundGT`, the verdict is the program's, and everything except
`LedgerGT`+cap, brick 1's count side condition and brick 4's run bundle is discharged here. -/

/-- The campaign's round count is at least one (the fuel's `T0 ≥ 1` for `htop`). -/
theorem one_le_KbcShallow_mul (G : QuantumMaxCutEnergy.Input) :
    1 ≤ QMCLeafB.UnionShallow.KbcShallow G * QMCLeafB.HalvePerG.mHalve (G.n * G.n) := by
  have h1 : QMCLeafB.UnionShallow.KbcShallow G
      = QMCLeafB.HalvePerG.mHalve (G.n * G.n)
        * ((G.n + 1) ^ 2 * ((QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 1)
            + (G.n + 9))) := rfl
  have hm : 0 < QMCLeafB.HalvePerG.mHalve (G.n * G.n) := QMCLeafB.HalvePerG.one_le_mHalve _
  have hp : 0 < (G.n + 1) ^ 2 := pow_pos (Nat.succ_pos G.n) 2
  have hq : 0 < (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 1) + (G.n + 9) := by
    have h : 0 < QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 1 := Nat.succ_pos _
    omega
  have hK : 0 < QMCLeafB.UnionShallow.KbcShallow G := by
    rw [h1]
    exact Nat.mul_pos hm (Nat.mul_pos hp hq)
  have : 0 < QMCLeafB.UnionShallow.KbcShallow G * QMCLeafB.HalvePerG.mHalve (G.n * G.n) :=
    Nat.mul_pos hK hm
  omega

/-- **The leaf at brick 5's campaign family, run at the guarded slack round.**

Open slots: `hKdqs` (brick 1's count side condition), `LedgerGT` + cap (brick 2), and one `RunParts`
per interior `(G,t)` at `paramsShallowK` (brick 4).  Everything else — init program, tape-freeness,
round program, verdict program, the orbit envelope, and `htop` — is discharged. -/
theorem endgame_shallow_at_roundGT
    (k : ℕ) (hk : 20 ≤ 2 ^ k) (hKdqs : QMCLeafB.UnionShallow.ShallowKbound)
    (M : RSt → ℕ) (C₀ c kr : ℕ) (hkr : 1 ≤ kr)
    (hled : LedgerGT M c)
    (hcap : ∀ s, M s ≤ C₀ * ((enc s).length + 1) ^ kr)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 roundGT
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.UnionShallow.KbcShallow G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsShallowK hKdqs G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.UnionShallow.solution_union_shallow k hk hKdqs
    QMCLeafB.RStInit.init0 roundGT QMCLeafB.RoundProgram.verdict
    QMCLeafB.RStInit.poly_init0 poly_roundGT QMCLeafB.RoundProgram.poly_verdict
    M C₀ c kr hkr
    (ledgerGT_of_ledgerGT hled).1 (ledgerGT_of_ledgerGT hled).2 hcap
    QMCLeafB.RStInit.init0_tape
    (fun G t _ hlo hhi => htop_roundGT
      (fun G' => QMCLeafB.UnionShallow.KbcShallow G'
        * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) one_le_KbcShallow_mul G t hlo hhi)
    hd



/-! ## 9.  Brick 2 discharged: the ledger at m3's `MszG`

m3's `Check_ledgerG_m3` proves `CapGuard.LedgerG MszG 6` together with the *branch* facts
`MszG_roundOk` / `enc_roundOk` (unconditional) and `MszG_round_cut_le_G` / `enc_round_cut_le_G`
(at normalised states).  Those are exactly §3's three pieces, so the branch-wise ledger is immediate. -/

/-- **The branch-wise ledger at `MszG`, `c = 6`.** -/
theorem ledgerGT_MszG : LedgerGT QMCLeafB.CapGuard.MszG 6 := by
  refine ⟨?_, ?_, ?_, ?_, 11448595, 6, QMCLeafB.CapGuard.MszG_le_pow⟩
  · intro s
    rw [QMCLeafB.CapGuard.MszG_roundOk]
  · intro s
    rw [QMCLeafB.CapGuard.enc_roundOk]
    exact le_max_left _ _
  · intro s hn
    cases hc : (oracleR s).1 with
    | false =>
        rw [QMCLeafB.CapGuard.round_of_not_cut s hc, QMCLeafB.CapGuard.MszG_roundOk]
    | true =>
        exact QMCLeafB.CapGuard.MszG_round_cut_le_G s hn hc
  · intro s hn
    cases hc : (oracleR s).1 with
    | false =>
        rw [QMCLeafB.CapGuard.round_of_not_cut s hc, QMCLeafB.CapGuard.enc_roundOk]
        exact le_max_left _ _
    | true =>
        exact le_trans (QMCLeafB.CapGuard.enc_round_cut_le_G s hn hc) (le_max_right _ _)

/-- **THE LEAF, from two hypotheses.**  `SolutionStatement` at brick 5's campaign family
(`paramsShallowK`, `dq = dqShallow`), the run being the guarded slack round `roundGT` from m1's
`init0`, with `MszG`-ledger and `htop` discharged here.  What is left is exactly:

* `hKdqs` — brick 1's round-count side condition at `dqShallow`;
* `hd` — brick 4's `RunParts` bundle on the strict interior bracket. -/
theorem endgame_leaf_of_hKdqs_hd
    (k : ℕ) (hk : 20 ≤ 2 ^ k) (hKdqs : QMCLeafB.UnionShallow.ShallowKbound)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 roundGT
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.UnionShallow.KbcShallow G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsShallowK hKdqs G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  endgame_shallow_at_roundGT k hk hKdqs QMCLeafB.CapGuard.MszG 11448595 6 6 (by norm_num)
    ledgerGT_MszG QMCLeafB.CapGuard.MszG_le_pow hd

/-- The same, in the exact `d9f601e5` type. -/
theorem solution_of_hKdqs_hd
    (k : ℕ) (hk : 20 ≤ 2 ^ k) (hKdqs : QMCLeafB.UnionShallow.ShallowKbound)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 roundGT
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.UnionShallow.KbcShallow G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsShallowK hKdqs G)) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue
          (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  statement_lock_of_solutionStatement (endgame_leaf_of_hKdqs_hd k hk hKdqs hd)


/-! ## 10.  Degenerating the init: the assembly at brick 1's `dqShallow` init0

Brick 1 re-packs `init0` at `mu = 2n² + 2·dqShallow²`, so its state function is a *different* term
from `RStInit.init0`.  Everything in §9 used `RStInit.init0` only through four facts — `Poly`,
tape-freeness, `fvR = 0`, `stT = t`, `epsOf = Rq/40000`, and normalisation — so they are the exact
interface brick 1 has to meet, and the two-hypothesis leaf is available at its `init0` too. -/

/-- **`htop` at the guarded slack round, for any init with the four scalar facts.** -/
theorem htop_roundGT_init
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → RSt)
    (hnorm : ∀ p, (stX (init p)).length = stN (init p) * stN (init p))
    (hfv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      fvR (init (QMCLeafB.FinalStroke.noTape G t)) = 0)
    (hT : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      stT (init (QMCLeafB.FinalStroke.noTape G t)) = t)
    (heps : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.RoundT.epsOf (init (QMCLeafB.FinalStroke.noTape G t))
        = QMCLeafB.EngineRuntime.Rq G / 40000)
    (K : QuantumMaxCutEnergy.Input → ℕ) (hK : ∀ G, 1 ≤ K G)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hlo : -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ)) (hhi : t ≤ 0) :
    QMCLeafB.FinalStroke.loopBit init roundGT QMCLeafB.RoundProgram.verdict
      (fun G' _ => K G') G t = true := by
  unfold QMCLeafB.FinalStroke.loopBit
  rw [roundGT_iterate_eq_roundT hnorm]
  set s := init (QMCLeafB.FinalStroke.noTape G t) with hs
  have hloR : -((QMCLeafB.EngineRuntime.Rq G : ℝ) / 40000) ≤ (t : ℝ) := by
    have h := hlo
    push_cast at h
    linarith
  have hslack : (0 : ℚ) ≤ t + QMCLeafB.EngineRuntime.Rq G / 40000 := by
    have hcast : ((t + QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ)
        = (t : ℝ) + (QMCLeafB.EngineRuntime.Rq G : ℝ) / 40000 := by
      push_cast
      ring
    have hpos : (0 : ℝ) ≤ ((t + QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ) := by
      rw [hcast]
      linarith
    exact_mod_cast hpos
  have hbranch : fvR s ≤ stT s + QMCLeafB.RoundT.epsOf s := by
    rw [hfv G t, hT G t, heps G t]
    linarith
  have hok : stOks (QMCLeafB.RoundT.roundT s) = stOks s ++ [true] := by
    rw [QMCLeafB.RoundT.roundT, if_pos hbranch]
    rfl
  have hmem : true ∈ stOks (QMCLeafB.RoundT.roundT^[1] s) := by
    rw [Function.iterate_one, hok]
    exact List.mem_append_right _ (List.mem_singleton_self true)
  have hpre' : true ∈ stOks (QMCLeafB.RoundT.roundT^[K G] s) :=
    (QMCLeafB.RoundT.stOks_prefix_iterateT s (hK G)).mem hmem
  exact QMCLeafB.Htop.verdict_of_mem hpre'

/-- **THE LEAF at an arbitrary `dqShallow` init0.**  `SolutionStatement` from brick 1's count side
condition and brick 1's four init facts, plus brick 4's run bundle. -/
theorem endgame_leaf_at_init
    (k : ℕ) (hk : 20 ≤ 2 ^ k) (hKdqs : QMCLeafB.UnionShallow.ShallowKbound)
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → RSt)
    (hinit : Automatic.Poly init)
    (hinitTape : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (hnorm : ∀ p, (stX (init p)).length = stN (init p) * stN (init p))
    (hfv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      fvR (init (QMCLeafB.FinalStroke.noTape G t)) = 0)
    (hT : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      stT (init (QMCLeafB.FinalStroke.noTape G t)) = t)
    (heps : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.RoundT.epsOf (init (QMCLeafB.FinalStroke.noTape G t))
        = QMCLeafB.EngineRuntime.Rq G / 40000)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init roundGT QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.UnionShallow.KbcShallow G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsShallowK hKdqs G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.UnionShallow.solution_union_shallow k hk hKdqs
    init roundGT QMCLeafB.RoundProgram.verdict
    hinit poly_roundGT QMCLeafB.RoundProgram.poly_verdict
    QMCLeafB.CapGuard.MszG 11448595 6 6 (by norm_num)
    (ledgerGT_of_ledgerGT ledgerGT_MszG).1 (ledgerGT_of_ledgerGT ledgerGT_MszG).2
    QMCLeafB.CapGuard.MszG_le_pow hinitTape
    (fun G t _ hlo hhi => htop_roundGT_init init hnorm hfv hT heps
      (fun G' => QMCLeafB.UnionShallow.KbcShallow G'
        * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) one_le_KbcShallow_mul G t hlo hhi)
    hd


/-! ## 11.  The flag stream: what brick 4 reads off `roundGT`

`RunParts` needs three things from the program: the `ok` stream (its flags), `hverdict`
(`o G t = anyOk ok (K·m)`), and at every `ok = false` round a genuine cut.  The flag is
`okGT`; the two lemmas below spell out exactly what `true` and `false` give, and the third is
`hverdict` itself. -/

/-- **A `false` flag is the oracle's cut.** -/
theorem okGT_eq_false {s : RSt} (h : okGT s = false) : (oracleR s).1 = true := by
  by_cases hg : (stX s).length = stN s * stN s
  · rw [okGT, if_pos hg] at h
    by_cases hs : fvR s ≤ stT s + QMCLeafB.RoundT.epsOf s
    · rw [if_pos hs] at h
      exact absurd h (by simp)
    · rw [if_neg hs] at h
      simpa using h
  · rw [okGT, if_neg hg] at h
    exact absurd h (by simp)

/-- **What a `true` flag at a normalised state gives**: either the state's own point is feasible at
the campaign's slack (`fvR ≤ t + εw`, the self-certifying branch), or the oracle itself said `ok`
(and the certificate comes from its answer, m5's `hcert_of_relaxMem` route). -/
theorem okGT_eq_true {s : RSt} (hn : (stX s).length = stN s * stN s) (h : okGT s = true) :
    fvR s ≤ stT s + QMCLeafB.RoundT.epsOf s ∨ (oracleR s).1 = false := by
  by_cases hs : fvR s ≤ stT s + QMCLeafB.RoundT.epsOf s
  · exact Or.inl hs
  · refine Or.inr ?_
    rw [okGT, if_pos hn, if_neg hs] at h
    simpa using h

/-- **`hverdict` for the guarded slack loop**: at `K G = P.K * P.m` rounds the loop's bit is the
run's `anyOk` of the flag stream.  (Brick 4's `RunParts.hverdict` with `o := loopBit …` and
`ok := fun k => okGT (roundGT^[k] (init0 (noTape G t)))`.) -/
theorem hverdict_GT (K : QuantumMaxCutEnergy.Input → ℕ)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (T : ℕ) (hT : K G = T) :
    QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 roundGT
        QMCLeafB.RoundProgram.verdict (fun G' _ => K G') G t
      = QMCLeafB.SimLoop.anyOk
          (fun k => okGT (roundGT^[k] (QMCLeafB.RStInit.init0
            (QMCLeafB.FinalStroke.noTape G t)))) T := by
  subst hT
  exact verdict_iterate_eq_anyOk_GT _ (QMCLeafB.RStInit.stOks_init0 _) (K G)


/-! ## 12.  The last hole: brick 4

m2's `Check_loopclose_m2` discharges the whole count side of the campaign family at the factor
`Kbc4 m G = 4·Kbc m G`: `budgetRounds_le_Kbc4_dqShallow` (`hK`, unconditional),
`poly_Kbc4_mHalve_mul` (`hKf`), `Kbc4_mHalve_le_seed` (`hseed`, at `21 ≤ 2^k`).  So at that family
the leaf's remaining hypothesis is exactly brick 4's run bundle. -/

/-- The campaign's round factor, as a function of the input. -/
noncomputable def Kf4 (G : QuantumMaxCutEnergy.Input) : ℕ :=
  QMCLeafB.LoopClose.Kbc4 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G

/-- The count side of `RunParams` at `Kf4`, discharged. -/
theorem budgetRounds_le_Kf4 (G : QuantumMaxCutEnergy.Input) :
    QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G)
      (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) ≤ Kf4 G :=
  QMCLeafB.LoopClose.budgetRounds_le_Kbc4_dqShallow G (QMCLeafB.HalvePerG.mHalve (G.n * G.n))

/-- `Kf4 · m ≥ 1` — the `1 ≤ K G` that `htop` needs. -/
theorem one_le_Kf4_mul (G : QuantumMaxCutEnergy.Input) :
    1 ≤ Kf4 G * QMCLeafB.HalvePerG.mHalve (G.n * G.n) := by
  have hK : Kf4 G = 4 * (QMCLeafB.HalvePerG.mHalve (G.n * G.n)
      * ((G.n + 1) ^ 2 * ((QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 1)
          + (G.n + 9)))) := rfl
  have hm : 0 < QMCLeafB.HalvePerG.mHalve (G.n * G.n) := QMCLeafB.HalvePerG.one_le_mHalve _
  have hp : 0 < (G.n + 1) ^ 2 := pow_pos (Nat.succ_pos G.n) 2
  have hq : 0 < (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 1) + (G.n + 9) := by
    have h : 0 < QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 1 := Nat.succ_pos _
    omega
  have hpos : 0 < Kf4 G := by
    rw [hK]
    exact Nat.mul_pos (by norm_num) (Nat.mul_pos hm (Nat.mul_pos hp hq))
  have : 0 < Kf4 G * QMCLeafB.HalvePerG.mHalve (G.n * G.n) := Nat.mul_pos hpos hm
  omega

/-- **THE LEAF FROM BRICK 4 ALONE.**  At m1's `RStInit.init0`, the campaign family
`paramsShallowKf Kf4 budgetRounds_le_Kf4` (`dq = dqShallow`, `m = mHalve (n·n)`, `K = 4·Kbc`), the
guarded slack round `roundGT` and the program's verdict, the only thing left is the interior run
bundle. -/
theorem endgame_leaf_of_hd
    (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 roundGT
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => Kf4 G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsShallowKf Kf4 budgetRounds_le_Kf4 G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.UnionShallow.solution_union_shallow_gen Kf4 k
    (QMCLeafB.LoopClose.poly_Kbc4_mHalve_mul)
    (fun p => QMCLeafB.LoopClose.Kbc4_mHalve_le_seed k hk p)
    budgetRounds_le_Kf4
    QMCLeafB.RStInit.init0 roundGT QMCLeafB.RoundProgram.verdict
    QMCLeafB.RStInit.poly_init0 poly_roundGT QMCLeafB.RoundProgram.poly_verdict
    QMCLeafB.CapGuard.MszG 11448595 6 6 (by norm_num)
    (ledgerGT_of_ledgerGT ledgerGT_MszG).1 (ledgerGT_of_ledgerGT ledgerGT_MszG).2
    QMCLeafB.CapGuard.MszG_le_pow QMCLeafB.RStInit.init0_tape
    (fun G t _ hlo hhi => htop_roundGT
      (fun G' => Kf4 G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) one_le_Kf4_mul G t hlo hhi)
    hd

/-- The same, in the exact `d9f601e5` type. -/
theorem solution_of_hd
    (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 roundGT
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => Kf4 G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsShallowKf Kf4 budgetRounds_le_Kf4 G)) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue
          (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  statement_lock_of_solutionStatement (endgame_leaf_of_hd k hk hd)


/-! ## 13.  The other verdict slot: `verdictT`, which is compatible with brick 4

`RunPartsStream.runParts_of_stream_data` asks (`hmem`) the oracle's answer at every `ok` round to be
`RelaxMem` at level `t - ε` with tolerance `P.dq`.  The `roundT` flag cannot supply that: `roundT`
reports `ok` as soon as `fvR s ≤ stT s + εw`, while `RelaxMem` at the centre needs (roughly)
`fvR ≤ t - ε + dq`, and `dq ≪ ε` leaves the whole window `(t - ε + dq, t + ε]` in which the flag is
`true` and the oracle's answer is a **cut**.

`RoundProgram.round`'s flag has the opposite property: it is exactly the oracle's own verdict
(`!cut`), so `hmem`/`hcert` are read off the answer (`RunInduction.okReport_of_runPiv`).  What that
round cannot do is `htop` — at `init0` the oracle reports a cut on the whole top slice.  The fix is
to put the top-slice test in the **verdict** instead of in the round (m1's `verdictT` recipe): the
loop's bit is `verdictT s = verdict s ∨ (0 ≤ stT s + εw(s))`, and

* on the top slice the second disjunct is `true` at *every* state of the run (`stA` and `stT` are
  round invariants), so `htop` holds with no count hypothesis at all;
* on the strict interior, where `hd` is the only thing asked, the second disjunct is `false`, so
  `verdictT` *is* the `anyOk` of the oracle's flag stream — which is exactly `RunParts.hverdict`.

This section builds that slot, so brick 4 can run at `round`/`roundG` with the oracle's own stream. -/

/-- **The verdict with the top-slice test built in.** -/
noncomputable def verdictT (s : RSt) : Bool :=
  QMCLeafB.RoundProgram.verdict s || decide (0 ≤ stT s + QMCLeafB.RoundT.epsOf s)

theorem verdictT_eq_ite (s : RSt) :
    verdictT s = if QMCLeafB.RoundProgram.verdict s then true
      else decide (0 ≤ stT s + QMCLeafB.RoundT.epsOf s) := by
  unfold verdictT
  cases QMCLeafB.RoundProgram.verdict s <;> rfl

theorem verdictT_eq_true_iff (s : RSt) :
    verdictT s = true ↔
      QMCLeafB.RoundProgram.verdict s = true ∨ 0 ≤ stT s + QMCLeafB.RoundT.epsOf s := by
  unfold verdictT
  rw [Bool.or_eq_true, decide_eq_true_iff]

theorem verdictT_eq_false_iff (s : RSt) :
    verdictT s = false ↔
      QMCLeafB.RoundProgram.verdict s = false ∧ ¬ (0 ≤ stT s + QMCLeafB.RoundT.epsOf s) := by
  unfold verdictT
  rw [Bool.or_eq_false_iff, decide_eq_false_iff_not]

/-- **`verdictT` is a program.** -/
theorem poly_verdictT : Automatic.Poly verdictT := by
  have hsum : Automatic.Poly (fun s : RSt => stT s + QMCLeafB.RoundT.epsOf s) := by
    have h1 : Automatic.Poly (fun s : RSt => (stT s, QMCLeafB.RoundT.epsOf s)) :=
      Automatic.Poly.pair (f := fun s : RSt => stT s)
        (g := fun s : RSt => QMCLeafB.RoundT.epsOf s) poly_stT QMCLeafB.RoundT.poly_epsOf
    exact Automatic.Poly.comp (f := fun q : ℚ × ℚ => q.1 + q.2)
      (g := fun s : RSt => (stT s, QMCLeafB.RoundT.epsOf s)) Automatic.Poly.rat_add h1
  have hc : Automatic.Poly (fun s : RSt => decide (0 ≤ stT s + QMCLeafB.RoundT.epsOf s)) :=
    Automatic.Poly.rat_le_comp (Automatic.Poly.const 0) hsum
  have hp : Automatic.Poly (fun s : RSt => decide (QMCLeafB.RoundProgram.verdict s = true)) :=
    QMCLeafB.FinishLine.poly_of_pointwise QMCLeafB.RoundProgram.poly_verdict
      (fun s => by by_cases h : QMCLeafB.RoundProgram.verdict s <;> simp [h])
  have hif : Automatic.Poly (fun s : RSt =>
      if QMCLeafB.RoundProgram.verdict s = true then true
      else decide (0 ≤ stT s + QMCLeafB.RoundT.epsOf s)) :=
    Automatic.Poly.ite_prop (p := fun s : RSt => QMCLeafB.RoundProgram.verdict s = true)
      hp (Automatic.Poly.const true) hc
  exact QMCLeafB.FinishLine.poly_of_pointwise hif (fun s => (verdictT_eq_ite s).symm)

theorem stT_roundG' (s : RSt) : stT (QMCLeafB.GuardedRound.roundG s) = stT s := by
  by_cases h : (stX s).length = stN s * stN s
  · rw [QMCLeafB.GuardedRound.roundG_of_normalised s h]
    exact QMCLeafB.RStInit.stT_round s
  · rw [QMCLeafB.GuardedRound.roundG_of_abnormal s h]
    rfl

theorem stA_roundG' (s : RSt) : stA (QMCLeafB.GuardedRound.roundG s) = stA s := by
  by_cases h : (stX s).length = stN s * stN s
  · rw [QMCLeafB.GuardedRound.roundG_of_normalised s h]
    exact QMCLeafB.RStInit.stA_round s
  · rw [QMCLeafB.GuardedRound.roundG_of_abnormal s h]
    rfl

theorem stT_iterate_roundG (s : RSt) (j : ℕ) :
    stT (QMCLeafB.GuardedRound.roundG^[j] s) = stT s := by
  induction j with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', stT_roundG', ih]

theorem stA_iterate_roundG (s : RSt) (j : ℕ) :
    stA (QMCLeafB.GuardedRound.roundG^[j] s) = stA s := by
  induction j with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', stA_roundG', ih]

theorem epsOf_iterate_roundG (s : RSt) (j : ℕ) :
    QMCLeafB.RoundT.epsOf (QMCLeafB.GuardedRound.roundG^[j] s) = QMCLeafB.RoundT.epsOf s := by
  unfold QMCLeafB.RoundT.epsOf QMCLeafB.RoundT.massV
  rw [stA_iterate_roundG]

/-- **`htop` at `roundG` with `verdictT`** — the top-slice test is a round invariant, so this holds
for *every* round count (no `1 ≤ K G` needed). -/
theorem htop_verdictT (K : QuantumMaxCutEnergy.Input → ℕ)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hlo : -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ)) (hhi : t ≤ 0) :
    QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.GuardedRound.roundG
      verdictT (fun G' _ => K G') G t = true := by
  unfold QMCLeafB.FinalStroke.loopBit
  change verdictT (QMCLeafB.GuardedRound.roundG^[K G]
    (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))) = true
  refine (verdictT_eq_true_iff _).mpr (Or.inr ?_)
  rw [stT_iterate_roundG, epsOf_iterate_roundG]
  have hst : stT (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)) = t := rfl
  have heps : QMCLeafB.RoundT.epsOf
      (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))
      = QMCLeafB.EngineRuntime.Rq G / 40000 := epsOf_init0 _
  rw [hst, heps]
  have hloR : -((QMCLeafB.EngineRuntime.Rq G : ℝ) / 40000) ≤ (t : ℝ) := by
    have h := hlo
    push_cast at h
    linarith
  have hcast : ((t + QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ)
      = (t : ℝ) + (QMCLeafB.EngineRuntime.Rq G : ℝ) / 40000 := by
    push_cast
    ring
  have hpos : (0 : ℝ) ≤ ((t + QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ) := by
    rw [hcast]
    linarith
  exact_mod_cast hpos

/-- **`hverdict` on the strict interior**: there the top-slice disjunct is `false`, so `verdictT` is
exactly the `anyOk` of the oracle's flag stream — `RunParts.hverdict` at `roundG`. -/
theorem hverdict_verdictT_interior (K : QuantumMaxCutEnergy.Input → ℕ)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (T : ℕ) (hT : K G = T)
    (hneg : t + QMCLeafB.EngineRuntime.Rq G / 40000 < 0) :
    QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.GuardedRound.roundG
        verdictT (fun G' _ => K G') G t
      = QMCLeafB.SimLoop.anyOk
          (fun k => QMCLeafB.GuardedRound.okG
            (QMCLeafB.GuardedRound.roundG^[k] (QMCLeafB.RStInit.init0
              (QMCLeafB.FinalStroke.noTape G t)))) T := by
  subst hT
  unfold QMCLeafB.FinalStroke.loopBit
  change verdictT (QMCLeafB.GuardedRound.roundG^[K G]
    (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)))
    = QMCLeafB.SimLoop.anyOk (fun k => QMCLeafB.GuardedRound.okG
        (QMCLeafB.GuardedRound.roundG^[k] (QMCLeafB.RStInit.init0
          (QMCLeafB.FinalStroke.noTape G t)))) (K G)
  have hoff : ¬ (0 ≤ stT (QMCLeafB.GuardedRound.roundG^[K G]
      (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)))
      + QMCLeafB.RoundT.epsOf (QMCLeafB.GuardedRound.roundG^[K G]
        (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)))) := by
    rw [stT_iterate_roundG, epsOf_iterate_roundG]
    have hst : stT (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)) = t := rfl
    have heps : QMCLeafB.RoundT.epsOf
        (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))
        = QMCLeafB.EngineRuntime.Rq G / 40000 := epsOf_init0 _
    rw [hst, heps]
    exact not_le.mpr hneg
  have hsplit := (verdictT_eq_false_iff (QMCLeafB.GuardedRound.roundG^[K G]
    (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))))
  have hval : verdictT (QMCLeafB.GuardedRound.roundG^[K G]
      (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)))
      = QMCLeafB.RoundProgram.verdict (QMCLeafB.GuardedRound.roundG^[K G]
        (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))) := by
    unfold verdictT
    rw [decide_eq_false hoff, Bool.or_false]
  rw [hval]
  exact QMCLeafB.GuardedRound.verdict_iterate_eq_anyOk_G _ (QMCLeafB.RStInit.stOks_init0 _) (K G)

/-- **THE LEAF with the verdict slot that brick 4 can certify.**  `(init0, roundG, verdictT)` at the
campaign family: the only hypothesis is the interior run bundle with the *oracle's own* flag stream. -/
theorem endgame_verdictT_of_hd
    (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.GuardedRound.roundG
          verdictT (fun G' _ => Kf4 G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsShallowKf Kf4 budgetRounds_le_Kf4 G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.UnionShallow.solution_union_shallow_gen Kf4 k
    (QMCLeafB.LoopClose.poly_Kbc4_mHalve_mul)
    (fun p => QMCLeafB.LoopClose.Kbc4_mHalve_le_seed k hk p)
    budgetRounds_le_Kf4
    QMCLeafB.RStInit.init0 QMCLeafB.GuardedRound.roundG verdictT
    QMCLeafB.RStInit.poly_init0 QMCLeafB.GuardedRound.poly_roundG poly_verdictT
    QMCLeafB.CapGuard.MszG 11448595 6 6 (by norm_num)
    QMCLeafB.CapGuard.ledgerG_MszG.1 QMCLeafB.CapGuard.ledgerG_MszG.2.1
    QMCLeafB.CapGuard.MszG_le_pow QMCLeafB.RStInit.init0_tape
    (fun G t _ hlo hhi => htop_verdictT
      (fun G' => Kf4 G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G t hlo hhi)
    hd

/-- The same, typed verbatim as `d9f601e5`. -/
theorem solution_verdictT_of_hd
    (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.GuardedRound.roundG
          verdictT (fun G' _ => Kf4 G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsShallowKf Kf4 budgetRounds_le_Kf4 G)) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue
          (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  statement_lock_of_solutionStatement (endgame_verdictT_of_hd k hk hd)


/-! ## 14.  The `epsOf` slot at brick 1's own `init0`

m5's final glue (`UnionAtGT.endgame_final_at_roundGT`) needs six facts about the init, five of which
`Check_initdq_m1` supplies (`poly_init0`, `init0_tape`, `init_normalised`, `fvR_init0`,
`stT_init0`).  The sixth — `epsOf (init0 p) = Rq G/40000` — is not in any brick: `epsOf` reads the
weight code `stA`, and brick 1's init packs it as `RStInit.wProg` *by definition*, so the flat-code
bridge of §1 applies verbatim. -/

/-- **The ℓ¹ mass at brick 1's `init0` is `Rq G`.** -/
theorem massV_init0_initdq (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    QMCLeafB.RoundT.massV (QMCLeafB.InitDq.init0 p) = QMCLeafB.EngineRuntime.Rq p.1.1 := by
  obtain ⟨⟨G, coins⟩, t⟩ := p
  set es := parseEdges (QuantumMaxCutEnergy.encodeRequest (G, coins)) with hes
  have hA : stA (QMCLeafB.InitDq.init0 ((G, coins), t))
      = MatQ.mk G.n (QMCLeafB.RStInit.wVal es) := by
    show stA (QMCLeafB.InitDq.initCoreD (QuantumMaxCutEnergy.encodeRequest (G, coins))
      (QMCLeafB.InitDq.muOfD ((G, coins), t)) t) = MatQ.mk G.n (QMCLeafB.RStInit.wVal es)
    rw [QMCLeafB.InitDq.initCoreD_stA, QMCLeafB.RStInit.wProg_eq,
      QMCNumericRuntime.inputWidth_request]
  have hpt : ∀ (i j : Fin G.n), QMCLeafB.RoundProgram.absq (QMCLeafB.RStInit.wVal es i j)
      = |QMCLeafB.RStInit.wMatQ G i j| := by
    intro i j
    rw [QMCLeafB.RoundProgram.absq_eq]
    congr 1
    have h1 := (QMCLeafB.RStInit.wProg_correct G coins).2 i j
    rw [QMCLeafB.RStInit.wProg_eq, QMCNumericRuntime.inputWidth_request,
      MatQ.entry_mk _ _ i.isLt j.isLt] at h1
    exact h1
  unfold QMCLeafB.RoundT.massV
  rw [hA, map_mk, mk_sum]
  calc ∑ i : Fin G.n, ∑ j : Fin G.n, QMCLeafB.RoundProgram.absq (QMCLeafB.RStInit.wVal es i j)
      = ∑ i : Fin G.n, ∑ j : Fin G.n, |QMCLeafB.RStInit.wMatQ G i j| :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hpt i j
    _ = QMCLeafB.EngineRuntime.Rq G := QMCLeafB.RStInit.abs_sum_wMatQ G

/-- **The sixth init fact**: brick 1's slack is the leaf's own `εw`. -/
theorem epsOf_init0_initdq (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    QMCLeafB.RoundT.epsOf (QMCLeafB.InitDq.init0 p)
      = QMCLeafB.EngineRuntime.Rq p.1.1 / 40000 := by
  unfold QMCLeafB.RoundT.epsOf
  rw [massV_init0_initdq]
  ring

/-- **THE LEAF AT BRICK 1's `init0`, from brick 4 alone** — m5's `endgame_final_at_roundGT` with
every one of its six init slots discharged here (`InitDq.poly_init0`, `init0_tape`,
`init_normalised`, `fvR_init0`, `stT_init0`, and §14's `epsOf_init0_initdq`), the count at m2's
`4·Kbc` factor, and the ledger from m3. -/
theorem endgame_final_dqShallow_of_hd
    (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 roundGT
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => Kf4 G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsShallowKf Kf4 budgetRounds_le_Kf4 G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.UnionShallow.solution_union_shallow_gen Kf4 k
    (QMCLeafB.LoopClose.poly_Kbc4_mHalve_mul)
    (fun p => QMCLeafB.LoopClose.Kbc4_mHalve_le_seed k hk p)
    budgetRounds_le_Kf4
    QMCLeafB.InitDq.init0 roundGT QMCLeafB.RoundProgram.verdict
    QMCLeafB.InitDq.poly_init0 poly_roundGT QMCLeafB.RoundProgram.poly_verdict
    QMCLeafB.CapGuard.MszG 11448595 6 6 (by norm_num)
    (ledgerGT_of_ledgerGT ledgerGT_MszG).1 (ledgerGT_of_ledgerGT ledgerGT_MszG).2
    QMCLeafB.CapGuard.MszG_le_pow QMCLeafB.InitDq.init0_tape
    (fun G t _ hlo hhi => htop_roundGT_init QMCLeafB.InitDq.init0
      QMCLeafB.InitDq.init_normalised
      (fun G' t' => QMCLeafB.InitDq.fvR_init0 G' t')
      (fun G' t' => QMCLeafB.InitDq.stT_init0 _)
      (fun G' t' => epsOf_init0_initdq _)
      (fun G' => Kf4 G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) one_le_Kf4_mul G t hlo hhi)
    hd

/-- The same at m1's `init0`, typed verbatim as `d9f601e5`. -/
theorem solution_dqShallow_of_hd
    (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 roundGT
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => Kf4 G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsShallowKf Kf4 budgetRounds_le_Kf4 G)) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue
          (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  statement_lock_of_solutionStatement (endgame_final_dqShallow_of_hd k hk hd)


/-- **The leaf at brick 1's `init0`, from brick 4 alone, at ANY count family.**  Same as
`endgame_final_dqShallow_of_hd` with the round factor left to the caller, so whichever monomial
brick 4 builds at (`Kbc2`, `4·Kbc`, …) plugs in here without touching the init facts. -/
theorem endgame_final_gen_dqShallow
    (Kf : QuantumMaxCutEnergy.Input → ℕ) (k : ℕ)
    (hKf : Automatic.Poly (fun p : QMCLeafB.FuelWire.Pkg =>
      Kf p.1.1 * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)))
    (hseed : ∀ p : QMCLeafB.FuelWire.Pkg,
      Kf p.1.1 * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)
        ≤ QMCLeafB.FuelWire.seedLen p ^ (2 ^ k))
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G)
        (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) ≤ Kf G)
    (hpos : ∀ G : QuantumMaxCutEnergy.Input,
      1 ≤ Kf G * QMCLeafB.HalvePerG.mHalve (G.n * G.n))
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 roundGT
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => Kf G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsShallowKf Kf hK G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.UnionShallow.solution_union_shallow_gen Kf k hKf hseed hK
    QMCLeafB.InitDq.init0 roundGT QMCLeafB.RoundProgram.verdict
    QMCLeafB.InitDq.poly_init0 poly_roundGT QMCLeafB.RoundProgram.poly_verdict
    QMCLeafB.CapGuard.MszG 11448595 6 6 (by norm_num)
    (ledgerGT_of_ledgerGT ledgerGT_MszG).1 (ledgerGT_of_ledgerGT ledgerGT_MszG).2
    QMCLeafB.CapGuard.MszG_le_pow QMCLeafB.InitDq.init0_tape
    (fun G t _ hlo hhi => htop_roundGT_init QMCLeafB.InitDq.init0
      QMCLeafB.InitDq.init_normalised
      (fun G' t' => QMCLeafB.InitDq.fvR_init0 G' t')
      (fun G' t' => QMCLeafB.InitDq.stT_init0 _)
      (fun G' t' => epsOf_init0_initdq _)
      (fun G' => Kf G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) hpos G t hlo hhi)
    hd


/-! ## 15.  The final wiring at m7's `roundGU`

m7's `RoundGUEndgame.roundGU` is the round that satisfies *both* requirements at once (slack above
`-εw`, the shelf round below it — a run invariant), and on the interior its run is literally the shelf
round's (`loopBit_GU_eq_round_of_init`).  So `hd` can be brick 4's bundle at
`RoundProgram.round`, which is what `RunPartsStream`/`RunPartsDilate` actually build.

`RoundGUEndgame.solution_roundGU_of_init_hd_round` is that endgame with six init facts and `hd` as
hypotheses.  Below, the six facts are discharged at brick 1's `InitDq.init0` (five from
`Check_initdq_m1`, the sixth from §14), so the leaf is exactly brick 4's bundle at the shelf round. -/

/-- **THE LEAF: one hypothesis, at the shelf round.** -/
theorem endgame_leaf_final
    (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.UnionShallow.Kbc2
            (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.RoundGUEndgame.solution_roundGU_of_init_hd_round QMCLeafB.InitDq.init0 k hk
    QMCLeafB.InitDq.poly_init0
    QMCLeafB.InitDq.init_normalised
    (fun p => by
      rw [QMCLeafB.InitDq.init0_tape p]
      exact QMCLeafB.InitDq.fvR_init0 p.1.1 p.2)
    QMCLeafB.InitDq.stT_init0
    (fun p => epsOf_init0_initdq p)
    QMCLeafB.InitDq.init0_tape
    hd

/-- **`d9f601e5`, verbatim, from one hypothesis.** -/
theorem solution_final
    (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.UnionShallow.Kbc2
            (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G)) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue
          (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  statement_lock_of_solutionStatement (endgame_leaf_final k hk hd)

end QMCLeafB.ConformanceM8

/-! ## Axiom audit -/

#print axioms QMCLeafB.ConformanceM8.map_mk
#print axioms QMCLeafB.ConformanceM8.mk_sum
#print axioms QMCLeafB.ConformanceM8.massV_init0
#print axioms QMCLeafB.ConformanceM8.epsOf_init0
#print axioms QMCLeafB.ConformanceM8.poly_roundGT
#print axioms QMCLeafB.ConformanceM8.roundGT_iterate_eq_roundT
#print axioms QMCLeafB.ConformanceM8.stOks_roundGT
#print axioms QMCLeafB.ConformanceM8.verdict_iterate_eq_anyOk_GT
#print axioms QMCLeafB.ConformanceM8.loopBit_GT_eq_roundT
#print axioms QMCLeafB.ConformanceM8.ledgerG_of_ledgerGT
#print axioms QMCLeafB.ConformanceM8.ledgerGT_of_ledgerGT
#print axioms QMCLeafB.ConformanceM8.htop_roundGT
#print axioms QMCLeafB.ConformanceM8.endgame_of_phase16
#print axioms QMCLeafB.ConformanceM8.endgame_phase16_at_init0
#print axioms QMCLeafB.ConformanceM8.statement_lock_of_solutionStatement
#print axioms QMCLeafB.ConformanceM8.solution_of_phase16
#print axioms QMCLeafB.ConformanceM8.endgame_general
#print axioms QMCLeafB.ConformanceM8.htop_roundT_at
#print axioms QMCLeafB.ConformanceM8.one_le_KbcShallow_mul
#print axioms QMCLeafB.ConformanceM8.endgame_shallow_at_roundGT
#print axioms QMCLeafB.ConformanceM8.ledgerGT_MszG
#print axioms QMCLeafB.ConformanceM8.endgame_leaf_of_hKdqs_hd
#print axioms QMCLeafB.ConformanceM8.solution_of_hKdqs_hd
#print axioms QMCLeafB.ConformanceM8.htop_roundGT_init
#print axioms QMCLeafB.ConformanceM8.endgame_leaf_at_init
#print axioms QMCLeafB.ConformanceM8.okGT_eq_false
#print axioms QMCLeafB.ConformanceM8.okGT_eq_true
#print axioms QMCLeafB.ConformanceM8.hverdict_GT
#print axioms QMCLeafB.ConformanceM8.one_le_Kf4_mul
#print axioms QMCLeafB.ConformanceM8.budgetRounds_le_Kf4
#print axioms QMCLeafB.ConformanceM8.endgame_leaf_of_hd
#print axioms QMCLeafB.ConformanceM8.solution_of_hd
#print axioms QMCLeafB.ConformanceM8.poly_verdictT
#print axioms QMCLeafB.ConformanceM8.htop_verdictT
#print axioms QMCLeafB.ConformanceM8.hverdict_verdictT_interior
#print axioms QMCLeafB.ConformanceM8.endgame_verdictT_of_hd
#print axioms QMCLeafB.ConformanceM8.solution_verdictT_of_hd
#print axioms QMCLeafB.ConformanceM8.massV_init0_initdq
#print axioms QMCLeafB.ConformanceM8.epsOf_init0_initdq
#print axioms QMCLeafB.ConformanceM8.endgame_final_dqShallow_of_hd
#print axioms QMCLeafB.ConformanceM8.solution_dqShallow_of_hd
#print axioms QMCLeafB.ConformanceM8.endgame_final_gen_dqShallow
#print axioms QMCLeafB.ConformanceM8.endgame_leaf_final
#print axioms QMCLeafB.ConformanceM8.solution_final


