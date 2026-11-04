-- Prove2me | Definitions.Def_QMCLeafB_SlackRoute_m2
-- name    : QMCLeafB_SlackRoute_m2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:14:58.934325+00:00
-- url     : https://prove2.me/theorems/4efa2f9c-f484-4aa2-a3f6-1e380c0a53f7
-- title:
--   QMCLeafB SlackRoute_m2
-- statement:
--   # leaf B phase 5 — the slack route's value form (swarm `smvzxba5a`, member `m2`, direction d9)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_answer_producer
import Definitions.Def_QMCLeafB_EngineRuntime_m6
/-
# leaf B phase 5 — the slack route's value form (swarm `smvzxba5a`, member `m2`, direction d9)

`QMCLeafB.EngineRuntime.leafB_of_decider` (the machine-checked closing form of phase 5) is built
on the **exact** per-threshold answer `Answer`, so its decider `o` has to reproduce `answerBit`
at *every* rational threshold — i.e. it has to decide exact SDP feasibility, including at the
boundary `t = v*`, where the campaign's executable engine certifies nothing (`OkReport` gives
`t - d/2 ≤ [A, cX]`, not `[A, cX] ≤ t`; a `.witness` is not a feasible point at `t`).  The campaign
already possesses the way around that: `Check_answer_producer`'s **slack** driver, whose sandwich

    0 ≤ Lq,   Lq ≤ S,   S − Lq ≤ R/32768 + (εw + εr)/4,   and with εw + εr ≤ W/7500:  W/10000

is machine-checked (`leafB_threshold_driver_slack`, `leafB_budget_of_weight`).  On that route the
decider decides nothing mathematically: it *is* the engine's own verdict, so agreement is
definitional and no exactness obligation enters.

What was missing is the *value form* on the slack side — the analogue of
`EngineRuntime.iter_pair_eq_stateOf` / `iterB_bitsOf`: the slack bracket after `k` steps is a
straight-line fold of the `k` engine **bits** and nothing else.  This file supplies it:

* `sbit eng t` — the bit a slack answer carries (`true` on `.witness`);
* `sstate o k p` — the pair-level bisection recursion, with `iterB_bitsF` and `sstate_succ`;
* `step_pair` — a slack step moves `(lo, hi)` by `bstep` of the bit, payload unused;
* `iter_pair_sstate` — **the value form**;
* `iter_pair_bitsF` — the same as the `bitsF`/`iterB` fold the exact route already programs;
* `iter_hi_bval` — **the printed value**: `(R − hi)/4 = bval k R (bitsF (sbit eng) k (−R, 0))`,
  so `EngineRuntime.bval_poly` is the value program on the slack route too;
* `value_of_bits_poly` — **the route's residual obligation, exactly**: one `Poly` program for a
  Boolean threshold verdict plus one for the total weight give the value program;
* `sbit_toSlack` — **consistency**: at zero slack the slack bit *is* `EngineRuntime.answerBit`,
  so this is a strict generalisation of the exact route and the two value forms coincide;
* **§6 `leafB_of_slack_verdict` — the closing**: the slack engine plus *the same two programs*
  (`Poly o`, `Poly Rq`) give a conclusion **token-identical** to `leafB_of_decider`'s, with the
  exactness hypothesis `∀ t, answerBit (E G) t = o G t` replaced by the definitional
  `∀ t, sbit (eng G) t = o G t` (true when `o` is the engine's own verdict).

`sorry`-free, standard three axioms (audited in §7).
-/

open scoped BigOperators
open Matrix
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.SlackRoute

open QMCLeafB.AnswerProducer
open QMCLeafB.EngineRuntime

/-! ## 0.  The decider fold, copied verbatim from `Solutions/Check_EngineRuntime_m6.lean` §7

`bitsF` and its `Poly` proof sit in §7 of that source but not in the installed
`Solutions/Check_EngineRuntime_m6.olean` (which was built before §7 was written — the same
staleness d2 and d7 report).  They are restated here character for character so that this file
compiles on its own; the coordinator's rebuilt olean makes them redundant.
-/

/-- `k` bisection steps driven by a Boolean decider `o : ℚ → Bool` at the midpoints. -/
def bitsF (o : ℚ → Bool) : ℕ → ℚ × ℚ → List Bool
  | 0, _ => []
  | (k + 1), p => o ((p.1 + p.2) / 2) :: bitsF o k (bstep (o ((p.1 + p.2) / 2)) p)

/-- **The bits of a recursive decider are a straight-line program** (verbatim copy). -/
theorem bitsF_poly {α : Type} [Coding α] (o : α → ℚ → Bool)
    (ho : Automatic.Poly (fun p : α × ℚ => o p.1 p.2)) :
    ∀ k : ℕ, Automatic.Poly (fun x : α × (ℚ × ℚ) => bitsF (o x.1) k x.2)
  | 0 => by
      have h : (fun x : α × (ℚ × ℚ) => bitsF (o x.1) 0 x.2)
          = fun _ : α × (ℚ × ℚ) => ([] : List Bool) := rfl
      rw [h]
      exact Automatic.Poly.const []
  | (k + 1) => by
      have hrec := bitsF_poly o ho k
      have ho' : Automatic.Poly (fun x : (α × (ℚ × ℚ)) × ℚ => o x.1.1 x.2) := by
        have hp : Automatic.Poly (fun x : (α × (ℚ × ℚ)) × ℚ => (x.1.1, x.2)) :=
          Automatic.Poly.pair (Automatic.Poly.comp Automatic.Poly.fst Automatic.Poly.fst)
            Automatic.Poly.snd
        exact Automatic.Poly.comp ho hp
      have hmid : Automatic.Poly (fun x : α × (ℚ × ℚ) => (x.2.1 + x.2.2) / 2) := by
        have h1 : Automatic.Poly (fun x : α × (ℚ × ℚ) => x.2.1 + x.2.2) :=
          Automatic.Poly.comp Automatic.Poly.rat_add
            (Automatic.Poly.pair (Automatic.Poly.comp Automatic.Poly.fst Automatic.Poly.snd)
              (Automatic.Poly.comp Automatic.Poly.snd Automatic.Poly.snd))
        exact Automatic.Poly.comp Automatic.Poly.rat_div
          (Automatic.Poly.pair h1 (Automatic.Poly.const 2))
      have hbit : Automatic.Poly (fun x : α × (ℚ × ℚ) => o x.1 ((x.2.1 + x.2.2) / 2)) := by
        have hpair : Automatic.Poly (fun x : α × (ℚ × ℚ) =>
            ((x.1, x.2), (x.2.1 + x.2.2) / 2)) :=
          Automatic.Poly.pair (Automatic.Poly.pair Automatic.Poly.fst Automatic.Poly.snd) hmid
        exact Automatic.Poly.comp ho' hpair
      have hstate : Automatic.Poly (fun x : α × (ℚ × ℚ) =>
          (x.1, bstep (o x.1 ((x.2.1 + x.2.2) / 2)) x.2)) := by
        have hb : Automatic.Poly (fun x : α × (ℚ × ℚ) =>
            bstep (o x.1 ((x.2.1 + x.2.2) / 2)) x.2) := by
          have hp : Automatic.Poly (fun x : α × (ℚ × ℚ) =>
              (x.2, o x.1 ((x.2.1 + x.2.2) / 2))) :=
            Automatic.Poly.pair Automatic.Poly.snd hbit
          exact Automatic.Poly.comp bstep_poly hp
        exact Automatic.Poly.pair Automatic.Poly.fst hb
      have hnext : Automatic.Poly (fun x : α × (ℚ × ℚ) =>
          bitsF (o x.1) k (bstep (o x.1 ((x.2.1 + x.2.2) / 2)) x.2)) :=
        Automatic.Poly.comp hrec hstate
      have hgoal : Automatic.Poly (fun x : α × (ℚ × ℚ) =>
          o x.1 ((x.2.1 + x.2.2) / 2) ::
            bitsF (o x.1) k (bstep (o x.1 ((x.2.1 + x.2.2) / 2)) x.2)) := by
        have hp : Automatic.Poly (fun x : α × (ℚ × ℚ) =>
            (o x.1 ((x.2.1 + x.2.2) / 2),
             bitsF (o x.1) k (bstep (o x.1 ((x.2.1 + x.2.2) / 2)) x.2))) :=
          Automatic.Poly.pair hbit hnext
        exact Automatic.Poly.comp Automatic.Poly.list_cons hp
      have hsh : (fun x : α × (ℚ × ℚ) => bitsF (o x.1) (k + 1) x.2)
          = fun x : α × (ℚ × ℚ) =>
              o x.1 ((x.2.1 + x.2.2) / 2) ::
                bitsF (o x.1) k (bstep (o x.1 ((x.2.1 + x.2.2) / 2)) x.2) := rfl
      rw [hsh]
      exact hgoal

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {εw εr : ℚ}

/-! ## 1.  The bit a slack answer carries, and the pair-level recursion -/

/-- The Boolean a slack answer carries: `true` for a witness (the driver moves `hi` down),
`false` for a refutation (it moves `lo` up).  Only this bit ever reaches the bracket. -/
def sbit (eng : ∀ t : ℚ, Answerε A t εw εr) (t : ℚ) : Bool :=
  match eng t with
  | .witness _ _ _ => true
  | .refuted _ => false

/-- The bracket pair after `k` slack steps, as a recursion that never mentions `SlackBrack`:
this is the object a straight-line program computes. -/
def sstate (o : ℚ → Bool) : ℕ → ℚ × ℚ → ℚ × ℚ
  | 0, p => p
  | (k + 1), p => sstate o k (bstep (o ((p.1 + p.2) / 2)) p)

/-- The `sbit` fold is the `bitsF` fold: the adapter between the two recursions. -/
theorem iterB_bitsF (o : ℚ → Bool) : ∀ (k : ℕ) (p : ℚ × ℚ),
    iterB k p (bitsF o k p) = sstate o k p
  | 0, p => rfl
  | (k + 1), p => by
      have h1 : bitsF o (k + 1) p
          = o ((p.1 + p.2) / 2) :: bitsF o k (bstep (o ((p.1 + p.2) / 2)) p) := rfl
      rw [h1]
      exact iterB_bitsF o k (bstep (o ((p.1 + p.2) / 2)) p)

/-- `sstate` unrolled from the outside: the `(k+1)`-st step is applied to the `k`-step pair. -/
theorem sstate_succ (o : ℚ → Bool) : ∀ (k : ℕ) (p : ℚ × ℚ),
    sstate o (k + 1) p
      = bstep (o (((sstate o k p).1 + (sstate o k p).2) / 2)) (sstate o k p)
  | 0, p => rfl
  | (k + 1), p => by
      have h : sstate o (k + 2) p = sstate o (k + 1) (bstep (o ((p.1 + p.2) / 2)) p) := rfl
      rw [h, sstate_succ o k]
      rfl

/-! ## 2.  One slack step is one `bstep` of one bit -/

/-- **A slack step touches only `(lo, hi)`, and only through the bit.**  The witness matrix and
the two slack proofs the constructors carry are never consulted. -/
theorem step_pair (eng : ∀ t : ℚ, Answerε A t εw εr) (B : SlackBrack A εw εr) :
    ((step eng B).lo, (step eng B).hi)
      = bstep (sbit eng ((B.lo + B.hi) / 2)) (B.lo, B.hi) := by
  cases h : eng ((B.lo + B.hi) / 2) with
  | witness X hX htr =>
      simp only [step, sbit, h, bstep, if_true]
  | refuted hlb =>
      simp only [step, sbit, h, bstep, Bool.false_eq_true, if_false]

/-! ## 3.  The value form -/

/-- **The value form of the slack driver**: after `k` engine calls the bracket is exactly the
`k`-fold `bstep` of the `k` bits, with no reference to the answers' payload. -/
theorem iter_pair_sstate (eng : ∀ t : ℚ, Answerε A t εw εr) (B : SlackBrack A εw εr) :
    ∀ k : ℕ, ((iter eng B k).lo, (iter eng B k).hi)
      = sstate (sbit eng) k (B.lo, B.hi)
  | 0 => rfl
  | (k + 1) => by
      have hstep : ((iter eng B (k + 1)).lo, (iter eng B (k + 1)).hi)
          = bstep (sbit eng (((iter eng B k).lo + (iter eng B k).hi) / 2))
              ((iter eng B k).lo, (iter eng B k).hi) := by
        have h : iter eng B (k + 1) = step eng (iter eng B k) := rfl
        rw [h]
        exact step_pair eng (iter eng B k)
      calc ((iter eng B (k + 1)).lo, (iter eng B (k + 1)).hi)
          = bstep (sbit eng (((iter eng B k).lo + (iter eng B k).hi) / 2))
              ((iter eng B k).lo, (iter eng B k).hi) := hstep
        _ = bstep (sbit eng (((sstate (sbit eng) k (B.lo, B.hi)).1
                + (sstate (sbit eng) k (B.lo, B.hi)).2) / 2))
              (sstate (sbit eng) k (B.lo, B.hi)) := by
            have ih := iter_pair_sstate eng B k
            have hidx : ((iter eng B k).lo + (iter eng B k).hi)
                = ((sstate (sbit eng) k (B.lo, B.hi)).1
                    + (sstate (sbit eng) k (B.lo, B.hi)).2) :=
              congrArg (fun q : ℚ × ℚ => q.1 + q.2) ih
            rw [hidx, ih]
        _ = sstate (sbit eng) (k + 1) (B.lo, B.hi) :=
            (sstate_succ (sbit eng) k (B.lo, B.hi)).symm

/-- The same statement in the vocabulary of the **program** side: the bracket is the
`iterB`/`bitsF` fold that `Check_EngineRuntime_m6` already proves is a `Poly` program. -/
theorem iter_pair_bitsF (eng : ∀ t : ℚ, Answerε A t εw εr) (B : SlackBrack A εw εr) (k : ℕ) :
    ((iter eng B k).lo, (iter eng B k).hi)
      = iterB k (B.lo, B.hi) (bitsF (sbit eng) k (B.lo, B.hi)) := by
  rw [iter_pair_sstate eng B k]
  exact (iterB_bitsF (sbit eng) k (B.lo, B.hi)).symm

/-- **The printed value of the slack driver is `bval` of the bit list** — the exact same function
whose program is `EngineRuntime.bval_poly`. -/
theorem iter_hi_bval (eng : ∀ t : ℚ, Answerε A t εw εr) (B : SlackBrack A εw εr)
    (R : ℚ) (hB : B.lo = -R) (hB' : B.hi = 0) (k : ℕ) :
    (R - (iter eng B k).hi) / 4 = bval k R (bitsF (sbit eng) k (-R, 0)) := by
  have hhi : (iter eng B k).hi
      = (iterB k (B.lo, B.hi) (bitsF (sbit eng) k (B.lo, B.hi))).2 := by
    simpa using congrArg Prod.snd (iter_pair_bitsF eng B k)
  simp only [bval]
  rw [hhi, hB, hB']

/-! ## 4.  The residual obligation on this route: one program for the verdict bit, one for `Rq` -/

section Program

variable {α : Type} [Coding α]

/-- **The value program of the slack route.**  A `Poly` program for a Boolean threshold verdict
`o` (read off the encoded instance) and one for the total weight `R` give a `Poly` program for the
value `(R − hi)/4` of the `k`-call bisection driven by `o`.  This is the programme-level content
of `iter_hi_bval`: on the slack route `o` is the engine's own verdict computation, so no agreement
lemma between `o` and an exact answer is needed anywhere. -/
theorem value_of_bits_poly (R : α → ℚ) (o : α → ℚ → Bool)
    (hR : Automatic.Poly R) (ho : Automatic.Poly (fun p : α × ℚ => o p.1 p.2)) (k : ℕ) :
    Automatic.Poly (fun x : α => bval k (R x) (bitsF (o x) k (-(R x), 0))) := by
  have hinit : Automatic.Poly (fun x : α => (-(R x), (0 : ℚ))) :=
    Automatic.Poly.pair (Automatic.Poly.comp Automatic.Poly.rat_neg hR)
      (Automatic.Poly.const 0)
  have hbits : Automatic.Poly (fun x : α => bitsF (o x) k (-(R x), 0)) := by
    have h := bitsF_poly (α := α) (o := o) ho k
    exact Automatic.Poly.comp h (Automatic.Poly.pair Automatic.Poly.identity hinit)
  exact Automatic.Poly.comp (bval_poly k) (Automatic.Poly.pair hR hbits)

end Program

/-! ## 5.  Consistency with the exact route: zero slack recovers `answerBit` -/

/-- The exact answer of the driver, read as a zero-slack answer.  (`AnswerProducer` restates
`Answer` and `Answerε` in its own namespace, so the transport is spelled out here.) -/
def toSlackA {A : Matrix (Fin n) (Fin n) ℝ} {t : ℚ} :
    QMCLeafB.ThresholdDriver.Answer A t → Answerε A t 0 0
  | .feasible X hX htr => .witness X hX (by simpa using htr)
  | .infeasible hlb => .refuted (fun Z hZ => by simpa using hlb Z hZ)

/-- **The slack route contains the exact one.**  Reading a zero-slack answer through
`toSlackA`, the slack bit is `EngineRuntime.answerBit`; so the slack value form specialises to
`EngineRuntime.iter_pair_eq_stateOf`, and the two routes cannot disagree. -/
theorem sbit_toSlack (E : ∀ t : ℚ, QMCLeafB.ThresholdDriver.Answer A t) (t : ℚ) :
    sbit (A := A) (εw := 0) (εr := 0) (fun s => toSlackA (E s)) t = answerBit E t := by
  cases h : E t with
  | feasible X hX htr =>
      simp only [sbit, answerBit, h, toSlackA]
  | infeasible hlb =>
      simp only [sbit, answerBit, h, toSlackA]

/-! ## 6.  The closing: `d9f601e5` from the slack engine and the same two programs

With the value form in hand the closing form of the leaf on the **slack** route is exactly as
cheap as on the exact route, and it does not ask the decider to decide anything: `o` only has to
be *the engine's own verdict*, `hag` is then `rfl`-shaped, and `ho` is the program that computes
it. -/

section Closing

variable {o : QuantumMaxCutEnergy.Input → ℚ → Bool}

/-- The leaf's own encoder, so that `Poly` in this section speaks `encodeRequest`. -/
local instance instRequestCoding : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-- Congruence of the bit fold in the decider (the copy of `EngineRuntime.bitsF_congr`, §7). -/
theorem bitsF_congr {o o' : ℚ → Bool} (h : ∀ t : ℚ, o t = o' t) :
    ∀ (k : ℕ) (p : ℚ × ℚ), bitsF o k p = bitsF o' k p
  | 0, p => rfl
  | (k + 1), p => by
      rw [show bitsF o (k + 1) p
            = o ((p.1 + p.2) / 2) :: bitsF o k (bstep (o ((p.1 + p.2) / 2)) p) from rfl,
          show bitsF o' (k + 1) p
            = o' ((p.1 + p.2) / 2) :: bitsF o' k (bstep (o' ((p.1 + p.2) / 2)) p) from rfl,
          h ((p.1 + p.2) / 2)]
      exact congrArg (fun l => o' ((p.1 + p.2) / 2) :: l)
        (bitsF_congr h k (bstep (o' ((p.1 + p.2) / 2)) p))

/-- The slack start bracket of the graph instance, both slacks `Rq G / 40000`. -/
noncomputable def vstart (G : QuantumMaxCutEnergy.Input) :
    SlackBrack (QMCLeafB.wMatrix G) (Rq G / 40000) (Rq G / 40000) :=
  startBrack (div_nonneg (Rq_nonneg G) (by norm_num))
    (div_nonneg (Rq_nonneg G) (by norm_num))
    (QMCLeafB.wMatrix_nonneg G) (fun _ => QMCLeafB.wMatrix_apply_of_eq) (Rq G) (Rq_abs_sum G)

theorem vstart_lo (G : QuantumMaxCutEnergy.Input) : (vstart G).lo = -Rq G := rfl

theorem vstart_hi (G : QuantumMaxCutEnergy.Input) : (vstart G).hi = 0 := rfl

/-- The value the slack driver prints: `bval` of the thirteen verdict bits, degraded by
`εw = Rq/40000` (the `εw/4` term that keeps it below the SDP value). -/
noncomputable def vLq (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) : ℚ :=
  bval 13 (Rq G) (bitsF (o G) 13 (-Rq G, 0)) - Rq G / 160000

/-- The same value in bracket form. -/
theorem vLq_eq (G : QuantumMaxCutEnergy.Input) :
    vLq o G = (Rq G - (iterB 13 (-Rq G, 0) (bitsF (o G) 13 (-Rq G, 0))).2
      - Rq G / 40000) / 4 := by
  unfold vLq bval
  ring

/-- **The driver's `hi` is the fold of the verdict bits** (value form + agreement). -/
theorem vhi_eq (eng : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      Answerε (QMCLeafB.wMatrix G) t (Rq G / 40000) (Rq G / 40000))
    (hag : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), sbit (eng G) t = o G t)
    (G : QuantumMaxCutEnergy.Input) :
    (iter (eng G) (vstart G) 13).hi
      = (iterB 13 (-Rq G, 0) (bitsF (o G) 13 (-Rq G, 0))).2 := by
  have h := congrArg Prod.snd (iter_pair_bitsF (eng G) (vstart G) 13)
  rw [vstart_lo, vstart_hi] at h
  have hc : bitsF (sbit (eng G)) 13 (-Rq G, 0) = bitsF (o G) 13 (-Rq G, 0) :=
    bitsF_congr (fun t => hag G t) 13 _
  rw [hc] at h
  exact h

/-- **The closing theorem of the slack route.**  `agm_classical_sdp_lower_value_tm2` (d9f601e5)
from

* `eng` — a per-graph engine with the two slacks `εw = εr = Rq/40000` (mathematics; the
  `answer-producer` brick produces it, and its budget `εw + εr = W/10000 ≤ W/7500` is met);
* `o` — the same engine's verdict as a Boolean function of the instance and the threshold;
* `hag` — the definitional agreement (no mathematics: on this route `o` *is* the verdict);
* `ho`, `hR` — **one** program for `o` and one for the total weight, exactly the two programs the
  exact closing form asks for.

No exact SDP-feasibility decision, and no agreement of `o` with `feasBit`, enters anywhere. -/
theorem leafB_of_slack_verdict
    (eng : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      Answerε (QMCLeafB.wMatrix G) t (Rq G / 40000) (Rq G / 40000))
    (hag : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), sbit (eng G) t = o G t)
    (ho : Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (hR : Automatic.Poly (fun a : QuantumMaxCutEnergy.Input × List Bool => Rq a.1)) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by
  classical
  have hnonneg : ∀ G : QuantumMaxCutEnergy.Input, 0 ≤ vLq o G := by
    intro G
    rw [vLq_eq]
    have hhi0 : (iterB 13 (-Rq G, 0) (bitsF (o G) 13 (-Rq G, 0))).2 ≤ 0 := by
      rw [← vhi_eq eng hag G]
      exact (hi_le_start (eng G) (vstart G) 13).trans_eq (vstart_hi G)
    have hR0 : (0 : ℚ) ≤ Rq G := Rq_nonneg G
    have hε0 : (0 : ℚ) ≤ Rq G / 40000 := div_nonneg hR0 (by norm_num)
    linarith
  let L : QuantumMaxCutEnergy.Input → ℚ≥0 := fun G => ⟨vLq o G, hnonneg G⟩
  have hLv : Automatic.Poly (fun a : QuantumMaxCutEnergy.Input × List Bool => vLq o a.1) := by
    have hbval := value_of_bits_poly (α := QuantumMaxCutEnergy.Input × List Bool)
      (R := fun a : QuantumMaxCutEnergy.Input × List Bool => Rq a.1)
      (o := fun a t => o a.1 t) hR ho 13
    have hcorr : Automatic.Poly (fun a : QuantumMaxCutEnergy.Input × List Bool =>
        Rq a.1 / 160000) :=
      Automatic.Poly.comp Automatic.Poly.rat_div
        (Automatic.Poly.pair hR (Automatic.Poly.const 160000))
    have h := Automatic.Poly.comp Automatic.Poly.rat_sub
      (Automatic.Poly.pair hbval hcorr)
    simpa only [vLq] using h
  refine QMCLeafB.AuditM2.target_of_value_program L ?_ ?_
  · exact hLv.program
  · intro G
    obtain ⟨S, hS⟩ := QMCLeafBExistence.exists_isMaxcutSDPValue (QMCLeafB.wMatrix G)
    have hV : AnswerProducer.V (QMCLeafB.wMatrix G) = (Rq G : ℝ) := Rq_cast G
    have hlow := lower_bound (A := QMCLeafB.wMatrix G) hS (iter (eng G) (vstart G) 13)
    have hup := upper_bound (A := QMCLeafB.wMatrix G) hS (iter (eng G) (vstart G) 13)
    rw [hV] at hlow hup
    have hval : ((vLq o G : ℚ) : ℝ)
        = ((Rq G : ℝ) - ((iter (eng G) (vstart G) 13).hi : ℝ)
            - ((Rq G / 40000 : ℚ) : ℝ)) / 4 := by
      rw [vLq_eq, vhi_eq eng hag G]
      push_cast
      ring
    have hcast : ((L G : ℚ≥0) : ℝ) = ((vLq o G : ℚ) : ℝ) := rfl
    have hwidth : ((iter (eng G) (vstart G) 13).hi : ℝ)
        - ((iter (eng G) (vstart G) 13).lo : ℝ) = (Rq G : ℝ) / 8192 := by
      have h := congrArg (fun q : ℚ => ((q : ℚ) : ℝ)) (iter_width (eng G) (vstart G) 13)
      rw [vstart_lo, vstart_hi] at h
      push_cast at h
      rw [h]
      norm_num
    have hRqT : (Rq G : ℝ) = 2 * ∑ e, (G.weights e : ℝ) := by
      unfold Rq
      push_cast
      ring
    have hW0 : (0 : ℝ) ≤ ∑ e, (G.weights e : ℝ) :=
      Finset.sum_nonneg fun e _ => by positivity
    have hkey : (∑ e, (G.weights e : ℝ)) / 16384 + (∑ e, (G.weights e : ℝ)) / 40000
        ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by
      have h1 : (∑ e, (G.weights e : ℝ)) / 16384 + (∑ e, (G.weights e : ℝ)) / 40000
          = (∑ e, (G.weights e : ℝ)) * (1 / 16384 + 1 / 40000) := by ring
      rw [h1]
      refine mul_le_mul_of_nonneg_left ?_ hW0
      norm_num
    refine ⟨S, hS, ?_, ?_⟩
    · rw [hcast, hval]
      have hεc : ((Rq G / 40000 : ℚ) : ℝ) = (Rq G : ℝ) / 40000 := by push_cast; ring
      rw [hεc] at hlow ⊢
      linarith [hlow]
    · rw [hcast, hval]
      have hεc : ((Rq G / 40000 : ℚ) : ℝ) = (Rq G : ℝ) / 40000 := by push_cast; ring
      rw [hεc] at hup ⊢
      have hlin : S - ((Rq G : ℝ) - ((iter (eng G) (vstart G) 13).hi : ℝ)
            - (Rq G : ℝ) / 40000) / 4
          ≤ (∑ e, (G.weights e : ℝ)) / 16384 + (∑ e, (G.weights e : ℝ)) / 40000 := by
        nlinarith [hup, hwidth, hRqT]
      exact hlin.trans hkey

end Closing

/-! ## 7.  Axiom audit -/

#print axioms QMCLeafB.SlackRoute.bitsF_poly
#print axioms QMCLeafB.SlackRoute.iterB_bitsF
#print axioms QMCLeafB.SlackRoute.sstate_succ
#print axioms QMCLeafB.SlackRoute.step_pair
#print axioms QMCLeafB.SlackRoute.iter_pair_sstate
#print axioms QMCLeafB.SlackRoute.iter_pair_bitsF
#print axioms QMCLeafB.SlackRoute.iter_hi_bval
#print axioms QMCLeafB.SlackRoute.value_of_bits_poly
#print axioms QMCLeafB.SlackRoute.sbit_toSlack
#print axioms QMCLeafB.SlackRoute.bitsF_congr
#print axioms QMCLeafB.SlackRoute.vhi_eq
#print axioms QMCLeafB.SlackRoute.leafB_of_slack_verdict

end QMCLeafB.SlackRoute

namespace QMCLeafB.SlackRoute
open OAI.MetricKMedian.Binary.Automatic
local instance instRequestCodingChk : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩
#check @QMCLeafB.SlackRoute.leafB_of_slack_verdict
#check @QMCLeafB.EngineRuntime.leafB_of_decider
#check @QMCLeafB.SlackRoute.value_of_bits_poly
#check @QMCLeafB.SlackRoute.iter_pair_bitsF
#check @QMCLeafB.SlackRoute.iter_hi_bval
#check @QMCLeafB.SlackRoute.step_pair
end QMCLeafB.SlackRoute


