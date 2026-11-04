-- Prove2me | Definitions.Def_QMCLeafB_EngineRuntime_m6
-- name    : QMCLeafB_EngineRuntime_m6
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:13:55.594791+00:00
-- url     : https://prove2.me/theorems/0a0553dc-512c-43ed-aa43-e90eeb9bf3f0
-- title:
--   QMCLeafB EngineRuntime_m6
-- statement:
--   # leaf B phase 4 — brick `engine-runtime` (m6)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_ThresholdDriver
import Definitions.Def_QMCLeafB_InterfaceAudit_m2
/-
# leaf B phase 4 — brick `engine-runtime` (m6)

The runtime seam of the threshold engine: **the leaf's rational lower value depends on the
threshold engine only through thirteen bits, and it is a `PolyProgram` in those bits and in the
total weight.**

## What is proved here

1. `bit`, `bstep`, `iterB`, `bval` — the *value* half of the bisection: one bracket update from
   one Boolean, the thirteen-fold fold of those updates, and the printed value `(R − hi)/4`.
   The fold is a straight-line program (`iterB` is unrolled over the natural `k`, so `k = 13` is a
   fixed program, not a loop whose length depends on the input).
2. `bit_poly`, `bstep_poly`, `iterB_poly`, `bval_poly` — `Poly` proofs, i.e. actual
   `PolyProgram`s for the fold and for the printed value.
3. `answerBit`, `stateOf`, `bitsOf`, `iterB_bitsOf`, `iter_pair_eq_stateOf` — **the value-form
   theorem**: `ThresholdDriver.iter`'s bracket after `k` steps is *exactly* `iterB k` applied to
   the `k` answer bits of the engine.  So the driver's `Lq = (R − hi)/4` is
   `bval 13 (Rq G) (bitsOf …)` and depends on the engine's `Answer` data only through those bits
   (`answerBit`), never through the real matrix carried by the `feasible` constructor.
4. `Rq`, `Rq_cast`, `Rq_abs_sum`, `startB`, `driver_hi_eq`, `driver_hi_le_zero`,
   `bval_nonneg`, `leafB_value_bounds_bval` — the sandwich *at the thirteen-bit value*: for every
   max-cut SDP value `S` of `wMatrix G`, `bval 13 (Rq G) bits ≤ S` and
   `S − bval 13 (Rq G) bits ≤ (∑ₑ wₑ)/10000`, with no hypothesis beyond the per-threshold engine.
5. `value_program` — the `PolyProgram` the value route consumes, produced from a `PolyProgram`
   for the bits and one for the total weight, at exactly the encoder
   `QuantumMaxCutEnergy.encodeRequest`.
6. `leafB_of_engine_bits` — the leaf's sentence (`agm_classical_sdp_lower_value_tm2`) from a
   per-graph threshold-answering engine plus those two programs, via
   `QMCLeafB.AuditM2.target_of_value_program`.

Residual obligation this brick leaves (stated exactly, not hidden): a `PolyProgram` over
`QuantumMaxCutEnergy.encodeRequest` for the thirteen answer bits of the engine (`hb`) and one for
`Rq` (`hR`).  Both are parse-then-compute programs over the self-delimiting `encodeInput`
(`QMCLeafB.InputLen`); nothing else in the chain is unproved.

No `sorry`, no `axiom`; the audit at the end of the file shows the standard three axioms.
-/

open scoped BigOperators
open Matrix

namespace QMCLeafB.EngineRuntime

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic

/-- The `i`-th answer bit, defaulting to `false` past the end of the list. -/
def bit (bits : List Bool) (i : ℕ) : Bool := bits[i]?.getD false

/-- **One bisection step on the bracket, driven by one bit.** -/
def bstep (b : Bool) (p : ℚ × ℚ) : ℚ × ℚ :=
  if b then (p.1, (p.1 + p.2) / 2) else ((p.1 + p.2) / 2, p.2)

/-- `k` bisection steps, reading the bits from the front of the list. -/
def iterB : ℕ → ℚ × ℚ → List Bool → ℚ × ℚ
  | 0, p, _ => p
  | (k + 1), p, bits => iterB k (bstep (bits.head?.getD false) p) bits.tail

theorem iterB_zero (p : ℚ × ℚ) (bits : List Bool) : iterB 0 p bits = p := rfl

theorem iterB_succ (k : ℕ) (p : ℚ × ℚ) (bits : List Bool) :
    iterB (k + 1) p bits = iterB k (bstep (bits.head?.getD false) p) bits.tail := rfl

theorem bit_poly (i : ℕ) : Poly (fun bits : List Bool => bit bits i) :=
  Automatic.Poly.list_getD_comp false Automatic.Poly.identity (Automatic.Poly.const i)

theorem bstep_poly : Poly (fun x : (ℚ × ℚ) × Bool => bstep x.2 x.1) := by
  have h : (fun x : (ℚ × ℚ) × Bool => bstep x.2 x.1)
      = fun x : (ℚ × ℚ) × Bool =>
          if x.2 then (x.1.1, (x.1.1 + x.1.2) / 2) else ((x.1.1 + x.1.2) / 2, x.1.2) := by
    funext x
    cases x.2 <;> rfl
  rw [h]
  fun_prop

theorem iterB_poly : ∀ k : ℕ, Poly (fun q : (ℚ × ℚ) × List Bool => iterB k q.1 q.2)
  | 0 => by
      have h : (fun q : (ℚ × ℚ) × List Bool => iterB 0 q.1 q.2)
          = fun q : (ℚ × ℚ) × List Bool => q.1 := rfl
      rw [h]
      exact Automatic.Poly.fst
  | (k + 1) => by
      have hrec := iterB_poly k
      have hinner : Poly (fun q : (ℚ × ℚ) × List Bool =>
          iterB k (bstep (q.2.head?.getD false) q.1) q.2.tail) := by
        have hpair : Poly (fun q : (ℚ × ℚ) × List Bool =>
            (bstep (q.2.head?.getD false) q.1, q.2.tail)) := by
          have h1 : Poly (fun q : (ℚ × ℚ) × List Bool => bstep (q.2.head?.getD false) q.1) :=
            Poly.comp bstep_poly (Automatic.Poly.pair (Automatic.Poly.fst) (Automatic.Poly.comp (Automatic.Poly.list_head false) Automatic.Poly.snd))
          exact Automatic.Poly.pair h1 (Automatic.Poly.comp Automatic.Poly.list_tail Automatic.Poly.snd)
        exact Automatic.Poly.comp hrec hpair
      have h : (fun q : (ℚ × ℚ) × List Bool => iterB (k + 1) q.1 q.2)
          = fun q : (ℚ × ℚ) × List Bool =>
              iterB k (bstep (q.2.head?.getD false) q.1) q.2.tail := by
        funext q
        rfl
      rw [h]
      exact hinner

/-- The printed value: the leaf's rational lower bound read off the bracket. -/
def bval (k : ℕ) (R : ℚ) (bits : List Bool) : ℚ := (R - (iterB k (-R, 0) bits).2) / 4

theorem bval_poly (k : ℕ) : Poly (fun x : ℚ × List Bool => bval k x.1 x.2) := by
  have hstate : Poly (fun x : ℚ × List Bool => iterB k (-x.1, (0 : ℚ)) x.2) := by
    refine Automatic.Poly.comp (iterB_poly k) (Automatic.Poly.pair (Automatic.Poly.pair ?_ ?_) Automatic.Poly.snd)
    · exact Automatic.Poly.comp Automatic.Poly.rat_neg Automatic.Poly.fst
    · exact Automatic.Poly.const 0
  have hhi : Poly (fun x : ℚ × List Bool => (iterB k (-x.1, (0 : ℚ)) x.2).2) :=
    Automatic.Poly.comp Automatic.Poly.snd hstate
  have hsub : Poly (fun x : ℚ × List Bool => x.1 - (iterB k (-x.1, (0 : ℚ)) x.2).2) := by
    have h := Automatic.Poly.comp (f := fun y : ℚ × ℚ => y.1 - y.2) (g := fun x : ℚ × List Bool =>
      (x.1, (iterB k (-x.1, (0 : ℚ)) x.2).2)) Automatic.Poly.rat_sub (Automatic.Poly.pair Automatic.Poly.fst hhi)
    exact h
  have hval : (fun x : ℚ × List Bool => bval k x.1 x.2)
      = fun x : ℚ × List Bool => (x.1 - (iterB k (-x.1, (0 : ℚ)) x.2).2) / 4 := rfl
  rw [hval]
  refine Automatic.Poly.comp (f := fun y : ℚ × ℚ => y.1 / y.2) (g := fun x : ℚ × List Bool =>
    (x.1 - (iterB k (-x.1, (0 : ℚ)) x.2).2, (4 : ℚ))) Automatic.Poly.rat_div (Automatic.Poly.pair hsub ?_)
  exact Automatic.Poly.const 4

end QMCLeafB.EngineRuntime

/-! ## 3.  The bits an engine's answers produce, and the value-form theorem -/

namespace QMCLeafB.EngineRuntime

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open QMCLeafB.ThresholdDriver

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}

/-- The Boolean an engine's answer carries at one threshold: `true` for a feasible witness,
`false` for a refutation.  This is the *whole* of the engine's data that the bracket keeps. -/
def answerBit (eng : ∀ t : ℚ, Answer A t) (t : ℚ) : Bool :=
  match eng t with
  | .feasible _ _ _ => true
  | .infeasible _ => false

/-- The bracket state after `k` bisection steps, driven by the engine's answers. -/
def stateOf (eng : ∀ t : ℚ, Answer A t) : ℕ → ℚ × ℚ → ℚ × ℚ
  | 0, p => p
  | (k + 1), p => stateOf eng k (bstep (answerBit eng ((p.1 + p.2) / 2)) p)

/-- The first `k` answer bits, in the order the engine meets them. -/
def bitsOf (eng : ∀ t : ℚ, Answer A t) : ℕ → ℚ × ℚ → List Bool
  | 0, _ => []
  | (k + 1), p =>
      answerBit eng ((p.1 + p.2) / 2) :: bitsOf eng k (bstep (answerBit eng ((p.1 + p.2) / 2)) p)

/-- **One driver step is one `bstep`**: the bracket moves by `bstep` on the answer bit, and the
witness/proof data the `Answer` carries is never consulted. -/
theorem step_pair (eng : ∀ t : ℚ, Answer A t) (B : Brack A) :
    ((step eng B).lo, (step eng B).hi)
      = bstep (answerBit eng ((B.lo + B.hi) / 2)) (B.lo, B.hi) := by
  rcases h : eng ((B.lo + B.hi) / 2) with X | hlb
  · simp only [answerBit, h, bstep, if_true]
    unfold step
    rw [h]
  · simp only [answerBit, h, bstep, if_false, Bool.false_eq_true]
    unfold step
    rw [h]

/-- **`iterB` reproduces the engine-driven state**: the fold over the bits is the state
recursion. -/
theorem iterB_bitsOf (eng : ∀ t : ℚ, Answer A t) :
    ∀ (k : ℕ) (p : ℚ × ℚ), iterB k p (bitsOf eng k p) = stateOf eng k p
  | 0, p => rfl
  | (k + 1), p => by
      have hb : (answerBit eng ((p.1 + p.2) / 2) :: bitsOf eng k
          (bstep (answerBit eng ((p.1 + p.2) / 2)) p)).head?.getD false
          = answerBit eng ((p.1 + p.2) / 2) := rfl
      have ht : (answerBit eng ((p.1 + p.2) / 2) :: bitsOf eng k
          (bstep (answerBit eng ((p.1 + p.2) / 2)) p)).tail
          = bitsOf eng k (bstep (answerBit eng ((p.1 + p.2) / 2)) p) := rfl
      rw [bitsOf, iterB_succ, hb, ht]
      exact iterB_bitsOf eng k _

/-- `stateOf` unrolled from the outside: the `(k+1)`-st step is applied to the `k`-step state. -/
theorem stateOf_succ (eng : ∀ t : ℚ, Answer A t) :
    ∀ (k : ℕ) (p : ℚ × ℚ), stateOf eng (k + 1) p
      = bstep (answerBit eng (((stateOf eng k p).1 + (stateOf eng k p).2) / 2)) (stateOf eng k p)
  | 0, p => rfl
  | (k + 1), p => by
      have h : stateOf eng (k + 2) p
          = stateOf eng (k + 1) (bstep (answerBit eng ((p.1 + p.2) / 2)) p) := rfl
      rw [h, stateOf_succ eng k]
      rfl

/-- **The value-form theorem.**  After `k` bisection steps the driver's bracket is exactly the
`k`-fold `bstep` of the engine's answer bits: the driver's `Lq` is a function of thirteen bits. -/
theorem iter_pair_eq_stateOf (eng : ∀ t : ℚ, Answer A t) (B : Brack A) :
    ∀ k : ℕ, ((iter eng B k).lo, (iter eng B k).hi) = stateOf eng k (B.lo, B.hi)
  | 0 => by simp only [iter, stateOf]
  | (k + 1) => by
      have hstep : ((iter eng B (k + 1)).lo, (iter eng B (k + 1)).hi)
          = bstep (answerBit eng (((iter eng B k).lo + (iter eng B k).hi) / 2))
              ((iter eng B k).lo, (iter eng B k).hi) :=
        step_pair eng (iter eng B k)
      calc ((iter eng B (k + 1)).lo, (iter eng B (k + 1)).hi)
          = bstep (answerBit eng (((iter eng B k).lo + (iter eng B k).hi) / 2))
              ((iter eng B k).lo, (iter eng B k).hi) := hstep
        _ = bstep (answerBit eng (((stateOf eng k (B.lo, B.hi)).1
              + (stateOf eng k (B.lo, B.hi)).2) / 2)) (stateOf eng k (B.lo, B.hi)) := by
            have hP : ((iter eng B k).lo, (iter eng B k).hi) = stateOf eng k (B.lo, B.hi) :=
              iter_pair_eq_stateOf eng B k
            have hidx : (iter eng B k).lo + (iter eng B k).hi
                = (stateOf eng k (B.lo, B.hi)).1 + (stateOf eng k (B.lo, B.hi)).2 :=
              congrArg (fun q : ℚ × ℚ => q.1 + q.2) hP
            rw [hidx, hP]
        _ = stateOf eng (k + 1) (B.lo, B.hi) := (stateOf_succ eng k (B.lo, B.hi)).symm

/-- The engine's answer bits at the leaf's start bracket `(−R, 0)`: the thirteen bits the value
depends on. -/
def engineBits (eng : ∀ t : ℚ, Answer A t) (R : ℚ) : List Bool := bitsOf eng 13 (-R, 0)

end QMCLeafB.EngineRuntime

/-! ## 4.  The leaf's value: `bval` is the driver's `Lq`, and it is sandwiched -/

namespace QMCLeafB.EngineRuntime

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open QMCLeafB.ThresholdDriver

/-- The rational total weight `V A = 2 ∑ₑ wₑ` of the input, as the engine's start width `R`. -/
noncomputable def Rq (G : QuantumMaxCutEnergy.Input) : ℚ :=
  2 * ∑ e, ((G.weights e : ℚ≥0) : ℚ)

theorem Rq_nonneg (G : QuantumMaxCutEnergy.Input) : (0 : ℚ) ≤ Rq G := by
  unfold Rq
  have : (0 : ℚ) ≤ ∑ e, ((G.weights e : ℚ≥0) : ℚ) :=
    Finset.sum_nonneg fun e _ => by positivity
  linarith

theorem Rq_cast (G : QuantumMaxCutEnergy.Input) :
    QMCLeafB.V (QMCLeafB.wMatrix G) = (Rq G : ℝ) := by
  rw [QMCLeafB.V_wMatrix]
  unfold Rq
  push_cast
  ring

theorem Rq_abs_sum (G : QuantumMaxCutEnergy.Input) :
    (∑ i, ∑ j, |QMCLeafB.wMatrix G i j|) = (Rq G : ℝ) := by
  rw [← Rq_cast G]
  show (∑ i, ∑ j, |QMCLeafB.wMatrix G i j|) = ∑ i, ∑ j, QMCLeafB.wMatrix G i j
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    abs_of_nonneg (QMCLeafB.wMatrix_nonneg G i j)

/-- The start bracket of the leaf, whose width is the total weight. -/
noncomputable def startB (G : QuantumMaxCutEnergy.Input) (_eng : ∀ t : ℚ,
    Answer (QMCLeafB.wMatrix G) t) : Brack (QMCLeafB.wMatrix G) :=
  startBrack (QMCLeafB.wMatrix_nonneg G) (fun _ => QMCLeafB.wMatrix_apply_of_eq) (Rq G)
    (Rq_abs_sum G)

theorem startB_lo (G : QuantumMaxCutEnergy.Input) (eng : ∀ t : ℚ,
    Answer (QMCLeafB.wMatrix G) t) : (startB G eng).lo = -Rq G := rfl

theorem startB_hi (G : QuantumMaxCutEnergy.Input) (eng : ∀ t : ℚ,
    Answer (QMCLeafB.wMatrix G) t) : (startB G eng).hi = 0 := rfl



/-- **The final `hi` of the driver is the thirteen-bit fold.** -/
theorem driver_hi_eq (G : QuantumMaxCutEnergy.Input) (eng : ∀ t : ℚ,
    Answer (QMCLeafB.wMatrix G) t) :
    (iter eng (startB G eng) 13).hi
      = (iterB 13 (-Rq G, 0) (bitsOf eng 13 (-Rq G, 0))).2 := by
  have hpair := iter_pair_eq_stateOf eng (startB G eng) 13
  have hstart : ((startB G eng).lo, (startB G eng).hi) = (-Rq G, (0 : ℚ)) := rfl
  have hst : stateOf eng 13 (-Rq G, (0 : ℚ))
      = iterB 13 (-Rq G, (0 : ℚ)) (bitsOf eng 13 (-Rq G, (0 : ℚ))) :=
    (iterB_bitsOf eng 13 (-Rq G, (0 : ℚ))).symm
  calc (iter eng (startB G eng) 13).hi
      = (stateOf eng 13 ((startB G eng).lo, (startB G eng).hi)).2 := by rw [← hpair]
    _ = (stateOf eng 13 (-Rq G, (0 : ℚ))).2 := by rw [hstart]
    _ = (iterB 13 (-Rq G, (0 : ℚ)) (bitsOf eng 13 (-Rq G, (0 : ℚ)))).2 := by rw [hst]

/-- The witnessed endpoint never rises above the (zero) start, so the thirteen-bit `hi` is at
most `0`. -/
theorem driver_hi_le_zero (G : QuantumMaxCutEnergy.Input) (eng : ∀ t : ℚ,
    Answer (QMCLeafB.wMatrix G) t) :
    (iterB 13 (-Rq G, 0) (bitsOf eng 13 (-Rq G, 0))).2 ≤ 0 := by
  have h := hi_le_start eng (startB G eng) 13
  rw [startB_hi] at h
  rwa [driver_hi_eq] at h

theorem bval_nonneg (G : QuantumMaxCutEnergy.Input) (eng : ∀ t : ℚ,
    Answer (QMCLeafB.wMatrix G) t) :
    0 ≤ bval 13 (Rq G) (bitsOf eng 13 (-Rq G, 0)) := by
  have h1 := driver_hi_le_zero G eng
  have h2 := Rq_nonneg G
  unfold bval
  linarith

/-- **The leaf's value bounds, at the thirteen-bit value.**  For every max-cut SDP value `S` of
the input's weight matrix, `bval 13 (Rq G) (bits) ≤ S` and `S − bval 13 … ≤ W/10000`. -/
theorem leafB_value_bounds_bval (G : QuantumMaxCutEnergy.Input) {S : ℝ}
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S)
    (eng : ∀ t : ℚ, Answer (QMCLeafB.wMatrix G) t) :
    ((bval 13 (Rq G) (bitsOf eng 13 (-Rq G, 0)) : ℚ) : ℝ) ≤ S ∧
      S - ((bval 13 (Rq G) (bitsOf eng 13 (-Rq G, 0)) : ℚ) : ℝ)
        ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by
  set B₀ : Brack (QMCLeafB.wMatrix G) := startB G eng with hB₀
  set Bk : Brack (QMCLeafB.wMatrix G) := iter eng B₀ 13 with hBk
  have hR0 : (0 : ℝ) ≤ (Rq G : ℝ) := by
    rw [← Rq_cast G]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      QMCLeafB.wMatrix_nonneg G i j
  have hhi : (iterB 13 (-Rq G, 0) (bitsOf eng 13 (-Rq G, 0))).2 = Bk.hi := by
    rw [hBk]
    exact (driver_hi_eq G eng).symm
  -- the bracket has halved thirteen times
  have hwQ : Bk.hi - Bk.lo = Rq G / 2 ^ 13 := by
    rw [hBk, iter_width]
    have hw : B₀.hi - B₀.lo = Rq G := by rw [hB₀]; exact startBrack_width _ _ _ _
    rw [hw]
  have hwR : (Bk.hi : ℝ) - (Bk.lo : ℝ) = (Rq G : ℝ) / 2 ^ 13 := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) hwQ
    push_cast at h
    simpa using h
  have hlow : (QMCLeafB.V (QMCLeafB.wMatrix G) - (Bk.hi : ℝ)) / 4 ≤ S :=
    (driver_bounds hS eng B₀ 13).1
  have hup : S ≤ (QMCLeafB.V (QMCLeafB.wMatrix G) - (Bk.lo : ℝ)) / 4 :=
    (driver_bounds hS eng B₀ 13).2
  have hVc : QMCLeafB.V (QMCLeafB.wMatrix G) = (Rq G : ℝ) := Rq_cast G
  have hbval : ((bval 13 (Rq G) (bitsOf eng 13 (-Rq G, 0)) : ℚ) : ℝ)
      = ((Rq G : ℝ) - (Bk.hi : ℝ)) / 4 := by
    unfold bval
    rw [hhi]
    push_cast
    ring
  refine ⟨?_, ?_⟩
  · rw [hbval]
    rw [hVc] at hlow
    exact hlow
  · rw [hbval]
    rw [hVc] at hup
    have hw0 : (0 : ℝ) ≤ ∑ e, (G.weights e : ℝ) :=
      Finset.sum_nonneg fun e _ => by positivity
    have hRqT : (Rq G : ℝ) = 2 * ∑ e, (G.weights e : ℝ) := by
      unfold Rq
      push_cast
      ring
    have hstep : (Rq G : ℝ) / 2 ^ 13 / 4 ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by
      have h2 : (Rq G : ℝ) / 2 ^ 13 / 4 = (Rq G : ℝ) / 32768 := by
        rw [div_div]
        norm_num
      rw [h2, hRqT]
      nlinarith
    nlinarith [hup, hwR, hstep]

/-! ## 5.  The `PolyProgram` for the value, and the leaf's sentence -/

/-- **The runtime brick.**  A program for the thirteen answer bits and a program for the total
weight compose into a program for the leaf's rational lower value — at exactly the encoder
`QuantumMaxCutEnergy.encodeRequest` that the leaf's sentence is stated over, so
`QMCLeafB.AuditM2.target_of_value_program` consumes it unchanged. -/
noncomputable def value_program (bits : QuantumMaxCutEnergy.Input → List Bool)
    (R : QuantumMaxCutEnergy.Input → ℚ)
    (hb : PolyProgram QuantumMaxCutEnergy.encodeRequest (encodeList encodeBool)
      (fun request : QuantumMaxCutEnergy.Input × List Bool => bits request.1))
    (hR : PolyProgram QuantumMaxCutEnergy.encodeRequest Ratio.encode
      (fun request : QuantumMaxCutEnergy.Input × List Bool => R request.1)) :
    PolyProgram QuantumMaxCutEnergy.encodeRequest Ratio.encode
      (fun request : QuantumMaxCutEnergy.Input × List Bool =>
        (bval 13 (R request.1) (bits request.1) : ℚ)) := by
  have hpair : PolyProgram QuantumMaxCutEnergy.encodeRequest
      (encodePair Ratio.encode (encodeList encodeBool))
      (fun request : QuantumMaxCutEnergy.Input × List Bool =>
        (R request.1, bits request.1)) := hR.fanout hb
  have hfold : PolyProgram (encodePair Ratio.encode (encodeList encodeBool)) Ratio.encode
      (fun x : ℚ × List Bool => bval 13 x.1 x.2) :=
    (bval_poly 13).program.recode id (fun a => rfl) (fun a => rfl)
  exact (hpair.comp hfold).congr _ (fun a => rfl)

/-- **The leaf's sentence from the engine's thirteen bits.**  The mathematical input is a
per-graph family of threshold answers (`E`, no computability content: `Answer` carries proofs);
the computational input is the two programs.  Everything else — the bisection, the sandwich, the
`ℚ≥0` packaging, the `∑ w / 10000` slack and the TM2 obligation — is discharged here. -/
theorem leafB_of_engine_bits
    (E : (G : QuantumMaxCutEnergy.Input) → ∀ t : ℚ, Answer (QMCLeafB.wMatrix G) t)
    (hb : PolyProgram QuantumMaxCutEnergy.encodeRequest (encodeList encodeBool)
      (fun request : QuantumMaxCutEnergy.Input × List Bool =>
        bitsOf (E request.1) 13 (-Rq request.1, 0)))
    (hR : PolyProgram QuantumMaxCutEnergy.encodeRequest Ratio.encode
      (fun request : QuantumMaxCutEnergy.Input × List Bool => Rq request.1)) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by
  let Lv : QuantumMaxCutEnergy.Input → ℚ≥0 := fun G =>
    ⟨bval 13 (Rq G) (bitsOf (E G) 13 (-Rq G, 0)), bval_nonneg G (E G)⟩
  have hPL : PolyProgram QuantumMaxCutEnergy.encodeRequest Ratio.encode
      (fun request : QuantumMaxCutEnergy.Input × List Bool => (Lv request.1 : ℚ)) :=
    value_program (bits := fun G => bitsOf (E G) 13 (-Rq G, 0)) (R := Rq) hb hR
  refine QMCLeafB.AuditM2.target_of_value_program Lv hPL ?_
  intro G
  obtain ⟨S, hS⟩ := QMCLeafBExistence.exists_isMaxcutSDPValue (QMCLeafB.wMatrix G)
  have hbnd := leafB_value_bounds_bval G hS (E G)
  refine ⟨S, hS, ?_, ?_⟩
  · rw [show ((Lv G : ℚ≥0) : ℝ) = ((bval 13 (Rq G) (bitsOf (E G) 13 (-Rq G, 0)) : ℚ) : ℝ)
      from rfl]
    exact hbnd.1
  · rw [show ((Lv G : ℚ≥0) : ℝ) = ((bval 13 (Rq G) (bitsOf (E G) 13 (-Rq G, 0)) : ℚ) : ℝ)
      from rfl]
    exact hbnd.2

end QMCLeafB.EngineRuntime



/-! ## 6.  Reducing the residual to a single-query decider -/

namespace QMCLeafB.EngineRuntime

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open QMCLeafB.ThresholdDriver

section Decider

variable {α : Type} [Coding α]

/-- `k` bisection steps driven by a Boolean decider `o : ℚ → Bool` at the midpoints. -/
def bitsF (o : ℚ → Bool) : ℕ → ℚ × ℚ → List Bool
  | 0, _ => []
  | (k + 1), p => o ((p.1 + p.2) / 2) :: bitsF o k (bstep (o ((p.1 + p.2) / 2)) p)

/-- The same, with the decider read out of an ambient context (so that `Poly` can talk about it). -/
def bitsO (o : α → ℚ → Bool) (a : α) (k : ℕ) (p : ℚ × ℚ) : List Bool := bitsF (o a) k p

omit [Coding α] in
theorem bitsF_congr {o o' : ℚ → Bool} (h : ∀ t : ℚ, o t = o' t) :
    ∀ (k : ℕ) (p : ℚ × ℚ), bitsF o k p = bitsF o' k p := by
  intro k
  induction k with
  | zero => intro p; rfl
  | succ k ih =>
      intro p
      have hb : o ((p.1 + p.2) / 2) = o' ((p.1 + p.2) / 2) := h _
      have h1 : bitsF o (k + 1) p
          = o ((p.1 + p.2) / 2) :: bitsF o k (bstep (o ((p.1 + p.2) / 2)) p) := rfl
      have h2 : bitsF o' (k + 1) p
          = o' ((p.1 + p.2) / 2) :: bitsF o' k (bstep (o' ((p.1 + p.2) / 2)) p) := rfl
      rw [h1, h2, hb, ih]

/-- **The bits of a recursive decider are a straight-line program.**  One query per step, `k`
unrolled steps, one context read per query. -/
theorem bitsF_poly (o : α → ℚ → Bool) (ho : Poly (fun p : α × ℚ => o p.1 p.2)) :
    ∀ k : ℕ, Poly (fun x : α × (ℚ × ℚ) => bitsF (o x.1) k x.2)
  | 0 => by
      have h : (fun x : α × (ℚ × ℚ) => bitsF (o x.1) 0 x.2)
          = fun _ : α × (ℚ × ℚ) => ([] : List Bool) := rfl
      rw [h]
      exact Automatic.Poly.const []
  | (k + 1) => by
      have hrec := bitsF_poly o ho k
      have ho' : Poly (fun x : (α × (ℚ × ℚ)) × ℚ => o x.1.1 x.2) := by
        have hp : Poly (fun x : (α × (ℚ × ℚ)) × ℚ => (x.1.1, x.2)) :=
          Automatic.Poly.pair (Automatic.Poly.comp Automatic.Poly.fst Automatic.Poly.fst)
            Automatic.Poly.snd
        exact Automatic.Poly.comp ho hp
      have hmid : Poly (fun x : α × (ℚ × ℚ) => (x.2.1 + x.2.2) / 2) := by
        have h1 : Poly (fun x : α × (ℚ × ℚ) => x.2.1 + x.2.2) :=
          Automatic.Poly.comp Automatic.Poly.rat_add
            (Automatic.Poly.pair (Automatic.Poly.comp Automatic.Poly.fst Automatic.Poly.snd)
              (Automatic.Poly.comp Automatic.Poly.snd Automatic.Poly.snd))
        exact Automatic.Poly.comp Automatic.Poly.rat_div
          (Automatic.Poly.pair h1 (Automatic.Poly.const 2))
      have hbit : Poly (fun x : α × (ℚ × ℚ) => o x.1 ((x.2.1 + x.2.2) / 2)) := by
        have hpair : Poly (fun x : α × (ℚ × ℚ) =>
            ((x.1, x.2), (x.2.1 + x.2.2) / 2)) :=
          Automatic.Poly.pair (Automatic.Poly.pair Automatic.Poly.fst Automatic.Poly.snd) hmid
        exact Automatic.Poly.comp ho' hpair
      have hstate : Poly (fun x : α × (ℚ × ℚ) =>
          (x.1, bstep (o x.1 ((x.2.1 + x.2.2) / 2)) x.2)) := by
        have hb : Poly (fun x : α × (ℚ × ℚ) =>
            bstep (o x.1 ((x.2.1 + x.2.2) / 2)) x.2) := by
          have hp : Poly (fun x : α × (ℚ × ℚ) => (x.2, o x.1 ((x.2.1 + x.2.2) / 2))) :=
            Automatic.Poly.pair Automatic.Poly.snd hbit
          exact Automatic.Poly.comp bstep_poly hp
        exact Automatic.Poly.pair Automatic.Poly.fst hb
      have hnext : Poly (fun x : α × (ℚ × ℚ) =>
          bitsF (o x.1) k (bstep (o x.1 ((x.2.1 + x.2.2) / 2)) x.2)) :=
        Automatic.Poly.comp hrec hstate
      have hgoal : Poly (fun x : α × (ℚ × ℚ) =>
          o x.1 ((x.2.1 + x.2.2) / 2) ::
            bitsF (o x.1) k (bstep (o x.1 ((x.2.1 + x.2.2) / 2)) x.2)) := by
        have hp : Poly (fun x : α × (ℚ × ℚ) =>
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

end Decider

section Engine

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}

/-- The driver's answer bits are exactly the bits of the decider `answerBit`. -/
theorem bitsOf_eq_bitsF (eng : ∀ t : ℚ, Answer A t) :
    ∀ (k : ℕ) (p : ℚ × ℚ), bitsOf eng k p = bitsF (answerBit eng) k p := by
  intro k
  induction k with
  | zero => intro p; rfl
  | succ k ih =>
      intro p
      have h1 : bitsOf eng (k + 1) p = answerBit eng ((p.1 + p.2) / 2)
          :: bitsOf eng k (bstep (answerBit eng ((p.1 + p.2) / 2)) p) := rfl
      have h2 : bitsF (answerBit eng) (k + 1) p = answerBit eng ((p.1 + p.2) / 2)
          :: bitsF (answerBit eng) k (bstep (answerBit eng ((p.1 + p.2) / 2)) p) := rfl
      rw [h1, h2, ih]

end Engine
/-! ## Axiom audit -/

#print axioms QMCLeafB.EngineRuntime.bit_poly
#print axioms QMCLeafB.EngineRuntime.bstep_poly
#print axioms QMCLeafB.EngineRuntime.iterB_poly
#print axioms QMCLeafB.EngineRuntime.bval_poly
#print axioms QMCLeafB.EngineRuntime.iterB_bitsOf
#print axioms QMCLeafB.EngineRuntime.iter_pair_eq_stateOf
#print axioms QMCLeafB.EngineRuntime.driver_hi_eq
#print axioms QMCLeafB.EngineRuntime.leafB_value_bounds_bval
#print axioms QMCLeafB.EngineRuntime.value_program
#print axioms QMCLeafB.EngineRuntime.leafB_of_engine_bits

/-! ## 7.  The decider bridge at the leaf's own encoder

The leaf's sentence is stated over `QuantumMaxCutEnergy.encodeRequest`.  The `Coding` instance
below makes the substrate's `Poly` automation speak exactly that encoder, so the program the
decider produces is the `hb` slot of `leafB_of_engine_bits` unchanged. -/

section Request

open OAI.MetricKMedian.Binary.Automatic

local instance instRequestCoding : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-- **One query per step is enough.**  A `Poly` decider for the fixed-threshold body, read off the
whole encoded request, computes the thirteen answer bits: the residual of `leafB_of_engine_bits`
collapses to a *single-query* oracle program. -/
noncomputable def bits_program_of_decider (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (E : (G : QuantumMaxCutEnergy.Input) → ∀ t : ℚ, Answer (QMCLeafB.wMatrix G) t)
    (hag : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), answerBit (E G) t = o G t)
    (ho : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (hR : Poly (fun a : QuantumMaxCutEnergy.Input × List Bool => Rq a.1)) :
    PolyProgram QuantumMaxCutEnergy.encodeRequest
      (OAI.MetricKMedian.Binary.encodeList OAI.MetricKMedian.Binary.encodeBool)
      (fun a : QuantumMaxCutEnergy.Input × List Bool => bitsOf (E a.1) 13 (-Rq a.1, 0)) := by
  have hinit : Poly (fun a : QuantumMaxCutEnergy.Input × List Bool => (-Rq a.1, (0 : ℚ))) :=
    Automatic.Poly.pair (Automatic.Poly.comp Automatic.Poly.rat_neg hR) (Automatic.Poly.const 0)
  have hstep : Poly (fun a : QuantumMaxCutEnergy.Input × List Bool =>
      bitsF (fun t => o a.1 t) 13 (-Rq a.1, 0)) := by
    have h := bitsF_poly (α := QuantumMaxCutEnergy.Input × List Bool)
      (o := fun a t => o a.1 t) ho 13
    exact Automatic.Poly.comp h (Automatic.Poly.pair Automatic.Poly.identity hinit)
  have hcongr : ∀ a : QuantumMaxCutEnergy.Input × List Bool,
      bitsF (fun t => o a.1 t) 13 (-Rq a.1, 0) = bitsOf (E a.1) 13 (-Rq a.1, 0) := by
    intro a
    rw [bitsOf_eq_bitsF (E a.1) 13 (-Rq a.1, 0)]
    exact bitsF_congr (fun t => (hag a.1 t).symm) 13 _
  exact (hstep.program).congr _ hcongr

end Request

section RequestFinal

open OAI.MetricKMedian.Binary.Automatic

local instance instRequestCoding' : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-- **The leaf, from a single-query decider.**  `agm_classical_sdp_lower_value_tm2`
(d9f601e5) from

* `E` — the threshold engine's per-threshold answers (mathematics, no computability content);
* `o` — a Boolean decider for the same thresholds, agreeing with the answers;
* `ho` — **one** poly-time program for `o`, read off the encoded request;
* `hR` — one poly-time program for the total weight `Rq`.

Nothing else: the thirteen-call bisection, the value form, the sandwich, the slack constant, the
`ℚ≥0` packaging and the TM2 obligation are all discharged in this file. -/
theorem leafB_of_decider (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (E : (G : QuantumMaxCutEnergy.Input) → ∀ t : ℚ, Answer (QMCLeafB.wMatrix G) t)
    (hag : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), answerBit (E G) t = o G t)
    (ho : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (hR : Poly (fun a : QuantumMaxCutEnergy.Input × List Bool => Rq a.1)) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by
  have hb := bits_program_of_decider o E hag ho hR
  have hRp : PolyProgram QuantumMaxCutEnergy.encodeRequest Ratio.encode
      (fun request : QuantumMaxCutEnergy.Input × List Bool => Rq request.1) := hR.program
  exact leafB_of_engine_bits E hb hRp

end RequestFinal

/-! ## 8.  Removing the engine hypothesis: the decider is the feasibility predicate itself

`ThresholdDriver.Answer A t` is inhabited classically at every threshold (a trichotomy: either a
feasible point at `t` exists, or `t` is below every feasible trace).  So the *mathematics* of the
leaf needs no engine at all — the only content left is that the feasibility predicate itself is
computable.  That is what this section states and proves: the residual hypotheses become a single
semantically specified decider plus the total weight. -/

section Feas
open Classical

variable {n : ℕ}

/-- **Every threshold is answerable.**  Classical trichotomy on the existence of a feasible point:
if the body is nonempty, take a point; if not, `t` is below every feasible trace.  (No duality, no
oracle: this is the *truth*, not a computation of it.) -/
noncomputable def answerTotal (A : Matrix (Fin n) (Fin n) ℝ) : ∀ t : ℚ, Answer A t :=
  fun t =>
    if h : ∃ X : Matrix (Fin n) (Fin n) ℝ,
        ModernConvex.Relaxations.IsUnitDiagPSD X ∧ (A * X).trace ≤ (t : ℝ) then
      Answer.feasible h.choose h.choose_spec.1 h.choose_spec.2
    else
      Answer.infeasible (fun Z hZ => by
        by_contra hlt
        exact h ⟨Z, hZ, (not_le.mp hlt).le⟩)

/-- The Boolean truth value of "the threshold body is nonempty". -/
noncomputable def feasBit (A : Matrix (Fin n) (Fin n) ℝ) (t : ℚ) : Bool :=
  if _ : ∃ X : Matrix (Fin n) (Fin n) ℝ,
      ModernConvex.Relaxations.IsUnitDiagPSD X ∧ (A * X).trace ≤ (t : ℝ) then true else false

theorem feasBit_eq_true_iff (A : Matrix (Fin n) (Fin n) ℝ) (t : ℚ) :
    feasBit A t = true ↔ ∃ X : Matrix (Fin n) (Fin n) ℝ,
      ModernConvex.Relaxations.IsUnitDiagPSD X ∧ (A * X).trace ≤ (t : ℝ) := by
  unfold feasBit
  by_cases h : ∃ X : Matrix (Fin n) (Fin n) ℝ,
      ModernConvex.Relaxations.IsUnitDiagPSD X ∧ (A * X).trace ≤ (t : ℝ)
  · rw [dif_pos h]; simp [h]
  · rw [dif_neg h]; simp [h]

/-- The classical answer's bit is the feasibility truth value: the bit is canonical, not an
artefact of the choice. -/
theorem answerBit_answerTotal (A : Matrix (Fin n) (Fin n) ℝ) (t : ℚ) :
    answerBit (answerTotal A) t = feasBit A t := by
  unfold answerBit answerTotal feasBit
  by_cases h : ∃ X : Matrix (Fin n) (Fin n) ℝ,
      ModernConvex.Relaxations.IsUnitDiagPSD X ∧ (A * X).trace ≤ (t : ℝ)
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h]

end Feas


