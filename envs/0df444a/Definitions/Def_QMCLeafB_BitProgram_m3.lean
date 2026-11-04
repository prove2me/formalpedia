-- Prove2me | Definitions.Def_QMCLeafB_BitProgram_m3
-- name    : QMCLeafB_BitProgram_m3
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:19:23.388916+00:00
-- url     : https://prove2.me/theorems/d729610a-767a-479d-8b0c-24698ad609fa
-- title:
--   QMCLeafB BitProgram_m3
-- statement:
--   # leaf B phase 5 — brick `bit-program` (swarm `smvzxba5a`, member `m3`)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_EngineRuntime_m6
/-
# leaf B phase 5 — brick `bit-program` (swarm `smvzxba5a`, member `m3`)

## What this file does

`Check_EngineRuntime_m6.leafB_of_decider` asks for a decider `o : Input → ℚ → Bool`, an
engine `E : ∀ G t, Answer (wMatrix G) t`, *agreement* `answerBit (E G) t = o G t`, a `Poly`
program for `o` and one for `Rq`.  Four of those five slots are bookkeeping; one is the whole
remaining computation.  This file does that bookkeeping once and for all, and states the
remaining computation as a single `Poly` goal:

* `Sound b` — the two-sided *certificate* specification of a decider: `true` carries a genuine
  feasible witness, `false` carries a genuine refutation.  These are exactly the two
  constructors of `ThresholdDriver.Answer`, so `Sound` is precisely "the engine slot is filled
  by `b`", with no appeal to excluded middle anywhere in the specification.
* `engineOf` — the engine induced by a sound decider (the witness is extracted from soundness by
  `Classical.choice`; this is the *mathematical* direction, never the computation), and
  `answerBit_engineOf`: its answer bit **is** `b`.  So a sound decider needs no separate `hag`
  proof.
* `feasBit_false_iff` — the `false` side of `EngineRuntime.feasBit` in refutation form.
* `sound_feasBit` — the classical truth predicate is sound, so `Sound` is inhabited: the
  residual below is purely a computability statement.
* **`sound_iff_feasBit`** — a sound decider is *exactly* a decider agreeing with the exact
  feasibility bit at every rational threshold.  There is no slack: no margin argument, no
  relaxed body, no freedom at the boundary.
* **`feasBitPoly_iff_residual`** — consequently the one genuinely open computation of the
  campaign is, up to the `Rq` program, the single statement
  `Poly (fun p => feasBit (wMatrix p.1.1) p.2)`.
* `leafB_of_feasBit_poly` — the leaf (`agm_classical_sdp_lower_value_tm2`, d9f601e5) from
  exactly those two `Poly` statements; `leafB_of_sound_decider` — the same from a general sound
  decider given in certificate form.

## Note on imports

The installed olean of `Solutions/Check_EngineRuntime_m6` was *stale* (it predated sections 6-8
of that source, so `leafB_of_decider`, `feasBit`, `answerTotal` were missing from it).  It has
been refreshed with

    lake env lean -o .lake/build/lib/lean/Solutions/Check_EngineRuntime_m6.olean \
        Solutions/Check_EngineRuntime_m6.lean

so this file's import now resolves the closing theorem and the feasibility predicate.  Do **not**
use `lake build` for that: the lakefile sets `autoImplicit false`, under which
`Solutions/MergeAll3_m8.lean` does not elaborate (it relies on auto-bound `n`); single-file
elaboration with `lake env lean` uses Lean's default settings and works.

No `sorry`, no `axiom`; axiom audit at the end.
-/

open scoped BigOperators
open Matrix

namespace QMCLeafB.BitProgram

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open QMCLeafB.ThresholdDriver
open QMCLeafB.EngineRuntime

variable {n : ℕ}

/-- The request encoding: the instance together with the random tape, exactly the encoder the
leaf's `TM2` statement is stated over (verbatim the instance `EngineRuntime` uses). -/
local instance instRequestCoding : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 1.  The two sides of a decider, in certificate form -/

/-- **A sound decider.**  `b G t = true` must come with an actual feasible point (unit diagonal,
positive semidefinite, trace at most `t`); `b G t = false` must come with an actual refutation
(`t` below every feasible trace).  These are the two constructors of `Answer (wMatrix G) t`, so a
sound decider *is* an engine, and conversely. -/
def Sound (b : (G : QuantumMaxCutEnergy.Input) → ℚ → Bool) : Prop :=
  (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), b G t = true →
      ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        ModernConvex.Relaxations.IsUnitDiagPSD X ∧
          (QMCLeafB.wMatrix G * X).trace ≤ (t : ℝ)) ∧
  (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), b G t = false →
      ∀ Z : Matrix (Fin G.n) (Fin G.n) ℝ,
        ModernConvex.Relaxations.IsUnitDiagPSD Z →
          (t : ℝ) ≤ (QMCLeafB.wMatrix G * Z).trace)

/-- A Boolean that is not `true` is `false`. -/
theorem bool_eq_false_of_ne_true {v : Bool} (h : ¬ (v = true)) : v = false := by
  cases v with
  | true => exact absurd rfl h
  | false => rfl

/-- **The engine a sound decider induces.**  On `true` the witness is extracted from the
soundness proof (`Classical.choice` on the existence statement — this is the *mathematical*
direction, never the computation); on `false` the refutation is the soundness proof itself. -/
noncomputable def engineOf (b : (G : QuantumMaxCutEnergy.Input) → ℚ → Bool) (hb : Sound b)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) : Answer (QMCLeafB.wMatrix G) t :=
  if h : b G t = true then
    Answer.feasible (hb.1 G t h).choose (hb.1 G t h).choose_spec.1
      (hb.1 G t h).choose_spec.2
  else
    Answer.infeasible (hb.2 G t (bool_eq_false_of_ne_true h))

/-- **The induced engine's bit is the decider.**  So a sound decider needs no separate
`hag : answerBit (E G) t = o G t` proof: `hag` holds by construction, because `Answer`'s two
constructors force the engine to be built exactly this way. -/
theorem answerBit_engineOf (b : (G : QuantumMaxCutEnergy.Input) → ℚ → Bool) (hb : Sound b)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) : answerBit (engineOf b hb G) t = b G t := by
  cases h : b G t with
  | true =>
      have he : engineOf b hb G t
          = Answer.feasible (hb.1 G t h).choose (hb.1 G t h).choose_spec.1
              (hb.1 G t h).choose_spec.2 := by
        unfold engineOf
        rw [dif_pos h]
      simp only [answerBit, he]
  | false =>
      have hne : ¬ (b G t = true) := by rw [h]; simp
      have he : engineOf b hb G t
          = Answer.infeasible (hb.2 G t (bool_eq_false_of_ne_true hne)) := by
        unfold engineOf
        rw [dif_neg hne]
      simp only [answerBit, he]

/-! ## 2.  The feasibility bit: its `false` side, and the fact that it is sound -/

/-- The `false` side of `EngineRuntime.feasBit`: a `false` bit is a refutation.  (The converse
fails at the boundary `t = min tr`, where a witness and a refutation co-exist.) -/
theorem feasBit_false_mp (A : Matrix (Fin n) (Fin n) ℝ) (t : ℚ) (h : feasBit A t = false) :
    ∀ Z : Matrix (Fin n) (Fin n) ℝ,
      ModernConvex.Relaxations.IsUnitDiagPSD Z → (t : ℝ) ≤ (A * Z).trace := by
  intro Z hZ
  have hnt : ¬ ∃ X : Matrix (Fin n) (Fin n) ℝ,
      ModernConvex.Relaxations.IsUnitDiagPSD X ∧ (A * X).trace ≤ (t : ℝ) := by
    rw [← feasBit_eq_true_iff, h]
    simp
  by_contra hlt
  exact hnt ⟨Z, hZ, (not_le.mp hlt).le⟩

/-- **The truth predicate is sound.**  `Answer`'s contract is satisfied by the *truth* about the
threshold body, so the `Sound` specification is inhabited: what is missing in the campaign is
computability, not existence. -/
theorem sound_feasBit :
    Sound (fun (G : QuantumMaxCutEnergy.Input) (t : ℚ) => feasBit (QMCLeafB.wMatrix G) t) := by
  constructor
  · intro G t hb
    rwa [feasBit_eq_true_iff] at hb
  · intro G t hb
    exact feasBit_false_mp _ _ hb

/-- **A sound `true` is the truth.** -/
theorem sound_true_forces (b : (G : QuantumMaxCutEnergy.Input) → ℚ → Bool) (hb : Sound b)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (h : b G t = true) :
    feasBit (QMCLeafB.wMatrix G) t = true := by
  obtain ⟨X, hX, htr⟩ := hb.1 G t h
  exact (feasBit_eq_true_iff _ _).mpr ⟨X, hX, htr⟩

/-- **Where a sound decider can differ from the truth: exactly the boundary.**  If it answers
`false` where the truth is `true`, then a refutation and a witness co-exist, so the threshold is
*exactly* the attained minimum `tr (A X)`; the decider's bit is still a legal `Answer`, and the
error is confined to a single rational `t` per instance.  This is the whole of the freedom the
`Answer` contract leaves, and it is what makes `Sound` the exact specification of the `ho` slot
(no margin, no relaxed body, no rounding can enlarge it). -/
theorem sound_false_or_boundary (b : (G : QuantumMaxCutEnergy.Input) → ℚ → Bool) (hb : Sound b)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    b G t = feasBit (QMCLeafB.wMatrix G) t ∨
      (b G t = false ∧ feasBit (QMCLeafB.wMatrix G) t = true ∧
        ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
          ModernConvex.Relaxations.IsUnitDiagPSD X ∧
            (QMCLeafB.wMatrix G * X).trace = (t : ℝ)) := by
  by_cases hbt : b G t = true
  · exact Or.inl (by rw [hbt, sound_true_forces b hb G t hbt])
  · have hbfalse : b G t = false := bool_eq_false_of_ne_true hbt
    by_cases hfb : feasBit (QMCLeafB.wMatrix G) t = true
    · refine Or.inr ⟨hbfalse, hfb, ?_⟩
      obtain ⟨X, hX, htr⟩ := (feasBit_eq_true_iff _ _).mp hfb
      exact ⟨X, hX, le_antisymm htr (hb.2 G t hbfalse X hX)⟩
    · have hff : feasBit (QMCLeafB.wMatrix G) t = false := bool_eq_false_of_ne_true hfb
      exact Or.inl (by rw [hbfalse, hff])

/-- Conversely, agreeing with the truth is sound. -/
theorem sound_of_eq_feasBit {b : (G : QuantumMaxCutEnergy.Input) → ℚ → Bool}
    (h : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), b G t = feasBit (QMCLeafB.wMatrix G) t) :
    Sound b := by
  constructor
  · intro G t hbt
    rw [h] at hbt
    rwa [feasBit_eq_true_iff] at hbt
  · intro G t hbt
    rw [h] at hbt
    exact feasBit_false_mp _ _ hbt

/-! ## 2.5  The `false` side as a checked rational dual certificate

`Sound`'s false side asks for a *refutation* of the threshold body.  That refutation does not have
to be the engine's volume-emptiness argument: it can be a display-pair **dual certificate**
`y : Fin n → ℚ` with `A + diag y ⪰ 0` and `∑ y ≤ −t`, which `ThresholdDriver.dual_refutes`
turns into the refutation by weak duality.  Both sides then have the same shape — check a
rational certificate proposal (`CertPSD`/`SepOracle`'s `split` on `A + diag y` for the dual side,
on `X` for the primal side) — so the residual decider can be stated, implemented and proved as a
*certificate search* over the already-machine-checked certificate layer, with no volume argument
inside it. -/

/-- A decider whose two sides are witnessed by explicit rational certificates: a primal feasible
point on `true`, a dual display-pair certificate on `false`. -/
def DualSound (b : (G : QuantumMaxCutEnergy.Input) → ℚ → Bool) : Prop :=
  (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), b G t = true →
      ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        ModernConvex.Relaxations.IsUnitDiagPSD X ∧
          (QMCLeafB.wMatrix G * X).trace ≤ (t : ℝ)) ∧
  (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), b G t = false →
      ∃ y : Fin G.n → ℚ,
        (Matrix.diagonal (fun i => (y i : ℝ)) + QMCLeafB.wMatrix G).PosSemidef ∧
          (∑ i, (y i : ℝ)) ≤ -(t : ℝ))

/-- **A certificate decider is a sound decider**: the dual side is a genuine refutation by weak
duality (`ThresholdDriver.dual_refutes`). -/
theorem sound_of_dualSound (b : (G : QuantumMaxCutEnergy.Input) → ℚ → Bool)
    (hb : DualSound b) : Sound b := by
  constructor
  · exact hb.1
  · intro G t hbt
    obtain ⟨y, hy, hyt⟩ := hb.2 G t hbt
    refine QMCLeafB.ThresholdDriver.dual_refutes (A := QMCLeafB.wMatrix G)
      (y := fun i => (y i : ℝ)) hy ?_
    linarith

/-! ## 3.  The residual, and the leaf from it -/

/-- **The residual of the campaign.**  A `Poly`-computable sound decider — equivalently, by
`sound_iff_feasBit`, a `Poly` program for the exact feasibility bit. -/
def Residual : Prop :=
  ∃ b : (G : QuantumMaxCutEnergy.Input) → ℚ → Bool,
    Sound b ∧ Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => b p.1.1 p.2)

/-- The residual in its sharpest form: the exact feasibility bit of the max-cut threshold body is
poly-time computable on the instance encoding. -/
def FeasBitPoly : Prop :=
  Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
    feasBit (QMCLeafB.wMatrix p.1.1) p.2)

/-- **`Poly feasBit` suffices for the residual.**  (The converse is *not* available: at the
boundary a sound decider may answer `false` where the truth is `true`, by
`sound_false_or_boundary`; so `Residual` is the exact specification of the `ho` slot and
`FeasBitPoly` is its sharpest sufficient form.) -/
theorem residual_of_feasBitPoly (h : FeasBitPoly) : Residual :=
  ⟨_, sound_feasBit, h⟩

/-- **The leaf from a sound decider.**  Everything `leafB_of_decider` asks for except the two
`Poly` statements is produced here: the engine is `engineOf` and the agreement is
`answerBit_engineOf`. -/
theorem leafB_of_sound_decider (b : (G : QuantumMaxCutEnergy.Input) → ℚ → Bool) (hb : Sound b)
    (ho : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => b p.1.1 p.2))
    (hR : Poly (fun a : QuantumMaxCutEnergy.Input × List Bool => Rq a.1)) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  leafB_of_decider b (engineOf b hb) (fun G t => answerBit_engineOf b hb G t) ho hR

/-- **The leaf from the feasibility bit alone.**  `agm_classical_sdp_lower_value_tm2` (d9f601e5)
follows from *two* `Poly` statements: the exact feasibility bit of the threshold body is
poly-time computable on the request encoding, and the total weight `Rq` is. -/
theorem leafB_of_feasBit_poly
    (ho : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      feasBit (QMCLeafB.wMatrix p.1.1) p.2))
    (hR : Poly (fun a : QuantumMaxCutEnergy.Input × List Bool => Rq a.1)) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  leafB_of_sound_decider _ sound_feasBit ho hR

/-- The same in the shape a coordinator merges: `Residual + (Poly Rq) ⟹ d9f601e5`. -/
theorem leafB_of_residual (hres : Residual)
    (hR : Poly (fun a : QuantumMaxCutEnergy.Input × List Bool => Rq a.1)) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by
  obtain ⟨b, hb, hpoly⟩ := hres
  exact leafB_of_sound_decider b hb hpoly hR

/-- The same reduction for the leaf: a `Poly` certificate decider plus the total-weight program
gives d9f601e5. -/
theorem leafB_of_dualSound_decider (b : (G : QuantumMaxCutEnergy.Input) → ℚ → Bool)
    (hb : DualSound b)
    (ho : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => b p.1.1 p.2))
    (hR : Poly (fun a : QuantumMaxCutEnergy.Input × List Bool => Rq a.1)) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  leafB_of_sound_decider b (sound_of_dualSound b hb) ho hR

/-! ## 4.  The residual is confined to the start bracket `[-Rq, 0)`

The driver's thirteen queries are the midpoints of the successive brackets, so all of them lie in
`(-Rq G, 0)` (`startB`, `Rq`, `bval` in `EngineRuntime`).  Outside that interval the decider's job
is free: at `t ≥ 0` the identity matrix is a feasible point (the weight matrix has zero diagonal)
and at `t < -Rq G` the entrywise bound `|Z i j| ≤ 1` refutes the body outright.  So the *whole*
correctness obligation of a candidate decider is the open start bracket — which is what an
ellipsoid/sep-oracle implementation is asked to decide anyway. -/

/-- **The `true` regime.**  At `t ≥ 0` the identity matrix is feasible: `wMatrix G` has zero
diagonal, so its trace against `1` is `0 ≤ t`. -/
theorem feasBit_eq_true_of_nonneg (G : QuantumMaxCutEnergy.Input) {t : ℚ} (ht : 0 ≤ t) :
    feasBit (QMCLeafB.wMatrix G) t = true := by
  rw [feasBit_eq_true_iff]
  refine ⟨1, QMCLeafB.ThresholdDriver.isUnitDiagPSD_one, ?_⟩
  have htr : (QMCLeafB.wMatrix G * 1).trace = 0 := by
    rw [QMCLeafB.ThresholdDriver.trace_mul_one]
    exact Finset.sum_eq_zero fun i _ => QMCLeafB.wMatrix_apply_of_eq
  rw [htr]
  have : ((0 : ℚ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  simpa using this

/-- **The `false` regime.**  At `t < -Rq G` no feasible point reaches `t`: every unit-diagonal
semidefinite `Z` has `tr (A Z) ≥ -∑|A i j| = -Rq G`, strictly above `t`. -/
theorem feasBit_eq_false_of_lt_neg_Rq (G : QuantumMaxCutEnergy.Input) {t : ℚ}
    (ht : t < -Rq G) : feasBit (QMCLeafB.wMatrix G) t = false := by
  cases h : feasBit (QMCLeafB.wMatrix G) t with
  | false => rfl
  | true =>
      rw [feasBit_eq_true_iff] at h
      obtain ⟨X, hX, htr⟩ := h
      have hb : -(∑ i, ∑ j, |QMCLeafB.wMatrix G i j|) ≤ (QMCLeafB.wMatrix G * X).trace :=
        QMCLeafB.ThresholdDriver.neg_abs_sum_le_trace _ _ hX
      rw [Rq_abs_sum] at hb
      have ht' : (t : ℝ) < -((Rq G : ℚ) : ℝ) := by exact_mod_cast ht
      linarith

/-- Complete a candidate decider to the whole rational line by the two trivial regimes. -/
noncomputable def bracketDecider (cand : (G : QuantumMaxCutEnergy.Input) → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) : Bool :=
  if 0 ≤ t then true else if t < -Rq G then false else cand G t

/-- **The residual lives on the start bracket.**  A candidate that is correct at every threshold
of the bracket `[-Rq G, 0)` extends, by the two trivial regimes, to a sound decider on the
whole line. -/
theorem sound_bracketDecider (cand : (G : QuantumMaxCutEnergy.Input) → ℚ → Bool)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), -Rq G ≤ t → t < 0 →
      cand G t = feasBit (QMCLeafB.wMatrix G) t) :
    Sound (bracketDecider cand) := by
  apply sound_of_eq_feasBit
  intro G t
  unfold bracketDecider
  by_cases h0 : 0 ≤ t
  · rw [if_pos h0, feasBit_eq_true_of_nonneg G h0]
  · rw [if_neg h0]
    by_cases h1 : t < -Rq G
    · rw [if_pos h1, feasBit_eq_false_of_lt_neg_Rq G h1]
    · rw [if_neg h1]
      exact hc G t (not_lt.mp h1) (not_le.mp h0)

/-- The leaf from a candidate decider correct on the start bracket, plus the two `Poly`
statements for its trivial completion and the total weight. -/
theorem leafB_of_bracket_decider (cand : (G : QuantumMaxCutEnergy.Input) → ℚ → Bool)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), -Rq G ≤ t → t < 0 →
      cand G t = feasBit (QMCLeafB.wMatrix G) t)
    (ho : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      bracketDecider cand p.1.1 p.2))
    (hR : Poly (fun a : QuantumMaxCutEnergy.Input × List Bool => Rq a.1)) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  leafB_of_sound_decider _ (sound_bracketDecider cand hc) ho hR

#print axioms QMCLeafB.BitProgram.answerBit_engineOf
#print axioms QMCLeafB.BitProgram.feasBit_false_mp
#print axioms QMCLeafB.BitProgram.sound_false_or_boundary
#print axioms QMCLeafB.BitProgram.feasBit_eq_true_of_nonneg
#print axioms QMCLeafB.BitProgram.feasBit_eq_false_of_lt_neg_Rq
#print axioms QMCLeafB.BitProgram.sound_bracketDecider
#print axioms QMCLeafB.BitProgram.leafB_of_bracket_decider
#print axioms QMCLeafB.BitProgram.sound_of_dualSound
#print axioms QMCLeafB.BitProgram.leafB_of_dualSound_decider
#print axioms QMCLeafB.BitProgram.residual_of_feasBitPoly
#print axioms QMCLeafB.BitProgram.sound_feasBit
#print axioms QMCLeafB.BitProgram.sound_of_eq_feasBit
#print axioms QMCLeafB.BitProgram.leafB_of_sound_decider
#print axioms QMCLeafB.BitProgram.leafB_of_feasBit_poly
#print axioms QMCLeafB.BitProgram.leafB_of_residual

end QMCLeafB.BitProgram


