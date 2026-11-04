-- Prove2me | Definitions.Def_QMCLeafB_LoopRestate
-- name    : QMCLeafB_LoopRestate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:04:45.351032+00:00
-- url     : https://prove2.me/theorems/5f5e1096-9614-4299-af92-1088fcb5714b
-- title:
--   QMCLeafB LoopRestate
-- statement:
--   # leaf B phase 13 — brick `loop-restate` (coordinator, for the integration)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_sim_poly_m4
import Definitions.Def_QMCLeafB_brick_finish_line
/-
# leaf B phase 13 — brick `loop-restate` (coordinator, for the integration)

`QMCLeafB.SimPoly.poly_loop_state`'s size hypothesis `hsize` is the *fixed-point ball* form

    ∀ a x, (encSt x).length ≤ sizes.eval (encSt a).length →
      (encSt (round x.1, x.2.tail)).length ≤ sizes.eval (encSt a).length

whose right-hand side does not mention `x`.  As m3's obstruction file argues (phase 13,
`.ultramath/smw17fqzz/m3/hsize-obstruction.md`), with the heights inside a polynomial ball able to
sit almost anywhere, that form is not dischargeable for a round that keeps `n²` matrix entries.
It is a *form* issue, not a math gap: the loop only ever visits the orbit of its own initial
state, and `PolyProgram.loop`'s `BoundedRun` is already indexed by that visit sequence
(`SimPoly.boundedRun_loopBody` manufactures it from a ball hypothesis, which is the only place
the ball ever appears).

This module restates the loop lemmas against the orbit:

1. `boundedRun_loopBody_orbit` — drop-in replacement for `SimPoly.boundedRun_loopBody`, with the
   size hypothesis ranging over the visited indexed states
   `∀ k ≤ f.length, (encSt (round^[k] s, f.drop k)).length ≤ S` instead of the whole ball.
   Callers supply their per-round orbit ledger (the dyadic snap's height reset, indexed by
   round), never an adversarial ball.
2. `ho_of_loop_bounded` — the closing `ho` (the `Automatic.Poly` simulate) from the orbit bound.
3. `solution_of_loop_bounded` — the `SolutionStatement` from the orbit bound, `hspec` and the
   bracket soundness, mirroring `SimPoly.solution_of_loop` slot for slot.  The broken `hsize`/
   `hsize0` pair never appears; the route goes straight to
   `FinishLine.solution_of_bracket_verdict`.

No `sorry`, no `axiom`; audits at the end.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.LoopRestate

open QMCLeafB.SimPoly

variable {σ : Type} [Coding σ]

/-! ## 1.  The orbit-indexed run lemma -/

/-- **The loop terminates along the orbit.**  Same conclusion as
`SimPoly.boundedRun_loopBody`, but the size hypothesis only has to hold at the states the run
actually visits — `(round^[k] s, f.drop k)` for `k ≤ f.length`. -/
theorem boundedRun_loopBody_orbit (round : σ → σ) (verdict : σ → Bool) (S : ℕ)
    (s : σ) (f : List Bool)
    (h : ∀ k : ℕ, k ≤ f.length → (encSt (round^[k] s, f.drop k)).length ≤ S) :
    ∃ n ≤ f.length + 1, BoundedRun encSt (loopBody round verdict) S n (s, f)
      (verdict (round^[f.length] s)) := by
  induction f generalizing s with
  | nil =>
      refine ⟨1, by simp, BoundedRun.stop ?_ ?_⟩
      · simpa using h 0 (Nat.zero_le 0)
      · simp [loopBody]
  | cons a f ih =>
      have hb : loopBody round verdict (s, a :: f) = Sum.inr (round s, f) := by
        simp [loopBody]
      have hcur : (encSt (s, a :: f)).length ≤ S := h 0 (Nat.zero_le _)
      have hrest : ∀ k : ℕ, k ≤ f.length → (encSt (round^[k] (round s), f.drop k)).length ≤ S := by
        intro k hk
        have hkk := h (k + 1) (by rw [List.length_cons]; omega)
        rwa [Function.iterate_succ_apply] at hkk
      obtain ⟨n, hn, hrun⟩ := ih (round s) hrest
      refine ⟨n + 1, by simpa using Nat.add_le_add_right hn 1, ?_⟩
      exact BoundedRun.step (ea := encSt) (f := loopBody round verdict) hcur hb hrun

/-! ## 2.  The bounded simulate, at a per-input orbit envelope -/

section Orbit

/-- The iteration bound is the same as `SimPoly`'s: one fuel bit per round, `X + 1` dominates. -/
theorem iter_bound_of_fuel (a : σ × List Bool) :
    a.2.length + 1 ≤ (Polynomial.X + 1 : Polynomial ℕ).eval (encSt a).length := by
  have h1 : a.2.length ≤ (encodeList (enc : Bool → List Bool) a.2).length :=
    EncodedList.length_le (enc : Bool → List Bool) a.2
  have h2 : (encSt a).length
      = 2 * (enc a.1).length + 1 + (encodeList (enc : Bool → List Bool) a.2).length :=
    encodePair_length (enc : σ → List Bool) (enc : List Bool → List Bool) a
  have h3 : (Polynomial.X + 1 : Polynomial ℕ).eval (encSt a).length = (encSt a).length + 1 := by
    simp [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  omega

/-- **The bounded simulate from an orbit envelope.**  The size envelope is
`sizes.eval (encSt a)` — the enclosed length budget read off the *concrete* initial state `a` of
the loop — and the hypothesis is that every visited indexed state fits inside it.  This is the
statement a dyadic-snap ledger proves per round on the orbit. -/
theorem ho_of_loop_bounded {α : Type} [Coding α]
    (init : α → σ) (fuel : α → List Bool) (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hfuel : Automatic.Poly fuel)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (horbit : ∀ a : σ × List Bool, ∀ k : ℕ, k ≤ a.2.length →
      (encSt (Nat.iterate round k a.1, a.2.drop k)).length ≤ sizes.eval (encSt a).length) :
    Automatic.Poly (fun a => verdict (Nat.iterate round (fuel a).length (init a))) := by
  classical
  have hg : Automatic.Poly (fun a : σ × List Bool => verdict (Nat.iterate round a.2.length a.1)) := by
    refine ⟨?_⟩
    refine (poly_loopBody round verdict hr hv).some.loop
      (fun a : σ × List Bool => verdict (Nat.iterate round a.2.length a.1))
      (Polynomial.X + 1) sizes ?_
    intro a
    obtain ⟨n, hn, hrun⟩ :=
      boundedRun_loopBody_orbit round verdict (sizes.eval (encSt a).length) a.1 a.2
        (fun k hk => horbit a k hk)
    exact ⟨n, hn.trans (iter_bound_of_fuel a), hrun⟩
  exact ⟨(Automatic.Poly.pair hinit hfuel).program.comp hg.some⟩

end Orbit


/-! ## 3.  The endgame slot, bypassing the broken ball forms -/

section Closing

open QuantumMaxCutEnergy

/-- The request coding of the leaf, as in `Check_brick_finish_line` / `Check_sim_poly_m4`. -/
local instance instRequestCodingRestate : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-- **`SolutionStatement` from the orbit envelope.**  Slot-for-slot mirror of
`QMCLeafB.SimPoly.solution_of_loop`: the same concrete simulate, the same `hspec`, the same
`SoundεOnBracket`, but the size accounting is the per-initial-state orbit envelope of §2 instead
of the broken global ball pair `hsize`/`hsize0`.  This is the form the endgame integration should
target once the concrete round has its snap ledger indexed by round. -/
theorem solution_of_loop_bounded
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hfuel : Automatic.Poly fuel)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (horbit : ∀ a : σ × List Bool, ∀ k : ℕ, k ≤ a.2.length →
      (encSt (Nat.iterate round k a.1, a.2.drop k)).length ≤ sizes.eval (encSt a).length)
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hspec : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      verdict (Nat.iterate round (fuel p).length (init p)) = o p.1.1 p.2)
    (hsound : QMCLeafB.FinishLine.SoundεOnBracket o) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinishLine.solution_of_bracket_verdict o hsound
    (QMCLeafB.FinishLine.poly_of_pointwise
      (ho_of_loop_bounded init fuel round verdict hinit hfuel hr hv sizes horbit) hspec)

end Closing

/-! ## 4.  Axiom audit -/

#print axioms QMCLeafB.LoopRestate.boundedRun_loopBody_orbit
#print axioms QMCLeafB.LoopRestate.ho_of_loop_bounded
#print axioms QMCLeafB.LoopRestate.solution_of_loop_bounded

end QMCLeafB.LoopRestate


