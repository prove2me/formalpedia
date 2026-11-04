-- Prove2me | Definitions.Def_QMCLeafB_sim_poly_m4
-- name    : QMCLeafB_sim_poly_m4
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:18:12.669041+00:00
-- url     : https://prove2.me/theorems/465f7404-ba61-4cbb-8202-f9f6899b02aa
-- title:
--   QMCLeafB sim_poly_m4
-- statement:
--   # leaf B phase 8 — brick `sim-poly` (swarm `smw00sb1m`, member m4, direction d5)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_brick_finish_line
/-
# leaf B phase 8 — brick `sim-poly` (swarm `smw00sb1m`, member m4, direction d5)

The **Poly-level iteration** brick: a `Poly` program for *one* simulate round gives the `Poly`
program for *T₀ rounds*, and hence the verbatim closing hypothesis

    ho : Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2)

Nothing analytic is assumed; the whole file is `Automatic.Poly` / `PolyProgram` plumbing.

Contents:

* §1 `poly_iterate` — `Poly f → Poly (f^[n])` for a **numeral** `n`: the literal "unfold a fixed
  number of rounds into one `Poly`".  Hypothesis-free.  `ho_of_fixed_rounds` (§4) is its closing
  use: with a numeral round count there is no size or iteration accounting at all.
* §2 `loopBody` — the round loop as the body of the compiled bounded-loop combinator
  `PolyProgram.loop`.  The loop state is `σ × List Bool`: the `List Bool` is **fuel** (one round per
  bit), and `isEmpty`/`tail` are the compiled list programs.  `poly_loopBody` shows the body **is** a
  `Poly` program; `boundedRun_loopBody` gives termination and the exact count (`f.length + 1` body
  calls, i.e. `f.length` rounds and the final verdict).
  Fuel is a *list* and not a `ℕ` on purpose — see §5, item 1: `PolyProgram.loop`'s iteration bound
  is a polynomial in the encoded length of the state, and `Nat.bits` is logarithmic, so no
  polynomial can dominate a `ℕ` counter, while `f.length ≤ (encSt (s,f)).length` holds outright.
* §3 `poly_loop_state` — the bounded for-loop as an `Automatic.Poly` statement
  `Poly (fun a => verdict (round^[a.2.length] a.1))`, from one genuine hypothesis: the **size
  invariance** of the round map inside the polynomial ball.  This is exactly what the per-round
  dyadic snap with its height reset (`hasHeight_snapAbs`) buys; without it the encoding grows
  exponentially, which is the phase-6 obstruction.  The iteration condition is *proved*, not
  assumed.  §3 also gives the canonical shape `sizes = C * (X + 1)`.
* §4 `poly_simulate_count`, `ho_of_loop`, `ho_of_fixed_rounds`, `solution_of_loop` — the simulate
  function in the closing forms' shape, the **verbatim `ho`**, and `d9f601e5`
  (`SolutionStatement`) from `SoundεOnBracket o` plus per-round data.
* §5 what is, and is not, automatic here.
* §6 axiom audit.

Interfaces of the compiled library used (all from `Solutions/Check_brick_finish_line.lean` and
`Definitions/Def_QuantumMaxCutFiniteNumericRuntime`):

* `Automatic.Poly f = Nonempty (PolyProgram enc enc f)` — a `Prop`;
* `PolyProgram.comp P Q : PolyProgram ea ec (g ∘ f)` — `P` first, then `Q`;
* `PolyProgram.loop P g iterations sizes h` — repeat the `β ⊕ α`-valued body `P` while it returns
  `inr` (`inr` = one more round, `inl` = done), at most `iterations` times, every intermediate
  state of encoded length `≤ sizes`, both evaluated at the encoded length of the initial state;
* `encodeLoop ea eb : β ⊕ α → List Bool` — `ea` encodes the **state** (`inr`), `eb` the output
  (`inl`); `injectLeft`/`injectRight` are the two tagged copies.
-/

open scoped BigOperators
open Matrix
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.SimPoly

/-! ## 1.  Unfolding a fixed number of rounds -/

/-- **`Poly` is closed under a numeral number of iterations.**  Each fold is one `comp`, so the
program is a chain of `n` copies of the round machine and the time polynomial is the library's
`compTime` recursion.  No hypothesis beyond the one round. -/
theorem poly_iterate {α : Type} [Coding α] {round : α → α}
    (hr : Automatic.Poly round) (n : ℕ) :
    Automatic.Poly (fun a => Nat.iterate round n a) := by
  induction n with
  | zero =>
      have h : (fun a => Nat.iterate round 0 a) = (id : α → α) := by
        funext a
        simp
      rw [h]
      exact Automatic.Poly.identity
  | succ k ih =>
      have h : (fun a => Nat.iterate round (k + 1) a) = fun a => round (Nat.iterate round k a) := by
        funext a
        exact Function.iterate_succ_apply' round k a
      rw [h]
      exact Automatic.Poly.comp hr ih

/-- The same in `Function.iterate` notation. -/
theorem poly_iterate' {α : Type} [Coding α] {round : α → α}
    (hr : Automatic.Poly round) (n : ℕ) :
    Automatic.Poly (round^[n]) := poly_iterate hr n

/-! ## 2.  The round loop as one `PolyProgram` body

`PolyProgram.loop` wants a body `σ → β ⊕ σ`: `inr` = "one more round", `inl` = "done, here is the
verdict".  The state carries a fuel list, one round per bit, so the loop is a `for` loop with a
shrinking fuel cell and no condition on the round map other than size-invariance. -/

section LoopBody

variable {σ : Type} [Coding σ]

/-- The encoding of the loop state `σ × List Bool`: the library's `encodePair` of the state
encoding and the encoding of the fuel list.  It is definitionally the `Coding` instance of the
product type. -/
abbrev encSt : σ × List Bool → List Bool :=
  encodePair (enc : σ → List Bool) (enc : List Bool → List Bool)

/-- **The round loop.**  One round per fuel bit; at `[]` report `verdict`, so `f.length + 1` body
calls from `(s, f)`. -/
def loopBody (round : σ → σ) (verdict : σ → Bool) : σ × List Bool → Bool ⊕ (σ × List Bool) :=
  fun x => if x.2.isEmpty then Sum.inl (verdict x.1) else Sum.inr (round x.1, x.2.tail)

/-- **The loop body is a `Poly` program.**  Everything is an explicit `comp` chain (the library's
`fun_prop` automation does not handle `Prod.fst`/`List.getD` chains here): the fuel test is
`listIsEmpty`, the decrement is `listTail`, and the two `Sum` injections are the compiled
`injectLeft`/`injectRight`, which prepend the tag bit. -/
theorem poly_loopBody (round : σ → σ) (verdict : σ → Bool)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict) :
    Nonempty (PolyProgram encSt (encodeLoop encSt (enc : Bool → List Bool))
      (loopBody round verdict)) := by
  classical
  obtain ⟨Pr⟩ := hr
  obtain ⟨Pv⟩ := hv
  have hz : PolyProgram encSt encodeBool (fun x : σ × List Bool => x.2.isEmpty) :=
    (PolyProgram.snd (enc : σ → List Bool) (enc : List Bool → List Bool)).comp
      (PolyProgram.listIsEmpty (enc : Bool → List Bool))
  have hr' : PolyProgram encSt (enc : σ → List Bool) (fun x : σ × List Bool => round x.1) :=
    (PolyProgram.fst (enc : σ → List Bool) (enc : List Bool → List Bool)).comp Pr
  have htail : PolyProgram encSt (enc : List Bool → List Bool)
      (fun x : σ × List Bool => x.2.tail) :=
    (PolyProgram.snd (enc : σ → List Bool) (enc : List Bool → List Bool)).comp
      (PolyProgram.listTail (enc : Bool → List Bool) false)
  have hstep : PolyProgram encSt encSt (fun x : σ × List Bool => (round x.1, x.2.tail)) :=
    PolyProgram.fanout hr' htail
  have hcont : PolyProgram encSt (encodeLoop encSt (enc : Bool → List Bool))
      (fun x : σ × List Bool => Sum.inr (round x.1, x.2.tail)) :=
    hstep.comp (PolyProgram.injectRight (α := σ × List Bool) (β := Bool) encSt
      (enc : Bool → List Bool))
  have hstop : PolyProgram encSt (encodeLoop encSt (enc : Bool → List Bool))
      (fun x : σ × List Bool => Sum.inl (verdict x.1)) :=
    ((PolyProgram.fst (enc : σ → List Bool) (enc : List Bool → List Bool)).comp Pv).comp
      (PolyProgram.injectLeft (α := σ × List Bool) (β := Bool) encSt (enc : Bool → List Bool))
  have hbody : PolyProgram encSt (encodeLoop encSt (enc : Bool → List Bool))
      (fun x : σ × List Bool =>
        if x.2.isEmpty = true then Sum.inl (verdict x.1) else Sum.inr (round x.1, x.2.tail)) :=
    PolyProgram.ite hz hcont hstop
  refine ⟨hbody.congr (loopBody round verdict) ?_⟩
  intro x
  cases hb : x.2.isEmpty <;> simp [loopBody, hb]

/-- **The loop terminates and the count is right.**  From `(s, f)` the body is called `f.length + 1`
times, provided the encoding of every intermediate state stays under `S`.  This is the hypothesis
`PolyProgram.loop` asks for, in the form a consumer proves by induction on the fuel alone — no
mathematics about the round map. -/
theorem boundedRun_loopBody (round : σ → σ) (verdict : σ → Bool) (S : ℕ)
    (hS : ∀ (s : σ) (f : List Bool),
      (encSt (s, f)).length ≤ S → (encSt (round s, f.tail)).length ≤ S)
    (s : σ) (f : List Bool) (hs : (encSt (s, f)).length ≤ S) :
    ∃ n ≤ f.length + 1, BoundedRun encSt (loopBody round verdict) S n (s, f)
      (verdict (round^[f.length] s)) := by
  induction f generalizing s with
  | nil =>
      refine ⟨1, by simp, BoundedRun.stop hs ?_⟩
      simp [loopBody]
  | cons a f ih =>
      have hb : loopBody round verdict (s, a :: f) = Sum.inr (round s, f) := by
        simp [loopBody]
      obtain ⟨n, hn, hrun⟩ := ih (round s) (hS s (a :: f) hs)
      refine ⟨n + 1, ?_, ?_⟩
      · simp only [List.length_cons]
        omega
      · have hstep := BoundedRun.step (ea := encSt) (f := loopBody round verdict) hs hb hrun
        simp only [List.length_cons]
        rw [Function.iterate_succ_apply]
        exact hstep

end LoopBody

/-! ## 3.  The bounded for-loop as an `Automatic.Poly` statement

`PolyProgram.loop` is a *machine* combinator: it asks for a polynomial iteration bound and a
polynomial size bound, both evaluated at the encoded length of the loop's **initial state**.  §3
turns that into the statement a mathematician can use.  Of the two side conditions, the iteration
one is **proved** here (`iterations = X + 1` suffices because `f.length ≤ (encSt (s,f)).length`),
so only the size invariance of the round map is left as a hypothesis — which is exactly the ledger's
per-round height reset.  Neither condition has any content about what the round computes. -/

section Loop

variable {σ : Type} [Coding σ]

/-- **The bounded round loop is `Poly`.**  The fuel list says how many rounds are left, so the output
is `verdict` after exactly `fuel.length` rounds. -/
theorem poly_loop_state (round : σ → σ) (verdict : σ → Bool)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (hsize : ∀ a x : σ × List Bool, (encSt x).length ≤ sizes.eval (encSt a).length →
      (encSt (round x.1, x.2.tail)).length ≤ sizes.eval (encSt a).length)
    (hsize0 : ∀ a : σ × List Bool, (encSt a).length ≤ sizes.eval (encSt a).length) :
    Nonempty (PolyProgram encSt encodeBool
      (fun a : σ × List Bool => verdict (Nat.iterate round a.2.length a.1))) := by
  classical
  have hiter : ∀ a : σ × List Bool,
      a.2.length + 1 ≤ (Polynomial.X + 1 : Polynomial ℕ).eval (encSt a).length := by
    intro a
    have h1 : a.2.length ≤ (encodeList (enc : Bool → List Bool) a.2).length :=
      EncodedList.length_le (enc : Bool → List Bool) a.2
    have h2 : (encSt a).length
        = 2 * (enc a.1).length + 1 + (encodeList (enc : Bool → List Bool) a.2).length :=
      encodePair_length (enc : σ → List Bool) (enc : List Bool → List Bool) a
    have h3 : (Polynomial.X + 1 : Polynomial ℕ).eval (encSt a).length = (encSt a).length + 1 := by
      simp [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    omega
  have hbound : ∀ a : σ × List Bool,
      ∃ n ≤ (Polynomial.X + 1 : Polynomial ℕ).eval (encSt a).length,
        BoundedRun encSt (loopBody round verdict) (sizes.eval (encSt a).length) n a
          (verdict (Nat.iterate round a.2.length a.1)) := by
    intro a
    obtain ⟨n, hn, hrun⟩ :=
      boundedRun_loopBody round verdict (sizes.eval (encSt a).length)
        (fun s f h => hsize a (s, f) h) a.1 a.2 (hsize0 a)
    exact ⟨n, hn.trans (hiter a), hrun⟩
  exact ⟨(poly_loopBody round verdict hr hv).some.loop
    (fun a : σ × List Bool => verdict (Nat.iterate round a.2.length a.1))
    (Polynomial.X + 1) sizes hbound⟩

/-- `poly_loop_state` in `Automatic.Poly` form (the encodings agree definitionally). -/
theorem poly_loop_state' (round : σ → σ) (verdict : σ → Bool)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (hsize : ∀ a x : σ × List Bool, (encSt x).length ≤ sizes.eval (encSt a).length →
      (encSt (round x.1, x.2.tail)).length ≤ sizes.eval (encSt a).length)
    (hsize0 : ∀ a : σ × List Bool, (encSt a).length ≤ sizes.eval (encSt a).length) :
    Automatic.Poly (fun a : σ × List Bool => verdict (Nat.iterate round a.2.length a.1)) :=
  poly_loop_state round verdict hr hv sizes hsize hsize0

/-- **The canonical polynomial.**  `sizes = C * (X + 1)` with `1 ≤ C`: the size condition becomes the
monomial `C * ((encSt a).length + 1)` shape the certsize bookkeeping produces, and `sizes`' own
side condition is then free. -/
theorem poly_loop_state_class (round : σ → σ) (verdict : σ → Bool)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (C : ℕ) (hC : 1 ≤ C)
    (hsize : ∀ a x : σ × List Bool,
      (encSt x).length ≤ C * ((encSt a).length + 1) →
        (encSt (round x.1, x.2.tail)).length ≤ C * ((encSt a).length + 1)) :
    Nonempty (PolyProgram encSt encodeBool
      (fun a : σ × List Bool => verdict (Nat.iterate round a.2.length a.1))) := by
  refine poly_loop_state round verdict hr hv ((C : Polynomial ℕ) * (Polynomial.X + 1)) ?_ ?_
  · intro a x hx
    have e : ((C : Polynomial ℕ) * (Polynomial.X + 1)).eval (encSt a).length
        = C * ((encSt a).length + 1) := by
      simp [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
        Polynomial.eval_natCast]
    rw [e] at hx ⊢
    exact hsize a x hx
  · intro a
    have e : ((C : Polynomial ℕ) * (Polynomial.X + 1)).eval (encSt a).length
        = C * ((encSt a).length + 1) := by
      simp [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
        Polynomial.eval_natCast]
    rw [e]
    have h1 : (encSt a).length + 1 ≤ C * ((encSt a).length + 1) :=
      calc (encSt a).length + 1 = 1 * ((encSt a).length + 1) := by rw [Nat.one_mul]
        _ ≤ C * ((encSt a).length + 1) := Nat.mul_le_mul_right _ hC
    omega

/-- **The simulate function, in the closing forms' shape.**  A `Poly` initial state, a `Poly` fuel
list (one round per bit), one `Poly` round, one `Poly` verdict and the loop accounting; the output is
the verdict after `(fuel a).length` rounds.  This is the function the closing form
`solution_of_bracket_program` wants for its `sim`. -/
theorem poly_simulate_count {α : Type} [Coding α]
    (init : α → σ) (fuel : α → List Bool) (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hfuel : Automatic.Poly fuel)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (hsize : ∀ a x : σ × List Bool, (encSt x).length ≤ sizes.eval (encSt a).length →
      (encSt (round x.1, x.2.tail)).length ≤ sizes.eval (encSt a).length)
    (hsize0 : ∀ a : σ × List Bool, (encSt a).length ≤ sizes.eval (encSt a).length) :
    Automatic.Poly (fun a : α => verdict (Nat.iterate round (fuel a).length (init a))) :=
  ⟨(Automatic.Poly.pair hinit hfuel).program.comp
    (poly_loop_state round verdict hr hv sizes hsize hsize0).some⟩

/-- `poly_simulate_count` at the canonical `sizes = C * (X + 1)`. -/
theorem poly_simulate_count_class {α : Type} [Coding α]
    (init : α → σ) (fuel : α → List Bool) (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hfuel : Automatic.Poly fuel)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (C : ℕ) (hC : 1 ≤ C)
    (hsize : ∀ a x : σ × List Bool,
      (encSt x).length ≤ C * ((encSt a).length + 1) →
        (encSt (round x.1, x.2.tail)).length ≤ C * ((encSt a).length + 1)) :
    Automatic.Poly (fun a : α => verdict (Nat.iterate round (fuel a).length (init a))) :=
  ⟨(Automatic.Poly.pair hinit hfuel).program.comp
    (poly_loop_state_class round verdict hr hv C hC hsize).some⟩

end Loop

/-! ## 4.  The verbatim `ho`, and `d9f601e5`

The closing form `solution_of_bracket_verdict` (from `Check_brick_finish_line`) asks for

    o          : Input → ℚ → Bool
    SoundεOnBracket o
    ho         : Automatic.Poly (fun p : ((Input × List Bool) × ℚ) => o p.1.1 p.2)

§4 produces the third from per-round data plus `hspec`, the (analytic) statement that the loop's
output is `o`.  Note the tape: `o` does not see the random tape `p.1.2`, while `ho`'s program may
use it; `hspec` is where the simulation's tape-independence is discharged.  (The tape is also the
obvious choice of fuel list, since it is already part of the input.) -/

section Closing

open QuantumMaxCutEnergy

variable {σ : Type} [Coding σ]

/-- The request coding of the leaf, definitionally as in `Check_brick_finish_line` (its
`instRequestCoding`): the closing forms are stated with `encodeRequest`, so the same instance must
be used here or `ho` would be about a different encoding. -/
local instance instRequestCodingSimPoly : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-- **The verbatim `ho`.**  Given the simulate's pieces and the pointwise identification of the
loop's output with `o`, the closing hypothesis of `solution_of_ho` is a theorem. -/
theorem ho_of_loop
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hfuel : Automatic.Poly fuel)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (hsize : ∀ a x : σ × List Bool, (encSt x).length ≤ sizes.eval (encSt a).length →
      (encSt (round x.1, x.2.tail)).length ≤ sizes.eval (encSt a).length)
    (hsize0 : ∀ a : σ × List Bool, (encSt a).length ≤ sizes.eval (encSt a).length)
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hspec : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      verdict (Nat.iterate round (fuel p).length (init p)) = o p.1.1 p.2) :
    Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2) :=
  QMCLeafB.FinishLine.poly_of_pointwise
    (poly_simulate_count init fuel round verdict hinit hfuel hr hv sizes hsize hsize0) hspec

/-- **The fixed-numeral form.**  If the round count is a literal `n` — a bound extracted from the
boundary and used as a constant — then §1 gives the verbatim `ho` with no fuel, no size bound and no
iteration accounting at all.  This is the cheapest route to `ho` for anyone who can fix the round
count up front, and the only route when the count cannot be tied to the input's encoded length. -/
theorem ho_of_fixed_rounds
    (n : ℕ) (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hspec : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      verdict (Nat.iterate round n (init p)) = o p.1.1 p.2) :
    Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2) :=
  QMCLeafB.FinishLine.poly_of_pointwise
    (Automatic.Poly.comp hv (Automatic.Poly.comp (poly_iterate hr n) hinit)) hspec

/-- **`d9f601e5` from one round.**  `SolutionStatement` — the leaf's sentence, verbatim from
`Check_brick_finish_line` — follows from soundness of `o` on the driver's bracket, one `Poly` round,
and the size accounting of the loop.  Nothing else. -/
theorem solution_of_loop
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hfuel : Automatic.Poly fuel)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (hsize : ∀ a x : σ × List Bool, (encSt x).length ≤ sizes.eval (encSt a).length →
      (encSt (round x.1, x.2.tail)).length ≤ sizes.eval (encSt a).length)
    (hsize0 : ∀ a : σ × List Bool, (encSt a).length ≤ sizes.eval (encSt a).length)
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hspec : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      verdict (Nat.iterate round (fuel p).length (init p)) = o p.1.1 p.2)
    (hsound : QMCLeafB.FinishLine.SoundεOnBracket o) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinishLine.solution_of_bracket_verdict o hsound
    (ho_of_loop init fuel round verdict hinit hfuel hr hv sizes hsize hsize0 o hspec)

end Closing

/-! ## 5.  What is, and is not, automatic here

Four warnings for whoever instantiates this, all checked in the real environment:

1. **The loop counter must be a list, not a `ℕ`.**  `PolyProgram.loop`'s `iterations` is a
   polynomial evaluated at the *encoded length of the state*, and `Nat.bits` is logarithmic:
   `(Nat.bits 4).length = 3` (`decide`), `(Nat.bits n).length = log2 n + 1`.  So a `ℕ` counter in the
   state is exponentially larger than its own encoding, and *no* polynomial `iterations` dominates
   it — an earlier version of this file used `σ × ℕ` and its iteration hypothesis, though true as a
   statement, was not satisfiable.  With fuel as a `List Bool` the count condition is a theorem:
   `f.length ≤ (encSt (s,f)).length`, hence `iterations = X + 1` always works.
2. **The fuel must still be produced by a `Poly` program**, and its length is the number of rounds.
   `List.replicate T ()` is *not* available for free: unary expansion is not poly-time in this
   library's fragment (`Nat.bits` has length `log`, and a list of length `T` can have length up to
   the input length, so the program must go through `listFold` over the bits with a linear size
   bound).  The cheap choices are: the random tape `p.1.2` (already a `List Bool` in the input), or
   a numeral count via `ho_of_fixed_rounds`.  Note a trap if you take the tape: `Automatic.Poly` on
   `Input × List Bool` uses `encodeRequest`, not `encodePair`, so the generic `Poly.snd` does not
   apply at that type and the projection has to be built at the `PolyProgram`/`recode` level.
3. **`sizes` must hold along the run, not just at the start.**  `hsize` quantifies over all `x`
   inside the ball of radius `sizes.eval (encSt a).length`, which is exactly the ledger's height
   reset: the per-round dyadic snap keeps `(encSt x).length` inside a fixed monomial.  Without the
   snap no polynomial `sizes` exists (the phase-6 obstruction).
4. **The verdict must be tape-independent.**  `o : Input → ℚ → Bool` does not see `p.1.2`, while the
   program may use it; `hspec` is the (analytic) statement that the loop's output does not depend on
   the tape.

Axiom audit below: every declaration depends on `[propext, Classical.choice, Quot.sound]` only, and
there is no `sorry`. -/

/-! ## 6.  Axiom audit -/

#print axioms QMCLeafB.SimPoly.poly_iterate
#print axioms QMCLeafB.SimPoly.poly_iterate'
#print axioms QMCLeafB.SimPoly.poly_loopBody
#print axioms QMCLeafB.SimPoly.boundedRun_loopBody
#print axioms QMCLeafB.SimPoly.poly_loop_state
#print axioms QMCLeafB.SimPoly.poly_loop_state'
#print axioms QMCLeafB.SimPoly.poly_loop_state_class
#print axioms QMCLeafB.SimPoly.poly_simulate_count
#print axioms QMCLeafB.SimPoly.poly_simulate_count_class

section Audit

open QuantumMaxCutEnergy

local instance instRequestCodingAudit : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

#print axioms QMCLeafB.SimPoly.ho_of_loop
#print axioms QMCLeafB.SimPoly.ho_of_fixed_rounds
#print axioms QMCLeafB.SimPoly.solution_of_loop

#check @QMCLeafB.SimPoly.ho_of_loop
#check @QMCLeafB.SimPoly.ho_of_fixed_rounds
#check @QMCLeafB.SimPoly.solution_of_loop
#check @QMCLeafB.SimPoly.poly_loop_state_class
#check @QMCLeafB.SimPoly.poly_simulate_count_class

end Audit

end QMCLeafB.SimPoly


