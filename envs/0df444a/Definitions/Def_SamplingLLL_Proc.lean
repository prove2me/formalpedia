-- Prove2me | Definitions.Def_SamplingLLL_Proc
-- name    : SamplingLLL_Proc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:52:33.475175+00:00
-- url     : https://prove2.me/theorems/8ff64e51-e9d9-4321-b3ae-9e22cd6256d1
-- title:
--   Randomized procedures with tick and call counters
-- statement:
--   A procedure is a subdistribution on triples (output, ticks, calls). Sequential composition uses independent randomness and adds the counters. A loop is the increasing limit of its fuel-bounded unfoldings, where running out of fuel has mass $0$, so the total mass of a procedure is its probability of termination, and its output law and its expected ticks and calls are read off the same object. A fair bit costs one tick. The cap of p.25 replaces every outcome above $T$ ticks by a default output with exactly $T$ ticks.
--
--   This is the cost model of the mission's running-time statements. Loops of the sampler terminate only almost surely, which is why a procedure is not a probability mass function.
--
--   **Formalization Note** Ticks and calls are the only counted resources. Every charge is made explicitly by the procedures that follow.
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), the paper names no machine; "bit operations", p.10; "Cap the total work", p.25

import Mathlib

set_option autoImplicit false

open scoped ENNReal

namespace SamplingLLL

/-- A randomized procedure as a subdistribution on (output, ticks, calls). Loops of the sampler
terminate only almost surely, so a procedure is a mass function, not a `PMF`: termination, law and
expectations are read off one object (`mass`, `law`, `expTicks`, `expCalls`).

Source of the semantics: Achlioptas, STOC 2027 submission (manuscript sha256 7a943167…); the paper
names no machine ("bit operations", p.10). -/
def Proc (α : Type) : Type := α × ℕ × ℕ → ℝ≥0∞

namespace Proc

open Classical in
/-- Point mass at output `a` with zero counters. -/
noncomputable def ret {α : Type} (a : α) : Proc α := fun r => if r = (a, 0, 0) then 1 else 0

/-- Sequential composition; independent randomness, counters add. -/
noncomputable def seq {α β : Type} (p : Proc α) (f : α → Proc β) : Proc β := fun r =>
  ∑' s : α × ℕ × ℕ, p s *
    if s.2.1 ≤ r.2.1 ∧ s.2.2 ≤ r.2.2 then f s.1 (r.1, r.2.1 - s.2.1, r.2.2 - s.2.2) else 0

noncomputable instance : Monad Proc where
  pure := ret
  bind := seq

open Classical in
/-- Charge `k` ticks. -/
noncomputable def tick (k : ℕ) : Proc Unit := fun r => if r = ((), k, 0) then 1 else 0

open Classical in
/-- Count `k` recursive invocations (`k = 1` for a counted call). -/
noncomputable def countCall (k : ℕ) : Proc Unit := fun r => if r = ((), 0, k) then 1 else 0

/-- A fair bit, charged one tick. -/
noncomputable def flip : Proc Bool := fun r => if r.2 = (1, 0) then 2⁻¹ else 0

/-- A coin with a given real bias, no charge. Not used by the sampler: only analysis statements use
it, to replace a child coin by its exact law. -/
noncomputable def bernoulli (b : ℝ≥0∞) : Proc Bool := fun r =>
  if r.2 = (0, 0) then (if r.1 then b else 1 - b) else 0

/-- The fuel-bounded unfolding of a loop; fuel exhaustion has mass `0`. -/
noncomputable def loopFuel {β α : Type} (body : β → Proc (β ⊕ α)) : ℕ → β → Proc α
  | 0, _ => fun _ => 0
  | k + 1, b => seq (body b) fun
      | Sum.inl b' => loopFuel body k b'
      | Sum.inr a => ret a

/-- `loop body b`: run `body` until it returns `Sum.inr`. The pointwise supremum over fuel, an
increasing limit because fuel exhaustion has mass `0`. -/
noncomputable def loop {β α : Type} (body : β → Proc (β ⊕ α)) (b : β) : Proc α := fun r =>
  ⨆ k, loopFuel body k b r

/-- Total mass (the probability of termination). -/
noncomputable def mass {α : Type} (p : Proc α) : ℝ≥0∞ := ∑' r, p r

/-- The output law (marginal on the output, unnormalized if `p` has mass below `1`). -/
noncomputable def law {α : Type} (p : Proc α) (a : α) : ℝ≥0∞ := ∑' c : ℕ × ℕ, p (a, c)

/-- Expected ticks. -/
noncomputable def expTicks {α : Type} (p : Proc α) : ℝ≥0∞ := ∑' r, p r * (r.2.1 : ℝ≥0∞)

/-- Expected calls. -/
noncomputable def expCalls {α : Type} (p : Proc α) : ℝ≥0∞ := ∑' r, p r * (r.2.2 : ℝ≥0∞)

/-- The probability of an event on the output. -/
noncomputable def probOf {α : Type} (p : Proc α) (E : α → Prop) : ℝ≥0∞ :=
  by classical exact ∑' r, if E r.1 then p r else 0

open Classical in
/-- `capped T d p`: stop at `T` ticks. Outcomes within the cap are unchanged; every outcome over the
cap is replaced by the default output `d` with exactly `T` ticks (p.25: "Cap the total work"). -/
noncomputable def capped {α : Type} (T : ℕ) (d : α) (p : Proc α) : Proc α := fun r =>
  (if r.2.1 ≤ T then p r else 0) +
    if r = (d, T, 0) then ∑' s, (if T < s.2.1 then p s else 0) else 0

/-- The image law of a finite input measure under a kernel in `Proc`. -/
noncomputable def push {Ω α : Type} [Fintype Ω] (ρ : Ω → ℝ) (k : Ω → Proc α) (y : α) : ℝ≥0∞ :=
  ∑ x, ENNReal.ofReal (ρ x) * law (k x) y

/-- A row that charges no ticks (used to read the number of passes of a loop off its ticks). -/
def TickFree {α : Type} (p : Proc α) : Prop := ∀ r, p r ≠ 0 → r.2.1 = 0

end Proc

end SamplingLLL


