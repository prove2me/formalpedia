-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Iteration
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Iteration
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:53:58.83247+00:00
-- url     : https://prove2.me/theorems/5bbd94f6-7e06-4512-99d2-c805b3c603b2
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration — Polynomial-time iteration with invariants
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The loop count is computed in unary, so its value is polynomially bounded in the encoded input.
--   The caller certifies the step and bounds the encoded intermediate states. The specification
--   interface is adapted from `IsPolyTime.iterate_spec` in the cslib `crypto` branch.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterate`: iteration with a size bound.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterateWith`: the same bound with captured data.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterate_spec`: a loop invariant gives both
--     polynomial-time computation and the final postcondition.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterateWith_spec`: capture a computed parameter
--     while retaining a uniform joint certificate for the step.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterate_of_bounded_growth`: constant additive
--     state growth discharges intermediate-size obligations.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterateWith_of_bounded_growth`: captured loops
--     with a polynomial per-step growth bound depending on the original input.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterateWithInput_of_bounded_growth`: the same
--     growth contract with the original input captured directly, for certificate inference.
--
--   ### References
--
--   Adapted from Computability/Probabilistic/Iteration.lean on the cslib `crypto` branch at
--   `5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the tidy fold calculus and its
--   captured-input rules.
--
--   **Contents.** The module is published as a whole: 7 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Iteration`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Iteration.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeLoops
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Fold
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Plain

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Polynomial-time iteration with invariants

The loop count is computed in unary, so its value is polynomially bounded in the encoded input.
The caller certifies the step and bounds the encoded intermediate states. The specification
interface is adapted from `IsPolyTime.iterate_spec` in the cslib `crypto` branch.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterate`: iteration with a size bound.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterateWith`: the same bound with captured data.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterate_spec`: a loop invariant gives both
  polynomial-time computation and the final postcondition.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterateWith_spec`: capture a computed parameter
  while retaining a uniform joint certificate for the step.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterate_of_bounded_growth`: constant additive
  state growth discharges intermediate-size obligations.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterateWith_of_bounded_growth`: captured loops
  with a polynomial per-step growth bound depending on the original input.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterateWithInput_of_bounded_growth`: the same
  growth contract with the original input captured directly, for certificate inference.

## References

Adapted from Computability/Probabilistic/Iteration.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the tidy fold calculus and its
captured-input rules.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

variable {α β : Type} {encIn : α ↪ List Bool} {encState : β ↪ List Bool}

/-- Capture a computed parameter while bounding every intermediate loop state. -/
theorem iterateWith {π : Type} {encPar : π ↪ List Bool}
    {par : α → π} {count : α → ℕ} {init : α → β} {step : π → β → β}
    (hpar : ComputableTidilyInPolyTime par encIn encPar)
    (hcount : ComputableTidilyInPolyTime count encIn encUnary)
    (hinit : ComputableTidilyInPolyTime init encIn encState)
    (hstep : ComputableTidilyInPolyTime (fun p : π × β => step p.1 p.2)
      (encPair encPar encState) encState)
    {bound : α → ℕ} (hbound : PolyBounded (fun x => (encIn x).length) bound)
    (hstates : ∀ x, ∀ i ≤ count x,
      (encState ((step (par x))^[i] (init x))).length ≤ bound x) :
    ComputableTidilyInPolyTime (fun x => (step (par x))^[count x] (init x)) encIn encState := by
  have hlist : ComputableTidilyInPolyTime (fun x => List.replicate (count x) true)
      encIn encBits := hcount.of_enc_eq fun _ => rfl
  simpa only [List.foldl_const, List.length_replicate] using
    foldlWith (encA := encBool) (step := fun par state _ => step par state)
      hpar hlist hinit (hstep.comp (fst (encPair encPar encState) encBool)) hbound
      (fun x i _ => by
        simpa only [List.take_replicate, List.foldl_const, List.length_replicate] using
          hstates x (min i (count x)) (Nat.min_le_right _ _))

/-- A unary loop count and polynomially bounded intermediate states give a polynomial-time loop. -/
theorem iterate {count : α → ℕ} {init : α → β} {step : β → β}
    (hcount : ComputableTidilyInPolyTime count encIn encUnary)
    (hinit : ComputableTidilyInPolyTime init encIn encState)
    (hstep : ComputableTidilyInPolyTime step encState encState)
    {bound : α → ℕ} (hbound : PolyBounded (fun x => (encIn x).length) bound)
    (hstates : ∀ x, ∀ i ≤ count x, (encState (step^[i] (init x))).length ≤ bound x) :
    ComputableTidilyInPolyTime (fun x => step^[count x] (init x)) encIn encState :=
  iterateWith (step := fun (_ : Bool) => step) (const false) hcount hinit
    (hstep.comp (snd encBool encState)) hbound hstates

/-- Iteration may capture a computed parameter. The joint step certificate must be uniform
in that parameter; the invariant and size bound concern the original input. The bound need not
be computable and may use properties of the input beyond its encoded length. -/
theorem iterateWith_spec {π : Type} {encPar : π ↪ List Bool}
    {par : α → π} {count : α → ℕ} {init : α → β} {step : π → β → β}
    (hpar : ComputableTidilyInPolyTime par encIn encPar)
    (hcount : ComputableTidilyInPolyTime count encIn encUnary)
    (hinit : ComputableTidilyInPolyTime init encIn encState)
    (hstep : ComputableTidilyInPolyTime (fun p : π × β => step p.1 p.2)
      (encPair encPar encState) encState)
    (invariant : α → ℕ → β → Prop)
    (hbase : ∀ x, invariant x 0 (init x))
    (hpreserve : ∀ x i state, i < count x → invariant x i state →
      invariant x (i + 1) (step (par x) state))
    {size : α → ℕ} (hsize : PolyBounded (fun x => (encIn x).length) size)
    (hbound : ∀ x i state, i ≤ count x → invariant x i state →
      (encState state).length ≤ size x) :
    ComputableTidilyInPolyTime (fun x => (step (par x))^[count x] (init x)) encIn encState ∧
      ∀ x, invariant x (count x) ((step (par x))^[count x] (init x)) := by
  have htrace (x : α) (i : ℕ) (hi : i ≤ count x) :
      invariant x i ((step (par x))^[i] (init x)) := by
    induction i with
    | zero => exact hbase x
    | succ i ih =>
      simpa only [Function.iterate_succ_apply'] using
        hpreserve x i _ (by lia) (ih (by lia))
  exact ⟨iterateWith hpar hcount hinit hstep hsize
    (fun x i hi => hbound x i _ hi (htrace x i hi)), fun x => htrace x (count x) le_rfl⟩

/-- One invariant proves both the resource bound and the final loop postcondition. -/
theorem iterate_spec {count : α → ℕ} {init : α → β} {step : β → β}
    (hcount : ComputableTidilyInPolyTime count encIn encUnary)
    (hinit : ComputableTidilyInPolyTime init encIn encState)
    (hstep : ComputableTidilyInPolyTime step encState encState)
    (invariant : α → ℕ → β → Prop)
    (hbase : ∀ x, invariant x 0 (init x))
    (hpreserve : ∀ x i state, i < count x → invariant x i state →
      invariant x (i + 1) (step state))
    {size : α → ℕ} (hsize : PolyBounded (fun x => (encIn x).length) size)
    (hbound : ∀ x i state, i ≤ count x → invariant x i state →
      (encState state).length ≤ size x) :
    ComputableTidilyInPolyTime (fun x => step^[count x] (init x)) encIn encState ∧
      ∀ x, invariant x (count x) (step^[count x] (init x)) :=
  iterateWith_spec (step := fun (_ : Bool) => step) (const false) hcount hinit
    (hstep.comp (snd encBool encState)) invariant hbase hpreserve hsize hbound

/-- A captured loop may add a polynomial amount of storage per iteration, measured against the
original input. A bound depending only on the current state would not justify this rule. -/
theorem iterateWith_of_bounded_growth {π : Type} {encPar : π ↪ List Bool}
    {par : α → π} {count : α → ℕ} {init : α → β} {step : π → β → β}
    (hpar : ComputableTidilyInPolyTime par encIn encPar)
    (hcount : ComputableTidilyInPolyTime count encIn encUnary)
    (hinit : ComputableTidilyInPolyTime init encIn encState)
    (hstep : ComputableTidilyInPolyTime (fun p : π × β => step p.1 p.2)
      (encPair encPar encState) encState)
    {growth : α → ℕ} (hpoly : PolyBounded (fun x => (encIn x).length) growth)
    (hgrowth : ∀ x state, (encState (step (par x) state)).length ≤
      (encState state).length + growth x) :
    ComputableTidilyInPolyTime (fun x => (step (par x))^[count x] (init x)) encIn encState := by
  refine (iterateWith_spec hpar hcount hinit hstep
    (fun x i state => (encState state).length ≤ (encState (init x)).length + i * growth x)
    (by simp) ?_ (hinit.polyBounded_length.add (hcount.polyBounded.mul hpoly)) ?_).1
  · intro x i state _ hstate
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using
      (hgrowth x state).trans (Nat.add_le_add_right hstate _)
  · intro x i state hi hstate
    exact hstate.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _)

/-- An iteration step may capture its original input. Paired growth obligations let automation
select a common polynomial bound. The uniform joint step certificate charges the captured input
on every iteration; the growth bound need not itself be computable. -/
theorem iterateWithInput_of_bounded_growth {count : α → ℕ} {init : α → β} {step : α → β → β}
    (hcount : ComputableTidilyInPolyTime count encIn encUnary)
    (hinit : ComputableTidilyInPolyTime init encIn encState)
    (hstep : ComputableTidilyInPolyTime (fun p : α × β => step p.1 p.2)
      (encPair encIn encState) encState)
    {growth : α → ℕ} (hbound : PolyBounded (fun x => (encIn x).length) growth ∧
      ∀ x state, (encState (step x state)).length ≤ (encState state).length + growth x) :
    ComputableTidilyInPolyTime (fun x => (step x)^[count x] (init x)) encIn encState :=
  iterateWith_of_bounded_growth id' hcount hinit hstep hbound.1 hbound.2

/-- A loop with constant additive state growth has polynomially bounded intermediate states. -/
theorem iterate_of_bounded_growth {count : α → ℕ} {init : α → β} {step : β → β}
    (hcount : ComputableTidilyInPolyTime count encIn encUnary)
    (hinit : ComputableTidilyInPolyTime init encIn encState)
    (hstep : ComputableTidilyInPolyTime step encState encState)
    {growth : ℕ} (hgrowth : ∀ state, (encState (step state)).length ≤
      (encState state).length + growth) :
    ComputableTidilyInPolyTime (fun x => step^[count x] (init x)) encIn encState := by
  exact iterateWith_of_bounded_growth (step := fun (_ : Bool) => step)
    (const false) hcount hinit (hstep.comp (snd encBool encState)) (.const growth)
    (fun _ state => hgrowth state)

end Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-! ### Plain captured-input iteration -/


