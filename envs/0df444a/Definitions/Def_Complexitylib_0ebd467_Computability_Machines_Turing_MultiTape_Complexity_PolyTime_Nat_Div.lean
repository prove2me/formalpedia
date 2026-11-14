-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Div
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Div
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:54:50.798849+00:00
-- url     : https://prove2.me/theorems/5f132302-5267-484a-85b0-99b9aa0499f6
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div — Division and remainder of unary counters
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   A quotient/remainder loop scans the unary dividend and captures the divisor. One invariant
--   proves its arithmetic specification and the linear bound on encoded intermediate states,
--   including divisor zero. The fixed-divisor interface follows by composition.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_divMod`: compute quotient and remainder.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_div`, `.unary_mod`: project either result.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_div_const`: division by a fixed natural.
--
--   ### References
--
--   The machine realization uses the invariant-based loop calculus in `PolyTime.Iteration`.
--
--   **Contents.** The module is published as a whole: 8 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Div`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Nat/Div.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Iteration
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Plain

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Division and remainder of unary counters

A quotient/remainder loop scans the unary dividend and captures the divisor. One invariant
proves its arithmetic specification and the linear bound on encoded intermediate states,
including divisor zero. The fixed-divisor interface follows by composition.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_divMod`: compute quotient and remainder.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_div`, `.unary_mod`: project either result.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_div_const`: division by a fixed natural.

## References

The machine realization uses the invariant-based loop calculus in `PolyTime.Iteration`.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- Compute both quotient and remainder with a runtime unary divisor. Division by zero returns
`(0, dividend)`, matching Lean's conventions. All intermediate counters have linear size. -/
theorem unary_divMod : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => (p.1 / p.2, p.1 % p.2))
    (encPair encUnary encUnary) (encPair encUnary encUnary) := by
  let step (divisor : ℕ) (state : ℕ × ℕ) :=
    if state.2 + 1 == divisor then (state.1 + 1, 0) else (state.1, state.2 + 1)
  have hstep : ComputableTidilyInPolyTime (fun p : ℕ × (ℕ × ℕ) => step p.1 p.2)
      (encPair encUnary (encPair encUnary encUnary)) (encPair encUnary encUnary) := by
    unfold step
    fun_prop
  obtain ⟨hefficient, hspec⟩ := iterateWith_spec (par := Prod.snd) (count := Prod.fst)
    (init := fun _ => (0, 0)) (encIn := encPair encUnary encUnary)
    (snd encUnary encUnary) (fst encUnary encUnary) (const (0, 0)) hstep
    (fun p i state => i = p.2 * state.1 + state.2 ∧ state.1 ≤ i ∧
      (p.2 = 0 → state.1 = 0) ∧ (0 < p.2 → state.2 < p.2))
    (fun _ => by simp) (fun p i state _ h => by
      dsimp only [step]
      split <;> rename_i htest
      · have heq : state.2 + 1 = p.2 := by simpa using htest
        exact ⟨by nlinarith [h.1], by lia, by lia, by lia⟩
      · have hne : state.2 + 1 ≠ p.2 := by simpa using htest
        exact ⟨by nlinarith [h.1], by lia, h.2.2.1, fun hpos => by
          have := h.2.2.2 hpos
          lia⟩)
    (size := fun p => 3 * p.1 + 1) (polyBounded (by fun_prop)) (fun _ i state hi h => by
      simp only [length_encPair, encUnary_apply, List.length_replicate]
      nlinarith [h.1, h.2.1])
  have hresult (p : ℕ × ℕ) : (step p.2)^[p.1] (0, 0) = (p.1 / p.2, p.1 % p.2) := by
    have h := hspec p
    have hquot : ((step p.2)^[p.1] (0, 0)).1 = p.1 / p.2 := by
      rcases Nat.eq_zero_or_pos p.2 with hzero | hpos
      · simpa only [hzero, Nat.div_zero] using h.2.2.1 hzero
      · symm
        apply Nat.div_eq_of_lt_le <;> nlinarith [h.1, h.2.2.2 hpos]
    apply Prod.ext hquot
    have := Nat.mod_add_div p.1 p.2
    nlinarith [h.1]
  simpa only [hresult] using hefficient

/-- Division of two unary counters. -/
@[fun_prop]
theorem unary_div : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 / p.2)
    (encPair encUnary encUnary) encUnary := unary_divMod.fst'

/-- Remainder of two unary counters. -/
@[fun_prop]
theorem unary_mod : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 % p.2)
    (encPair encUnary encUnary) encUnary := unary_divMod.snd'

/-- Division by a fixed natural is a special case of runtime unary division. -/
@[fun_prop]
theorem unary_div_const (divisor : ℕ) :
    ComputableTidilyInPolyTime (fun n : ℕ => n / divisor) encUnary encUnary :=
  unary_div.comp (id'.prod (const divisor))

end Turing.MultiTapeTM.ComputableTidilyInPolyTime

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Division of two unary counters, including divisor zero. -/
@[fun_prop]
theorem unary_div : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 / p.2)
    (encPair encUnary encUnary) encUnary :=
  .of_tidy ComputableTidilyInPolyTime.unary_div

/-- Remainder of two unary counters, including divisor zero. -/
@[fun_prop]
theorem unary_mod : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 % p.2)
    (encPair encUnary encUnary) encUnary :=
  .of_tidy ComputableTidilyInPolyTime.unary_mod

/-- Compute both quotient and remainder with a runtime unary divisor. Division by zero returns
`(0, dividend)`, matching Lean's conventions. All intermediate counters have linear size. -/
theorem unary_divMod : ComputableInPolyTime (fun p : ℕ × ℕ => (p.1 / p.2, p.1 % p.2))
    (encPair encUnary encUnary) (encPair encUnary encUnary) :=
  .of_tidy (ComputableTidilyInPolyTime.unary_divMod)

/-- Division by a fixed natural is a special case of runtime unary division. -/
@[fun_prop]
theorem unary_div_const (divisor : ℕ) :
    ComputableInPolyTime (fun n : ℕ => n / divisor) encUnary encUnary :=
  .of_tidy (ComputableTidilyInPolyTime.unary_div_const (divisor := divisor))

end Turing.MultiTapeTM.ComputableInPolyTime


