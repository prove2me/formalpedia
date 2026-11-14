-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Bounds
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Bounds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:23.268751+00:00
-- url     : https://prove2.me/theorems/e3c1b901-40ed-43c6-b831-f393958aec87
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds — Direct polynomial resource consequences
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   These rules retain a single realizing machine. Existence of cost and output degrees is obtained
--   from its actual polynomial clocks; it does not use a higher normal-form calculus.
--
--   ### Main results
--
--   * `ComputableInTimeAndSpace.computableInPolyTime`: polynomial time suffices at arbitrary space.
--   * `ComputableInPolyTime.exists_degree`: fixed resource and independent output degrees exist.
--
--   **Contents.** The module is published as a whole: 2 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Bounds`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Bounds.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_ResourceBounds
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_ResourceFacts

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Direct polynomial resource consequences

These rules retain a single realizing machine. Existence of cost and output degrees is obtained
from its actual polynomial clocks; it does not use a higher normal-form calculus.

## Main results

* `ComputableInTimeAndSpace.computableInPolyTime`: polynomial time suffices at arbitrary space.
* `ComputableInPolyTime.exists_degree`: fixed resource and independent output degrees exist.
-/

@[expose] public section
namespace Turing.MultiTapeTM

open Cslib

variable {α β : Type*} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}

/-- **A polynomial time bound alone suffices.** A function computable by some machine within a time
bound polynomial in the length of the encoded input, with any space bound, is computable in
polynomial time: within `t` steps the machine visits at most `c t + c` work-tape cells. -/
theorem ComputableInTimeAndSpace.computableInPolyTime {t : ℕ → ℕ} {s : α → ℕ}
    (ht : PolynomiallyBounded t)
    (h : ComputableInTimeAndSpace f encIn encOut (fun a => t (encIn a).length) s) :
    ComputableInPolyTime f encIn encOut :=
  let ⟨c, h⟩ := h.exists_space_linear
  ⟨t, fun n => c * t n + c, ht, by fun_prop, h⟩

/-- Every polynomial-time realization has fixed resource and output degrees. The output degree
comes from its clock; it is not identified with its workspace degree. -/
theorem ComputableInPolyTime.exists_degree (h : ComputableInPolyTime f encIn encOut) :
    ∃ d e, ComputableInDegree f encIn encOut d e := by
  obtain ⟨t, s, ht, hs, h⟩ := h
  obtain ⟨ct, dt, ht⟩ := polynomiallyBounded_iff_le.mp ht
  obtain ⟨cs, ds, hs⟩ := polynomiallyBounded_iff_le.mp hs
  have htime : DegreeBounded (fun a => (encIn a).length)
      (fun a => t (encIn a).length) dt := ⟨ct, fun a => ht _⟩
  have hspace : DegreeBounded (fun a => (encIn a).length)
      (fun a => s (encIn a).length) ds := ⟨cs, fun a => hs _⟩
  exact ⟨max dt ds, dt, ⟨⟨_, _, htime.mono_deg (le_max_left _ _),
    hspace.mono_deg (le_max_right _ _), h⟩, htime.mono h.length_le⟩⟩

end Turing.MultiTapeTM


