-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO_PolyTime
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO_PolyTime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:18.581991+00:00
-- url     : https://prove2.me/theorems/148a3c2a-af51-4298-92ca-f89b63933735
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime — Polynomial time as charged asymptotic bounds
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   A function computable in polynomial time is computable within charged bounds `O(T)` and `O(S)`
--   that are polynomial in the length of the encoded input. The time bound is the time of a realizing
--   machine; the space bound is the sum of its time and space, since the charged space also bounds the
--   length of the encoded output, which the machine's time bounds.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputableInPolyTime.exists_computableInO`: polynomial time gives
--     polynomial charged bounds.
--
--   **Contents.** The module is published as a whole: 1 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO_PolyTime`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/BigO/PolyTime.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO_Bounds
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_ResourceBounds_Polynomial
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_ResourceFacts

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Polynomial time as charged asymptotic bounds

A function computable in polynomial time is computable within charged bounds `O(T)` and `O(S)`
that are polynomial in the length of the encoded input. The time bound is the time of a realizing
machine; the space bound is the sum of its time and space, since the charged space also bounds the
length of the encoded output, which the machine's time bounds.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.exists_computableInO`: polynomial time gives
  polynomial charged bounds.
-/

namespace Turing.MultiTapeTM

variable {α β : Type*} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}

/-- **Polynomial time gives polynomial charged bounds**: a function computable in polynomial time is
computable within time `O(T)` and space `O(S)` for bounds polynomial in the length of the encoded
input, namely the time of a realizing machine and the sum of its time and space. -/
public theorem ComputableInPolyTime.exists_computableInO (h : ComputableInPolyTime f encIn encOut) :
    ∃ T S, PolyBounded (fun a => (encIn a).length) T ∧ PolyBounded (fun a => (encIn a).length) S ∧
      ComputableInO f encIn encOut T S := by
  obtain ⟨t, s, ht, hs, h⟩ := h
  exact ⟨_, _, .of_polynomiallyBounded _ ht,
    (PolyBounded.of_polynomiallyBounded _ ht).add (.of_polynomiallyBounded _ hs),
    .of_bounds h 1 (fun _ => by omega) (fun _ => by omega) fun a => by
      have := h.length_le a
      omega⟩

end Turing.MultiTapeTM


