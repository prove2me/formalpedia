-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_TidyNormalForm
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_TidyNormalForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:38:22.651166+00:00
-- url     : https://prove2.me/theorems/3bf6b6cc-5562-4aae-b2fe-257fe75c33f3
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm — The tidy normal form
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Every computation can be made tidy (`Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace`) at a
--   linear cost in time and space: `tidy m₀ m₁ tm` runs `tm` with every work tape shadowed
--   (`Turing.MultiTapeTM.shadow`), then clears each work tape along its shadow
--   (`Turing.MultiTapeTM.clearShadowed`), and finally rewinds the input head
--   (`Turing.MultiTapeTM.rewindInput`); the symbols `m₀ ≠ m₁` mark the shadows. A computation of `tm`
--   within `t` steps and `s` cells becomes a tidy computation of `tidy m₀ m₁ tm` within
--   `2 t + 3 s + 2 k + 4` steps (`ComputesInTimeAndSpace.computesTidily_tidy`). So tidiness, which
--   makes machines composable, is no restriction on what is computable within given resources up to
--   constant factors (`ComputableInTimeAndSpace.exists_computableTidilyInTimeAndSpace`).
--
--   The shadow tapes are needed because a work tape may hold blanks among the cells `tm` has written:
--   sweeping until the first blank would not find them all.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.clearList`: clear a list of work tapes along their shadows.
--   * `Turing.MultiTapeTM.tidy`: the tidy normal form of a machine.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.exists_runPath_tidy`: the run path of `tidy m₀ m₁ tm` when `tm` halts.
--   * `Turing.MultiTapeTM.ComputesInTimeAndSpace.computesTidily_tidy`: `tidy m₀ m₁ tm` computes
--     tidily what `tm` computes.
--   * `Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_computableTidilyInTimeAndSpace`: computable
--     functions are tidily computable.
--
--   **Contents.** The module is published as a whole: 1 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_TidyNormalForm`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Combinators/TidyNormalForm.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

-- upstream: candidate (coordinate with crei on #611)

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelNormalForm
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_ClearShadowed
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_ExtendTapes
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_RewindInput
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Sequential
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Tidy_Defs
public import Definitions.Def_Cslib_254e30e_Foundations_Data_Fin_Tuple
public import Mathlib.Data.Finite.Sum
public import Mathlib.Data.Fin.Tuple.Embedding
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_ExtendTapesView
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The tidy normal form

Every computation can be made tidy (`Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace`) at a
linear cost in time and space: `tidy m₀ m₁ tm` runs `tm` with every work tape shadowed
(`Turing.MultiTapeTM.shadow`), then clears each work tape along its shadow
(`Turing.MultiTapeTM.clearShadowed`), and finally rewinds the input head
(`Turing.MultiTapeTM.rewindInput`); the symbols `m₀ ≠ m₁` mark the shadows. A computation of `tm`
within `t` steps and `s` cells becomes a tidy computation of `tidy m₀ m₁ tm` within
`2 t + 3 s + 2 k + 4` steps (`ComputesInTimeAndSpace.computesTidily_tidy`). So tidiness, which
makes machines composable, is no restriction on what is computable within given resources up to
constant factors (`ComputableInTimeAndSpace.exists_computableTidilyInTimeAndSpace`).

The shadow tapes are needed because a work tape may hold blanks among the cells `tm` has written:
sweeping until the first blank would not find them all.

## Main definitions

* `Turing.MultiTapeTM.clearList`: clear a list of work tapes along their shadows.
* `Turing.MultiTapeTM.tidy`: the tidy normal form of a machine.

## Main results

* `Turing.MultiTapeTM.exists_runPath_tidy`: the run path of `tidy m₀ m₁ tm` when `tm` halts.
* `Turing.MultiTapeTM.ComputesInTimeAndSpace.computesTidily_tidy`: `tidy m₀ m₁ tm` computes
  tidily what `tm` computes.
* `Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_computableTidilyInTimeAndSpace`: computable
  functions are tidily computable.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- **Computable functions are tidily computable**, at a linear cost: a function computable within
time `t` and space `s` is computable tidily within time `2 t + 3 s + c` and space `c (s + 1)`, for a
constant `c` that depends on the number of work tapes of the machine. -/
theorem ComputableInTimeAndSpace.exists_computableTidilyInTimeAndSpace {α β : Type*}
    {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {t s : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t s) :
    ∃ c, ComputableTidilyInTimeAndSpace f encIn encOut (fun a => 2 * t a + 3 * s a + c)
      (fun a => c * (s a + 1)) := by
  obtain ⟨k, State, hfin, tm, htm⟩ := h
  refine ⟨4 * k * k + 6 * k + 4, k + k, _, inferInstance, tidy false true tm, fun a =>
    ((htm a).computesTidily_tidy Bool.false_ne_true).mono
      (by beta_reduce; generalize 4 * k * k = m; omega) ?_⟩
  beta_reduce
  have e₁ : 2 * s a + 2 * k * (3 * s a + 2 * k + 3) = (6 * k + 2) * s a + (4 * k * k + 6 * k) := by
    ring
  have e₂ : (4 * k * k + 6 * k + 4) * (s a + 1) =
      (4 * k * k + 6 * k + 4) * s a + (4 * k * k + 6 * k + 4) := by ring
  have : (6 * k + 2) * s a ≤ (4 * k * k + 6 * k + 4) * s a :=
    Nat.mul_le_mul_right _ (by generalize 4 * k * k = m; omega)
  rw [e₁, e₂]
  exact Nat.add_le_add this (by generalize 4 * k * k = m; omega)

end Turing.MultiTapeTM


