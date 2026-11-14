-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Space
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Space
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:34:25.40813+00:00
-- url     : https://prove2.me/theorems/0e659e41-a992-4831-b53f-904491988b85
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Space — Every work tape costs a cell
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Space` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The additions of cslib PR #1138 to `Cslib.Computability.Machines.Turing.MultiTape.Space`: every
--   work head visits the cell it starts on, so a run path visits at least one cell per work tape, and a
--   space bound is at least the number of work tapes.
--
--   ### Main results
--
--   * `Turing.MultiTapeNTM.RunPath.le_space`: a run path visits at least `k` cells.
--   * `Turing.MultiTapeNTM.RunsInSpace.le`: a space bound is at least the number of work tapes.
--
--   **Contents.** The module is published as a whole: 2 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Space`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Space.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: submitted #1138 @b1635b2e

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Space

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Space` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Every work tape costs a cell

The additions of cslib PR #1138 to `Cslib.Computability.Machines.Turing.MultiTape.Space`: every
work head visits the cell it starts on, so a run path visits at least one cell per work tape, and a
space bound is at least the number of work tapes.

## Main results

* `Turing.MultiTapeNTM.RunPath.le_space`: a run path visits at least `k` cells.
* `Turing.MultiTapeNTM.RunsInSpace.le`: a space bound is at least the number of work tapes.
-/

@[expose] public section

namespace Turing.MultiTapeNTM

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}
variable {ntm : MultiTapeNTM k Symbol State}

namespace RunPath

/-- Every work head visits at least the cell it starts on, so a path visits at least `k` cells. -/
lemma le_space (p : ntm.RunPath input) : k ≤ p.space :=
  calc k = ∑ _ : Fin k, 1 := by rw [← Finset.card_eq_sum_ones, Finset.card_univ, Fintype.card_fin]
    _ ≤ p.space := Finset.sum_le_sum fun _ _ =>
      Finset.card_pos.mpr (Finset.univ_nonempty.image _)

end RunPath

/-- A space bound leaves room for every work tape: already the computation path that has not
moved yet visits one cell per tape. -/
lemma RunsInSpace.le {s : ℕ} (h : ntm.RunsInSpace input s) : k ≤ s :=
  RunPath.le_space _ |>.trans <| h ⟨RelSeries.singleton _ (ntm.initCfg input), rfl⟩

end Turing.MultiTapeNTM


