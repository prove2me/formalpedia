-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_TransformsTapes
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_TransformsTapes
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:35:46.56386+00:00
-- url     : https://prove2.me/theorems/c0eb06d5-0902-4f5f-92b5-368bca5d0125
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes — Tape transformations as runs
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   `Turing.MultiTapeTM.TransformsTapes` asks for a run path to the halted normal form within the time
--   and space bounds. Since a deterministic machine stays where it halted, this is the same as asking
--   that the run of exactly `t` steps ends in the normal form, using at most `s` cells: the form in
--   which Christian Reitwiessner's branch `crei/tidy-universal` states and proves its specifications.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.runFrom_nop_withState`: `nop` halts in one step from any configuration and
--     changes nothing else.
--   * `Turing.MultiTapeTM.transformsTapes_iff_runFrom`: a tape transformation, read on runs.
--
--   **Contents.** The module is published as a whole: 2 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_TransformsTapes`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Plumbing/TransformsTapes.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Plumbing/TransformsTapes.lean`; bridges the `runFrom` form of
-- `TransformsTapes` in crei:crei/tidy-universal @7f7c0696 to the run paths of cslib #1117)

public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_TransformsTapes
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_TapeLemmas

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Tape transformations as runs

`Turing.MultiTapeTM.TransformsTapes` asks for a run path to the halted normal form within the time
and space bounds. Since a deterministic machine stays where it halted, this is the same as asking
that the run of exactly `t` steps ends in the normal form, using at most `s` cells: the form in
which Christian Reitwiessner's branch `crei/tidy-universal` states and proves its specifications.

## Main results

* `Turing.MultiTapeTM.runFrom_nop_withState`: `nop` halts in one step from any configuration and
  changes nothing else.
* `Turing.MultiTapeTM.transformsTapes_iff_runFrom`: a tape transformation, read on runs.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {tm : MultiTapeTM k Symbol State}

/-- `nop` halts in one step from any configuration and changes nothing else. -/
theorem runFrom_nop_withState {input : List Symbol} (C : Cfg k Symbol State input) :
    (nop k Symbol).runFrom (C.withState (some ())) 1 = C.withState none := by
  rw [runFrom_one, step_of_state rfl]
  refine Cfg.ext (by simp [nop]) ?_ ?_ ?_ ?_
  · simp only [nop, tr_ofTr, Action.apply_inputPos, moveInputPos_zero, Cfg.withState]
  · funext j
    simp only [nop, tr_ofTr, Action.apply_workTapes, Cfg.withState]
  · funext j
    simp only [nop, tr_ofTr, Action.apply_workTapePos, SignType.coe_zero, add_zero, Cfg.withState]
  · simp only [nop, tr_ofTr, Action.apply_output, Option.toList_none, List.append_nil,
      Cfg.withState]

/-- **A tape transformation, read on runs.** `TransformsTapes tm P Q t s` holds exactly when, on
words `ws` satisfying `P`, the run of `t` steps ends in the halted normal form, holding words `ws'`
and having emitted `emitted` with `Q input ws ws' emitted`, and uses at most `s` cells. -/
theorem transformsTapes_iff_runFrom
    {P : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) →
      List Symbol → Prop} {t s : ℕ} :
    TransformsTapes tm P Q t s ↔ ∀ (input : List Symbol) (ws : Fin k → List Symbol)
      (out : List Symbol), P input ws → ∃ ws' emitted,
        tm.runFrom (wordsCfg input (some tm.q₀) ws out) t =
          wordsCfg input none ws' (out ++ emitted) ∧
        Q input ws ws' emitted ∧
          (MultiTapeNTM.RunPath.ofDeterministic tm (wordsCfg input (some tm.q₀) ws out) t).space ≤
            s := by
  refine forall₄_congr fun input ws out _ => exists₂_congr fun ws' emitted => ?_
  rw [exists_runPath_iff_runFrom rfl]
  tauto

end Turing.MultiTapeTM


