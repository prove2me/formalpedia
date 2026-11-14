-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_ExtendTapesView
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_ExtendTapesView
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:29.665015+00:00
-- url     : https://prove2.me/theorems/32362207-6875-4b3b-bdf9-758b6b0da6e6
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapesView — The view of a configuration through a tape embedding
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapesView` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   For an embedding `e : Fin k ↪ Fin k'` of work tapes, `viewCfg e cfg` is the configuration of a
--   machine with `k` work tapes that sees the tapes `e j` of `cfg`. Placing it back with
--   `Turing.MultiTapeTM.embed` gives `cfg` (`embed_viewCfg`), so the run of `tm.extendTapes e` from
--   any configuration is the run of `tm` on the view, placed back (`runFrom_extendTapes`). This
--   generalises `Turing.MultiTapeTM.oneTapeCfg` and `Turing.MultiTapeTM.runFrom_tapeEmb` from one tape
--   to any embedding.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.viewCfg`: the view of a configuration through a tape embedding.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.runFrom_extendTapes`, `Turing.MultiTapeTM.space_extendTapes_le`: the run
--     and the space of a machine run on the tapes selected by an embedding.
--   * `Turing.MultiTapeTM.embed_castAdd`, `Turing.MultiTapeTM.embed_natAdd`,
--     `Turing.MultiTapeTM.embed_castSucc`: tape blocks as appended families.
--
--   **Contents.** The module is published as a whole: 7 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_ExtendTapesView`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Plumbing/ExtendTapesView.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Plumbing/ExtendTapes.lean`)

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_ExtendTapes
public import Definitions.Def_Cslib_254e30e_Foundations_Data_Fin_Tuple

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapesView` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The view of a configuration through a tape embedding

For an embedding `e : Fin k ↪ Fin k'` of work tapes, `viewCfg e cfg` is the configuration of a
machine with `k` work tapes that sees the tapes `e j` of `cfg`. Placing it back with
`Turing.MultiTapeTM.embed` gives `cfg` (`embed_viewCfg`), so the run of `tm.extendTapes e` from
any configuration is the run of `tm` on the view, placed back (`runFrom_extendTapes`). This
generalises `Turing.MultiTapeTM.oneTapeCfg` and `Turing.MultiTapeTM.runFrom_tapeEmb` from one tape
to any embedding.

## Main definitions

* `Turing.MultiTapeTM.viewCfg`: the view of a configuration through a tape embedding.

## Main results

* `Turing.MultiTapeTM.runFrom_extendTapes`, `Turing.MultiTapeTM.space_extendTapes_le`: the run
  and the space of a machine run on the tapes selected by an embedding.
* `Turing.MultiTapeTM.embed_castAdd`, `Turing.MultiTapeTM.embed_natAdd`,
  `Turing.MultiTapeTM.embed_castSucc`: tape blocks as appended families.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k k' : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The configuration of a machine with `k` work tapes seeing the tapes `e j` of `cfg`. -/
def viewCfg (e : Fin k ↪ Fin k') (cfg : Cfg k' Symbol State input) : Cfg k Symbol State input :=
  ⟨cfg.state, cfg.inputPos, fun j => cfg.workTapes (e j), fun j => cfg.workTapePos (e j),
    cfg.output⟩

/-- A configuration is its view through `e`, placed back on the tapes `e j`. -/
theorem embed_viewCfg (e : Fin k ↪ Fin k') (cfg : Cfg k' Symbol State input) :
    embed e (viewCfg e cfg) cfg.workTapes cfg.workTapePos = cfg := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> simp only [embed, viewCfg] <;>
    · cases h : partialInv e l with
      | none => rfl
      | some j => rw [← partialInv_eq_some e h]

/-- **Running a machine on the tapes selected by an embedding.** The run is the run on the view of
the configuration, placed back on the selected tapes; every other tape and head keeps its starting
value. -/
theorem runFrom_extendTapes (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k')
    (cfg : Cfg k' Symbol State input) (n : ℕ) :
    (tm.extendTapes e).runFrom cfg n =
      embed e (tm.runFrom (viewCfg e cfg) n) cfg.workTapes cfg.workTapePos := by
  rw [← embedHom_apply tm, ← runFrom_map, embedHom_apply, embed_viewCfg]

/-- **Space of a machine run on the tapes selected by an embedding:** the space of the run on the
view, plus one cell for each tape the machine does not use. -/
theorem space_extendTapes_le (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k')
    (cfg : Cfg k' Symbol State input) (n : ℕ) :
    (MultiTapeNTM.RunPath.ofDeterministic (tm.extendTapes e) cfg n).space ≤
      (MultiTapeNTM.RunPath.ofDeterministic tm (viewCfg e cfg) n).space + (k' - k) := by
  conv_lhs => rw [← embed_viewCfg e cfg]
  exact space_embed_le _ _ _ _ _ _

/-- Placing a configuration before a block of extra tapes gives an appended family. -/
theorem embed_castAdd (cfg : Cfg k Symbol State input)
    (tapes : Fin (k + k') → ℤ → Option Symbol) (heads : Fin (k + k') → ℤ) :
    embed (Fin.castAddEmb k') cfg tapes heads =
      ⟨cfg.state, cfg.inputPos, Fin.append cfg.workTapes (fun i => tapes (Fin.natAdd k i)),
        Fin.append cfg.workTapePos (fun i => heads (Fin.natAdd k i)), cfg.output⟩ := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.addCases with
  | left i =>
    have h : partialInv (Fin.castAddEmb k') (i.castAdd k') = some i :=
      partialInv_embed (Fin.castAddEmb k') i
    simp [embed, h]
  | right i =>
    have h : Fin.natAdd k i ∉ Set.range (Fin.castAddEmb k') := by
      rintro ⟨j, hj⟩
      exact Fin.castAdd_ne_natAdd j i hj
    simp [embed, partialInv_eq_none _ h]

/-- Placing a configuration after a block of extra tapes gives an appended family. -/
theorem embed_natAdd (cfg : Cfg k Symbol State input)
    (tapes : Fin (k' + k) → ℤ → Option Symbol) (heads : Fin (k' + k) → ℤ) :
    embed (Fin.natAddEmb k') cfg tapes heads =
      ⟨cfg.state, cfg.inputPos, Fin.append (fun i => tapes (i.castAdd k)) cfg.workTapes,
        Fin.append (fun i => heads (i.castAdd k)) cfg.workTapePos, cfg.output⟩ := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.addCases with
  | left i =>
    have h : i.castAdd k ∉ Set.range (Fin.natAddEmb k') := by
      rintro ⟨j, hj⟩
      exact Fin.castAdd_ne_natAdd i j hj.symm
    simp [embed, partialInv_eq_none _ h]
  | right i =>
    have h : partialInv (Fin.natAddEmb k') (Fin.natAdd k' i) = some i :=
      partialInv_embed (Fin.natAddEmb k') i
    simp [embed, h]

/-- Reserving one last tape is the corresponding `Fin.lastCases` family. -/
theorem embed_castSucc (cfg : Cfg k Symbol State input)
    (tapes : Fin (k + 1) → ℤ → Option Symbol) (heads : Fin (k + 1) → ℤ) :
    embed Fin.castSuccEmb cfg tapes heads =
      ⟨cfg.state, cfg.inputPos, Fin.lastCases (tapes (Fin.last k)) cfg.workTapes,
        Fin.lastCases (heads (Fin.last k)) cfg.workTapePos, cfg.output⟩ := by
  change embed (Fin.castAddEmb 1) cfg tapes heads = _
  rw [embed_castAdd]
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.lastCases <;>
    simp [Fin.append, Fin.addCases]

end Turing.MultiTapeTM


