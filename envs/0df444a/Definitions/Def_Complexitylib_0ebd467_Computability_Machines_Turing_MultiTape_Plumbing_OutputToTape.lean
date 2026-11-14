-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_OutputToTape
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_OutputToTape
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:35.116331+00:00
-- url     : https://prove2.me/theorems/1461bb48-57ae-44e1-83b6-234da806fe85
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape — Writing the output as a word on a work tape
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The additions of cslib PR #1111 to
--   `Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape`.
--
--   `outputToWord tm` runs `tm` with its output redirected to a new last work tape
--   (`Turing.MultiTapeTM.outputToTape`), then moves the head of that tape back to cell `0`
--   (`Turing.MultiTapeTM.rewindWork`). If `tm` computes `output` tidily
--   (`Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace`), then `outputToWord tm` takes blank work tapes
--   to blank work tapes, except that the last one holds `output`, and emits nothing.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.outputToWord`: the machine writing its output as a word on a work tape.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.outputToWord`: its specification.
--   * `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.outputToWord_extendTapes`: preserve
--     unselected tapes while writing the output.
--   * `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.outputToWord_onTape`: the blank-tape case.
--
--   **Contents.** The module is published as a whole: 7 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_OutputToTape`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Plumbing/OutputToTape.lean

/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: submitted #1111 @3441fa81

public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_OutputToTape
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_ExtendTapes
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_RewindWork
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Sequential
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_Tidy_Defs

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Writing the output as a word on a work tape

The additions of cslib PR #1111 to
`Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape`.

`outputToWord tm` runs `tm` with its output redirected to a new last work tape
(`Turing.MultiTapeTM.outputToTape`), then moves the head of that tape back to cell `0`
(`Turing.MultiTapeTM.rewindWork`). If `tm` computes `output` tidily
(`Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace`), then `outputToWord tm` takes blank work tapes
to blank work tapes, except that the last one holds `output`, and emits nothing.

## Main definitions

* `Turing.MultiTapeTM.outputToWord`: the machine writing its output as a word on a work tape.

## Main results

* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.outputToWord`: its specification.
* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.outputToWord_extendTapes`: preserve
  unselected tapes while writing the output.
* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.outputToWord_onTape`: the blank-tape case.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-! ### Rewinding the output tape -/

/-- `tm` with its output written to a new last work tape, whose head is then moved back to
cell `0`. -/
@[expose] public noncomputable def outputToWord (tm : MultiTapeTM k Symbol State) :
    MultiTapeTM (k + 1) Symbol (State ⊕ RewindWorkState) :=
  tm.outputToTape.seq ((rewindWork Symbol).extendTapes (tapeEmb (Fin.last k)))

/-- Redirecting the output of a blank `wordsCfg` configuration adds a blank last work tape. -/
private lemma outCfg_wordsCfg (q : Option State) :
    outCfg (wordsCfg input q (fun _ : Fin k => []) []) = wordsCfg input q (fun _ => []) [] := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> induction l using Fin.lastCases <;>
    simp [outCfg, wordsCfg]

/-- The last work tape of `outCfg (wordsCfg input q ws out)`, as a one-tape configuration: it holds
`out`, with its head at the end of `out`. -/
private lemma oneTapeCfg_outCfg_wordsCfg (q : Option State) (ws : Fin k → List Symbol)
    (out : List Symbol) :
    oneTapeCfg (Fin.last k) (outCfg (wordsCfg input q ws out)) =
      ⟨q, 1, fun _ => tapeOfList out, fun _ => (out.length : ℤ), []⟩ := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext _ <;> simp [oneTapeCfg]

/-- Rewinding the last work tape of `outCfg (wordsCfg input q (fun _ => []) out)` takes
`out.length + 2` steps and leaves `out` as a word on that tape: it runs `rewindWork` on that tape.
-/
private lemma exists_runPath_rewindLast (out : List Symbol) :
    ∃ p : ((rewindWork Symbol).extendTapes (tapeEmb (Fin.last k))).RunPath input,
      p.head = outCfg (wordsCfg input (some (rewindWork Symbol).q₀) (fun _ : Fin k => []) out) ∧
      p.last = wordsCfg input none (Function.update (fun _ => []) (Fin.last k) out) [] ∧
      p.time = out.length + 2 ∧ p.space ≤ out.length + k + 3 := by
  let cfg := outCfg (wordsCfg input (some (rewindWork Symbol).q₀) (fun _ : Fin k => []) out)
  let r := MultiTapeNTM.RunPath.ofDeterministic (rewindWork Symbol) (oneTapeCfg (Fin.last k) cfg)
    (out.length + 2)
  refine ⟨r.map (embedHom _ (tapeEmb (Fin.last k)) cfg.workTapes cfg.workTapePos),
    embed_oneTapeCfg _ cfg, ?_, rfl, ?_⟩
  · change embed _ ((rewindWork Symbol).runFrom (oneTapeCfg _ cfg) (out.length + 2)) _ _ = _
    rw [oneTapeCfg_outCfg_wordsCfg, runFrom_rewindWork_none _ _ _ rfl le_rfl, embed_tapeEmb]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> induction l using Fin.lastCases <;>
      simp [cfg, wordsCfg]
  · -- the rewind takes `out.length + 2` steps on one tape, every other tape stays where it is
    have : r.space ≤ 1 * (out.length + 2 + 1) := r.space_le_mul_time_add_one
    exact (space_map_embedHom_le ..).trans (by omega)

open Sequential in
/-- If `tm` computes `output` tidily, then `outputToWord tm`, started on blank work tapes, halts
with `output` on its last work tape, every other work tape blank, and nothing emitted. -/
public theorem ComputesTidilyInTimeAndSpace.outputToWord {tm : MultiTapeTM k Symbol State}
    {input output : List Symbol} {t s : ℕ}
    (h : tm.ComputesTidilyInTimeAndSpace input output t s) :
    TransformsTapes tm.outputToWord
      (fun inp ws => inp = input ∧ ws = fun _ => [])
      (fun _ _ ws' e => ws' = Function.update (fun _ => []) (Fin.last k) output ∧ e = [])
      (t + output.length + 2) (s + 2 * output.length + k + 4) := by
  obtain ⟨p, hh, hl, ht, hs⟩ := computesTidily_iff.mp h
  unfold MultiTapeTM.outputToWord
  rw [transformsTapes_iff_nil_output]
  rintro inp _ ⟨hin, rfl⟩
  subst inp
  -- run `tm` with its output on the last work tape, then rewind that tape
  let p₀ := p.map (outCfgHom tm)
  have hl₀ : p₀.last = outCfg (wordsCfg input none (fun _ => []) output) := by simp [p₀, hl]
  have hs₀ : p₀.space ≤ p.space + (output.length + 1) := by
    simpa [hl] using space_map_outCfgHom_le tm p
  obtain ⟨p₁, hh₁, hl₁, ht₁, hs₁⟩ := exists_runPath_rewindLast (k := k) (input := input) output
  obtain ⟨q, hqh, hql, hqt, hqs⟩ := exists_runPath_seq_space_le (p₀ := p₀) (p₁ := p₁)
    (by rw [hl₀]; rfl) (by rw [hh₁, hl₀]; rfl) (by rw [hl₁]; rfl)
  refine ⟨_, [], ⟨rfl, rfl⟩, q, ?_, by simp [hql, hl₁, rightCfg], ?_, by omega⟩
  · simp only [hqh, p₀, RelSeries.head_map, outCfgHom_apply, hh, outCfg_wordsCfg]
    rfl
  · simp only [MultiTapeNTM.RunPath.time] at ht ht₁ ⊢
    have : p₀.length = p.length := rfl
    omega

-- upstream: candidate
/-- A tidy computation writes its output on the selected last tape, leaves its selected scratch
tapes blank, and preserves all unselected words. All selected tapes must initially be blank. -/
public theorem ComputesTidilyInTimeAndSpace.outputToWord_extendTapes
    {k n : ℕ} {Symbol State : Type*} {machine : MultiTapeTM k Symbol State}
    {input output : List Symbol} {t s : ℕ}
    (h : machine.ComputesTidilyInTimeAndSpace input output t s) (e : Fin (k + 1) ↪ Fin n) :
    TransformsTapes (machine.outputToWord.extendTapes e)
      (fun inp ws => inp = input ∧ ∀ j, ws (e j) = [])
      (fun _ ws ws' emitted => ws' = Function.update ws (e (Fin.last k)) output ∧ emitted = [])
      (t + output.length + 2) (s + 2 * output.length + k + 4 + (n - (k + 1))) := by
  refine (h.outputToWord.extendTapes e).imp (fun _ _ h => ⟨h.1, funext h.2⟩) ?_ le_rfl le_rfl
  rintro inp ws ws' emitted hP ⟨⟨hv, rfl⟩, hx⟩
  refine ⟨funext fun i => ?_, rfl⟩
  by_cases hi : i ∈ Set.range e
  · obtain ⟨j, rfl⟩ := hi
    simpa [Function.update_apply, e.injective.eq_iff, hP.2] using congrFun hv j
  · rw [hx i hi, Function.update_of_ne]
    exact fun h => hi ⟨Fin.last k, h.symm⟩

-- upstream: candidate
-- vendored: generalize the selected-tape helper from `Encodings/MultiPass` to a single run,
-- retaining the exact space bound for streaming clients.
/-- Write a tidy computation's output to a selected tape, leaving every other tape blank. -/
public theorem ComputesTidilyInTimeAndSpace.outputToWord_onTape
    {tm : MultiTapeTM k Symbol State} {input output : List Symbol} {t s K : ℕ}
    (h : tm.ComputesTidilyInTimeAndSpace input output t s)
    {e : Fin (k + 1) ↪ Fin K} {V : Fin K} (he : e (Fin.last k) = V) :
    TransformsTapes (tm.outputToWord.extendTapes e)
      (fun inp ws => inp = input ∧ ws = fun _ => [])
      (fun _ _ ws' em => ws' = Function.update (fun _ => []) V output ∧ em = [])
      (t + output.length + 2) (s + 2 * output.length + k + 4 + (K - (k + 1))) := by
  exact (h.outputToWord_extendTapes e).imp
    (fun _ _ ⟨hin, hws⟩ => ⟨hin, by simp [hws]⟩)
    (fun _ _ _ _ ⟨_, hws⟩ ⟨hws', hem⟩ => ⟨by simpa only [hws, he] using hws', hem⟩)
    le_rfl le_rfl

end Turing.MultiTapeTM


