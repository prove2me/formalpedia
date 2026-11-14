-- Prove2me | Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_OutputToTape
-- name    : Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_OutputToTape
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:34:58.061502+00:00
-- url     : https://prove2.me/theorems/2523a87c-8cd6-497a-8dd0-4253ab70cd2d
-- title:
--   Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape — Redirecting the output to a work tape
-- statement:
--   This is module `Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape` of [CSLib](https://github.com/leanprover/cslib) (Apache-2.0), at commit `254e30e`: part of its development of multi-tape Turing machines. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states its running-time bounds on these machines.
--
--   `outputToTape tm` behaves like `tm`, except that whatever `tm` would append to the write-only
--   output tape is written on a fresh work tape instead, whose head always stands at the write
--   frontier.
--
--   Since the output is append-only, the frontier position is a *function of the configuration* —
--   the length of the output so far — so the redirected machine mirrors the original through the
--   configuration map `outCfg`. The main lemmas show that one step and an entire run path of the
--   redirected machine mirror the corresponding step and run path of `tm`.
--
--   **Contents.** The module is published as a whole: 12 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_OutputToTape`.
-- source:
--   https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a/Cslib/Computability/Machines/Turing/MultiTape/Plumbing/OutputToTape.lean

/-
Copyright (c) 2026 Christian Reitwiessner and Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_WordsCfg
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_TapeLemmas

set_option autoImplicit true
set_option relaxedAutoImplicit true

/- Prove2me definition bundle for `Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Redirecting the output to a work tape

`outputToTape tm` behaves like `tm`, except that whatever `tm` would append to the write-only
output tape is written on a fresh work tape instead, whose head always stands at the write
frontier.

Since the output is append-only, the frontier position is a *function of the configuration* —
the length of the output so far — so the redirected machine mirrors the original through the
configuration map `outCfg`. The main lemmas show that one step and an entire run path of the
redirected machine mirror the corresponding step and run path of `tm`.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- `tm`, with its output writes redirected onto a fresh last work tape, whose head always stands
at the write frontier. -/
@[expose] public noncomputable def outputToTape (tm : MultiTapeTM k Symbol State) :
    MultiTapeTM (k + 1) Symbol State :=
  ofTr tm.q₀ fun q inp work =>
    let a := tm.tr q inp fun j => work j.castSucc
    { inputTape := a.inputTape
      workTapes := Fin.lastCases
        (match a.output with
          | none => (none, 0)
          | some s => (some (some s), 1))
        (fun j => a.workTapes j)
      output := none
      state := a.state }

/-- A configuration of `tm`, as the redirected machine sees it: the output so far sits on the
last work tape with the head at its end, and the real output is empty. -/
@[expose] public def outCfg (c : Cfg k Symbol State input) :
    Cfg (k + 1) Symbol State input :=
  ⟨c.state, c.inputPos,
    Fin.lastCases (tapeOfList c.output) (fun j => c.workTapes j),
    Fin.lastCases (c.output.length : ℤ) (fun j => c.workTapePos j),
    []⟩

@[simp]
public lemma outCfg_inputSymbol (c : Cfg k Symbol State input) :
    (outCfg c).inputSymbol = c.inputSymbol := rfl

@[simp]
public lemma outCfg_workTapes_last (c : Cfg k Symbol State input) :
    (outCfg c).workTapes (Fin.last k) = tapeOfList c.output := by
  simp [outCfg]

@[simp]
public lemma outCfg_workTapes_castSucc (c : Cfg k Symbol State input) (j : Fin k) :
    (outCfg c).workTapes j.castSucc = c.workTapes j := by
  simp [outCfg]

@[simp]
public lemma outCfg_workTapePos_last (c : Cfg k Symbol State input) :
    (outCfg c).workTapePos (Fin.last k) = (c.output.length : ℤ) := by
  simp [outCfg]

@[simp]
public lemma outCfg_workTapePos_castSucc (c : Cfg k Symbol State input) (j : Fin k) :
    (outCfg c).workTapePos j.castSucc = c.workTapePos j := by
  simp [outCfg]

@[simp]
public lemma outCfg_workTapeSymbols_castSucc (c : Cfg k Symbol State input) (j : Fin k) :
    (outCfg c).workTapeSymbols j.castSucc = c.workTapeSymbols j := by
  simp [Cfg.workTapeSymbols]

/-- The redirection is a step-semiconjugation. -/
public lemma step_outCfg (tm : MultiTapeTM k Symbol State) :
    Function.Semiconj (outCfg (input := input)) tm.step tm.outputToTape.step := by
  intro c
  symm
  cases hq : c.state with
  | none => simp [outCfg, hq]
  | some q =>
    rw [step_of_state (cfg := outCfg c) hq, step_of_state hq]
    simp only [outputToTape, tr_ofTr, outCfg_inputSymbol, outCfg_workTapeSymbols_castSucc]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> induction l using Fin.lastCases with
    | cast j => simp
    | last =>
      cases h : (tm.tr q c.inputSymbol c.workTapeSymbols).output <;>
        simp [h, tapeOfList_append_single, SignType.cast]

/-- The redirection preserves steps, so it maps run paths of `tm` to run paths of the redirected
machine. -/
@[expose, simps! apply] public noncomputable def outCfgHom (tm : MultiTapeTM k Symbol State) :
    (tm.stepRel input).Hom (tm.outputToTape.stepRel input) :=
  stepHom outCfg (step_outCfg tm)

/-- The initial configuration of the redirected machine is the original's through `outCfg`. -/
public lemma initCfg_outputToTape (tm : MultiTapeTM k Symbol State) (input : List Symbol) :
    tm.outputToTape.initCfg input = outCfg (tm.initCfg input) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> induction l using Fin.lastCases <;>
    simp [MultiTapeNTM.initCfg, Cfg.init]

/-- **Space of the output-redirected path.** The `k` inner tapes visit exactly what the original
path visits, and the frontier head only walks up to the final length of the output, so the
redirection costs at most the final output length plus one. -/
public lemma space_map_outCfgHom_le (tm : MultiTapeTM k Symbol State) (p : tm.RunPath input) :
    (p.map (outCfgHom tm)).space ≤ p.space + (p.last.output.length + 1) := by
  simpa [Finset.card_compl] using p.space_map_le _ Fin.castSuccEmb
    (fun _ => .Icc 0 (p.last.output.length : ℤ)) (fun c _ => outCfg_workTapePos_castSucc c)
    fun c ⟨n, hn⟩ l hl => by
      induction l using Fin.lastCases with
      | last =>
        have : c.output.length ≤ p.last.output.length := hn ▸ p.length_output_mono (Fin.le_last n)
        simpa using this
      | cast j => exact absurd ⟨j, rfl⟩ hl

end Turing.MultiTapeTM


