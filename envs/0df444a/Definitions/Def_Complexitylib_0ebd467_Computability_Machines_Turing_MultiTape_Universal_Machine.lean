-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Machine
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Machine
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:03:40.617258+00:00
-- url     : https://prove2.me/theorems/fa1311cd-7584-4dc7-ab6f-918c110a4946
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Universal.Machine — The universal machine
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Universal.Machine` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The universal function takes a description of a multi-tape machine, an input given by symbol
--   numbers, and a number of steps in binary, and returns the output of the described machine after
--   that many steps and whether it has halted by then. One machine computes it for every multi-tape
--   machine, whatever its number of work tapes, states and symbols
--   (`Turing.MultiTapeTM.Universal.universal_desc`).
--
--   For `t` steps, a description of encoded length `D`, an input of encoded length `N`, and a binary
--   clock of length `L`, the time certificate is
--   `O((t + 1) * (stepBound D N t + runBound D N t + (L + 1)^2) + (I + 1)^2)`,
--   where `I` is the complete encoded input length. The space certificate is `O(runBound D N t + I)`.
--   The simulation iterates a step, counting down `t` in binary, and keeps the description, the input,
--   the configuration and the output so far. The setup term is included even when the clock is zero.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.Universal.universal`: the universal function.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.Universal.computableTidilyInO_universal`: the time and space of the universal
--     function.
--   * `Turing.MultiTapeTM.Universal.universal_desc`: on descriptions of machines, it returns their
--     output.
--
--   **Contents.** The module is published as a whole: 17 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Machine`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Universal/Machine.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Bound
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Correct
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Universal.Machine` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The universal machine

The universal function takes a description of a multi-tape machine, an input given by symbol
numbers, and a number of steps in binary, and returns the output of the described machine after
that many steps and whether it has halted by then. One machine computes it for every multi-tape
machine, whatever its number of work tapes, states and symbols
(`Turing.MultiTapeTM.Universal.universal_desc`).

For `t` steps, a description of encoded length `D`, an input of encoded length `N`, and a binary
clock of length `L`, the time certificate is
`O((t + 1) * (stepBound D N t + runBound D N t + (L + 1)^2) + (I + 1)^2)`,
where `I` is the complete encoded input length. The space certificate is `O(runBound D N t + I)`.
The simulation iterates a step, counting down `t` in binary, and keeps the description, the input,
the configuration and the output so far. The setup term is included even when the clock is zero.

## Main definitions

* `Turing.MultiTapeTM.Universal.universal`: the universal function.

## Main results

* `Turing.MultiTapeTM.Universal.computableTidilyInO_universal`: the time and space of the universal
  function.
* `Turing.MultiTapeTM.Universal.universal_desc`: on descriptions of machines, it returns their
  output.
-/

namespace Turing.MultiTapeTM.Universal

/-- The universal function: the output of the machine described by `i.1` on the input `i.2.1`
after `i.2.2` steps, and whether it has halted. -/
@[expose] public def universal (i : Desc × List ℕ × ℕ) : List ℕ × Bool :=
  simulate i.1 i.2.1 i.2.2

/-- The encoding of inputs of the universal function, with the number of steps in binary. -/
public abbrev eIn : Desc × List ℕ × ℕ ↪ List Bool :=
  encPair eDesc (encPair (encList encUnary) encNat)

/-- The encoding of outputs of the universal function. -/
public abbrev eOut : List ℕ × Bool ↪ List Bool := encPair (encList encUnary) encBool

/-- The state of the simulation: the context of a step and the output so far. -/
public abbrev eRun : Ctx × List ℕ ↪ List Bool := encPair eCtx (encList encUnary)

/-- A round of the simulation: a step, collecting the emitted symbol. -/
@[expose] public def round (s : Ctx × List ℕ) : Ctx × List ℕ :=
  ((s.1.1, (step s.1.1.1 s.1.1.2 s.1.2).1), s.2 ++ (step s.1.1.1 s.1.1.2 s.1.2).2.toList)

lemma round_iterate (d : Desc) (x : List ℕ) (k : ℕ) :
    round^[k] (((d, x), init d), []) =
      (((d, x), ((stepOut d x)^[k] (init d, [])).1), ((stepOut d x)^[k] (init d, [])).2) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']; rfl

open ComputableTidilyInO

/-- A round, within the time of a step and linear space. -/
lemma round_inO : ComputableTidilyInO round eRun eRun (fun s => stepTime s.1 + (eRun s).length)
    fun s => (eRun s).length := by
  have hctx := fst eCtx (encList encUnary)
  have hout := snd eCtx (encList encUnary)
  -- bridge for #862: tidy client of the plain `step_inO`
  have hstep := step_inO.tidy.comp hctx
  have hnewout := ((ComputableTidilyInDegree.isSome encUnary).inO_one.comp_linear
    hstep.snd').ite ((ComputableTidilyInDegree.snoc encUnary).inO_one.comp_linear
      (hout.prod ((ComputableTidilyInDegree.getD (enc₁ := encUnary) 0).inO_one.comp_linear
        hstep.snd'))) hout
  refine (((hctx.fst'.prod hstep.fst').prod hnewout).mono 8 (fun s => ?_)
    fun s => ?_).of_enc_eq fun s => ?_
  all_goals
    have h₁ := length_le_encPair_left eCtx (encList encUnary) s
    simp only [Function.comp_apply]
    dsimp only [eRun] at *
  · split_ifs <;> omega
  · split_ifs <;> omega
  · simp only [round]
    generalize (step s.1.1.1 s.1.1.2 s.1.2).2 = o
    cases o <;> simp

lemma iterate_snoc_blank (k : ℕ) :
    (fun acc : List Tape => acc ++ [Tape.blank])^[k] [] = List.replicate k Tape.blank := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, List.replicate_succ']

lemma length_blanks (k : ℕ) : (encList eTape (List.replicate k Tape.blank)).length = 9 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, encList_cons, List.length_append, length_frame, ih]
    simp [Tape.blank]
    omega

/-- `n` blank work tapes, within time quadratic and space linear in `n`. -/
lemma blanks_inO : ComputableTidilyInO (fun n => List.replicate n Tape.blank) encUnary
    (encList eTape) (fun n => (n + 1) ^ 2) fun n => n + 1 := by
  have hstep := ((ComputableTidilyInDegree.snoc eTape).comp
    ((ComputableTidilyInDegree.fst (encList eTape) encBool).prod
      (ComputableTidilyInDegree.const Tape.blank))).inO_one
  have hacc (n i : ℕ) : (((List.replicate n true).take i).foldl
      (fun acc _ => acc ++ [Tape.blank]) []) = List.replicate (min i n) Tape.blank := by
    rw [List.foldl_const, iterate_snoc_blank, List.length_take, List.length_replicate]
  refine ((foldl (encA := encBool) (encL := encBits) (list := fun n => List.replicate n true)
    (step := fun acc _ => acc ++ [Tape.blank])
    (of_linear (.of_eq fun _ => rfl)) (const []) hstep
    (R := fun n => 18 * n + 4) (Q := fun n => 18 * n + 4) (B := fun n => 9 * n)
    (fun n i hi => ?_) (fun n i hi => ?_) (fun n i hi => ?_)).mono 64 (fun n => ?_)
      fun n => ?_).of_enc_eq fun n => ?_
  all_goals simp only [hacc, length_encPair, length_blanks, encUnary_apply, encBits_apply,
    List.length_replicate, encBool_apply, List.length_singleton] at *
  · omega
  · omega
  · omega
  · nlinarith
  · omega
  · rw [List.foldl_const, iterate_snoc_blank, List.length_replicate]

/-- The initial configuration, within time quadratic and space linear in the length of the
description. -/
public lemma init_inO : ComputableTidilyInO init eDesc eCfg (fun d => ((eDesc d).length + 1) ^ 2)
    fun d => (eDesc d).length + 1 := by
  have hf := (of_linear (.of_eq (f := fun d : Desc => (d.tapes, d.q₀, d.table)) (encIn := eDesc)
    (encMid := encPair encUnary (encPair encUnary (encList (encPair eKey eAct)))) fun _ => rfl))
  have hq := (ComputableTidilyInDegree.optionSome (enc₁ := encUnary) (enc := eSym)).inO_one
    |>.comp_linear hf.snd'.fst'
  have ht := blanks_inO.comp hf.fst'
  refine ((hq.prod ((const (encMid := encNat) 1).prod ht)).mono 4 (fun d => ?_)
    fun d => ?_).of_enc_eq fun _ => rfl
  all_goals
    have : d.tapes ≤ (eDesc d).length := by
      simp only [eDesc_apply, length_encPair, encUnary_apply, List.length_replicate]; omega
  · nlinarith
  · omega

/-- The bound on the state of the simulation after `t` steps: the context and the output. -/
public abbrev runBound (D N t : ℕ) : ℕ := 2 * ctxBound D N t + 1 + t * (2 * D + 1)

lemma ctxBound_mono {D N j j' : ℕ} (h : j ≤ j') : ctxBound D N j ≤ ctxBound D N j' := by
  unfold ctxBound cfgBound tapeBound
  gcongr

lemma length_eRun_le (d : Desc) (x : List ℕ) {k t : ℕ} (hk : k ≤ t) :
    (eRun (round^[k] (((d, x), init d), []))).length ≤
      runBound (descLen d) (encList encUnary x).length t := by
  obtain ⟨h₁, h₂, h₃⟩ := inv_iterate d x k
  have h₄ := (length_eCtx_le d x h₁).trans (ctxBound_mono hk)
  have h₅ := (length_encList_le encUnary _ (b := descLen d) fun o ho => by
    simpa using h₃ o ho).trans (Nat.mul_le_mul_right (2 * descLen d + 1) (h₂.trans hk))
  rw [round_iterate]
  simp only [length_encPair, runBound] at *
  omega

lemma universal_eq (i : Desc × List ℕ × ℕ) : universal i =
    ((round^[i.2.2] (((i.1, i.2.1), init i.1), [])).2,
      !(round^[i.2.2] (((i.1, i.2.1), init i.1), [])).1.2.state.isSome) := by
  simp only [universal, simulate, round_iterate]
  cases ((stepOut i.1 i.2.1)^[i.2.2] (init i.1, [])).1.state <;> rfl

/-- **The time and space of the universal function**, for a description of length `D`, an input of
encoded length `N` and `t` steps: time `O((t + 1) * (stepBound D N t + runBound D N t))` and space
`O(runBound D N t)`, plus terms in the length of the encoded input. -/
public theorem computableTidilyInO_universal :
    ComputableTidilyInO universal eIn eOut
      (fun i => (i.2.2 + 1) * (stepBound (descLen i.1) (encList encUnary i.2.1).length i.2.2 +
        runBound (descLen i.1) (encList encUnary i.2.1).length i.2.2 +
          ((encNat i.2.2).length + 1) ^ 2) + ((eIn i).length + 1) ^ 2)
      fun i => runBound (descLen i.1) (encList encUnary i.2.1).length i.2.2 + (eIn i).length := by
  have hd := fst eDesc (encPair (encList encUnary) encNat)
  have hx := (snd eDesc (encPair (encList encUnary) encNat)).fst'
  have ht := (snd eDesc (encPair (encList encUnary) encNat)).snd'
  have hinit := (((hd.prod hx).prod (init_inO.comp hd)).prod
    (const (encMid := encList encUnary) [])).of_enc_eq (encOut := eRun)
    (g := fun i : Desc × List ℕ × ℕ => (((i.1, i.2.1), init i.1), ([] : List ℕ))) fun _ => rfl
  have hiter := (ComputableInO.iterate (encB := eRun) (step := round) (n := fun i => i.2.2)
    ht.computableInO hinit.computableInO round_inO.computableInO
    (R := fun i => stepBound (descLen i.1) (encList encUnary i.2.1).length i.2.2 +
      runBound (descLen i.1) (encList encUnary i.2.1).length i.2.2)
    (Q := fun i => runBound (descLen i.1) (encList encUnary i.2.1).length i.2.2)
    (B := fun i => runBound (descLen i.1) (encList encUnary i.2.1).length i.2.2)
    (fun i k hk => by
      have h₁ := length_eRun_le i.1 i.2.1 hk
      have h₂ := (stepTime_iterate_le i.1 i.2.1 k).trans (stepBound_mono le_rfl le_rfl hk)
      rw [round_iterate] at h₁
      simp only [round_iterate]
      exact Nat.add_le_add h₂ h₁)
    (fun i k hk => by
      show (eRun (round^[k] (((i.1, i.2.1), init i.1), []))).length ≤ _
      exact length_eRun_le i.1 i.2.1 hk)
    (fun i k hk => by
      show (eRun (round^[k] (((i.1, i.2.1), init i.1), []))).length ≤ _
      exact length_eRun_le i.1 i.2.1 hk)).tidy
  have hhalted := (ComputableTidilyInDegree.of_finite (encIn := encBool) (encMid := encBool)
    (fun b : Bool => !b)).inO_one.comp_linear ((ComputableTidilyInDegree.isSome encUnary).inO_one
      -- bridge for #862: tidy client of the plain `state_inO`
      |>.comp_linear (state_inO.tidy.comp_linear hiter.fst'.snd'))
  refine ((hiter.snd'.prod hhalted).mono 16 (fun i => ?_) fun i => ?_).of_enc_eq fun i => ?_
  · have h₁ : (eDesc i.1).length ≤ (eIn i).length := length_le_encPair_left _ _ i
    have h₂ := Nat.pow_le_pow_left (Nat.add_le_add_right h₁ 1) 2
    have h₃ : (eIn i).length + 1 ≤ ((eIn i).length + 1) ^ 2 := Nat.le_self_pow two_ne_zero _
    have h₄ := Nat.mul_le_mul_left (i.2.2 + 1)
      (show stepBound (descLen i.1) (encList encUnary i.2.1).length i.2.2 +
        runBound (descLen i.1) (encList encUnary i.2.1).length i.2.2 +
        runBound (descLen i.1) (encList encUnary i.2.1).length i.2.2 +
          ((encNat i.2.2).length + 1) ^ 2 ≤
        2 * (stepBound (descLen i.1) (encList encUnary i.2.1).length i.2.2 +
          runBound (descLen i.1) (encList encUnary i.2.1).length i.2.2 +
          ((encNat i.2.2).length + 1) ^ 2) by omega)
    rw [Nat.mul_left_comm] at h₄
    dsimp only [eIn, descLen] at *
    omega
  · have h₁ : (eDesc i.1).length ≤ (eIn i).length := length_le_encPair_left _ _ i
    have h₂ : (encNat i.2.2).length ≤ (eIn i).length :=
      (length_le_encPair_right _ _ i.2).trans (length_le_encPair_right _ _ i)
    dsimp only [eIn, descLen] at *
    omega
  · rw [universal_eq]
    rfl

/-- On the description of a machine, the universal function returns the numbered output of the
machine after the given number of steps, and whether it has halted. -/
public theorem universal_desc {k : ℕ} {Symbol S : Type} [Fintype S] [Fintype Symbol]
    (eS : S ↪ ℕ) (eY : Symbol ↪ ℕ) (tm : MultiTapeTM k Symbol S) (x : List Symbol) (t : ℕ) :
    universal (desc eS eY tm, x.map eY, t) =
      ((tm.runFrom (tm.initCfg x) t).output.map eY,
        (tm.runFrom (tm.initCfg x) t).state.isNone) :=
  simulate_desc eS eY tm x t

end Turing.MultiTapeTM.Universal


