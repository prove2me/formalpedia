-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_ClearShadowed
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_ClearShadowed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:37:16.302966+00:00
-- url     : https://prove2.me/theorems/acf921c4-0406-4d84-a766-b20bf31bd333
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Plumbing.ClearShadowed — Clearing a work tape along its shadow
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.ClearShadowed` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   `clearShadowed m₀ m₁` is a machine with two work tapes, a work tape `W` and its shadow `S` in the
--   sense of `Turing.MultiTapeTM.shadow`, whose heads are on the same cell. When the shadow marks an
--   interval `[L, R]` of cells around the start cell, the start cell with `m₀` and the others with
--   `m₁`, except possibly the cell under the heads, and the work tape is blank outside `[L, R]`, the
--   machine blanks both tapes and parks both heads on the start cell (`runFrom_clearShadowed`):
--
--   * `start`: mark the cell under the heads (which the shadow may not have marked yet) and move left;
--   * `left`: move left to the blank cell `L - 1` and step back onto `L`;
--   * `sweep`: move right to `R + 1`, blanking both tapes, except for a temporary mark `m₁` on the
--     work tape at the start cell;
--   * `home`: move left to the temporary mark, erase it and halt.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.clearShadowed`: the clearing machine.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.runFrom_clearShadowed`: its run, in `a + 2 b + c + 5` steps for
--     `[L, R] = [-a, b]` and the heads at `c - a`.
--
--   **Contents.** The module is published as a whole: 12 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_ClearShadowed`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Plumbing/ClearShadowed.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Shadow
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.ClearShadowed` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Clearing a work tape along its shadow

`clearShadowed m₀ m₁` is a machine with two work tapes, a work tape `W` and its shadow `S` in the
sense of `Turing.MultiTapeTM.shadow`, whose heads are on the same cell. When the shadow marks an
interval `[L, R]` of cells around the start cell, the start cell with `m₀` and the others with
`m₁`, except possibly the cell under the heads, and the work tape is blank outside `[L, R]`, the
machine blanks both tapes and parks both heads on the start cell (`runFrom_clearShadowed`):

* `start`: mark the cell under the heads (which the shadow may not have marked yet) and move left;
* `left`: move left to the blank cell `L - 1` and step back onto `L`;
* `sweep`: move right to `R + 1`, blanking both tapes, except for a temporary mark `m₁` on the
  work tape at the start cell;
* `home`: move left to the temporary mark, erase it and halt.

## Main definitions

* `Turing.MultiTapeTM.clearShadowed`: the clearing machine.

## Main results

* `Turing.MultiTapeTM.runFrom_clearShadowed`: its run, in `a + 2 b + c + 5` steps for
  `[L, R] = [-a, b]` and the heads at `c - a`.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {Symbol : Type*} [DecidableEq Symbol] {input : List Symbol}

/-- The control states of `clearShadowed`. -/
inductive ClearShadowedState : Type
  | start
  | left
  | sweep
  | home
  deriving DecidableEq

instance : Fintype ClearShadowedState :=
  ⟨{.start, .left, .sweep, .home}, fun q => by cases q <;> simp⟩

open ClearShadowedState

/-- An action of `clearShadowed`: write `w₀` on the work tape and `w₁` on the shadow, move both
heads by `d` and enter `q`. -/
abbrev ClearShadowed.action (w₀ w₁ : Option (Option Symbol)) (d : SignType)
    (q : Option ClearShadowedState) : Action 2 Symbol ClearShadowedState :=
  ⟨0, ![(w₀, d), (w₁, d)], none, q⟩

variable (m₀ m₁ : Symbol)

/-- The machine clearing a work tape (tape `0`) along its shadow (tape `1`) marked with `m₀` on the
start cell and `m₁` elsewhere. -/
def clearShadowed : MultiTapeTM 2 Symbol ClearShadowedState :=
  ofTr .start fun q _ work =>
    match q with
    | .start => ClearShadowed.action none (if (work 1).isNone then some (some m₁) else none) (-1)
        (some .left)
    | .left => if (work 1).isNone then ClearShadowed.action none none 1 (some .sweep)
        else ClearShadowed.action none none (-1) (some .left)
    | .sweep => match work 1 with
      | none => ClearShadowed.action none none (-1) (some .home)
      | some m =>
        ClearShadowed.action (some (if m = m₀ then some m₁ else none)) (some none) 1 (some .sweep)
    | .home => match work 0 with
      | none => ClearShadowed.action none none (-1) (some .home)
      | some _ => ClearShadowed.action (some none) none 0 none

variable {m₀ m₁}

namespace ClearShadowed

/-- The configuration with work tape `W`, shadow `S`, both heads on cell `x`, input head `ip` and
output `out`. -/
abbrev cfg (q : Option ClearShadowedState) (ip : Fin (input.length + 2))
    (W S : ℤ → Option Symbol) (x : ℤ) (out : List Symbol) : Cfg 2 Symbol ClearShadowedState input :=
  ⟨q, ip, ![W, S], fun _ => x, out⟩

/-- One step of `clearShadowed` in state `q`, given the action it takes there. -/
private theorem step_cfg {q : ClearShadowedState} {ip : Fin (input.length + 2)}
    {W S : ℤ → Option Symbol} {x : ℤ} {out : List Symbol} {w₀ w₁ : Option (Option Symbol)}
    {d : SignType} {q' : Option ClearShadowedState}
    (h : (clearShadowed m₀ m₁).tr q (cfg q ip W S x out).inputSymbol ![W x, S x] =
      ClearShadowed.action w₀ w₁ d q') :
    (clearShadowed m₀ m₁).step (cfg (some q) ip W S x out) =
      cfg q' ip (w₀.elim W (Function.update W x)) (w₁.elim S (Function.update S x)) (x + d)
        out := by
  have hsym : (cfg (some q) ip W S x out).workTapeSymbols = ![W x, S x] := by
    funext j
    fin_cases j <;> rfl
  rw [step_of_state rfl, hsym, h]
  refine Cfg.ext rfl (by simp) ?_ ?_ (by simp)
  · funext j
    fin_cases j <;> cases w₀ <;> cases w₁ <;> rfl
  · funext j
    fin_cases j <;> rfl

variable {ip : Fin (input.length + 2)} {out : List Symbol}

/-- A leftward scan preserves the control, tapes, input head and output, moving both work heads
from `x` to `x - n`; the next step is then the action at the endpoint. -/
private theorem runFrom_leftward (q : ClearShadowedState) (n : ℕ) (x : ℤ)
    (W S : ℤ → Option Symbol)
    (hstep : ∀ j < n,
      (clearShadowed m₀ m₁).tr q (cfg (some q) ip W S (x - j) out).inputSymbol
        ![W (x - j), S (x - j)] = action none none (-1) (some q)) :
    (clearShadowed m₀ m₁).runFrom (cfg (some q) ip W S x out) (n + 1) =
      (clearShadowed m₀ m₁).step (cfg (some q) ip W S (x - n) out) := by
  let path : (clearShadowed m₀ m₁).RunPath input :=
    ⟨n, fun j => cfg (some q) ip W S (x - j) out, fun j => by
      simpa only [MultiTapeNTM.stepRel, Set.mem_ofPred_eq, MultiTapeTM.step_iff,
        Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one,
        sub_add_eq_sub_sub, Option.elim_none, SignType.coe_neg_one, ← sub_eq_add_neg] using
        step_cfg (hstep j j.isLt)⟩
  have hrun := (runPath_apply_eq_runFrom path (Fin.last n)).symm
  simp only [path, RelSeries.head, Fin.val_zero, Nat.cast_zero, sub_zero, Fin.val_last] at hrun
  rw [runFrom, Function.iterate_succ_apply', ← runFrom, hrun]

/-- In state `left`, the heads move left over marked cells to the first blank shadow cell, and
step back right. -/
private theorem runFrom_left (n : ℕ) (x : ℤ) (W : ℤ → Option Symbol) {S : ℤ → Option Symbol}
    (hS : ∀ j < n, S (x - j) ≠ none) (hn : S (x - n) = none) :
    (clearShadowed m₀ m₁).runFrom (cfg (some .left) ip W S x out) (n + 1) =
      cfg (some .sweep) ip W S (x - n + 1) out := by
  rw [runFrom_leftward .left n x W S
    (by intro j hj; simp [clearShadowed, Option.isNone_iff_eq_none, hS j hj])]
  rw [step_cfg (w₀ := none) (w₁ := none) (d := 1) (q' := some .sweep)
    (by simp [clearShadowed, hn])]
  simp

/-- In state `sweep`, the heads move right over the marked cells to the first blank shadow cell,
blanking both tapes except for a mark `m₁` on the work tape at the start cell, and step back
left. -/
private theorem runFrom_sweep (n : ℕ) (x : ℤ) (W S : ℤ → Option Symbol)
    (hS : ∀ j < n, S (x + j) ≠ none) (hn : S (x + n) = none) :
    (clearShadowed m₀ m₁).runFrom (cfg (some .sweep) ip W S x out) (n + 1) =
      cfg (some .home) ip
        (fun y => if x ≤ y ∧ y < x + n then (if S y = some m₀ then some m₁ else none) else W y)
        (fun y => if x ≤ y ∧ y < x + n then none else S y) (x + n - 1) out := by
  induction n generalizing x W S with
  | zero =>
    rw [runFrom_one, step_cfg (w₀ := none) (w₁ := none) (d := -1) (q' := some .home)
      (by simp [clearShadowed, by simpa using hn])]
    congr 1
    · funext y
      rw [Option.elim_none, if_neg (by omega)]
    · funext y
      rw [Option.elim_none, if_neg (by omega)]
    · simp only [SignType.coe_neg_one, Nat.cast_zero]
      omega
  | succ n ih =>
    obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.1 (by simpa using hS 0 (by omega))
    rw [runFrom, Function.iterate_succ_apply, ← runFrom,
      step_cfg (w₀ := some (if m = m₀ then some m₁ else none)) (w₁ := some none) (d := 1)
        (q' := some .sweep) (by simp [clearShadowed, hm]), Option.elim_some, Option.elim_some,
      ih (x + ((1 : SignType) : ℤ)) _ _ (fun j hj => by
        rw [Function.update_of_ne (by simp only [SignType.coe_one]; omega)]
        convert hS (j + 1) (by omega) using 2
        simp only [SignType.coe_one]
        omega) (by
        rw [Function.update_of_ne (by simp only [SignType.coe_one]; omega)]
        convert hn using 2
        simp only [SignType.coe_one]
        omega)]
    simp only [SignType.coe_one]
    congr 1
    · funext y
      by_cases hy : y = x
      · subst hy
        simp [hm]
      · simp only [Function.update_of_ne hy]
        split_ifs <;> first | rfl | omega
    · funext y
      by_cases hy : y = x
      · subst hy
        simp
      · simp only [Function.update_of_ne hy]
        split_ifs <;> first | rfl | omega
    · omega

/-- In state `home`, the heads move left over blank work-tape cells to the mark, which is erased,
and the machine halts. -/
private theorem runFrom_home (n : ℕ) (x : ℤ) (W S : ℤ → Option Symbol)
    (hW : ∀ j < n, W (x - j) = none) (hn : W (x - n) ≠ none) :
    (clearShadowed m₀ m₁).runFrom (cfg (some .home) ip W S x out) (n + 1) =
      cfg none ip (Function.update W (x - n) none) S (x - n) out := by
  rw [runFrom_leftward .home n x W S
    (by intro j hj; simp [clearShadowed, hW j hj])]
  obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.1 hn
  rw [step_cfg (w₀ := some none) (w₁ := none) (d := 0) (q' := none)
    (by simp [clearShadowed, hm])]
  simp

/-- The first step marks the cell under the heads and moves left. -/
private theorem step_start (W : ℤ → Option Symbol) (V : Finset ℤ) (x : ℤ) :
    (clearShadowed m₀ m₁).step (cfg (some .start) ip W (shadowTape m₀ m₁ V) x out) =
      cfg (some .left) ip W (shadowTape m₀ m₁ (insert x V)) (x - 1) out := by
  rw [step_cfg (w₀ := none)
    (w₁ := if (shadowTape m₀ m₁ V x).isNone then some (some m₁) else none)
    (d := -1) (q' := some .left) (by simp [clearShadowed]), Option.elim_none, shadowTape_insert]
  congr 1
  split_ifs <;> rfl

end ClearShadowed

open ClearShadowed

/-- **Clearing a shadowed tape.** If the shadow marks the cells `V`, which together with the cell
`c - a` under the heads form the interval `[-a, b]`, and the work tape is blank outside it, then
`clearShadowed m₀ m₁` blanks both tapes and parks both heads on the start cell, in
`a + 2 b + c + 5` steps. -/
theorem runFrom_clearShadowed (hm : m₀ ≠ m₁) {ip : Fin (input.length + 2)} {out : List Symbol}
    {a b c : ℕ} {V : Finset ℤ} (hV : insert ((c : ℤ) - a) V = Finset.Icc (-(a : ℤ)) b)
    {W : ℤ → Option Symbol} (hW : ∀ y ∉ Finset.Icc (-(a : ℤ)) b, W y = none) :
    (clearShadowed m₀ m₁).runFrom (cfg (some .start) ip W (shadowTape m₀ m₁ V) (c - a) out)
        (a + 2 * b + c + 5) =
      cfg none ip (fun _ => none) (fun _ => none) 0 out := by
  have hc : c ≤ a + b := by
    have := Finset.mem_Icc.1 (hV ▸ Finset.mem_insert_self _ _)
    omega
  set S := shadowTape m₀ m₁ (Finset.Icc (-(a : ℤ)) b)
  have hS : ∀ y, S y = none ↔ y ∉ Finset.Icc (-(a : ℤ)) b := fun y => by
    simp only [S, shadowTape_eq_none_iff, Finset.mem_Icc]
    omega
  rw [show a + 2 * b + c + 5 = 1 + ((c + 1) + ((a + b + 1 + 1) + (b + 1))) by omega,
    runFrom_add, runFrom_add, runFrom_add, runFrom_one, step_start, hV,
    runFrom_left c _ W (fun j hj => by rw [Ne, hS, Finset.mem_Icc]; omega)
      (by rw [hS, Finset.mem_Icc]; omega),
    show (c : ℤ) - a - 1 - c + 1 = -a by omega,
    runFrom_sweep (a + b + 1) _ W S (fun j hj => by rw [Ne, hS, Finset.mem_Icc]; omega)
      (by rw [hS, Finset.mem_Icc]; push_cast; omega),
    show -(a : ℤ) + ↑(a + b + 1) - 1 = b by push_cast; omega,
    runFrom_home b _ _ _ (fun j hj => by
        have : (b : ℤ) - j ≠ 0 := by omega
        have hmem : (b : ℤ) - j ∈ Finset.Icc (-(a : ℤ)) b := by rw [Finset.mem_Icc]; omega
        rw [if_pos (by push_cast; omega)]
        simp [S, shadowTape, this, hmem, hm.symm])
      (by
        rw [sub_self, if_pos (by push_cast; omega)]
        simp [S, shadowTape]),
    sub_self]
  congr 1
  · funext y
    by_cases hy : y = 0
    · simp [hy]
    · rw [Function.update_of_ne hy]
      split_ifs with h h'
      · simp [S, shadowTape, hy, hm.symm] at h'
      · rfl
      · exact hW y (by rw [Finset.mem_Icc]; push_cast at h; omega)
  · funext y
    split_ifs with h
    · rfl
    · exact (hS y).2 (by rw [Finset.mem_Icc]; push_cast at h; omega)

end Turing.MultiTapeTM


