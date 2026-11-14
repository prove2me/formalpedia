-- Prove2me | Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_WordsCfg
-- name    : Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_WordsCfg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:36.700317+00:00
-- url     : https://prove2.me/theorems/7cbf84f5-4054-4801-a24e-c8c08e36e7ec
-- title:
--   Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg — Tapes holding words and configurations of such tapes
-- statement:
--   This is module `Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg` of [CSLib](https://github.com/leanprover/cslib) (Apache-2.0), at commit `254e30e`: part of its development of multi-tape Turing machines. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states its running-time bounds on these machines.
--
--   The normal form in which "tape transformer" machines (cf. `TransformsTapes.lean`) start and finish:
--   every work tape holds a word in the cells `0, 1, …` and is blank everywhere else, with every head
--   at the start.
--
--   ### Main definitions
--
--   * `Turing.tapeOfList`: the tape holding exactly a given word.
--   * `Turing.wordsCfg`: the configuration whose tapes hold given words.
--
--   **Contents.** The module is published as a whole: 12 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_WordsCfg`.
-- source:
--   https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a/Cslib/Computability/Machines/Turing/MultiTape/Plumbing/WordsCfg.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Configuration

set_option autoImplicit true
set_option relaxedAutoImplicit true

/- Prove2me definition bundle for `Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Tapes holding words and configurations of such tapes

The normal form in which "tape transformer" machines (cf. `TransformsTapes.lean`) start and finish:
every work tape holds a word in the cells `0, 1, …` and is blank everywhere else, with every head
at the start.

## Main definitions

* `Turing.tapeOfList`: the tape holding exactly a given word.
* `Turing.wordsCfg`: the configuration whose tapes hold given words.
-/

@[expose] public section

namespace Turing

variable {k : ℕ} {State Symbol : Type*}

/-- A tape containing exactly the symbols of `xs` at positions `0, ..., xs.length - 1`. -/
def tapeOfList (xs : List Symbol) : ℤ → Option Symbol
  | .ofNat n => xs[n]?
  | .negSucc _ => none

@[simp]
lemma tapeOfList_ofNat (xs : List Symbol) (n : ℕ) : tapeOfList xs n = xs[n]? := rfl

@[simp]
lemma tapeOfList_negSucc (xs : List Symbol) (n : ℕ) :
    tapeOfList xs (.negSucc n) = none := rfl

/-- Appending one symbol writes precisely the cell after the existing word. -/
lemma tapeOfList_append_single (xs : List Symbol) (x : Symbol) :
    tapeOfList (xs ++ [x]) = Function.update (tapeOfList xs) (xs.length : ℤ) (some x) := by
  funext z
  cases z with
  | negSucc n => simp [tapeOfList]
  | ofNat n => grind [tapeOfList]

/-- A cell of `tapeOfList xs` is blank exactly outside the positions `0, …, xs.length - 1`. -/
lemma tapeOfList_eq_none_iff (xs : List Symbol) (z : ℤ) :
    tapeOfList xs z = none ↔ z < 0 ∨ (xs.length : ℤ) ≤ z := by
  cases z <;> simp

/-- The blank tape holds the empty word. -/
@[simp]
lemma tapeOfList_nil : tapeOfList ([] : List Symbol) = fun _ => none := by
  funext z
  cases z <;> simp

/-- The cell at position `0` holds the first symbol of the word. -/
lemma tapeOfList_zero (xs : List Symbol) : tapeOfList xs 0 = xs.head? := by
  have h : (0 : ℤ) = ((0 : ℕ) : ℤ) := rfl
  rw [h, tapeOfList_ofNat]
  cases xs <;> rfl

/-- The configuration whose work tape `i` holds exactly the word `ws i` with its head at the
start, whose input head is at the start of the input, in state `q` with output `out`. -/
@[simps]
def wordsCfg (input : List Symbol) (q : Option State)
    (ws : Fin k → List Symbol) (out : List Symbol) : Cfg k Symbol State input :=
  ⟨q, 1, fun i => tapeOfList (ws i), fun _ => 0, out⟩

/-- Remapping the state of a `wordsCfg` remaps its state and leaves the words alone. -/
@[simp]
lemma mapState_wordsCfg {State' : Type*} (φ : Option State → Option State')
    (input : List Symbol) (q : Option State) (ws : Fin k → List Symbol) (out : List Symbol) :
    (wordsCfg input q ws out).mapState φ = wordsCfg input (φ q) ws out := rfl

/-- Changing the state of a `wordsCfg` leaves the words alone. -/
@[simp]
lemma withState_wordsCfg {State' : Type*} (input : List Symbol) (q : Option State)
    (ws : Fin k → List Symbol) (out : List Symbol) (q' : Option State') :
    (wordsCfg input q ws out).withState q' = wordsCfg input q' ws out := rfl

/-- Prepending a word to the output of a `wordsCfg` prepends it to the output word. -/
@[simp]
lemma prependOutput_wordsCfg (input : List Symbol) (q : Option State)
    (ws : Fin k → List Symbol) (out pre : List Symbol) :
    (wordsCfg input q ws out).prependOutput pre = wordsCfg input q ws (pre ++ out) := rfl

/-- The initial configuration is the word configuration with blank tapes and no output. -/
lemma Cfg.init_eq_wordsCfg (q₀ : State) (input : List Symbol) :
    Cfg.init (k := k) q₀ input = wordsCfg input (some q₀) (fun _ => []) [] := by
  refine Cfg.ext rfl rfl ?_ rfl rfl
  funext i
  simp [Cfg.init, wordsCfg]

end Turing


