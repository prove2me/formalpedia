-- Prove2me | Definitions.Def_MatMulDS_Supplement_coinFrac
-- name    : MatMulDS_Supplement_coinFrac
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:11:43.281196+00:00
-- url     : https://prove2.me/theorems/785c4c82-9348-4757-a9d9-e9d320a8537d
-- title:
--   Success probability of a randomized word-RAM program
-- statement:
--   A **randomized word RAM** is a program of the mission's algebraic RAM over the two-element field $\mathbb F_2$: its coin instruction draws a uniform random bit, and every instruction costs one step.
--
--   For a program $P$, a word size $w$, input words and a bound $T$, the success probability of an event is the fraction of the coin vectors $c\in\mathbb F_2^T$ on which $P$ halts within $T$ steps with a final word memory satisfying the event; a run of at most $T$ steps reads at most $T$ coins, so this is the probability over uniformly random coins.
--
--   $P$ **always returns** a correct output if every halting run, on every coin sequence, ends with a correct output, and the run halts with probability one: for every $\delta>0$ it halts within some $T$ steps with probability at least $1-\delta$.
--
--   These notions express "always returns" and "runs in $O(\cdot)$ time with high probability" for the randomized algorithms of Theorems 8.11, 8.19, 8.23, E.4 and E.5.
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Theorems 8.11, 8.19, 8.23, E.4, E.5, pp.57–63, 98 (PDF pp.59–65, 100); "with high probability" in the proofs of Theorems E.4, E.5 and Lemma J.2, pp.105, 107, 117

import Mathlib
import Definitions.Def_MatroidSensOracle_AlgRAM

set_option autoImplicit false

open MatroidSensOracle

namespace MatMulDS.Supplement

/-- **Success probability of a randomized word-RAM program.** The fraction of the coin vectors `c ∈ 𝔽₂^T` on which the
program `P`, run on the published algebraic RAM over the field `𝔽₂ = ZMod 2` from the input words `inp` (no input field
elements), halts within `T` steps with a final word memory satisfying `good`. A run of at most `T` steps reads at most `T`
coins, so this is the probability of the event over uniformly random coin bits.

Source: Alman, Nogler, Vassilevska Williams, STOC 2027 submission (held file sha256 6c5a1c16…): the randomized algorithms
of Theorems 8.11, 8.19, 8.23, E.4, E.5 (pp.57–63, 98); "with high probability" as made explicit in the proofs of
Theorem E.5 (p.105), Theorem E.4 (p.107) and Lemma J.2 (p.117).

**Formalization Note.** A randomized word RAM is a program of the published algebraic RAM over `𝔽₂`: its coin
instruction `fcoin` draws a uniform bit, and its field cells are a bit array. Every instruction costs one step. -/
noncomputable def coinFrac (P : List AInstr) (w : ℕ) (inp : List ℤ) (T : ℕ)
    (good : (ℤ → BitVec w) → Prop) : ℝ :=
  open Classical in
  ((Finset.univ.filter fun c : Fin T → ZMod 2 =>
      ∃ st, aexec P (extendCoins c) T 0 0 (aloadWords w inp) (aloadFields []) = some st ∧ good st.1).card : ℝ) /
    (2 : ℝ) ^ T

/-- **"Always returns" a correct output.** On every coin sequence and for every step budget, a run of `P` on the input
words `inp` that halts ends with a final word memory satisfying `good`, and the run halts with probability one: for
every `δ > 0` it halts within some number `T` of steps with probability at least `1 − δ`. -/
def AlwaysReturns (P : List AInstr) (w : ℕ) (inp : List ℤ) (good : (ℤ → BitVec w) → Prop) : Prop :=
  (∀ (ω : ℕ → ZMod 2) (t : ℕ) (st : (ℤ → BitVec w) × (ℤ → ZMod 2)),
    aexec P ω t 0 0 (aloadWords w inp) (aloadFields []) = some st → good st.1) ∧
  ∀ δ : ℝ, 0 < δ → ∃ T : ℕ, 1 - δ ≤ coinFrac P w inp T fun _ => True

end MatMulDS.Supplement


