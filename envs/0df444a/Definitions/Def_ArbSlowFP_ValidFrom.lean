-- Prove2me | Definitions.Def_ArbSlowFP_ValidFrom
-- name    : ArbSlowFP_ValidFrom
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:45:53.195028+00:00
-- url     : https://prove2.me/theorems/7357b90a-4f31-4444-bb65-0e12e57ceb50
-- title:
--   Auxiliary process (6), valid words and heights
-- statement:
--   Fix a matrix $A\in\mathbb Q^{m\times m}$, a score vector $f\in\mathbb Q^m$ and a total priority order on the actions. The **auxiliary process** is
--   $$u_0=f,\qquad i_t=\text{the highest-priority maximizer of }u_t,\qquad u_{t+1}=u_t+Ae_{i_t}.$$
--   The **height** of a score state is $H=\max_i u_i$. A word is **valid** from a score state when, after every proper prefix, its next action maximizes the score over every action of the game and wins any tie by priority; actions absent from the word still take part in the comparison. A **bundle** is a concatenation $W(a)W(a+1)\cdots W(a+L-1)$ of consecutive phase words.
--
--   All of the construction is stated for this process. It is realized as fictitious play at the end, by the setup game.
--
--   **Formalization Note** A total priority is an injective map `rank` into the natural numbers, lower rank first. The theorems that need injectivity state it, or get it from `IsClock`.
-- source:
--   Abernethy, Lazarsfeld, Wibisono, Arbitrarily Slow Polynomial Convergence of Fictitious Play, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), p.13, eq. (6)

import Mathlib

open Matrix

namespace ArbSlowFP

variable {ι : Type*}

/-- One play of the auxiliary process (6), p.13: `u ↦ u + Ae_a`. -/
def play (A : Matrix ι ι ℚ) (u : ι → ℚ) (a : ι) : ι → ℚ := fun i => u i + A i a

/-- The score state after a word `w` starting from the score state `u`. -/
def scoreAfter (A : Matrix ι ι ℚ) (u : ι → ℚ) (w : List ι) : ι → ℚ := w.foldl (play A) u

/-- The action-count vector of a word (the plays of each action), as a rational vector. -/
def wordCount [DecidableEq ι] (w : List ι) (i : ι) : ℚ := (w.count i : ℚ)

/-- The height `max_i u_i` of a score state, p.13. -/
def height [Fintype ι] [Nonempty ι] (u : ι → ℚ) : ℚ := Finset.univ.sup' Finset.univ_nonempty u

/-- `a` is the highest-priority maximizer of `u`, as in (6), p.13: it maximizes the score over every
action, and wins any tie.

**Formalization Note.** A total priority order `≺` is encoded by an injective `rank : ι → ℕ`, where
a lower rank is a higher priority ("earlier in ≺ means higher priority"). Each theorem that uses
it assumes injectivity. -/
def IsPriorityMax (rank : ι → ℕ) (u : ι → ℚ) (a : ι) : Prop :=
  (∀ i, u i ≤ u a) ∧ ∀ i, u i = u a → rank a ≤ rank i

/-- `a` is the unique maximizer of `u`. -/
def IsUniqueMax (u : ι → ℚ) (a : ι) : Prop := ∀ i, i ≠ a → u i < u a

/-- A word is valid from a score state (p.13) "when, after every proper prefix, its next action
maximizes the score over every action in the game and wins any tie by priority. Actions absent
from the word are still included in this comparison." -/
def ValidFrom (A : Matrix ι ι ℚ) (rank : ι → ℕ) : (ι → ℚ) → List ι → Prop
  | _, [] => True
  | u, a :: w => IsPriorityMax rank u a ∧ ValidFrom A rank (play A u a) w

/-- The score state `u_t = f + Az_t` of (6), p.13, after the plays `i 0, …, i (t-1)`. -/
def procScore (A : Matrix ι ι ℚ) (f : ι → ℚ) (i : ℕ → ι) (t : ℕ) : ι → ℚ :=
  scoreAfter A f ((List.range t).map i)

/-- The auxiliary process (6), p.13: `i t` is the highest-priority maximizer of `u_t` at every `t`. -/
def IsPriorityRun (A : Matrix ι ι ℚ) (rank : ι → ℕ) (f : ι → ℚ) (i : ℕ → ι) : Prop :=
  ∀ t, IsPriorityMax rank (procScore A f i t) (i t)

/-- The bundle `W(a) W(a+1) ⋯ W(a+L-1)` of consecutive phase words, Lemma 4.2, p.26. -/
def bundle (W : ℕ → List ι) (a L : ℕ) : List ι := (List.range L).flatMap fun s => W (a + s)

end ArbSlowFP


