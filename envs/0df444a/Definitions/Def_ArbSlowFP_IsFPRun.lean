-- Prove2me | Definitions.Def_ArbSlowFP_IsFPRun
-- name    : ArbSlowFP_IsFPRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:45:49.155203+00:00
-- url     : https://prove2.me/theorems/0abc7a07-c037-4ba0-bd85-d2cb60ac83a7
-- title:
--   Duality gap (2), count vectors and simultaneous fictitious play (3)
-- statement:
--   For a payoff matrix $A$ with finitely many rows and columns, the **duality gap** of a pair of vectors is
--   $$\mathrm{Gap}_A(p,q)=\max_i (Aq)_i-\min_j (A^\top p)_j .$$
--   A play sequence $i_0,i_1,\dots$ has **cumulative count vector** $x_t$ after $t$ rounds, whose entry at an action is the number of rounds $s<t$ in which that action was played, and **empirical strategy** $x_t/t$. **Simultaneous fictitious play** from zero counts consists of two play sequences $(i_t)$, $(j_t)$ such that at every time $t\ge 0$,
--   $$ i_t\in\arg\max_i (Ay_t)_i,\qquad j_t\in\arg\min_j (A^\top x_t)_j ,$$
--   where $x_t$, $y_t$ are the count vectors of $(i_t)$ and $(j_t)$. Ties may be broken in any way.
--
--   These objects state the main theorem. The row and column best-response sets are named so that uniqueness can be stated on both.
--
--   **Formalization Note** Plays are functions of time and the counts are computed from them, so $x_0=y_0=0$ holds by construction. A rational payoff matrix is cast to the reals by `toReal`.
-- source:
--   Abernethy, Lazarsfeld, Wibisono, Arbitrarily Slow Polynomial Convergence of Fictitious Play, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), pp.1–2, eqs. (2), (3)

import Mathlib

open Matrix

namespace ArbSlowFP

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The duality gap (2) of Abernethy, Lazarsfeld, Wibisono, *Arbitrarily Slow Polynomial Convergence
of Fictitious Play*, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), p.2:
`Gap_A(p, q) = max_i (Aq)_i − min_j (A⊤p)_j`.

**Formalization Note.** The action types are finite, so the supremum and the infimum are a maximum
and a minimum as soon as the type is nonempty; every use has a nonempty action type. -/
noncomputable def gap (A : Matrix m n ℝ) (p : m → ℝ) (q : n → ℝ) : ℝ :=
  (⨆ i, (A *ᵥ q) i) - (⨅ j, (Aᵀ *ᵥ p) j)

open Classical in
/-- The cumulative count vector of a play sequence after `t` completed rounds, p.2: entry `b` is
the number of rounds `s < t` with `a s = b`. At `t = 0` it is the zero vector. -/
noncomputable def countVec {α : Type*} (a : ℕ → α) (t : ℕ) (b : α) : ℝ :=
  (((Finset.range t).filter (fun s => a s = b)).card : ℝ)

/-- The empirical strategy `x_t / t` of p.2. It is only used at `t ≥ 1`. -/
noncomputable def empirical {α : Type*} (a : ℕ → α) (t : ℕ) (b : α) : ℝ :=
  countVec a t b / (t : ℝ)

/-- The row player's best-response set `arg max_i (Ay)_i` of (3), p.2. -/
def rowBR (A : Matrix m n ℝ) (y : n → ℝ) : Set m :=
  {a | ∀ a', (A *ᵥ y) a' ≤ (A *ᵥ y) a}

/-- The column player's best-response set `arg min_j (A⊤x)_j` of (3), p.2. -/
def colBR (A : Matrix m n ℝ) (x : m → ℝ) : Set n :=
  {b | ∀ b', (Aᵀ *ᵥ x) b ≤ (Aᵀ *ᵥ x) b'}

/-- Simultaneous fictitious play (3), p.2, from zero counts: at every time `t ≥ 0` the action `i t`
is a best response to the column player's counts after `t` rounds, and `j t` is a best response to
the row player's counts after `t` rounds. The plays are the data: ties may be broken in any way.

**Formalization Note.** Plays are functions of time and the counts are computed from them, so
`x₀ = y₀ = 0` holds by construction. -/
def IsFPRun (A : Matrix m n ℝ) (i : ℕ → m) (j : ℕ → n) : Prop :=
  ∀ t, i t ∈ rowBR A (countVec j t) ∧ j t ∈ colBR A (countVec i t)

/-- The cast to `ℝ` of a rational payoff matrix. -/
def toReal (A : Matrix m n ℚ) : Matrix m n ℝ := A.map (fun x => (x : ℝ))

end ArbSlowFP


