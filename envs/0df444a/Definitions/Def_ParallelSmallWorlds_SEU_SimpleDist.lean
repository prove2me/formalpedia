-- Prove2me | Definitions.Def_ParallelSmallWorlds_SEU_SimpleDist
-- name    : ParallelSmallWorlds_SEU_SimpleDist
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:04.17202+00:00
-- url     : https://prove2.me/theorems/18df2525-6b19-4481-8cb6-1e17a359113f
-- title:
--   Simple distributions $\mathcal P_S$, degenerate gambles $\Psi_c$, two-point gambles $c_1\alpha c_2$, expectation
-- statement:
--   A **simple distribution** over a set $X$ is a function $p:X\to\mathbb R$ with finite support, nonnegative values and $\sum_x p(x)=1$; the set of simple distributions over the consequences $C_w$ is $\mathcal P_{S_w}$. Three constructions are attached:
--
--   1. the **degenerate distribution** $\Psi_x$, giving probability $1$ to $x$;
--   2. the **two-point gamble** $x\,\alpha\,y$ for $\alpha\in[0,1]$, giving probability $\alpha$ to $x$ and $1-\alpha$ to $y$ (when $x=y$ it is $\Psi_x$);
--   3. the **expectation** of $u:X\to\mathbb R$ under $p$,
--
--   $$E(u\mid p)=\sum_{x} p(x)\,u(x).$$
--
--   These are the bets of the paper's utility axioms: the decision maker compares consequences with simple bets on the reference experiment, and Lemma 2 represents her preferences between such bets by expected utility.
--
--   **Formalization Note** A simple distribution is a `Finsupp` with two proof fields; the probability $\alpha$ of a two-point gamble is an element of `unitInterval`.
-- source:
--   French, Axiomatising the Bayesian Paradigm in Parallel Small Worlds, author's accepted manuscript OPRE-2018-05-258 (WRAP 118263), pp.23–24 (PDF pp.24–25), definitions of PSw, Ψc (PSW10(c)) and c1αc2; Lemma 2, p.26

import Mathlib

namespace ParallelSmallWorlds.SEU

/-- **Simple distributions** (the set `PSw` of p.23, PDF p.24: "PSw, the set of simple
distributions over Cw, i.e. distributions that give positive probability to a finite number of
elements of Cw").
S. French, *Axiomatising the Bayesian Paradigm in Parallel Small Worlds*, author's accepted
manuscript OPRE-2018-05-258 (WRAP 118263), pp.23–25.

A `SimpleDist X` is a finitely supported function `p : X →₀ ℝ` with nonnegative values summing
to `1`. Also defined here:

* `SimpleDist.pure x` — the degenerate distribution `Ψx` of PSW10(c), p.24;
* `SimpleDist.twoPt x y α` — the two-point distribution `x α y` of p.24, giving probability
  `α` to `x` and `1 − α` to `y` (`α ∈ [0,1]`, as `unitInterval`);
* `SimpleDist.expect p u = Σ_x p(x) u(x)` — the expectation `E(u | p)` of Lemma 2, p.26.

**Formalization Note.** A simple distribution is a `Finsupp`, not a `PMF`. When `x = y`,
`twoPt x x α` is `Ψx`. -/
structure SimpleDist (X : Type*) where
  /-- The probability weights, finitely supported. -/
  toFun : X →₀ ℝ
  /-- The weights are nonnegative. -/
  nonneg : ∀ x, 0 ≤ toFun x
  /-- The weights sum to one. -/
  sum_eq_one : toFun.sum (fun _ r => r) = 1

namespace SimpleDist

variable {X : Type*}

/-- The degenerate distribution `Ψx` giving probability `1` to `x` (PSW10(c), p.24). -/
noncomputable def pure (x : X) : SimpleDist X where
  toFun := Finsupp.single x 1
  nonneg y := by
    classical
    rw [Finsupp.single_apply]
    split_ifs <;> norm_num
  sum_eq_one := by
    rw [Finsupp.sum_single_index rfl]

/-- The two-point distribution `x α y` (p.24): probability `α` to `x`, `1 − α` to `y`. -/
noncomputable def twoPt (x y : X) (α : unitInterval) : SimpleDist X where
  toFun := Finsupp.single x (α : ℝ) + Finsupp.single y (1 - (α : ℝ))
  nonneg z := by
    classical
    have h1 : (0 : ℝ) ≤ α := α.2.1
    have h2 : (α : ℝ) ≤ 1 := α.2.2
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> linarith
  sum_eq_one := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl]
    ring

/-- The expectation `E(u | p) = Σ_x p(x) u(x)` of `u : X → ℝ` under `p` (Lemma 2, p.26). -/
noncomputable def expect (p : SimpleDist X) (u : X → ℝ) : ℝ :=
  p.toFun.sum (fun x r => r * u x)

end SimpleDist

end ParallelSmallWorlds.SEU


