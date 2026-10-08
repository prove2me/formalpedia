-- Prove2me | Definitions.Def_BanditGD_Regret_Setting
-- name    : BanditGD_Regret_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T08:04:41.02808+00:00
-- url     : https://prove2.me/theorems/e9624d54-0195-4244-8f5f-89496c166030
-- title:
--   Figure 1, p. 7 and Lemma 2, p. 6 — the BGD(α, δ, ν) run and the expected-gradient-descent run
-- statement:
--   This file fixes the two algorithms analysed by Flaxman, Kalai and McMahan. Points live in $\mathbb R^d$ with the Euclidean norm $|\cdot|$. For a set $K\subseteq\mathbb R^d$, $P_K(z)$ denotes a nearest point of $K$ to $z$, i.e. a point $y\in K$ with $|y-z|\le|w-z|$ for every $w\in K$. Rounds are numbered $t=1,2,\dots$
--
--   1. **Bandit gradient descent, $\mathrm{BGD}(\alpha,\delta,\nu)$ (Figure 1).** Let $S\subseteq\mathbb R^d$ be the feasible set, $c_1,c_2,\dots:\mathbb R^d\to\mathbb R$ the cost functions, and $u_1,u_2,\dots$ a realization of the directions (unit vectors drawn uniformly at random in the algorithm). A sequence $y_1,y_2,\dots$ is a run of $\mathrm{BGD}(\alpha,\delta,\nu)$ when $y_1=0$ and, for every $t\ge1$, with the played point $x_t=y_t+\delta u_t$,
--   $$y_{t+1}=P_{(1-\alpha)S}\big(y_t-\nu\,c_t(x_t)\,u_t\big),$$
--   where $(1-\alpha)S=\{(1-\alpha)s : s\in S\}$ is the shrunk feasible set.
--   2. **Expected gradient descent (Lemma 2).** Given vectors $g_1,g_2,\dots$ and a step size $\eta$, a sequence $x_1,x_2,\dots$ is an expected-gradient-descent run on $S$ when $x_1=0$ and
--   $$x_{t+1}=P_S(x_t-\eta\,g_t)\qquad(t\ge1).$$
--
--   The algorithm only ever evaluates $c_t$ at the single point $x_t$; this is the bandit feedback model. Both definitions describe one realization: random runs are obtained by requiring them for every outcome $\omega$ of the underlying probability space.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`. The projection is the published predicate `IsNearestPoint K z y` (module `Def_RegretBandits_Nonlinear_OSGD`), so a run is a relation, not a function; for a nonempty closed convex set the nearest point exists and is unique, so the run is then determined by its inputs. The values at index $0$ are never used. The arguments are in Figure 1's order $(\alpha,\delta,\nu)$; Theorem 1 prints "BGD(ν, δ, α)" for the same algorithm.
-- source:
--   Flaxman, Kalai, McMahan, arXiv:cs/0408007v1, p. 7, Figure 1; p. 6, Lemma 2; p. 4, §1.4 (projection P_S)

import Mathlib
import Definitions.Def_RegretBandits_Nonlinear_OSGD
open scoped Pointwise

namespace BanditGD.Regret

/-- `(u, y)` is a run of `BGD(α, δ, ν)` (Flaxman, Kalai, McMahan, arXiv:cs/0408007v1, p. 7,
Figure 1) on the feasible set `S ⊆ ℝ^d` against the cost functions `c 1, c 2, …`, for one
realization `u 1, u 2, …` of the random directions: `y 1 = 0`, and at every period `t ≥ 1` the
point played is `x_t = y t + δ • u t` and
`y (t + 1) = P_{(1-α)S}(y t - ν c_t(x_t) u_t)`, the nearest point of the shrunk set `(1 - α) • S`
to `y t - ν c_t(x_t) u_t`. Rounds are `t = 1, 2, …`; the values `u 0`, `y 0` are never used. -/
def IsBGDRun {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (α δ ν : ℝ)
    (c : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (u y : ℕ → EuclideanSpace ℝ (Fin d)) : Prop :=
  y 1 = 0 ∧ ∀ t : ℕ, 1 ≤ t →
    RegretBandits.Nonlinear.IsNearestPoint ((1 - α) • S)
      (y t - (ν * c t (y t + δ • u t)) • u t) (y (t + 1))

/-- `x` is a run of expected gradient descent (p. 6, Lemma 2) on `S` with step size `η`, driven by
the vectors `g 1, g 2, …`: `x 1 = 0` and `x (t + 1) = P_S(x t - η • g t)` for every `t ≥ 1`, with
`P_S` the nearest-point projection onto `S`. The value `x 0` is never used. -/
def IsExpectedGDRun {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (η : ℝ)
    (g x : ℕ → EuclideanSpace ℝ (Fin d)) : Prop :=
  x 1 = 0 ∧ ∀ t : ℕ, 1 ≤ t →
    RegretBandits.Nonlinear.IsNearestPoint S (x t - η • g t) (x (t + 1))

end BanditGD.Regret


