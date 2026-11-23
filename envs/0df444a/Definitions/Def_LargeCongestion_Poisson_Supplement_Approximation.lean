-- Prove2me | Definitions.Def_LargeCongestion_Poisson_Supplement_Approximation
-- name    : LargeCongestion_Poisson_Supplement_Approximation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:28:37.093602+00:00
-- url     : https://prove2.me/theorems/e0fbef98-0f5c-4386-895c-790a88a8468a
-- title:
--   §6 — additive epsilon-Wardrop equilibrium (30) and derivatives on the closed load interval
-- statement:
--   For nonnegative error $\varepsilon$, an additive $\varepsilon$-Wardrop equilibrium is a feasible pair $(y,x)\in F(d)$ with
--   $$y_{t,s}>0\ \Longrightarrow\ \sum_{e\in s}C_e(x_e)\le\sum_{e\in s'}C_e(x_e)+\varepsilon\qquad(s,s'\in S_t).$$
--   This is (30), with the same feasible-pair representation as the published Wardrop definition. It is the hypothesis of Proposition 2(a).
--
--   A separate derivative interface supplies values $D_e(x)$ satisfying the derivative relation for $C_e$ on the closed interval $[0,d_{\max}]$. Endpoints use derivatives within that interval. On a singleton interval the derivative relation is harmless because feasible loads are zero. This expresses the source's interval derivative assumptions without imposing differentiability at negative loads or any extension beyond the interval.
-- source:
--   Cominetti, Scarsini, Schröder & Stier-Moses, Approximation and Convergence of Large Atomic Congestion Games, arXiv:2001.02797v7, pp. 24–25, (30), Proposition 2, Theorem 5

import Mathlib
import Definitions.Def_LargeCongestion_Poisson_Supplement_Weighted

namespace LargeCongestion.Poisson.Supplement

variable {E T : Type*} [Fintype E] [DecidableEq E] [Fintype T] [DecidableEq T]

/-- Additive epsilon-Wardrop condition (30), including the usual epsilon ≥ 0 convention. -/
def IsEpsWardrop (S : T → Finset (Finset E)) (C : E → ℝ → ℝ) (d : T → ℝ)
    (ε : ℝ) (y : T → Finset E → ℝ) (x : E → ℝ) : Prop :=
  0 ≤ ε ∧ IsFeasible S d y x ∧
    ∀ t, ∀ s ∈ S t, ∀ s' ∈ S t, 0 < y t s →
      ∑ e ∈ s, C e (x e) ≤ (∑ e ∈ s', C e (x e)) + ε

/-- Derivatives on the closed load interval; the endpoints use one-sided derivatives.
On a degenerate interval this imposes no spurious differentiability outside the domain. -/
def HasCostDerivative (C D : E → ℝ → ℝ) (dmax : ℝ) : Prop :=
  ∀ e x, x ∈ Set.Icc 0 dmax → HasDerivWithinAt (C e) (D e x) (Set.Icc 0 dmax) x

end LargeCongestion.Poisson.Supplement


