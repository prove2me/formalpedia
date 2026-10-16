-- Prove2me | Definitions.Def_EngagementOpt_Misalign_Model
-- name    : EngagementOpt_Misalign_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T08:05:17.443258+00:00
-- url     : https://prove2.me/theorems/01ace252-3caf-452e-84ad-889aeceb2807
-- title:
--   §4, pp. 15–16 — the parameter space Ω, the functions g_S, g_T and the maximizers (3), (4)
-- statement:
--   The engagement model of Kleinberg, Mullainathan and Raghavan (§2.1 and §4).
--
--   A **content distribution** is a triple $\omega=(p,q,\bar v)$ of real numbers: the **moreishness** $p$ (the probability that the impulsive system 1 is hooked by an item and consumes the next one), the **span** $q$ (the probability that the forward-looking system 2 still wants to continue after an item), and the **value** $\bar v$ (the mean value of an item to system 2). The parameter space is
--   $$\Omega=[0,1)\times[0,1)\times\mathbb R_{+},$$
--   i.e. $0\le p<1$, $0\le q<1$ and $\bar v\ge 0$. A **content manifold** is a set $\mathcal M\subseteq\Omega$.
--
--   With $W$ the per-step outside option of the user, define
--   $$g_S(\omega)=\frac{\bar v-W}{1-q}-\frac{pW}{1-p},\qquad g_T(\omega)=\frac{1}{1-q}+\frac{p}{1-p}.$$
--   When the user participates, these are system 2's expected utility $\mathbb E[S]$ (equation (1)) and the expected session length $\mathbb E[T]$ (equation (2)).
--
--   1. $\omega_S$ is a **utility maximizer** (3) if $\omega_S\in\mathcal M$ and $g_S(\omega_S)\ge g_S(\omega)$ for every $\omega\in\mathcal M$.
--   2. $\omega_T$ is an **engagement maximizer** (4) if $\omega_T\in\mathcal M$, $g_S(\omega_T)\ge 0$, and $g_T(\omega_T)\ge g_T(\omega)$ for every $\omega\in\mathcal M$ with $g_S(\omega)\ge0$.
--
--   These are the objects in which the paper's characterization of the misalignment between utility and engagement (Theorem 4.1) is stated.
--
--   **Formalization Note** A content distribution is a structure with three real fields; membership in $\Omega$ is the predicate `InOmega`, imposed by the theorems on the points they use (Lean's $x/0=0$ would otherwise give junk values at $p=1$ or $q=1$). The outside option $W$ is a real parameter; the paper normalizes $W=1$ but keeps $W$ in every formula. The paper writes $\arg\max$ with "ties broken consistently"; here a maximizer is any point attaining the maximum, so the theorems hold for every choice of maximizer. The paper's assumption that $\mathcal M$ is closed only ensures that maximizers exist, and is not part of these definitions.
-- source:
--   Kleinberg, Mullainathan, Raghavan, The Challenge of Understanding What Users Want, arXiv:2202.11776v3, p. 15, Ω and content manifold; p. 16, g_S, g_T, (3), (4); pp. 7–8, (1), (2); p. 5, outside option W

import Mathlib

/-!
# The engagement-optimization model of Kleinberg, Mullainathan and Raghavan (§2.1, §4)

Kleinberg, Mullainathan, Raghavan, *The Challenge of Understanding What Users Want*,
arXiv:2202.11776v3: the parameter space `Ω` and content manifolds (p. 15), the functions
`g_S`, `g_T` and the maximizers (3), (4) (p. 16). The outside option `W` (p. 5) is kept as a
parameter.
-/

namespace EngagementOpt.Misalign

/-- A content distribution `ω = (p, q, v̄)`: moreishness `p`, span `q`, value `v̄` (p. 15). -/
structure Params where
  /-- moreishness `p` -/
  p : ℝ
  /-- span `q` -/
  q : ℝ
  /-- value `v̄` -/
  v : ℝ

/-- Membership in `Ω = [0, 1) × [0, 1) × ℝ₊` (p. 15). -/
def InOmega (ω : Params) : Prop :=
  0 ≤ ω.p ∧ ω.p < 1 ∧ 0 ≤ ω.q ∧ ω.q < 1 ∧ 0 ≤ ω.v

/-- `g_S(ω) = (v̄ − W)/(1 − q) − pW/(1 − p)` (p. 16), with outside option `W`. -/
noncomputable def gS (W : ℝ) (ω : Params) : ℝ :=
  (ω.v - W) / (1 - ω.q) - ω.p * W / (1 - ω.p)

/-- `g_T(ω) = 1/(1 − q) + p/(1 − p)` (p. 16). -/
noncomputable def gT (ω : Params) : ℝ :=
  1 / (1 - ω.q) + ω.p / (1 - ω.p)

/-- (3), p. 16: `ω_S ∈ M` is a maximizer of `g_S` over the whole content manifold `M`. -/
def IsUtilityMaximizer (W : ℝ) (M : Set Params) (ωS : Params) : Prop :=
  ωS ∈ M ∧ IsMaxOn (gS W) M ωS

/-- (4), p. 16: `ω_T ∈ M` satisfies `g_S(ω_T) ≥ 0` and maximizes `g_T` over
`{ω ∈ M : g_S(ω) ≥ 0}`. -/
def IsEngagementMaximizer (W : ℝ) (M : Set Params) (ωT : Params) : Prop :=
  ωT ∈ M ∧ 0 ≤ gS W ωT ∧ IsMaxOn gT {ω | ω ∈ M ∧ 0 ≤ gS W ω} ωT

end EngagementOpt.Misalign


