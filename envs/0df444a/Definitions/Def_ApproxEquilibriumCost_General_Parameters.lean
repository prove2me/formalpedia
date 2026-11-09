-- Prove2me | Definitions.Def_ApproxEquilibriumCost_General_Parameters
-- name    : ApproxEquilibriumCost_General_Parameters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:46:29.769204+00:00
-- url     : https://prove2.me/theorems/1cc24cdb-8fd2-4ae6-9468-3b3ebdcdd85c
-- title:
--   Definition 3.1 — latency reduction μ, canonical root ρ, and threshold
-- statement:
--   For integer $d\ge1$ and $u\in[0,1]$, let
--
--   $$\mu_d(u)=u\bigl(1-(1-u)^{1/d}\bigr),\qquad b_d=\frac d{d+1},$$
--   $$\rho_d(\epsilon)=\inf\{u\in[0,1]:\epsilon(1-u)\le\mu_d(u)\}\quad(\epsilon\ge0).$$
--
--   The set in this infimum contains $1$ and is bounded below by $0$. Continuity and strict increase make the infimum exactly the unique root of $\mu_d(u)=\epsilon(1-u)$ in $[0,1)$ from Definition 3.1. The separate root-specification theorem states that interface explicitly. The formula for $\mu_d$ uses real powers; $\rho$ is zero outside the source parameter domain. These definitions contain no assumed analytic inequality or root axiom.
-- source:
--   Yu Cheng, Tianle Jiang, STOC 2027 submission #438 (October 2026), How Much Can Approximate Equilibria Change the Social Cost of Selfish Routing?, Definition 3.1; Lemma 3.6 threshold, printed p.10 = PDF p.10 (offset 0). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/438.pdf

import Mathlib

noncomputable section

namespace ApproxEquilibriumCost.General

/-- Definition 3.1, p.10. The source domain is d ≥ 1, x ∈ [0,1]. -/
def mu (d : ℕ) (x : ℝ) : ℝ := x * (1 - Real.rpow (1 - x) (1 / (d : ℝ)))

/-- Canonical construction of Definition 3.1's unique root. For d ≥ 1 the
set contains 1 and is bounded below by 0. Outside the source domain we use 0. -/
def rho (d : ℕ) (ε : ℝ) : ℝ :=
  if 1 ≤ d ∧ 0 ≤ ε then sInf {x : ℝ | x ∈ Set.Icc 0 1 ∧ ε * (1 - x) ≤ mu d x}
  else 0

/-- The exact minimization threshold in Lemma 3.6 and Theorem 3.2. -/
def criticalPoint (d : ℕ) : ℝ := (d : ℝ) / ((d : ℝ) + 1)

end ApproxEquilibriumCost.General


