-- Prove2me | Definitions.Def_RelaxedIndexability_Supplement_decisionBoundary
-- name    : RelaxedIndexability_Supplement_decisionBoundary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:02:02.387082+00:00
-- url     : https://prove2.me/theorems/312c3fec-546f-40f1-8f02-0042db769fc1
-- title:
--   Active set $A(m)$ and decision boundary $C(m)$
-- statement:
--   For one arm, a discount factor $\beta$ and a subsidy $m$, with $\mathbb X$ the belief simplex and $V_{\beta,m}(\omega;u)$ the optimal action values (13)–(14):
--
--   1. the **active set** is $A(m)=\mathbb X-P(m)=\{\omega\in\mathbb X:\ V_{\beta,m}(\omega;u=1)>V_{\beta,m}(\omega;u=0)\}$ (19);
--   2. the **decision boundary** is $C(m)=\{\omega\in\mathbb X:\ V_{\beta,m}(\omega;u=1)=V_{\beta,m}(\omega;u=0)\}$ (20).
--
--   Theorem 1 states its indexability criterion at the pairs $(\omega,m_\omega)$ with $\omega\in C(m_\omega)$.
-- source:
--   Liu, Relaxed Indexability and Index Policy for Partially Observable Restless Bandits, arXiv:2107.11939v4, (19)–(20), p.14

import Mathlib
import Definitions.Def_RelaxedIndexability_Supplement_optimalValue

namespace RelaxedIndexability.Supplement

variable {K : ℕ}

/-- **The active set `A(m) = {ω : V_{β,m}(ω; u = 1) > V_{β,m}(ω; u = 0)}`**
(Liu, arXiv:2107.11939v4, (19), p.14), a subset of the belief simplex. -/
def activeSet (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ) (B : Fin K → ℝ) (m : ℝ) :
    Set (Fin K → ℝ) :=
  {ω | ω ∈ stdSimplex ℝ (Fin K) ∧
    optimalActionValue β P B m false ω < optimalActionValue β P B m true ω}

/-- **The decision boundary `C(m) = {ω : V_{β,m}(ω; u = 1) = V_{β,m}(ω; u = 0)}`**
(Liu, arXiv:2107.11939v4, (20), p.14), a subset of the belief simplex. -/
def decisionBoundary (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ) (B : Fin K → ℝ) (m : ℝ) :
    Set (Fin K → ℝ) :=
  {ω | ω ∈ stdSimplex ℝ (Fin K) ∧
    optimalActionValue β P B m true ω = optimalActionValue β P B m false ω}

end RelaxedIndexability.Supplement


