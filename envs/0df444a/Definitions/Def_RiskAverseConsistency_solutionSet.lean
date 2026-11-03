-- Prove2me | Definitions.Def_RiskAverseConsistency_solutionSet
-- name    : RiskAverseConsistency_solutionSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:22:22.880632+00:00
-- url     : https://prove2.me/theorems/12f73097-1ebe-4b60-a1fd-fa4258b5c709
-- title:
--   Solution set
-- statement:
--   For a set $S$ and $g:S\to[-\infty,\infty]$, the **solution set** is
--
--   $$
--   \mathscr S=\Bigl\{z\in S:\ g(z)=\inf_{v\in S}g(v)\Bigr\}.
--   $$
--
--   It is the paper's $\mathscr S$ in Proposition 5 (p.6) and the solution set of (8) (p.9).
--
--   **Formalization Note** The paper defines it only when the infimum is finite (p.4); here it is total, and the theorems carry the finiteness where the paper relies on it.
-- source:
--   Milz, Surowiec, Asymptotic consistency for nonconvex risk-averse stochastic optimization with infinite dimensional decision spaces, arXiv:2207.14756v2, p.4; p.6; p.9

import Mathlib
import Definitions.Def_RiskAverseConsistency_optimalValue

namespace RiskAverseConsistency

/-- The **solution set** `{z ∈ S : g(z) = inf_{v ∈ S} g(v)}`.

Milz, Surowiec, arXiv:2207.14756v2, p.6 (`𝒮 := {z ∈ Z_ad : f(z) + φ(z) = 𝔪*}`) and p.9 (`𝒮`, the
solution set of (8)).

Formalization Note: the paper defines it only when the infimum is finite (p.4); the definition
here is total, and the theorems state the finiteness where the paper relies on it. -/
noncomputable def solutionSet {V : Type*} (S : Set V) (g : V → EReal) : Set V :=
  {z | z ∈ S ∧ g z = optimalValue S g}

end RiskAverseConsistency


