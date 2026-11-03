-- Prove2me | Definitions.Def_RiskAverseConsistency_epsSolutionSet
-- name    : RiskAverseConsistency_epsSolutionSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:22:26.66313+00:00
-- url     : https://prove2.me/theorems/06d22ef4-4228-45a1-a83b-173d6cc39d83
-- title:
--   $\varepsilon$-solution set
-- statement:
--   For a set $S$, $g:S\to[-\infty,\infty]$ and $\varepsilon\ge0$, the **$\varepsilon$-solution set** is
--
--   $$
--   \mathscr S^{\varepsilon}=\Bigl\{z\in S:\ g(z)\le\inf_{v\in S}g(v)+\varepsilon\Bigr\}.
--   $$
--
--   It is the paper's $\mathscr S^{\varepsilon_k}_k$ (p.6) and the set $\hat{\mathscr S}^r_N$ of $r$-minimizers of (10) (p.9).
--
--   **Formalization Note** The paper defines it only when the infimum is finite (p.4); here it is total, and the theorems carry the finiteness where the paper relies on it.
-- source:
--   Milz, Surowiec, Asymptotic consistency for nonconvex risk-averse stochastic optimization with infinite dimensional decision spaces, arXiv:2207.14756v2, p.4; p.6; p.9

import Mathlib
import Definitions.Def_RiskAverseConsistency_optimalValue

namespace RiskAverseConsistency

/-- The **ε-solution set** `{z ∈ S : g(z) ≤ inf_{v ∈ S} g(v) + ε}`.

Milz, Surowiec, arXiv:2207.14756v2, p.4 (`S^ε`), (5)–following display, p.6 (`𝒮^{εₖ}ₖ`), and p.9
(`Ŝ^r_N`, the set of `r`-minimizers of (10)).

Formalization Note: the paper defines it only when the infimum is finite; the definition here is
total, and the theorems state the finiteness where the paper relies on it. -/
noncomputable def epsSolutionSet {V : Type*} (S : Set V) (g : V → EReal) (ε : ℝ) : Set V :=
  {z | z ∈ S ∧ g z ≤ optimalValue S g + (ε : EReal)}

end RiskAverseConsistency


