-- Prove2me | Definitions.Def_TreeMultiflow_ipOpt
-- name    : TreeMultiflow_ipOpt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:01:38.4002+00:00
-- url     : https://prove2.me/theorems/8fadfd6d-b6e1-446f-a744-b5fdd8980980
-- title:
--   Integral optimum
-- statement:
--   The **integral optimum** is
--   $$
--   \mathrm{IP}^*=\max\Bigl\{w(S)=\sum_{f\in S} w_f : S\subseteq F \text{ feasible}\Bigr\}.
--   $$
--
--   **Formalization Note** $F$ is finite and $S=\varnothing$ is feasible, so the real supremum is this maximum.
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Section 1, p.2 (w(S); the integral optimum)

import Mathlib
import Definitions.Def_TreeMultiflow_IsFeasible

namespace TreeMultiflow

/-- **Integral optimum.**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Section 1,
p.2: "the integral optimum", the maximum of `w(S) = Σ_{f∈S} w_f` over feasible subsets `S`.

`ipOpt G u src dst w` is the supremum of `Σ_{f ∈ S} w f` over the feasible `S : Finset F`.

**Formalization Note.** `F` is finite, so the set of values is finite; it is nonempty (`S = ∅` is
feasible), so the real `sSup` is the maximum. -/
noncomputable def ipOpt {V F : Type*} [Fintype F] (G : SimpleGraph V) (u : Sym2 V → ℕ)
    (src dst : F → V) (w : F → ℝ) : ℝ :=
  sSup {v : ℝ | ∃ S : Finset F, IsFeasible G u src dst S ∧ v = ∑ f ∈ S, w f}

end TreeMultiflow


