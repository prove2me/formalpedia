-- Prove2me | Definitions.Def_SingleOrSample_IsValuation
-- name    : SingleOrSample_IsValuation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:46:52.362131+00:00
-- url     : https://prove2.me/theorems/0aa56f44-7bde-4f7a-b8f6-f07fa3312c81
-- title:
--   Valuation: non-decreasing and normalized at $\emptyset$
-- statement:
--   A **valuation** on a set of $m$ goods is a function $v:2^{[m]}\to\mathbb R$ that is non-decreasing, $v(S)\le v(T)$ for $S\subseteq T$, and normalized, $v(\emptyset)=0$. Nonnegativity follows from these two properties. This is the class of agent preferences of the paper, on which submodularity is then imposed.
--
--   **Formalization Note** Goods are `Fin m`, and bundles are `Finset (Fin m)`. Monotonicity is the published `SubsamplingSM.Offline.IsMonotoneSetFn`.
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), §2.1, p.5

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsMonotoneSetFn

namespace SingleOrSample

/-- A **valuation** on `m` goods: non-decreasing with `v ∅ = 0` (Chawla, Huang, Kulkarni, Mehta,
Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission,
arXiv:2609.32286, manuscript sha256 28cd3d7b…, §2.1, p.5).

**Formalization Note.** The page's "non-negative" follows from the two fields, so it is not a third
field. Monotonicity is the published `SubsamplingSM.Offline.IsMonotoneSetFn`. -/
def IsValuation {m : ℕ} (v : Finset (Fin m) → ℝ) : Prop :=
  SubsamplingSM.Offline.IsMonotoneSetFn v ∧ v ∅ = 0

end SingleOrSample


