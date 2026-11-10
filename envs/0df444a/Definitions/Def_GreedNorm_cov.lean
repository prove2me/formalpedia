-- Prove2me | Definitions.Def_GreedNorm_cov
-- name    : GreedNorm_cov
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:43:47.570317+00:00
-- url     : https://prove2.me/theorems/0f08ee7e-e688-4e82-a06b-337d3a3b4d77
-- title:
--   Coverage $\mathrm{cov}(\mathcal A)$ of a configuration set
-- statement:
--   A **configuration** is a pair $(i,S)$ with $i\in[m]$ (its type) and $S\subseteq U$. For a set $\mathcal A$ of configurations,
--
--   $$
--   \mathrm{cov}(\mathcal A)=\bigcup_{(i,S)\in\mathcal A} S .
--   $$
--
--   **Formalization Note** Configurations are `Fin m × Finset U`; configuration sets are `Finset`s. The paper's "at most $m$ configurations" is not built in; it follows from validity.
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), §3.2, p.7 (PDF 9)

import Mathlib

namespace GreedNorm

/-- **The coverage `cov(A) = ⋃_{(i,S) ∈ A} S` of a configuration set.**
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), §3.2 "Expressing ThreshBudgAlloc in terms of configurations", p.7 (PDF 9): "A configuration
is a tuple (i, S) consisting of a subset S ⊆ U and i ∈ [m]. [...] define cov(A) = ⋃_{(i,S)∈A} S."

**Formalization Note** A configuration is a pair `(i, S) : Fin m × Finset U` (types 0-based); a
configuration set is a `Finset` of configurations. The paper's bound "at most m configurations"
is not built in; it follows from validity (`IsValidConf`). -/
def cov {m : ℕ} {U : Type} [DecidableEq U] (A : Finset (Fin m × Finset U)) : Finset U :=
  A.biUnion Prod.snd

end GreedNorm


