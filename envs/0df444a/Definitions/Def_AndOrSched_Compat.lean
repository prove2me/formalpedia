-- Prove2me | Definitions.Def_AndOrSched_Compat
-- name    : AndOrSched_Compat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:28:19.496334+00:00
-- url     : https://prove2.me/theorems/6fac971c-8b98-47a7-9761-7e69ff1333e2
-- title:
--   Orders produced by the tie-breaking rule
-- statement:
--   Given sort keys $\kappa_j\in\mathbb N$ for the jobs, an order $\prec$ is **compatible** if
--   1. it is non-decreasing in the keys;
--   2. $a\prec b$ whenever $a\in\mathcal P(b)$ and $\kappa_a=\kappa_b$;
--   3. $i\prec j$ whenever $(i,j)\in E_\wedge$ and $\kappa_i=\kappa_j$.
--
--   "Break all other ties arbitrarily": every compatible order is a possible output of Algorithm 1 (keys $t^\alpha_a$, $t^\beta_b$) and Algorithm 2 (keys $l^\alpha_a$, $l^\beta_b$).
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §2, p.7 and p.9, "Sort the jobs in order of non-decreasing values … Break all other ties arbitrarily."

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_andRel
import Definitions.Def_AndOrSched_orPred
open scoped Classical NNReal

namespace AndOrSched

/-- The orders `≺` that Algorithms 1 and 2 may produce from given sort keys (Happach, Schulz, arXiv:2001.07011v1, §2, p.7 and
p.9): "Sort the jobs in order of non-decreasing values tαa (a ∈ A) and tβb (b ∈ B) … If there is
b ∈ B and a ∈ P(b) with tαa = tβb, then set a ≺ b. Similarly, set i ≺ j, if (i, j) ∈ E∧ and tαi = tαj
(for i, j ∈ A) or tβi = tβj (for i, j ∈ B). … Break all other ties arbitrarily."

**Formalization Note** `key j` is the sort key of job `j` (its `α`- or `β`-point, resp. interval;
see `key`). An order is a bijection `σ : N ≃ Fin |N|`; `Compat I key σ` says that `σ` is
non-decreasing in `key` and respects the two tie rules. "Break all other ties arbitrarily" is
read as: every such `σ` is a possible output. -/
def Compat (I : Instance) (key : I.N → ℕ) (σ : I.N ≃ Fin (Fintype.card I.N)) : Prop :=
  (∀ i j, σ i < σ j → key i ≤ key j) ∧
  (∀ b, ∀ a ∈ orPred I b, key (Sum.inl a) = key (Sum.inr b) → σ (Sum.inl a) < σ (Sum.inr b)) ∧
  (∀ i j, andRel I i j → key i = key j → σ i < σ j)

end AndOrSched


