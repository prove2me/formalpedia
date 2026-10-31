-- Prove2me | Definitions.Def_CompositeSAA_solutionSet
-- name    : CompositeSAA_solutionSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:31:42.891209+00:00
-- url     : https://prove2.me/theorems/5510946d-6f2b-44f6-ac3b-b4583ae17b9b
-- title:
--   Set of optimal solutions $S=\{u\in U:\rho(u)=\vartheta\}$
-- statement:
--   The **set of optimal solutions** of $\min_{u\in U}\rho(u)$ is
--
--   $$
--   S=\{u\in U:\ \rho(u)\le\rho(v)\ \text{for all } v\in U\}.
--   $$
--
--   When the minimum $\vartheta$ is attained this is the paper's $S=\{u\in U:\rho(u)=\vartheta\}$, and when it is not attained $S$ is empty.
-- source:
--   Dentcheva, Lin, Penev, arXiv:2201.01338v1, p.3 and display (8), p.5

import Mathlib

namespace CompositeSAA

/-- Dentcheva, Lin, Penev, arXiv:2201.01338v1, p.3 (`S = {u ∈ U : ϱ[u, X] = ϑ}`) and display (8),
p.5: the set of optimal solutions of `min_{u ∈ U} ρ(u)`.

**Formalization Note** Written as the set of minimizers `{u ∈ U | ∀ v ∈ U, ρ u ≤ ρ v}`. When the
minimum is attained this is the paper's `{u ∈ U : ρ(u) = ϑ}`; when it is not attained the set is
empty, as in the paper (no `u` attains a minimum that does not exist), instead of being
computed from a junk value of `sInf`. -/
def solutionSet {α : Type*} (ρ : α → ℝ) (U : Set α) : Set α :=
  {u | u ∈ U ∧ ∀ v ∈ U, ρ u ≤ ρ v}

end CompositeSAA


