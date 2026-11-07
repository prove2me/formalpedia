-- Prove2me | Definitions.Def_FairTeamContracts_IsAdditive
-- name    : FairTeamContracts_IsAdditive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:29:54.351943+00:00
-- url     : https://prove2.me/theorems/78871a4a-f5c8-4783-ac64-83b325347536
-- title:
--   Additive reward function $f(S)=\sum_{i\in S}f(i)$
-- statement:
--   A reward function $f$ on the agent set $N$ is **additive** if
--
--   $$f(S)=\sum_{i\in S}f(i)\qquad\text{for every }S\subseteq N,$$
--
--   where $f(i)=f(\{i\})$. For an additive $f$ the marginal contribution of an agent does not depend on the team, so its cut-off wage is $c_i/f(i)$. Additive functions are submodular; they are the first class for which the loss of non-discrimination is determined.
--
--   **Formalization Note** The identity is required for every set $S$, not only for singletons.
-- source:
--   Chen, Castiglioni, Li, Fair Team Contracts, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), §2, p.9 and §4, p.13

import Mathlib

namespace FairTeamContracts

/-- **Additive reward function** (Chen, Castiglioni, Li, *Fair Team Contracts*,
arXiv:2512.19388 (manuscript sha256 b8a12d9b…), §2, p.9, and §4, p.13): `f(S) = ∑_{i ∈ S} f(i)`
for every set of agents `S`, where `f(i)` is the value of the singleton `{i}`.

**Formalization Note.** The identity is required for every `S`, not only for singletons; agents
are `Fin n`. -/
def IsAdditive {n : ℕ} (f : Finset (Fin n) → ℝ) : Prop :=
  ∀ S : Finset (Fin n), f S = ∑ i ∈ S, f {i}

end FairTeamContracts


