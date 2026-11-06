-- Prove2me | Definitions.Def_PolytopeSchedPF_IsSupportSubmodular
-- name    : PolytopeSchedPF_IsSupportSubmodular
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:18:33.154772+00:00
-- url     : https://prove2.me/theorems/2c455961-a756-4c74-a33a-ea42c6d2425b
-- title:
--   Support-submodular rate polytope
-- statement:
--   A PSP instance and its rate polytope $\mathcal P$ are **support submodular** if for every $\alpha\in\mathbb R^n_{\ge0}$ the set function $U\mapsto H_\alpha(U)$ is submodular:
--   $$
--   H_\alpha(U\cup V)+H_\alpha(U\cap V)\le H_\alpha(U)+H_\alpha(V)\qquad\text{for all }U,V\subseteq J .
--   $$
--   The class contains single machines, unrelated machines and polymatroids; it is the class on which Proportional Fairness is $2$-competitive for weighted completion time.
--
--   **Formalization Note** Submodularity is the published definition `NonmonotoneSubmod.Shared.Submodular`, which bundles no other condition.
-- source:
--   Jäger, Lindermayr, Zondervan, Single-Machine Guarantees on Unrelated Machines and Beyond: Proportional Fairness for Nonclairvoyant Polytope Scheduling, arXiv:2610.32545v1, Definition 4.1, p.16 (PDF p.18) = Definition 1.1, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_PolytopeSchedPF_RatePolytope

namespace PolytopeSchedPF

/-- **Support-submodular PSP** (Jäger, Lindermayr, Zondervan, arXiv:2610.32545v1, Definition 4.1,
p.16 = Definition 1.1, p.2): the rate polytope is support submodular if for every `α ∈ ℝⁿ_{≥0}` the
set function `U ↦ H_α(U)` is submodular, `H_α(U ∪ V) + H_α(U ∩ V) ≤ H_α(U) + H_α(V)`.

**Formalization Note** Submodularity is the published `NonmonotoneSubmod.Shared.Submodular`
(no normalization or monotonicity bundled). -/
def IsSupportSubmodular {n D : ℕ} (P : RatePolytope n D) : Prop :=
  ∀ α : Fin n → ℝ, (∀ j, 0 ≤ α j) → NonmonotoneSubmod.Shared.Submodular (P.H α)

end PolytopeSchedPF


