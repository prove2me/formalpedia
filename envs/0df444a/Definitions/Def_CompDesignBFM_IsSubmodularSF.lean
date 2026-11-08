-- Prove2me | Definitions.Def_CompDesignBFM_IsSubmodularSF
-- name    : CompDesignBFM_IsSubmodularSF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:32:30.771263+00:00
-- url     : https://prove2.me/theorems/5440930b-cdc9-4d4b-8857-bcf242aee38b
-- title:
--   Submodular set function (marginal form)
-- statement:
--   A set function $v$ is **submodular** if marginals decrease:
--
--   $$v(S\cup\{i\})-v(S)\ge v(T\cup\{i\})-v(T)\quad\text{for all } S\subseteq T\subseteq N,\ i\notin T.$$
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Definition 1.1, p.1 (PDF 3)

import Mathlib

namespace CompDesignBFM

/-- A submodular set function in the printed marginal form (Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Definition 1.1, p.1, PDF 3):
`v(S ∪ {i}) - v(S) ≥ v(T ∪ {i}) - v(T)` for all `S ⊆ T ⊆ N` and `i ∉ T`. -/
def IsSubmodularSF {n : ℕ} (v : Finset (Fin n) → ℝ) : Prop :=
  ∀ S T i, S ⊆ T → i ∉ T → v (insert i T) - v T ≤ v (insert i S) - v S

end CompDesignBFM


