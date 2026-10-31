-- Prove2me | Definitions.Def_MissionAbort_clusterOf
-- name    : MissionAbort_clusterOf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:49:02.349636+00:00
-- url     : https://prove2.me/theorems/68b5bb33-dc7f-47ee-8604-375eb8812f21
-- title:
--   Clusters of the surrogate chain
-- statement:
--   The surrogate chain has states $\{1,\dots,m_1+m_2+1\}$. States $\mathcal X_1=\{1,\dots,m_1\}$ are healthy, states $\mathcal X_2=\{m_1+1,\dots,m_1+m_2\}$ defective, and $\mathcal X_3=\{m_1+m_2+1\}$ is failed.
--
--   **Formalization Note** States are $0$-based in Lean: the Lean state $x$ is the page's state $x+1$.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §4.1, p.13

import Mathlib
import Definitions.Def_MissionAbort_Cluster

namespace MissionAbort

/-- The cluster of a state of the surrogate chain (Sun, Hu & Ye, arXiv:2505.03225v1, §4.1, p.13):
`X₁ = {1, …, m₁}` is healthy, `X₂ = {m₁ + 1, …, m₁ + m₂}` defective, and `X₃ = {m₁ + m₂ + 1}` failed.

**Formalization Note.** States are 0-based: `x : Fin (m₁ + m₂ + 1)` is the page's state `x + 1`. -/
def clusterOf (m₁ m₂ : ℕ) (x : Fin (m₁ + m₂ + 1)) : Cluster :=
  if x.val < m₁ then .healthy else if x.val < m₁ + m₂ then .defective else .failed

end MissionAbort


