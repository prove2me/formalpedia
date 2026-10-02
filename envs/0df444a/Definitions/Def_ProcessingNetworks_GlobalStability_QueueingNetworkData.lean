-- Prove2me | Definitions.Def_ProcessingNetworks_GlobalStability_QueueingNetworkData
-- name    : ProcessingNetworks_GlobalStability_QueueingNetworkData
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T18:08:03.060709+00:00
-- url     : https://prove2.me/theorems/702c3e38-4fa1-4bbf-b119-1a818573c298
-- title:
--   Queueing network model data and fluid equations (6.1)-(6.6), restated
-- statement:
--   This mission restates missions IV/VI's queueing-network model data and fluid-equation
--   specialization, since drafts in this series do not import one another. See mission IV's
--   `MODERATION_NOTES.md` for the per-conjunct correspondence to (6.1)-(6.6); this is an
--   unmodified restatement.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 125, Section 2.6 and Eqs. (6.1)-(6.6) (restated)

import Mathlib

namespace ProcessingNetworks.GlobalStability

/-- A queueing network (Dai & Harrison, Section 2.6), restated from mission IV/VI's
`QueueingNetworkData` (drafts in this series do not import one another): `I` buffers/classes,
`K` server pools. `p i` is the pool serving class `i`; `P` is the `I × I` routing matrix; `m` is
the vector of mean service times; `lam` is the vector of external arrival rates; `b` is the
`K`-vector of server-pool capacities. -/
structure QueueingNetworkData (I K : ℕ) where
  p : Fin I → Fin K
  P : Matrix (Fin I) (Fin I) ℝ
  m : Fin I → ℝ
  lam : Fin I → ℝ
  b : Fin K → ℝ

/-- `I(k)` (Eq. (2.43)): the set of buffers/classes processed by server pool `k`. -/
def poolBuffers {I K : ℕ} (dat : QueueingNetworkData I K) (k : Fin K) : Finset (Fin I) :=
  Finset.univ.filter (fun i => dat.p i = k)

/-- The fluid equations (6.1)-(6.6), specialized to a queueing network, restated from mission
IV/VI's `IsFluidModelSolutionQN`. -/
def IsFluidModelSolutionQN {I K : ℕ} (dat : QueueingNetworkData I K)
    (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin I → ℝ) (Zh : ℝ → Fin I → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → ∀ i, Zh t i = Zh 0 i + dat.lam i * t + ∑ j, dat.P j i * Fh t j - Dh t i) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ i, 0 ≤ Zh t i) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ i, Dh t i = Fh t i) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ i, dat.m i * Fh t i = Th t i) ∧
  (Th 0 = 0 ∧ Monotone Th) ∧
  (∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ k, ∑ i ∈ poolBuffers dat k, (Th t i - Th s i) ≤ dat.b k * (t - s))

end ProcessingNetworks.GlobalStability


