-- Prove2me | Definitions.Def_ProcessingNetworks_FluidEquations_Hset
-- name    : ProcessingNetworks_FluidEquations_Hset
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T17:45:36.162712+00:00
-- url     : https://prove2.me/theorems/e13eff78-6eb3-4202-bb81-e59e626530d0
-- title:
--   H(j) — same-pool higher-or-equal priority buffers (Eq. 7.5)
-- statement:
--   An **SBP (static buffer priority) policy** is given by a permutation $\sigma$ of the buffer
--   index set: servers in a pool give priority to class $i$ over class $j$ (both served by the
--   same pool) iff $\sigma(i) < \sigma(j)$.
--
--   **Eq. (7.5).** For a buffer $j$, $H(j) := \{i \in I : p(i) = p(j),\ \sigma(i) \le \sigma(j)\}$
--   — the set of same-pool buffers whose priority is at least as high as $j$'s.
--
--   **Formalization note.** $\sigma$ is formalized as `Equiv.Perm (Fin I)` (a bijection of the
--   buffer index type), matching "a permutation $\sigma : I \to I$" exactly; $\sigma(i) \le
--   \sigma(j)$ compares the images under the ambient linear order on `Fin I`.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 128, Eq. (7.5)

import Mathlib
import Definitions.Def_ProcessingNetworks_FluidEquations_QueueingNetworkData

namespace ProcessingNetworks.FluidEquations

/-- `H(j)`, Eq. (7.5): for a buffer `j`, the set of same-pool buffers whose static-buffer-priority
rank (the permutation `σ : Fin I ≃ Fin I`) is at least as high as `j`'s — "at least as high"
meaning `σ i ≤ σ j` on the priority index (a *lower* index value is higher priority, matching the
book's "servers ... give priority to class `i` over class `j`` iff `σ(i) < σ(j)`"). -/
def Hset {I K : ℕ} (dat : QueueingNetworkData I K) (σ : Equiv.Perm (Fin I)) (j : Fin I) :
    Finset (Fin I) :=
  Finset.univ.filter (fun i => dat.p i = dat.p j ∧ σ i ≤ σ j)

end ProcessingNetworks.FluidEquations


