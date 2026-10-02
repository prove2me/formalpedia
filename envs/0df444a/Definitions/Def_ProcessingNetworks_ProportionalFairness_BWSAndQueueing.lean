-- Prove2me | Definitions.Def_ProcessingNetworks_ProportionalFairness_BWSAndQueueing
-- name    : ProcessingNetworks_ProportionalFairness_BWSAndQueueing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T19:30:29.191922+00:00
-- url     : https://prove2.me/theorems/33614187-9693-4113-a511-cfea54647f74
-- title:
--   The BWS network and the queueing network under HLPPS control (Sections 4.5-4.6, restated locally)
-- statement:
--   A **bandwidth sharing (BWS) network** (Section 4.5) is single-hop data specified by arrival
--   rates $\lambda$, mean service times $m > 0$, and a $K\times I$ capacity consumption matrix $A$
--   with capacities $b$. Its **standard load condition** (Eq. 5.1) is $A(\lambda\odot m) < b$
--   componentwise. A **queueing network under HLPPS control** (Sections 2.6, 4.6) additionally
--   routes via $P$ and assigns each class to a single server (`server : Fin I → Fin K`) with
--   capacity $b_k > 0$; HLPPS fluid stability is Definition 10.3's PF fluid model specialized to
--   the demand-group assignment `grp := server` and $\tilde{\mathcal A} := \prod_k [0,b_k]$ (Eq.
--   10.78) — the product structure under which the aggregate PF allocation $\tilde\psi(\cdot)\equiv
--   b$ coincides with HLPPS's own per-server capacity allocation (Section 10.6).
--
--   **Formalization note.** Mission II's own `BRIEF.md` did not pull the BWS/HLPPS definitions from
--   Chapter 4, so they are restated locally in this chunk rather than assumed available, per this
--   chunk's own `BRIEF.md` pitfall note.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 206-207, Sections 4.5-4.6 (restated locally), 10.6, Eq. (10.78)

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_RestatedCore
import Definitions.Def_ProcessingNetworks_ProportionalFairness_RestatedFluidModel

namespace ProcessingNetworks.ProportionalFairness

/-- The data of a bandwidth sharing (BWS) network (Section 4.5), restated locally per this
chunk's own `BRIEF.md` pitfall note (mission II's own `BRIEF.md` did not pull the BWS/HLPPS
definitions from Chapter 4): `I`-vectors `lam`, `m`, and a `K × I` capacity consumption matrix
`Amat` with capacities `bvec` (single-hop: no routing between classes). -/
structure BWSNetworkData (I K : ℕ) where
  lam : Fin I → ℝ
  m : Fin I → ℝ
  hm : ∀ i, 0 < m i
  Amat : Matrix (Fin K) (Fin I) ℝ
  bvec : Fin K → ℝ

/-- The standard load condition `ρ < b` (Eq. 5.1) for a BWS network: `A(λ ⊙ m) < b`
componentwise (single-hop, so the total arrival rate vector is `λ` itself). -/
def BWSLoadCondition {I K : ℕ} (dat : BWSNetworkData I K) : Prop :=
  ∀ k, (dat.Amat.mulVec (fun i => dat.lam i * dat.m i)) k < dat.bvec k

/-- The data of a queueing network (Section 2.6) under HLPPS control (Section 4.6): `I`-vectors
`lam`, `m`, an `I × I` routing matrix `P`, an assignment `server : Fin I → Fin K` of each class to
the single server that processes it, and server capacities `b > 0`. -/
structure QueueingNetworkDataHL (I K : ℕ) where
  lam : Fin I → ℝ
  m : Fin I → ℝ
  hm : ∀ i, 0 < m i
  P : Matrix (Fin I) (Fin I) ℝ
  server : Fin I → Fin K
  b : Fin K → ℝ
  hb : ∀ k, 0 < b k

/-- HLPPS fluid stability (Section 10.6, "Queueing network with HLPPS control"): the PF fluid
model specialized to `grp := server` and `TildeAllocSet := ∏_k [0,b_k]` (Eq. 10.78), the box under
which the aggregate PF allocation function `ψ̃` coincides with HLPPS's own per-server capacity
allocation. -/
def HLPPSFluidStable {I K : ℕ} (dat : QueueingNetworkDataHL I K) : Prop :=
  PFFluidStable (I := I) (L := K)
    ⟨dat.lam, dat.m, dat.hm, dat.P, dat.server, {y : Fin K → ℝ | ∀ k, 0 ≤ y k ∧ y k ≤ dat.b k}⟩

end ProcessingNetworks.ProportionalFairness


