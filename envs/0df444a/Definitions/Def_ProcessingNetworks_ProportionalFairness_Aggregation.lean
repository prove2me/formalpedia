-- Prove2me | Definitions.Def_ProcessingNetworks_ProportionalFairness_Aggregation
-- name    : ProcessingNetworks_ProportionalFairness_Aggregation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T19:14:50.005992+00:00
-- url     : https://prove2.me/theorems/5eacc7d3-bd81-4244-81bf-fc44a354fdd2
-- title:
--   Resource-relevant demand groups and the aggregation map (Eq. 10.22)
-- statement:
--   Section 10.3's demand-group partition $\{\mathcal I(\ell), \ell \in \mathcal L\}$ of $\mathcal
--   I$, encoded via a total function `grp : Fin I → Fin L` assigning each class to its group
--   (equivalent to the book's $L \times I$ indicator matrix $G$: $G_{\ell i} = 1 \iff \text{grp}\,
--   i = \ell$). `groupAggregate grp x ℓ` is $a_\ell(x) := \sum_{i \in \mathcal I(\ell)} x_i$ (Eq.
--   10.22), the group-level aggregate service rate.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 191, Section 10.3, Eq. (10.22)

import Mathlib

namespace ProcessingNetworks.ProportionalFairness

/-- The group-level aggregate `a_ℓ(x) := ∑_{i ∈ I(ℓ)} x_i` (Eq. 10.22), given a demand-group
assignment `grp : Fin I → Fin L` in place of the book's indicator matrix `G` (an equivalent,
more directly usable encoding of the same partition `{I(ℓ), ℓ ∈ L}`: `Gℓi = 1 ↔ grp i = ℓ`). -/
def groupAggregate {I L : ℕ} (grp : Fin I → Fin L) (x : Fin I → ℝ) (ℓ : Fin L) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => grp i = ℓ), x i

end ProcessingNetworks.ProportionalFairness


