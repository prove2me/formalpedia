-- Prove2me | Definitions.Def_DisruptReroute_Resil_OrderNetwork
-- name    : DisruptReroute_Resil_OrderNetwork
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T04:30:02.439658+00:00
-- url     : https://prove2.me/theorems/4f93d08a-659e-4077-b33a-2d8d731270b2
-- title:
--   §2 and §5.2 — finite good-indexed order network and tier structure
-- statement:
--   An order network on $N$ firms and $M$ goods records the nonnegative quantity $o^m_{ij}$ of good $m$ that firm $i$ commits to deliver to firm $j$. Goods are numbered $1,\ldots,M$; orders outside this range are zero. A tier assignment places each firm in one of tiers $1,\ldots,M+1$. A positive order of good $m$ runs from tier $m$ to tier $m+1$. Each nonfinal-tier firm sells its output good, each firm beyond tier 1 buys its input good, and the underlying undirected order graph is connected.
--
--   The buyer and supplier sets are the firms linked to a given firm by positive orders. Assumption 2.1 requires nonnegative uniform safety stock $\theta$ to be no larger than every positive supplier order of the good a firm buys.
--
--   This model fixes the directed order convention used throughout the resilience result.
--
--   **Formalization Note** The paper's printed minimum over all firms would include zero orders and force $\theta=0$. The minimum is read over actual suppliers. Tier and good numbers are one-based, while firms are indexed by a finite type.
-- source:
--   Birge, Capponi & Chen, Disruption and Rerouting in Supply Chain Networks, SSRN 3669363 (version of October 31, 2022; Oper. Res. 2023, DOI 10.1287/opre.2022.2409), pp. 8–9, 12, 26–27, network data, Assumption 2.1, §5.2

import Mathlib
noncomputable section

namespace DisruptReroute.Resil

/-- The directed, good-indexed order quantities of a finite supply chain. -/
structure OrderNetwork (N M : ℕ) where
  order : ℕ → Fin N → Fin N → ℝ
  order_nonneg : ∀ m i j, 0 ≤ order m i j
  order_outside : ∀ m i j, m ∉ Finset.Icc 1 M → order m i j = 0

/-- A tier assignment describes a weakly connected chain of consecutive goods. -/
def IsTiered {N M : ℕ} (O : OrderNetwork N M) (tier : Fin N → ℕ) : Prop :=
  (∀ i, 1 ≤ tier i ∧ tier i ≤ M + 1) ∧
  (∀ m i j, 0 < O.order m i j → tier i = m ∧ tier j = m + 1) ∧
  (∀ i, tier i ≤ M → ∃ j, 0 < O.order (tier i) i j) ∧
  (∀ i, 1 < tier i → ∃ j, 0 < O.order (tier i - 1) j i) ∧
  (∀ i j, Relation.ReflTransGen
    (fun a b => ∃ m, 0 < O.order m a b ∨ 0 < O.order m b a) i j)

/-- Firms buying firm `i`'s output good. -/
def buyers {N M : ℕ} (O : OrderNetwork N M) (tier : Fin N → ℕ)
    (i : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun j => 0 < O.order (tier i) i j)

/-- Firms supplying the good bought by `i`. -/
def suppliers {N M : ℕ} (O : OrderNetwork N M) (tier : Fin N → ℕ)
    (i : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun j => 0 < O.order (tier i - 1) j i)

/-- Assumption 2.1, read over actual suppliers and with nonnegative safety stock. -/
def AssumptionTwoOne {N M : ℕ} (O : OrderNetwork N M)
    (tier : Fin N → ℕ) (θ : ℝ) : Prop :=
  0 ≤ θ ∧ ∀ i j, j ∈ suppliers O tier i → θ ≤ O.order (tier i - 1) j i

end DisruptReroute.Resil


