-- Prove2me | Definitions.Def_DisruptReroute_Resil_Risk
-- name    : DisruptReroute_Resil_Risk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T04:30:42.735055+00:00
-- url     : https://prove2.me/theorems/fac2a8a7-34a1-4670-9663-f6b5e29901dc
-- title:
--   §5.1 — fundamental defaults, switched demand, and resilience ratio
-- statement:
--   Let $p^m$ be the price of good $m$, $w_i$ firm $i$'s equity, $\lambda_i^m$ its unit holding cost, and $s_m^{-1}$ the inverse supply curve. For a common realization $c_i$ of net production costs and uniform safety stock $\theta$, firm $i$ fundamentally defaults when
--
--   $$w_i+\sum_{m=1}^{M}\left(p^m\sum_j o^m_{ij}-\theta\lambda_i^m\right)-c_i<0.$$
--
--   If $D_0(\theta)$ is that default set, efficient switched demand is $\sigma_i^m(D_0(\theta),\theta)=\left(\sum_{k\in D_0(\theta)}o^m_{ki}-\theta\right)^+$. Firm cost $\zeta_i(\theta)$ sums holding cost and switched demand times the inverse supply price over all goods. The total percentage reduction is
--
--   $$\zeta(\theta)=\frac{\sum_i\zeta_i(0)-\sum_i\zeta_i(\theta)}{\sum_i\zeta_i(0)}.$$
--
--   These definitions measure resilience for two networks at the same realization of production costs.
--
--   **Formalization Note** Inverse supply curves are monotone and nonnegative on nonnegative quantities; the latter is a disclosed addition. More resilience means the ratio inequality for every cost realization and every safety stock admissible in both networks. If the denominator is zero, Lean's quotient is zero.
-- source:
--   Birge, Capponi & Chen, Disruption and Rerouting in Supply Chain Networks, SSRN 3669363 (version of October 31, 2022; Oper. Res. 2023, DOI 10.1287/opre.2022.2409), pp. 16, 25, Assumption 2.3, §5.1 and Definition 5.1; E-Companion, p. EC 18, proof of Theorem 5.1

import Mathlib
import Definitions.Def_DisruptReroute_Resil_OrderNetwork
noncomputable section

namespace DisruptReroute.Resil

/-- Data shared by two networks, including the inverse supply curves. -/
structure RiskData (N M : ℕ) where
  price : ℕ → ℝ
  price_nonneg : ∀ m ∈ Finset.Icc 1 M, 0 ≤ price m
  equity : Fin N → ℝ
  equity_nonneg : ∀ i, 0 ≤ equity i
  holding : ℕ → Fin N → ℝ
  holding_nonneg : ∀ m ∈ Finset.Icc 1 M, ∀ i, 0 ≤ holding m i
  sInv : ℕ → ℝ → ℝ
  sInv_monotone : ∀ m ∈ Finset.Icc 1 M, MonotoneOn (sInv m) (Set.Ici 0)
  sInv_nonneg : ∀ m ∈ Finset.Icc 1 M, ∀ x : ℝ, 0 ≤ x → 0 ≤ sInv m x

/-- The firms whose initial net worth is strictly negative. -/
def D0 {N M : ℕ} (R : RiskData N M) (O : OrderNetwork N M)
    (c : Fin N → ℝ) (θ : ℝ) : Finset (Fin N) :=
  Finset.univ.filter (fun i =>
    R.equity i + (∑ m ∈ Finset.Icc 1 M,
      (R.price m * (∑ j, O.order m i j) - θ * R.holding m i)) - c i < 0)

/-- Efficient switched demand after defaults, with safety stock `y`. -/
def sigmaSw {N M : ℕ} (O : OrderNetwork N M)
    (X : Finset (Fin N)) (y : ℝ) (m : ℕ) (i : Fin N) : ℝ :=
  max 0 ((∑ k ∈ X, O.order m k i) - y)

/-- Inventory cost plus switching cost for firm `i`. -/
def zetaI {N M : ℕ} (R : RiskData N M) (O : OrderNetwork N M)
    (c : Fin N → ℝ) (θ : ℝ) (i : Fin N) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M,
    (θ * R.holding m i +
      sigmaSw O (D0 R O c θ) θ m i *
        R.sInv m (∑ j, sigmaSw O (D0 R O c θ) θ m j))

/-- Buyers of at least one fundamentally defaulted firm, for good `m`. -/
def affectedBuyers {N M : ℕ} (R : RiskData N M) (O : OrderNetwork N M)
    (c : Fin N → ℝ) (θ : ℝ) (m : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun i =>
    ∃ k ∈ D0 R O c θ, 0 < O.order m k i)

/-- The unserved amount at good `m` after safety stocks, in the proof of Theorem 5.1. -/
def tierT {N M : ℕ} (R : RiskData N M) (O : OrderNetwork N M)
    (c : Fin N → ℝ) (θ : ℝ) (m : ℕ) : ℝ :=
  (∑ i ∈ affectedBuyers R O c θ m,
    ∑ k ∈ D0 R O c θ, O.order m k i) -
    ((affectedBuyers R O c θ m).card : ℝ) * θ

/-- The tier-grouped full inventory and switching cost. -/
def groupedCost {N M : ℕ} (R : RiskData N M) (O : OrderNetwork N M)
    (c : Fin N → ℝ) (θ : ℝ) : ℝ :=
  (∑ i, ∑ m ∈ Finset.Icc 1 M, θ * R.holding m i) +
    (∑ m ∈ Finset.Icc 1 M,
      tierT R O c θ m * R.sInv m (tierT R O c θ m))

/-- The total percentage reduction in out-of-stock loss. Lean's `0 / 0 = 0`. -/
def zeta {N M : ℕ} (R : RiskData N M) (O : OrderNetwork N M)
    (c : Fin N → ℝ) (θ : ℝ) : ℝ :=
  ((∑ i, zetaI R O c 0 i) - (∑ i, zetaI R O c θ i)) /
    (∑ i, zetaI R O c 0 i)

/-- Definition 5.1, interpreted for every common realization of production costs. -/
def MoreResilient {N M : ℕ} (R : RiskData N M)
    (B A : OrderNetwork N M) (tier : Fin N → ℕ) : Prop :=
  ∀ (c : Fin N → ℝ) (θ : ℝ),
    AssumptionTwoOne A tier θ → AssumptionTwoOne B tier θ →
      zeta R A c θ ≤ zeta R B c θ

end DisruptReroute.Resil


