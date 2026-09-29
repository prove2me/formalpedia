-- Prove2me | Definitions.Def_DecentralizedDistribution_FirstBest_Game
-- name    : DecentralizedDistribution_FirstBest_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T06:36:05.729225+00:00
-- url     : https://prove2.me/theorems/6c94e250-4081-40e8-a03c-66547946f07a
-- title:
--   The inventory game: centralized profit, first-best, payoffs (9), Nash equilibrium (10), AR-f (11) and AR-c
-- statement:
--   This file defines the stochastic, non-cooperative stage of the model. Demand $\vec D$ is a random vector with law $\mu$ on $\mathbb R^N$.
--
--   **Centralized system (§3).** With all pooled inventory claimed, the centralized profit in state $\vec D$ is
--   $$P^c_{\mathcal N}([Z],\vec D)=\sum_{n\in\mathcal N}\big[r_nS_n+v_nH_n-c_nX_n\big]-\sum_{w\in\mathcal W}(c_w-v_w)Y_w+W^*_{\mathcal N}([Z],\vec D),$$
--   the optimal value of (1)–(2), whose shipping part is the LP (6) for $\mathcal N$. Its expectation is $J^c_{\mathcal N}([Z])=E_{\vec D}\,P^c_{\mathcal N}([Z],\vec D)$ (3), and a **first-best** profile is a nonnegative profile maximizing $J^c_{\mathcal N}$ over all nonnegative profiles (4).
--
--   **Allocation rules and payoffs.** An allocation rule AR-$m$ assigns a surplus $\alpha^m_n([Z],\vec D)$ to every retailer for every profile and demand. Retailer $n$'s profit (9) and expected profit are
--   $$P^m_n([Z],\vec D)=r_nS_n+v_nH_n-c_nX_n-\sum_{w=1}^W(c_w-v_w)Y_{w,n}+\alpha^m_n([Z],\vec D),\qquad J^m_n([Z])=E_{\vec D}\,P^m_n([Z],\vec D).$$
--   A profile $[Z]^{m*}$ is a **pure-strategy Nash equilibrium** (10) when it is nonnegative and $J^m_n([Z]^{m*})\ge J^m_n([Z]^{m*}_{-n}\cup\vec Z_n)$ for every retailer $n$ and every nonnegative position $\vec Z_n$.
--
--   **AR-f and AR-c (§5.1).** For weights $\theta_n$, the fractional rule (11) is
--   $$\alpha^f_n([Z],\vec D)=\theta_nP^c_{\mathcal N}([Z],\vec D)-\Big[r_nS_n+v_nH_n-c_nX_n-\sum_{w=1}^W(c_w-v_w)Y_{w,n}\Big].$$
--   Given a profile $[Z]^{c*}$ and a choice $\vec D\mapsto(\nu,\gamma,\delta)(\vec D)$ of dual prices, the side payment is $w_n([Z]^{c*},\vec D)=\alpha^d_n([Z]^{c*},\vec D)-\alpha^f_n([Z]^{c*},\vec D)$, with $\alpha^d$ the dual-price allocation (8), and the modified fractional rule AR-c is
--   $$\alpha^c_n([Z],\vec D)=\alpha^f_n([Z],\vec D)+w_n([Z]^{c*},\vec D).$$
--
--   These are the objects of Theorems 5.1, 5.2 and Corollary 5.1.
--
--   **Formalization Note.** Expectations are Bochner integrals against $\mu$ (the value is $0$ for a non-integrable integrand; the statements that need it carry integrability hypotheses or make it provable). The paper's weights $\gamma_n$ are renamed $\theta_n$ because $\gamma_w$ denotes the warehouse dual prices. Eq. (11) is printed with $-v_nH_n$ inside the bracket; the bracket here carries $+v_nH_n$, the non-allocation part of (9), which is the reading the proof of Theorem 5.2 (p. 367, "$P^f_n=\gamma_nP^c_{\mathcal N}$") requires. The side payment is the one constructed in the proof of Theorem 5.1 (p. 367) at $[Z]^{c*}$; the choice of dual prices per realization is the paper's "appropriate way of breaking ties".
-- source:
--   Anupindi, Bassok & Zemel, A General Framework for the Study of Decentralized Distribution Systems, MSOM 3(4) 2001, pp. 354-355 Eq. (1)-(4); p. 359-360 Eq. (9)-(10); p. 361 Eq. (11), Theorem 5.2, Corollary 5.1; p. 367 proof of Theorem 5.1

import Mathlib
import Definitions.Def_DecentralizedDistribution_FirstBest_System
import Definitions.Def_DecentralizedDistribution_FirstBest_DualPrices

open MeasureTheory

namespace DecentralizedDistribution.FirstBest

/-- The non-allocation part of retailer `n`'s profit in Eq. (9):
`r_n S_n + v_n H_n - c_n X_n - ∑_w (c_w - v_w) Y_{w,n}`. -/
def localProfit {N W : ℕ} (sys : System N W) (Z : Profile N W) (D : Demand N) (n : Fin N) : ℝ :=
  sys.r n * sales Z D n + sys.v n * residualInv Z D n - sys.c n * (Z n).X
    - ∑ w, (sys.cw w - sys.vw w) * (Z n).Y w

/-- The centralized profit `P^c_𝒩([Z], D⃗)` of Eqs. (1)–(2a), with all pooled inventory claimed
(`Y_w = ∑_n Y_{w,n}`, p. 361):
`∑_n [r_n S_n + v_n H_n - c_n X_n] - ∑_w (c_w - v_w) Y_w + W*_𝒩([Z], D⃗)`, the last term being
the optimal shipping profit, the value of (2a)–(2e) = (6) for `𝒮 = 𝒩`. -/
noncomputable def centralProfit {N W : ℕ} (sys : System N W) (Z : Profile N W) (D : Demand N) : ℝ :=
  (∑ n, (sys.r n * sales Z D n + sys.v n * residualInv Z D n - sys.c n * (Z n).X))
    - (∑ w, (sys.cw w - sys.vw w) * ∑ n, (Z n).Y w)
    + coalitionValue sys Finset.univ Z D

/-- The expected centralized profit `J^c_𝒩([Z]) = E_D P^c_𝒩([Z], D⃗)` (Eq. (3)). -/
noncomputable def expectedCentralProfit {N W : ℕ} (sys : System N W)
    (μ : Measure (Demand N)) (Z : Profile N W) : ℝ :=
  ∫ D, centralProfit sys Z D ∂μ

/-- A first-best solution (Eq. (4)): a nonnegative profile maximizing `J^c_𝒩` over all
nonnegative profiles. -/
def IsFirstBest {N W : ℕ} (sys : System N W) (μ : Measure (Demand N)) (Z : Profile N W) : Prop :=
  Z.Nonneg ∧ ∀ Z' : Profile N W, Z'.Nonneg → expectedCentralProfit sys μ Z' ≤ expectedCentralProfit sys μ Z

/-- An allocation rule AR-m: a surplus allocation `α^m_n([Z], D⃗)` for every profile, demand
realization and retailer (p. 359). -/
abbrev AllocationRule (N W : ℕ) := Profile N W → Demand N → Fin N → ℝ

/-- Retailer `n`'s total profit under AR-m, Eq. (9):
`P^m_n([Z], D⃗) = r_n S_n + v_n H_n - c_n X_n - ∑_w (c_w - v_w) Y_{w,n} + α^m_n([Z], D⃗)`. -/
def payoff {N W : ℕ} (sys : System N W) (α : AllocationRule N W) (Z : Profile N W)
    (D : Demand N) (n : Fin N) : ℝ :=
  localProfit sys Z D n + α Z D n

/-- Retailer `n`'s expected profit `J^m_n([Z]) = E_D P^m_n([Z], D⃗)`. -/
noncomputable def expectedPayoff {N W : ℕ} (sys : System N W) (μ : Measure (Demand N))
    (α : AllocationRule N W) (Z : Profile N W) (n : Fin N) : ℝ :=
  ∫ D, payoff sys α Z D n ∂μ

/-- A pure-strategy Nash equilibrium of the inventory game under AR-m, Eq. (10): a nonnegative
profile `[Z]` such that no retailer `n` gains by replacing its own position by any nonnegative
position `z`, the other retailers' positions held fixed (`[Z]_{-n} ∪ z`). -/
def IsNashEquilibrium {N W : ℕ} (sys : System N W) (μ : Measure (Demand N))
    (α : AllocationRule N W) (Z : Profile N W) : Prop :=
  Z.Nonneg ∧ ∀ (n : Fin N) (z : Position W), z.Nonneg →
    expectedPayoff sys μ α (Function.update Z n z) n ≤ expectedPayoff sys μ α Z n

/-- The fractional allocation rule AR-f of Eq. (11) with weights `θ`:
`α^f_n([Z], D⃗) = θ_n P^c_𝒩([Z], D⃗) - [r_n S_n + v_n H_n - c_n X_n - ∑_w (c_w - v_w) Y_{w,n}]`
(the sign of `v_n H_n` follows Eq. (9) and the proof of Theorem 5.2, p. 367). -/
noncomputable def fractionalRule {N W : ℕ} (sys : System N W) (θ : Fin N → ℝ) : AllocationRule N W :=
  fun Z D n => θ n * centralProfit sys Z D - localProfit sys Z D n

/-- The side payment of AR-c (proof of Theorem 5.1, p. 367, applied to AR-f at the first-best
`[Z]^{c*}`): `w_n([Z]^{c*}, D⃗) = α^d_n([Z]^{c*}, D⃗) - α^f_n([Z]^{c*}, D⃗)`, where `α^d` is the
dual-price allocation (8) computed from the dual prices `sel D⃗` chosen for each realization. -/
noncomputable def firstBestSidePayment {N W : ℕ} (sys : System N W) (θ : Fin N → ℝ)
    (Zc : Profile N W) (sel : Demand N → DualPrices N W) (n : Fin N) (D : Demand N) : ℝ :=
  dualAllocation Zc D (sel D) n - fractionalRule sys θ Zc D n

/-- The modified fractional allocation rule AR-c of Corollary 5.1:
`α^c_n([Z], D⃗) = α^f_n([Z], D⃗) + w_n([Z]^{c*}, D⃗)`. -/
noncomputable def coreFractionalRule {N W : ℕ} (sys : System N W) (θ : Fin N → ℝ)
    (Zc : Profile N W) (sel : Demand N → DualPrices N W) : AllocationRule N W :=
  fun Z D n => fractionalRule sys θ Z D n + firstBestSidePayment sys θ Zc sel n D

end DecentralizedDistribution.FirstBest


