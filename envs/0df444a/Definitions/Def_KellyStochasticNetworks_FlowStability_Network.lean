-- Prove2me | Definitions.Def_KellyStochasticNetworks_FlowStability_Network
-- name    : KellyStochasticNetworks_FlowStability_Network
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:48:53.987801+00:00
-- url     : https://prove2.me/theorems/2410a9d6-160e-4a75-be45-aab73b5f50f4
-- title:
--   Flow-level network and weighted alpha-fair optimization
-- statement:
--   Let $J$ and $R$ be finite resource and route sets, with a zero-one incidence matrix $A$ and at least one resource on each route. Capacities $C_j$, arrival intensities $\nu_r$, exponential file-size parameters $\mu_r$, and weights $w_r$ are positive; $\alpha>0$. The state $n\in\mathbb N^R$ counts active files. Write $\rho_r=\nu_r/\mu_r$ and $X_r=n_rx_r$ for aggregate allocated capacity.
--
--   The allocation maximizes the published aggregate utility
--   $$G_n(X)=\begin{cases}\sum_r w_r n_r^\alpha X_r^{1-\alpha}/(1-\alpha),&\alpha\ne1,\\\sum_r w_r n_r\log X_r,&\alpha=1,\end{cases}$$
--   subject to $X\ge0$, $AX\le C$, with positive coordinates on active routes and zero coordinates on inactive routes. Subcriticality is $A\rho<C$ coordinatewise. The per-flow objective $F_n(x)$ has summands $w_rn_rx_r^{1-\alpha}/(1-\alpha)$ or $w_rn_r\log x_r$. Its finite-utility domain includes active zero coordinates when $\alpha<1$ and excludes them otherwise.
--
--   The associated Lyapunov function and first-order expression are
--   $$L(n)=\sum_r\frac{w_r}{\mu_r}\rho_r^{-\alpha}\frac{n_r^{\alpha+1}}{\alpha+1},\qquad H(n)=\sum_r w_r\rho_r^{-\alpha}n_r^\alpha(\rho_r-X_r(n)).$$
--   These definitions join the bandwidth optimization problem to the stochastic stability problem.
--
--   **Formalization Note** Routes and resources use finite index types; occupancies remain unbounded natural numbers. Inactive utility contributions are zero. Optimizing over positive active rates gives the same allocation as the source's extended-utility optimization; at $\alpha=1$, conversion from per-flow to aggregate utility changes only a constant depending on $n$. The published feasibility and utility definitions are reused.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed pp. 186, 188–190 (PDF pp. 194, 196–198), Sections 8.1–8.3, (8.1), (8.3), (8.4)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_FlowLevel

namespace KellyStochasticNetworks.FlowStability

/-- Finite resources and routes, each route using at least one resource. -/
structure Network (J R : ℕ) where
  A : Fin J → Fin R → ℝ
  C : Fin J → ℝ
  nu : Fin R → ℝ
  mu : Fin R → ℝ
  w : Fin R → ℝ
  alpha : ℝ
  incidence : ∀ j r, A j r = 0 ∨ A j r = 1
  route_nonempty : ∀ r, ∃ j, A j r = 1
  capacity_pos : ∀ j, 0 < C j
  arrival_pos : ∀ r, 0 < nu r
  service_pos : ∀ r, 0 < mu r
  weight_pos : ∀ r, 0 < w r
  alpha_pos : 0 < alpha

abbrev State (R : ℕ) := Fin R → ℕ

noncomputable def offeredLoad {J R : ℕ} (D : Network J R) (r : Fin R) : ℝ :=
  D.nu r / D.mu r

def Subcritical {J R : ℕ} (D : Network J R) : Prop :=
  ∀ j, KellyStochasticNetworks.linkFlow D.A (offeredLoad D) j < D.C j

/-- Active coordinates are positive; inactive aggregate rates are fixed to zero.
The omitted zero boundary has utility minus infinity for alpha >= 1, and cannot maximize
for alpha < 1. This domain determines the same unique active allocation as (8.1). -/
def activeFeasible {J R : ℕ} (D : Network J R) (n : State R) : Set (Fin R → ℝ) :=
  KellyStochasticNetworks.networkFeasible D.A D.C ∩
    {X | (∀ r, n r = 0 → X r = 0) ∧ (∀ r, 0 < n r → 0 < X r)}

noncomputable def aggregateUtility {J R : ℕ} (D : Network J R) (n : State R)
    (X : Fin R → ℝ) : ℝ :=
  KellyStochasticNetworks.alphaFairObjective D.w (fun r => (n r : ℝ)) D.alpha X

/-- Pointwise maximization, not a drift or stability assumption. -/
def IsAlphaFair {J R : ℕ} (D : Network J R) (X : State R → Fin R → ℝ) : Prop :=
  ∀ n, X n ∈ activeFeasible D n ∧
    ∀ Y ∈ activeFeasible D n, aggregateUtility D n Y ≤ aggregateUtility D n (X n)

/-- Per-flow objective (8.1), including zero-count routes, reusing the published utility. -/
noncomputable def perFlowUtility {R : ℕ} (w : Fin R → ℝ) (n : State R)
    (alpha : ℝ) (x : Fin R → ℝ) : ℝ :=
  KellyStochasticNetworks.alphaFairObjective (fun r => w r * (n r : ℝ))
    (fun _ => 1) alpha x

/-- Finite-utility part of the nonnegative per-flow domain; for alpha < 1 it
includes zero active rates, and otherwise active rates must be positive. -/
def utilityDomain {R : ℕ} (n : State R) (alpha : ℝ) : Set (Fin R → ℝ) :=
  {x | (∀ r, 0 ≤ x r) ∧ (1 ≤ alpha → ∀ r, 0 < n r → 0 < x r)}

noncomputable def lyapunov {J R : ℕ} (D : Network J R) (n : State R) : ℝ :=
  ∑ r, D.w r / D.mu r * offeredLoad D r ^ (-D.alpha) *
    ((n r : ℝ) ^ (D.alpha + 1) / (D.alpha + 1))

noncomputable def firstOrderDrift {J R : ℕ} (D : Network J R)
    (X : State R → Fin R → ℝ) (n : State R) : ℝ :=
  ∑ r, D.w r * offeredLoad D r ^ (-D.alpha) * (n r : ℝ) ^ D.alpha *
    (offeredLoad D r - X n r)

end KellyStochasticNetworks.FlowStability


