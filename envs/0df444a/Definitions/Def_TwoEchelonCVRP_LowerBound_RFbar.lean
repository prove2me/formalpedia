-- Prove2me | Definitions.Def_TwoEchelonCVRP_LowerBound_RFbar
-- name    : TwoEchelonCVRP_LowerBound_RFbar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T15:13:21.978852+00:00
-- url     : https://prove2.me/theorems/f7e6caa5-437c-434a-a3c6-febe7be3178e
-- title:
--   §3.2: loads $W_r$, the continuous knapsack KP(r, w), and the multiple-choice knapsack $\overline{RF}$ (19)–(22)
-- statement:
--   The relaxation $\overline{RF}$ of the 2E-CVRP replaces the assignment of customers to satellites by a choice of one load per first-level route.
--
--   **Loads.** The minimum and maximum loads of a first-level route $r$ are
--   $$w^{\min} = \max\{q_{\mathrm{tot}} - (m^1 - 1)Q_1,\, 0\}, \qquad w_r^{\max} = \min\Big\{Q_1,\ q_{\mathrm{tot}},\ \sum_{k \in R_r} m_k Q_2\Big\},$$
--   and $W_r = \{w \in \mathbb Z_+ : w^{\min} \le w \le w_r^{\max}\}$ is the set of its possible loads.
--
--   **Continuous knapsack.** For $\beta$ and a load $w \in W_r$, $\phi_{rw}$ is the optimal value of
--   $$KP(r,w):\quad \phi_{rw} = \min \sum_{i \in N_C} \Big(\min_{k \in R_r}\beta_{ik}\Big) z_i \quad\text{s.t.}\quad \sum_{i \in N_C} q_i z_i = w,\quad 0 \le z_i \le 1 .$$
--
--   **Multiple-choice knapsack.** With binary $\zeta_{rw}$ ($r$ used with load $w \in W_r$),
--   $$z(\overline{RF}(\beta,\lambda,\mu)) = \min \sum_{r \in \mathcal M}\sum_{w \in W_r}(g_r + \phi_{rw})\zeta_{rw} + \sum_{i \in N_C}\lambda_i + \sum_{k \in N_S} m_k\mu_k + m^2\mu_0 \qquad (19)$$
--   subject to
--   $$\sum_{r \in \mathcal M}\sum_{w \in W_r} w\,\zeta_{rw} = q_{\mathrm{tot}} \quad (20), \qquad \sum_{w \in W_r}\zeta_{rw} \le 1,\ r \in \mathcal M \quad (21), \qquad \zeta_{rw} \in \{0,1\} \quad (22).$$
--   It is solved by dynamic programming in the paper, and is the relaxation on which the lower bound LD1 of the paper rests.
--
--   **Formalization Note** $w^{\min}$ is computed in the integers before truncation at $0$, so $m^1 = 0$ gives $q_{\mathrm{tot}} + Q_1$ as printed. $\phi_{rw}$ and $z(\overline{RF})$ are infima in the extended reals: $\phi_{rw}$ is a finite, attained minimum for every $w \le q_{\mathrm{tot}}$, in particular for $w \in W_r$, and $z(\overline{RF}) = +\infty$ when (20)–(22) cannot be met. $\zeta_{rw}$ is a Boolean read only for $w \in W_r$. The minimum $\min_{k \in R_r}\beta_{ik}$ is over the satellites of route $r$ only.
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Oper. Res. 61(2) (2013), p. 299 (§2.1, w^min, w_r^max, W_r) and p. 302 (§3.2, KP(r, w), (19)–(22))

import Mathlib
import Definitions.Def_TwoEchelonCVRP_LowerBound_Model
import Definitions.Def_TwoEchelonCVRP_LowerBound_RF

namespace TwoEchelonCVRP.LowerBound

variable {I : Instance}

/-- `w^min = max{q_tot − (m^1 − 1) Q_1, 0}` (§2.1, p. 299), computed in `ℤ` and then cast back,
so that `m^1 = 0` gives `q_tot + Q_1` as printed. -/
def wmin (I : Instance) : ℕ :=
  (max ((I.qtot : ℤ) - ((I.m1 : ℤ) - 1) * (I.Q1 : ℤ)) 0).toNat

/-- `w_r^max = min{Q_1, q_tot, ∑_{k ∈ R_r} m_k Q_2}` (§2.1, p. 299). -/
def wmax (RS : RouteSystem I) (r : RS.FR) : ℕ :=
  min (min I.Q1 I.qtot) (∑ k ∈ RS.Rsat r, I.m k * I.Q2)

/-- `W_r = {w ∈ ℤ_+ : w^min ≤ w ≤ w_r^max}` (§2.1, p. 299). -/
def Wset (RS : RouteSystem I) (r : RS.FR) : Finset ℕ := Finset.Icc (wmin I) (wmax RS r)

/-- `min_{k ∈ R_r} β_{ik}`: the cheapest marginal cost of customer `i` over the satellites of the
first-level route `r` (`R_r` is nonempty). -/
def minBeta (RS : RouteSystem I) (β : Fin I.nc → Fin I.ns → ℝ) (r : RS.FR) (i : Fin I.nc) : ℝ :=
  (RS.Rsat r).inf' (by
    obtain ⟨k, hk⟩ := List.exists_mem_of_ne_nil _ (RS.tour1_ne r)
    exact ⟨k, List.mem_toFinset.mpr hk⟩) (fun k => β i k)

/-- The feasible set of the continuous knapsack problem KP(r, w) (§3.2, p. 302):
`∑_i q_i z_i = w`, `0 ≤ z_i ≤ 1`. -/
def KPFeasible (I : Instance) (w : ℕ) : Set (Fin I.nc → ℝ) :=
  {z | (∀ i, 0 ≤ z i ∧ z i ≤ 1) ∧ ∑ i, (I.q i : ℝ) * z i = (w : ℝ)}

/-- `φ_{rw}`: the optimal value of KP(r, w) (§3.2, p. 302),
`min ∑_i (min_{k ∈ R_r} β_{ik}) z_i` over `KPFeasible I w`, as an infimum in `EReal`.
For `w ≤ q_tot` (in particular for `w ∈ W_r`) the feasible set is nonempty and compact, so the
value is real and attained; it is `⊤` when the feasible set is empty. -/
noncomputable def phi (RS : RouteSystem I) (β : Fin I.nc → Fin I.ns → ℝ) (r : RS.FR) (w : ℕ) :
    EReal :=
  ⨅ (z : Fin I.nc → ℝ) (_ : z ∈ KPFeasible I w), ((∑ i, minBeta RS β r i * z i : ℝ) : EReal)

/-- Feasibility for RF-bar (§3.2, p. 302): (20) and (21); (22) is carried by the type of `ζ`.
`ζ r w = ζ_{rw}` is read only for `w ∈ W_r`. -/
def IsFeasibleRFbar (RS : RouteSystem I) (ζ : RS.FR → ℕ → Bool) : Prop :=
  -- (20): the loads of the chosen routes add up to `q_tot`
  (∑ r, ∑ w ∈ Wset RS r, w * (ζ r w).toNat = I.qtot) ∧
  -- (21): at most one load per first-level route
  (∀ r, ∑ w ∈ Wset RS r, (ζ r w).toNat ≤ 1)

/-- The objective (19) of RF-bar:
`∑_r ∑_{w ∈ W_r} (g_r + φ_{rw}) ζ_{rw} + ∑_i λ_i + ∑_k m_k μ_k + m^2 μ_0`. -/
noncomputable def objRFbar (RS : RouteSystem I) (β : Fin I.nc → Fin I.ns → ℝ)
    (lam : Fin I.nc → ℝ) (μ : Fin I.ns → ℝ) (μ0 : ℝ) (ζ : RS.FR → ℕ → Bool) : EReal :=
  (∑ r, ∑ w ∈ Wset RS r, if ζ r w then ((RS.g r : ℝ) : EReal) + phi RS β r w else 0)
    + ((penaltyConst I lam μ μ0 : ℝ) : EReal)

/-- `z(RF-bar(β, λ, μ))`: the optimal value of the multiple-choice knapsack problem RF-bar, in
`EReal` (`⊤` when (20)–(22) cannot be met). -/
noncomputable def zRFbar (RS : RouteSystem I) (β : Fin I.nc → Fin I.ns → ℝ)
    (lam : Fin I.nc → ℝ) (μ : Fin I.ns → ℝ) (μ0 : ℝ) : EReal :=
  ⨅ (ζ : RS.FR → ℕ → Bool) (_ : IsFeasibleRFbar RS ζ), objRFbar RS β lam μ μ0 ζ

end TwoEchelonCVRP.LowerBound


