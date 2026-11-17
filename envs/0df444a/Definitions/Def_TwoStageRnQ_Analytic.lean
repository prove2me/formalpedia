-- Prove2me | Definitions.Def_TwoStageRnQ_Analytic
-- name    : TwoStageRnQ_Analytic
-- status  : Definition
-- author  : @beatlesmania
-- created : 2026-11-17T00:19:44.987203+00:00
-- url     : https://prove2.me/theorems/8a0dafd6-75e2-4919-a752-9e82bba9cd69
-- title:
--   Analytic quantities for echelon $(R,nQ)$ policies
-- statement:
--   This file fixes the instance data and every analytic quantity of the paper.
--
--   An instance consists of a demand rate $\lambda\ge0$, lead times $L_1,L_2\ge0$, echelon holding rates $h_1,h_2\ge0$, a backlog rate $p\ge0$ and setup charges $K_1,K_2\ge0$. Write $\mu_i=\lambda L_i$, $k_i=\lambda K_i$, $H_0=h_2\lambda L_1$, and let $D_1,D_2$ be independent Poisson random variables with means $\mu_1,\mu_2$. With $\varphi_{a,b}(x)=ax^++bx^-$ the file defines:
--
--   1. $G_0(x)=H_0+\mathbb E\varphi_{h_1+h_2,p}(x-D_1)$ (eq. (6)), $P(x)=\mathbb E\varphi_{h_1+h_2,p}(x-D_1)$ and $F_{\mathrm{up}}(x)=\mathbb E\varphi_{h_2,p}(x-D_2)$.
--   2. $\mathcal L_jF(x)=\frac1j\sum_{v=0}^{j-1}F(x-v)$ and $\mathcal H_j(F)=\inf_{x\in\mathbb R}\mathcal L_jF(x)$ (eq. (7)); $\mathcal C_F(k)=\inf_{j\ge1}\{k/j+\mathcal H_j(F)\}$ (eq. (15)).
--   3. $I_{n,Q}(s,\ell)=\frac1n\sum_{j=0}^{n-1}\mathbb E\big[\mathcal L_QG_0(s-(\ell+jQ-D_2)^-)+h_2(\ell+jQ-D_2)^+\big]$ (eq. (8)) and the classical cost formula $\frac{k_1}Q+\frac{k_2}{nQ}+I_{n,Q}(R_1+Q,R_2-R_1)$ (eq. (9)).
--   4. $V_0=\inf_{r,y\in\mathbb R}\mathbb E[G_0(r-(y-D_2)^-)+h_2(y-D_2)^+]$ (eq. (12)), $B_1(k)=H_0+\mathcal C_P(k)$, $B_2(k)=\mathcal C_{F_{\mathrm{up}}}(k)$ (eq. (18)) and
--   $$L_{\mathrm{two}}=\max\Big\{\tfrac{B_1(2k_1)+B_2(2k_2)}2,\ \tfrac{V_0}2+\tfrac{B_1(4k_1)+B_2(4k_2)}4\Big\}\quad\text{(eq. (19))}.$$
--   5. $F_1^{\eta,\zeta}(x)=\mathbb E\varphi_{h_1+\eta h_2,\zeta p}(x-D_1)$, $F_2^{\eta,\zeta}(x)=\mathbb E\varphi_{(1-\eta)h_2,(1-\zeta)p}(x-D_1-D_2)$ (eqs. (13)–(14)), $\mathcal A(c_1,c_2)=\sup_{\eta,\zeta\in[0,1]}\{\eta H_0+\mathcal C_{F_1^{\eta,\zeta}}(c_1)+\mathcal C_{F_2^{\eta,\zeta}}(c_2)\}$ (eq. (16)) and $\mathrm{LB}^{\mathrm{SP}}=\sup_{0<u\le1}\{(1-u)V_0+u\,\mathcal A(k_1/u,k_2/u)\}$ (eq. (17)).
--   6. The joint inventory value $V_{m_1,m_2}$: the infimum, over a real level $z$ and downstream choices $x(D_2,J_{m_2})$ with $x\le z-D_2-J_{m_2}$ and $\mathbb E|x|<\infty$, of $\mathbb E[H_0+\varphi_{h_1+h_2,p}(x-D_1-J_{m_1})+h_2(z-D_2-J_{m_2}-x)]$, where $J_m$ is uniform on $\{0,\dots,m-1\}$ and independent of everything else (eqs. (D.3), (D.7)); and $\mathcal J(c_1,c_2)=\inf_{m_1,m_2\ge1}\{c_1/m_1+c_2/m_2+V_{m_1,m_2}\}$ (eq. (21)).
--
--   These quantities are shared by every analytic statement of the mission.
--
--   **Formalization Note** Poisson expectations are the series $\sum_n e^{-\mu}\mu^n/n!\,f(n)$. Infima and suprema are taken in $\mathbb R$; each is over a nonempty family that is bounded below (nonnegative values) or bounded above, so no default value of an empty or unbounded family is used. In $V_{m_1,m_2}$ the expectation over $(D_1,J_{m_1})$ is written inside as $\mathcal L_{m_1}G_0(x)$, and the downstream choice is a function of the value of $D_2$ and the index of the upstream position.
-- source:
--   M. Hu, "A 5/3 Guarantee for Echelon Stock (R,nQ) Policies in Two-Stage Stochastic Serial Systems", manuscript rq_167.tex (Sept. 28, 2026 version); posted as arXiv:2609.06318. Sections 4.2, 5, 6; Appendix D (eqs. (6)-(9), (12)-(19), (21), (D.3), (D.7)).

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.PNat.Basic

/-!
# Echelon stock `(R,nQ)` policies: analytic quantities

Analytic objects of M. Hu, "A 5/3 Guarantee for Echelon Stock (R,nQ) Policies in Two-Stage
Stochastic Serial Systems" (manuscript `rq_167.tex`): the loss `φ_{a,b}`, Poisson lead-time
demand, the downstream cost `G₀`, lattice windows `𝓛_j`, `𝓗_j`, the single-stage cycle cost
`𝓒_F(k)`, the zero-setup value `V₀`, the stage benchmarks `B₁, B₂`, the allocation bound `𝓐`,
the setup-preserving bound `LB^SP`, the composite bound `L_two`, the joint inventory value
`V_{m₁,m₂}`, the joint cycle cost `𝓙(k₁,k₂)`, and the exact cost formula of the classical rule.
-/

noncomputable section

namespace TwoStageRnQ

/-- The loss `φ_{a,b}(x) = a·x⁺ + b·x⁻` (paper, Section 4.2). -/
def phi (a b x : ℝ) : ℝ := a * max x 0 + b * max (-x) 0

/-- Poisson probability mass `e^{-μ} μⁿ / n!`. -/
def poisW (μ : ℝ) (n : ℕ) : ℝ := Real.exp (-μ) * μ ^ n / (n.factorial : ℝ)

/-- Expectation `𝔼 f(D)` of `f` evaluated at a Poisson random variable `D` with mean `μ`. -/
def pexp (μ : ℝ) (f : ℕ → ℝ) : ℝ := ∑' n : ℕ, poisW μ n * f n

/-- The lattice window average `𝓛_j F(x) = (1/j) ∑_{v=0}^{j-1} F(x - v)` (eq. (7)). -/
def latAvg (j : ℕ) (F : ℝ → ℝ) (x : ℝ) : ℝ := (∑ v ∈ Finset.range j, F (x - v)) / j

/-- The best placement of a lattice window, `𝓗_j(F) = inf_{x ∈ ℝ} 𝓛_j F(x)` (eq. (7)). -/
def latInf (j : ℕ) (F : ℝ → ℝ) : ℝ := ⨅ x : ℝ, latAvg j F x

/-- The single-stage cycle cost `𝓒_F(k) = inf_{j ∈ ℕ, j ≥ 1} { k/j + 𝓗_j(F) }` (eq. (15)). -/
def cycCost (F : ℝ → ℝ) (k : ℝ) : ℝ := ⨅ j : ℕ+, (k / ((j : ℕ) : ℝ) + latInf j F)

/-- Instance data of the two-stage serial system: demand rate `λ`, lead times `L₁, L₂`,
echelon holding rates `h₁, h₂`, backlog rate `p`, and setup charges `K₁, K₂`.
All are finite and nonnegative. -/
structure Params where
  lam : ℝ
  L1 : ℝ
  L2 : ℝ
  h1 : ℝ
  h2 : ℝ
  p : ℝ
  K1 : ℝ
  K2 : ℝ
  lam_nonneg : 0 ≤ lam
  L1_nonneg : 0 ≤ L1
  L2_nonneg : 0 ≤ L2
  h1_nonneg : 0 ≤ h1
  h2_nonneg : 0 ≤ h2
  p_nonneg : 0 ≤ p
  K1_nonneg : 0 ≤ K1
  K2_nonneg : 0 ≤ K2

namespace Params

variable (P : Params)

/-- Mean downstream lead-time demand `𝔼 D₁ = λ L₁`. -/
def mu1 : ℝ := P.lam * P.L1

/-- Mean upstream lead-time demand `𝔼 D₂ = λ L₂`. -/
def mu2 : ℝ := P.lam * P.L2

/-- Scaled downstream setup coefficient `k₁ = λ K₁`. -/
def k1 : ℝ := P.lam * P.K1

/-- Scaled upstream setup coefficient `k₂ = λ K₂`. -/
def k2 : ℝ := P.lam * P.K2

/-- Pipeline holding constant `H₀ = h₂ λ L₁`. -/
def H0 : ℝ := P.h2 * P.lam * P.L1

/-- Downstream mismatch loss `P(x) = 𝔼 φ_{h₁+h₂,p}(x - D₁)`. -/
def lossDown (x : ℝ) : ℝ := pexp P.mu1 (fun d => phi (P.h1 + P.h2) P.p (x - d))

/-- Downstream cost function `G₀(x) = H₀ + 𝔼 φ_{h₁+h₂,p}(x - D₁)` (eq. (6)). -/
def G0 (x : ℝ) : ℝ := P.H0 + P.lossDown x

/-- Upstream loss `F_up(x) = 𝔼 φ_{h₂,p}(x - D₂)`. -/
def lossUp (x : ℝ) : ℝ := pexp P.mu2 (fun d => phi P.h2 P.p (x - d))

/-- Inventory and backlog cost of the classical rule,
`I_{n,Q}(s,ℓ) = (1/n) ∑_{j=0}^{n-1} 𝔼[𝓛_Q G₀(s - (ℓ + jQ - D₂)⁻) + h₂ (ℓ + jQ - D₂)⁺]` (eq. (8)). -/
def invCost (n Q : ℕ) (s ℓ : ℝ) : ℝ :=
  (∑ j ∈ Finset.range n, pexp P.mu2 (fun d =>
      latAvg Q P.G0 (s - max (-(ℓ + (j : ℝ) * (Q : ℝ) - (d : ℝ))) 0)
        + P.h2 * max (ℓ + (j : ℝ) * (Q : ℝ) - (d : ℝ)) 0)) / n

/-- The exact lot-accounted cost formula of the classical rule with integer reorder points
`R₁, R₂`, lot size `Q` and multiplier `n` (Proposition 1, eq. (9)):
`k₁/Q + k₂/(nQ) + I_{n,Q}(R₁ + Q, R₂ - R₁)`. -/
def classicalFormula (R1 R2 : ℤ) (Q n : ℕ+) : ℝ :=
  P.k1 / ((Q : ℕ) : ℝ) + P.k2 / (((n : ℕ) : ℝ) * ((Q : ℕ) : ℝ))
    + P.invCost n Q ((R1 : ℝ) + ((Q : ℕ) : ℝ)) ((R2 : ℝ) - (R1 : ℝ))

/-- Zero-setup value `V₀ = inf_{r,y ∈ ℝ} 𝔼[G₀(r - (y - D₂)⁻) + h₂ (y - D₂)⁺]` (eq. (12)). -/
def V0 : ℝ :=
  ⨅ ry : ℝ × ℝ, pexp P.mu2 (fun d =>
      P.G0 (ry.1 - max (-(ry.2 - (d : ℝ))) 0) + P.h2 * max (ry.2 - (d : ℝ)) 0)

/-- Downstream single-stage benchmark `B₁(k) = H₀ + 𝓒_{P}(k)` (eq. (18)). -/
def B1 (k : ℝ) : ℝ := P.H0 + cycCost P.lossDown k

/-- Upstream single-stage benchmark `B₂(k) = 𝓒_{F_up}(k)` (eq. (18)). -/
def B2 (k : ℝ) : ℝ := cycCost P.lossUp k

/-- The composite lower bound
`L_two = max{ (B₁(2k₁) + B₂(2k₂))/2, V₀/2 + (B₁(4k₁) + B₂(4k₂))/4 }` (eq. (19)). -/
def Ltwo : ℝ :=
  max ((P.B1 (2 * P.k1) + P.B2 (2 * P.k2)) / 2)
      (P.V0 / 2 + (P.B1 (4 * P.k1) + P.B2 (4 * P.k2)) / 4)

/-- First allocated loss `F₁^{η,ζ}(x) = 𝔼 φ_{h₁+ηh₂, ζp}(x - D₁)` (eq. (13)). -/
def allocF1 (η ζ x : ℝ) : ℝ := pexp P.mu1 (fun d => phi (P.h1 + η * P.h2) (ζ * P.p) (x - d))

/-- Second allocated loss `F₂^{η,ζ}(x) = 𝔼 φ_{(1-η)h₂, (1-ζ)p}(x - D₁ - D₂)` with `D₁, D₂`
independent (eq. (14)). -/
def allocF2 (η ζ x : ℝ) : ℝ :=
  pexp P.mu1 (fun d1 => pexp P.mu2 (fun d2 =>
    phi ((1 - η) * P.h2) ((1 - ζ) * P.p) (x - d1 - d2)))

/-- The optimized allocation bound
`𝓐(c₁,c₂) = sup_{0 ≤ η,ζ ≤ 1} { η H₀ + 𝓒_{F₁^{η,ζ}}(c₁) + 𝓒_{F₂^{η,ζ}}(c₂) }` (eq. (16)). -/
def allocBound (c1 c2 : ℝ) : ℝ :=
  ⨆ q : {q : ℝ × ℝ // q.1 ∈ Set.Icc (0 : ℝ) 1 ∧ q.2 ∈ Set.Icc (0 : ℝ) 1},
    (q.1.1 * P.H0 + cycCost (P.allocF1 q.1.1 q.1.2) c1 + cycCost (P.allocF2 q.1.1 q.1.2) c2)

/-- The setup-preserving lower bound
`LB^SP = sup_{0 < u ≤ 1} { (1-u) V₀ + u 𝓐(k₁/u, k₂/u) }` (eq. (17)). -/
def LBsp : ℝ :=
  ⨆ u : Set.Ioc (0 : ℝ) 1, ((1 - (u : ℝ)) * P.V0 + (u : ℝ) * P.allocBound (P.k1 / u) (P.k2 / u))

/-- Feasibility in the joint-cycle calculation with upstream cycle size `m₂`: the downstream
choice `x(D₂, J)` may depend on the upstream lead-time demand `D₂` and the upstream cycle
position `J ∈ {0,…,m₂-1}`, must satisfy the availability limit `x ≤ z - D₂ - J`, and must be
integrable (`𝔼|x| < ∞`). -/
def JointFeasible (m2 : ℕ) (z : ℝ) (x : ℕ → Fin m2 → ℝ) : Prop :=
  (∀ (d : ℕ) (j : Fin m2), x d j ≤ z - (d : ℝ) - ((j : ℕ) : ℝ)) ∧
    ∀ j : Fin m2, Summable (fun d : ℕ => poisW P.mu2 d * |x d j|)

/-- Objective of the joint-cycle calculation with independent cycle positions `J_{m₁}`, `J_{m₂}`
(uniform on `{0,…,m₁-1}` and `{0,…,m₂-1}`):
`𝔼[H₀ + φ_{h₁+h₂,p}(x - D₁ - J_{m₁}) + h₂ (z - D₂ - J_{m₂} - x)]`, written with the inner
expectation over `(D₁, J_{m₁})`, i.e. `𝓛_{m₁} G₀(x) = 𝔼 G₀(x - J_{m₁})`. -/
def jointObj (m1 m2 : ℕ) (z : ℝ) (x : ℕ → Fin m2 → ℝ) : ℝ :=
  pexp P.mu2 (fun d => (∑ j : Fin m2,
      (latAvg m1 P.G0 (x d j) + P.h2 * (z - (d : ℝ) - ((j : ℕ) : ℝ) - x d j))) / m2)

/-- Joint inventory value `V_{m₁,m₂} = 𝓥(J_{m₁}, J_{m₂})` (eqs. (D.3), (D.7)). -/
def Vjoint (m1 m2 : ℕ) : ℝ :=
  ⨅ zx : {zx : ℝ × (ℕ → Fin m2 → ℝ) // P.JointFeasible m2 zx.1 zx.2},
    P.jointObj m1 m2 zx.1.1 zx.1.2

/-- Joint cycle cost `𝓙(c₁,c₂) = inf_{m₁,m₂ ∈ ℕ} { c₁/m₁ + c₂/m₂ + V_{m₁,m₂} }` (eqs. (21), (D.7)). -/
def Jjoint (c1 c2 : ℝ) : ℝ :=
  ⨅ m : ℕ+ × ℕ+, (c1 / ((m.1 : ℕ) : ℝ) + c2 / ((m.2 : ℕ) : ℝ) + P.Vjoint m.1 m.2)

end Params

end TwoStageRnQ


