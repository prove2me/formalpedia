-- Prove2me | Definitions.Def_ValueTrial_Asymptotic_Model
-- name    : ValueTrial_Asymptotic_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T16:16:38.803901+00:00
-- url     : https://prove2.me/theorems/33c6d03f-5d1f-4ed9-a70b-b83abddd5841
-- title:
--   §2–§3.2, pp. 6–12 — value-based two-armed trial: expected net gain V(T,r), fixed pool / fixed horizon, optimality on a decision set
-- statement:
--   This module sets up the value-based fixed sample size clinical trial of Alban, Chick and Forster.
--
--   A trial compares a new health technology N with the standard S. Before the trial a fraction $p_N\in[0,\tfrac12]$ of the eligible population is treated with N. The planner recruits patients for a duration $T\ge0$ at rate $r\ge0$, randomised in pairs, so that the sample size is $Q=Tr/2$ pairs. The incremental net monetary benefit $W$ of N over S has prior $\mathcal N(\mu_0,\sigma_0^2)$; each pair yields an observation $X_i\mid W\sim\mathcal N(W,\sigma_X^2)$, and $n_0=\sigma_X^2/\sigma_0^2$ is the prior's effective sample size, so $\sigma_0=\sigma_X/\sqrt{n_0}$. After $Q$ pairs the posterior mean $Z_{Tr}$ is, before the data are seen, distributed as $\mathcal N(\mu_0,\sigma_Z^2)$ with
--   $$
--   \sigma_Z^2=\frac{\sigma_X^2\,Q}{n_0(n_0+Q)} .
--   $$
--
--   The **parameters** are $p_N,\mu_0,\sigma_X,n_0$, the cost $c\ge0$ per patient, the indicator $\delta_{on}\in\{0,1\}$ of online learning, switching costs $I_N,I_S\ge0$, an incidence rate $\zeta>0$, an observation delay $\Delta\ge0$ and a discount rate $\rho\in[0,1)$; the **standing assumptions** collect exactly these sign conditions together with $\sigma_X>0$, $n_0>0$. The setup cost $c_{cap}(r)$ and the post-adoption population $P(T)$ are functions supplied as arguments. With $\tilde T_\rho(T)=(1-e^{-\rho T})/\rho$ and $P_\rho(T)=(\zeta/\rho)(1-e^{-\rho P(T)/\zeta})$ (both equal to $T$, resp. $P(T)$, when $\rho=0$), the **expected net gain** is, for $Tr>0$, equation (7):
--   $$
--   V(T,r)=-\big(c_{cap}(r)+c\tilde T_\rho(T)r\big)+\delta_{on}\frac{\tilde T_\rho(T)r}{2}(1-2p_N)\mu_0+e^{-\rho(T+\Delta)}\,\mathbb E\Big[\big(P_\rho(T)(1-p_N)Z_{Tr}-I_N\big)^++\big(-P_\rho(T)p_NZ_{Tr}-I_S\big)^+\Big],
--   $$
--   the expectation being over $Z_{Tr}\sim\mathcal N(\mu_0,\sigma_Z^2)$; and, for $Tr=0$ (no trial), equation (9):
--   $$
--   V(T,r)=\max\{0,\ (1-p_N)P_\rho(0)\mu_0-I_N,\ -p_NP_\rho(0)\mu_0-I_S\}.
--   $$
--
--   The module also defines the two post-adoption populations of §2.4.1, the **fixed patient pool** $P(T)=P$ and the **fixed horizon** $P(T)=\zeta(H-T-\mathbf 1_{T>0}\Delta)$; the predicate "$x$ maximises $f$ over $S$"; the feasible box $[0,T_{\max}]\times[0,r_{\max}]$ of problem (5); and the constants of the asymptotic results: $C=c-\delta_{on}(1-2p_N)\mu_0/2$, $\phi(\mu_0/\sigma_0)$ with $\phi$ the standard normal density, and
--   $$
--   v_\infty=(1-p_N)\sigma_0\Psi(-\mu_0/\sigma_0)+p_N\sigma_0\Psi(\mu_0/\sigma_0),
--   $$
--   where $\Psi(z)=\mathbb E[(Z-z)^+]$ is the standard normal linear loss function.
--
--   These objects are shared by every statement of the mission: existence and structure of optimal designs (Propositions 1–4), the closed form (8), and the square-root growth of the optimal sample size (Lemmas EC.1–EC.4, Proposition 5).
--
--   **Formalization Note** A design is a pair $x=(T,r)\in\mathbb R\times\mathbb R$; all quantities are real. The post-adoption term is the Bochner integral against `gaussianReal µ0 σZ²`, not the closed form (8), which is a separate theorem. $E[Z_{Tr}]=\mu_0$ is written directly. The (9) branch uses $P_\rho(0)$, i.e. `Ppop 0`, as the page does; for the fixed horizon that is $\zeta H$. $\Psi$ is the published `InventoryControl.normalLoss`.
-- source:
--   Alban, Chick & Forster, Value-based clinical trials, accepted manuscript (Management Science 69(6), 2023; IRIS UniBo 11585/879132), pp. 6–12 (PDF 8–14), §2, §3.1–3.2, eqs. (3)–(7), (9); §2.4.1; Table EC.1, p. ec1 (PDF 38)

import Mathlib
import Definitions.Def_InventoryControl_newsboy

namespace ValueTrial.Asymptotic

open MeasureTheory ProbabilityTheory Filter

/-- The scalar parameters of the value-based two-armed trial of Alban, Chick & Forster (§2):
`pN` the fraction of patients on the new technology before the trial, `mu0` the prior mean of
the incremental net monetary benefit `W`, `sigX` the sampling standard deviation of one pair's
observation, `n0` the prior's effective sample size, `c` the variable cost per patient,
`don` the online-learning indicator `δon`, `IN`, `IS` the fixed switching costs, `zeta` the
incidence rate, `Del` the observation delay `∆`, `rho` the discount rate. -/
structure Params where
  pN : ℝ
  mu0 : ℝ
  sigX : ℝ
  n0 : ℝ
  c : ℝ
  don : ℝ
  IN : ℝ
  IS : ℝ
  zeta : ℝ
  Del : ℝ
  rho : ℝ

/-- The standing assumptions of §2 (pp. 6–10) and Table EC.1, including `0 ≤ ρ < 1`. -/
def Params.Standing (θ : Params) : Prop :=
  0 ≤ θ.pN ∧ θ.pN ≤ 1 / 2 ∧ 0 < θ.sigX ∧ 0 < θ.n0 ∧ 0 ≤ θ.c ∧ (θ.don = 0 ∨ θ.don = 1) ∧
    0 ≤ θ.IN ∧ 0 ≤ θ.IS ∧ 0 < θ.zeta ∧ 0 ≤ θ.Del ∧ 0 ≤ θ.rho ∧ θ.rho < 1

/-- Prior standard deviation `σ0 = σX / √n0` (from `n0 = σX² / σ0²`, p. 11). -/
noncomputable def sig0 (θ : Params) : ℝ := θ.sigX / Real.sqrt θ.n0

/-- Standard deviation `σZ` of the preposterior mean after `Q = Tr/2` pairs (p. 11):
`σZ² = σX² Q / (n0 (n0 + Q))`. -/
noncomputable def sigZ (θ : Params) (Q : ℝ) : ℝ :=
  Real.sqrt (θ.sigX ^ 2 * Q / (θ.n0 * (θ.n0 + Q)))

/-- Discounted recruitment duration `T̃ρ(T) = (1 - e^{-ρT})/ρ`, and `T` when `ρ = 0` (p. 10). -/
noncomputable def Ttil (θ : Params) (T : ℝ) : ℝ :=
  if θ.rho = 0 then T else (1 - Real.exp (-θ.rho * T)) / θ.rho

/-- Discounted post-adoption population `Pρ = (ζ/ρ)(1 - e^{-ρ P/ζ})`, and `P` when `ρ = 0`
(p. 10), as a function of the undiscounted population `P = P(T)`. -/
noncomputable def Prho (θ : Params) (P : ℝ) : ℝ :=
  if θ.rho = 0 then P else θ.zeta / θ.rho * (1 - Real.exp (-θ.rho * P / θ.zeta))

/-- The post-adoption expected reward of (7): `E[(Pr(1-pN)Z - IN)^+ + (-Pr pN Z - IS)^+]` with
`Z ~ N(µ0, σZ(Q)²)`, the preposterior mean after `Q` pairs. -/
noncomputable def postGain (θ : Params) (Pr Q : ℝ) : ℝ :=
  ∫ z, (max (Pr * (1 - θ.pN) * z - θ.IN) 0 + max (-(Pr * θ.pN * z) - θ.IS) 0)
    ∂(gaussianReal θ.mu0 ((sigZ θ Q) ^ 2).toNNReal)

/-- The expected net gain `V(T, r)` of a design `x = (T, r)`: equation (9) when `Tr = 0` and
equation (7) (the expectation form of (4b)) when `Tr ≠ 0`. `ccap` is the setup cost as a
function of the recruitment rate and `Ppop` the post-adoption population `P(T)`. -/
noncomputable def V (θ : Params) (ccap Ppop : ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  if x.1 * x.2 = 0 then
    max 0 (max ((1 - θ.pN) * Prho θ (Ppop 0) * θ.mu0 - θ.IN)
      (-(θ.pN * Prho θ (Ppop 0) * θ.mu0) - θ.IS))
  else
    -(ccap x.2 + θ.c * Ttil θ x.1 * x.2) + θ.don * (Ttil θ x.1 * x.2 / 2) * (1 - 2 * θ.pN) * θ.mu0
      + Real.exp (-θ.rho * (x.1 + θ.Del)) * postGain θ (Prho θ (Ppop x.1)) (x.1 * x.2 / 2)

/-- Fixed patient pool: `P(T) = P` (§2.4.1, item 2). -/
def fixedPool (P : ℝ) : ℝ → ℝ := fun _ => P

/-- Fixed horizon: `P(T) = ζ (H - T - 1_{T>0} ∆)` (§2.4.1, item 1). -/
noncomputable def fixedHorizon (θ : Params) (H : ℝ) : ℝ → ℝ :=
  fun T => θ.zeta * (H - T - (if 0 < T then θ.Del else 0))

/-- `x` maximizes `f` over `S`. -/
def IsOptOn (f : ℝ × ℝ → ℝ) (S : Set (ℝ × ℝ)) (x : ℝ × ℝ) : Prop :=
  x ∈ S ∧ ∀ y ∈ S, f y ≤ f x

/-- The feasible set `[0, Tmax] × [0, rmax]` of problem (5). -/
def box (Tmax rmax : ℝ) : Set (ℝ × ℝ) := Set.Icc 0 Tmax ×ˢ Set.Icc 0 rmax

/-- Per-patient sampling cost net of online rewards, `c - δon (1 - 2pN) µ0 / 2`. -/
noncomputable def Cnet (θ : Params) : ℝ := θ.c - θ.don * (1 - 2 * θ.pN) * θ.mu0 / 2

/-- `ϕ(µ0/σ0)`, the standard normal density at `µ0/σ0`. -/
noncomputable def phi0 (θ : Params) : ℝ := gaussianPDFReal 0 1 (θ.mu0 / sig0 θ)

/-- The limiting per-patient value `(1 - pN) σ0 Ψ(-µ0/σ0) + pN σ0 Ψ(µ0/σ0)`. -/
noncomputable def vInf (θ : Params) : ℝ :=
  (1 - θ.pN) * sig0 θ * InventoryControl.normalLoss (-(θ.mu0 / sig0 θ))
    + θ.pN * sig0 θ * InventoryControl.normalLoss (θ.mu0 / sig0 θ)

end ValueTrial.Asymptotic


