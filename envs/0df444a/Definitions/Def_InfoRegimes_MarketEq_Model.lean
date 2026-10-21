-- Prove2me | Definitions.Def_InfoRegimes_MarketEq_Model
-- name    : InfoRegimes_MarketEq_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T16:21:46.187972+00:00
-- url     : https://prove2.me/theorems/8e62f268-0760-4f02-afa5-b06bb1d9c107
-- title:
--   §2, §4.1, App. B, pp. 6–13, 20–22, 41–44 — OLG market with a dynamic information state: Π_D, kernel of (6), mean-variance investors, linear prices (20), clearing (11), self-consistency (26)
-- statement:
--   The market of Glasserman, Mamaysky and Shen with a dynamic information state, together with the objects of its market-equilibrium analysis (§2, §4.1 and Appendix B).
--
--   **Parameters.** A gross riskless return $R$, dividend persistence $\rho$ and long-run level $\bar D$ in the dividend process
--   $$D_{t+1} = (1-\rho)\bar D + \rho D_t + M_{t+1}, \qquad \mu_D = (1-\rho)\bar D,$$
--   the standard deviations $\sigma_M$ of the innovation $M_{t+1}$ and $\sigma_X$ of the supply shock $X_t$, risk aversion $\gamma$, the private share $\phi$ of the knowable innovation, net supply $\bar X$, the coefficients $a_f, b_f, \kappa_f$ of the information dynamics, a grid size $m$, and the law of the shock $\epsilon_f$ (an arbitrary probability measure on $\mathbb R$). The **standing assumptions** are
--   $$R>1,\quad -1<\rho<1,\quad \sigma_M,\sigma_X,\gamma,\bar X>0,\quad 0\le\phi\le1,\quad m\ge1 .$$
--
--   **Information state.** The state space is the grid $\mathcal D = \{0, 1/m, \dots, 1\}$, and $f_i = i/m$. The map $\Pi_{\mathcal D}$ clips $x$ to $[0,1]$ and rounds it up to the nearest grid point. Given a fraction informed $\lambda : \mathcal D \to \mathbb R$, the state evolves by (6), $f_{t+1} = \Pi_{\mathcal D}(a_f + b_f\lambda(f_t) + \kappa_f(f_t - a_f) + \epsilon_{f,t+1})$, so the transition probability from $f_i$ to $f_j$ is the probability of the set of shocks sent to $f_j$. For $h:\mathcal D\to\mathbb R$, $E_t h(f_{t+1})$ at $f_t = f_i$ is $\sum_j p_{ij} h(f_j)$; its $k$-fold iterate is $E_t h(f_{t+k})$.
--
--   **Prices and demands.** A linear price process (20) is
--   $$P_t = a(f_t) + b(f_t)m_t + g\theta_t - c(f_t)X_t + dD_t,$$
--   with functions $a, b, c$ on $\mathcal D$ and constants $d, g$, none of them fixed in advance. Given a conjectured variance $V_B : \mathcal D \to \mathbb R$, the Kalman gain and the two expected conditional variances of the net profit are, as in (B.5), (B.7), (B.8),
--   $$K = \frac{b\phi f\sigma_M^2}{b^2\phi f\sigma_M^2 + c^2\sigma_X^2},\qquad q^I_D = (1+d)^2(1-f)\sigma_M^2 + E_tV_B(f_{t+1}),\qquad q^U_D = q^I_D + (1+d)^2\phi f\sigma_M^2(1-Kb).$$
--   The informed investor, who sees $f_t, \theta_t, D_t, P_t$ and $m_t$, chooses $q$ to maximize
--   $$q\big[(1+d)(\mu_D + \rho D_t + \theta_t + m_t) + E_t a(f_{t+1}) - RP_t\big] - \tfrac{\gamma}{2}q^2 q^I_D ,$$
--   the objective (B.1) with (23) and (B.3), up to the constant $RW_t$. The uninformed investor sees $f_t, \theta_t, D_t$ and $P_t$ only; from them it recovers $s = P_t - a(f_t) - g\theta_t - dD_t = bm_t - cX_t$ and uses $E[m_t\mid P_t,\theta_t] = Ks$, maximizing the same expression with $m_t$ replaced by $Ks$ and $q^I_D$ by $q^U_D$.
--
--   **Equilibrium.** The price process **clears the market** if at every state $f_i$ and every realization $(m_t, \theta_t, X_t, D_t) \in \mathbb R^4$ there are maximizers $q^I, q^U$ of the two objectives at the price (20) with
--   $$\lambda q^I + (1-\lambda)q^U = \bar X + X_t. \tag{11}$$
--   $V_B$ is **self-consistent** for the coefficients if
--   $$V_B(f) = b(f)^2\phi f\sigma_M^2 + g^2(1-\phi)f\sigma_M^2 + c(f)^2\sigma_X^2 \quad \text{for all } f. \tag{26}$$
--   A **market equilibrium** for $\lambda$ is a conjecture $V_B > 0$ and price coefficients that clear the market and for which $V_B$ is self-consistent.
--
--   **The recipe.** With $d = \rho/(R-\rho)$ and $g = 1/(R-\rho)$ (B.10), the steps (B.13)–(B.18) compute from $V_B$ and $\lambda$ the quantities $q^I_D$, $r = \lambda(1+d)/(\gamma q^I_D)$, $\mathcal R^2 = r^2f\phi\sigma_M^2/(r^2f\phi\sigma_M^2+\sigma_X^2)$, $q^U_D = q^I_D + (1+d)^2f\phi\sigma_M^2(1-\mathcal R^2)$,
--   $$b = \frac{1+d}{R}\,\frac{\lambda q^U_D + (1-\lambda)q^I_D\mathcal R^2}{\lambda q^U_D + (1-\lambda)q^I_D},\qquad c = \begin{cases} b/r, & \lambda>0,\\ \gamma q^U_D/R, & \lambda = 0,\end{cases}$$
--   and the **self-consistency map** $T$ sends $V_B$ to the right side of (26) evaluated at these $b, c, g$.
--
--   These objects are shared by every statement of the mission: Lemma 4.1, the reduction of p. 22, Proposition 4.1 and the equations of Appendix B.
--
--   **Formalization Note.** The bound $-1<\rho<1$ is added: the paper never states the range of $\rho$, while $d$ and (27) need $\rho<R$ and the dividend is a mean-reverting AR(1). The grid is `Fin (m+1)`. Transition probabilities are the real values (`toReal`) of the shock law on preimage sets. The Gaussian posterior mean and variance (B.7)–(B.8) are written in closed form rather than derived from a joint law; milestone `posterior_variance` checks the variance identity behind them. Demands are maximizers (`IsMaxOn` with an existential), not closed-form formulas. Clearing is required for every realization in $\mathbb R^4$, which is how Appendix B "collects terms". When $b = c = 0$ the gain $K$ is $0/0$, which Lean evaluates to $0$ (the price carries no signal).
-- source:
--   Glasserman, Mamaysky & Shen, Dynamic Information Regimes in Financial Markets, SSRN 3324789 (version of October 17, 2023), pp. 6–13, 20–22, 41–44, §2 eqs. (1)–(4), (6), footnote 6, (7)–(9), (11); §4.1 eqs. (20), (23), (25), (26); App. B eqs. (B.1)–(B.18)

import Mathlib

namespace InfoRegimes.MarketEq

/-- Parameters of the model of §2 (pp. 6–13). The information-state grid is
`D = {0, 1/m, …, 1}` (footnote 6, p. 9, with `n = m + 1`), and `shock` is the law of `ε_f`
in (6). -/
structure Params where
  /-- gross return `R` on the riskless asset (p. 11) -/
  R : ℝ
  /-- dividend persistence `ρ` in (1) -/
  rho : ℝ
  /-- long-run dividend level `D̄` in (1) -/
  Dbar : ℝ
  /-- standard deviation `σ_M` of the dividend innovation `M_{t+1}` -/
  sigM : ℝ
  /-- standard deviation `σ_X` of the supply shock `X_t` -/
  sigX : ℝ
  /-- risk aversion `γ` in (9) -/
  gam : ℝ
  /-- `ϕ` in (4): the share of the knowable innovation that is private -/
  phi : ℝ
  /-- constant net supply `X̄` -/
  Xbar : ℝ
  /-- `a_f` in (6) -/
  af : ℝ
  /-- `b_f` in (6) -/
  bf : ℝ
  /-- `κ_f` in (6) -/
  kf : ℝ
  /-- the grid `D` has `m + 1` points `0, 1/m, …, 1` -/
  m : ℕ
  /-- the law of the shock `ε_{f,t+1}` in (6) -/
  shock : MeasureTheory.ProbabilityMeasure ℝ

/-- Standing assumptions of §2: `R > 1` (p. 11), `-1 < ρ < 1` (added; the paper never states
the range of `ρ`), `σ_M, σ_X, γ, X̄ > 0` (pp. 7, 12), `ϕ ∈ [0, 1]` (p. 7), and a grid with at
least two points (footnote 6). -/
def Params.Standing (P : Params) : Prop :=
  1 < P.R ∧ -1 < P.rho ∧ P.rho < 1 ∧ 0 < P.sigM ∧ 0 < P.sigX ∧ 0 < P.gam ∧
    0 ≤ P.phi ∧ P.phi ≤ 1 ∧ 0 < P.Xbar ∧ 1 ≤ P.m

/-- Information states: the index set of the grid `D`. -/
abbrev State (P : Params) := Fin (P.m + 1)

/-- The grid point `f_i = i / m ∈ D`. -/
noncomputable def grid (P : Params) (i : State P) : ℝ := ((i : ℕ) : ℝ) / (P.m : ℝ)

/-- `μ_D = (1 - ρ) D̄`, (1). -/
def muD (P : Params) : ℝ := (1 - P.rho) * P.Dbar

/-- `Π_D` of footnote 6: clip to `[0, 1]`, then round up to the closest grid point. Returns the
index of that grid point. -/
noncomputable def projD (P : Params) (x : ℝ) : State P :=
  ⟨min P.m ⌈(P.m : ℝ) * max 0 (min 1 x)⌉₊, Nat.lt_succ_of_le (min_le_left _ _)⟩

/-- The transition kernel of (6) at the fraction informed `lam`:
`P(f_{t+1} = f_j | f_t = f_i) = P(Π_D(a_f + b_f λ(f_i) + κ_f (f_i - a_f) + ε) = f_j)`. -/
noncomputable def trans (P : Params) (lam : State P → ℝ) (i j : State P) : ℝ :=
  ((P.shock : MeasureTheory.Measure ℝ)
    {e : ℝ | projD P (P.af + P.bf * lam i + P.kf * (grid P i - P.af) + e) = j}).toReal

/-- `E[h(f_{t+1}) | f_t = f_i]` under the kernel of (6). -/
noncomputable def Ef (P : Params) (lam : State P → ℝ) (i : State P) (h : State P → ℝ) : ℝ :=
  ∑ j, trans P lam i j * h j

/-- `k`-fold conditional expectation: `EfIter k h i = E[h(f_{t+k}) | f_t = f_i]`. -/
noncomputable def EfIter (P : Params) (lam : State P → ℝ) : ℕ → (State P → ℝ) → State P → ℝ
  | 0, h => h
  | k + 1, h => fun i => Ef P lam i (EfIter P lam k h)

/-- Coefficients of a linear price process (20):
`P_t = a(f_t) + b(f_t) m_t + g θ_t - c(f_t) X_t + d D_t`. No coefficient is fixed in advance. -/
structure PriceCoeffs (P : Params) where
  a : State P → ℝ
  b : State P → ℝ
  c : State P → ℝ
  d : ℝ
  g : ℝ

/-- The price (20) at state `i` and realization `(m_t, θ_t, X_t, D_t)`. -/
def price {P : Params} (C : PriceCoeffs P) (i : State P) (mm θ X D : ℝ) : ℝ :=
  C.a i + C.b i * mm + C.g * θ - C.c i * X + C.d * D

/-- `K_t` of (B.8): `b ϕ f σ_M² / (b² ϕ f σ_M² + c² σ_X²)`. -/
noncomputable def Kgain (P : Params) (C : PriceCoeffs P) (i : State P) : ℝ :=
  C.b i * P.phi * grid P i * P.sigM ^ 2 /
    (C.b i ^ 2 * P.phi * grid P i * P.sigM ^ 2 + C.c i ^ 2 * P.sigX ^ 2)

/-- `q^I_D` of (B.5): `(1 + d)² (1 - f) σ_M² + E_t V_B(f_{t+1})`. -/
noncomputable def qID (P : Params) (lam : State P → ℝ) (VB : State P → ℝ) (C : PriceCoeffs P)
    (i : State P) : ℝ :=
  (1 + C.d) ^ 2 * (1 - grid P i) * P.sigM ^ 2 + Ef P lam i VB

/-- `q^U_D` of (B.5) with (B.7): `q^I_D + (1 + d)² ϕ f σ_M² (1 - K b)`. -/
noncomputable def qUD (P : Params) (lam : State P → ℝ) (VB : State P → ℝ) (C : PriceCoeffs P)
    (i : State P) : ℝ :=
  qID P lam VB C i + (1 + C.d) ^ 2 * (P.phi * grid P i * P.sigM ^ 2 * (1 - Kgain P C i * C.b i))

/-- Informed objective (B.1) with (23) and (B.3), at state `i`, private signal `mm = m_t`,
public signal `θ`, dividend `D = D_t`, price `p = P_t`, as a function of the demand `q`.
The term `R W_t`, which does not depend on `q`, is omitted. -/
noncomputable def objI (P : Params) (lam : State P → ℝ) (VB : State P → ℝ) (C : PriceCoeffs P)
    (i : State P) (mm θ D p : ℝ) (q : ℝ) : ℝ :=
  q * ((1 + C.d) * (muD P + P.rho * D + θ + mm) + Ef P lam i C.a - P.R * p)
    - P.gam / 2 * q ^ 2 * qID P lam VB C i

/-- Uninformed objective (B.1) with (23), (B.3), (B.7): it sees only the state, `θ`, `D = D_t`
and the price `p`. It infers `s = p - a - g θ - d D = b m_t - c X_t` and uses the Gaussian
posterior mean `E[m_t | P_t, θ_t] = K_t s`. -/
noncomputable def objU (P : Params) (lam : State P → ℝ) (VB : State P → ℝ) (C : PriceCoeffs P)
    (i : State P) (θ D p : ℝ) (q : ℝ) : ℝ :=
  q * ((1 + C.d) * (muD P + P.rho * D + θ + Kgain P C i * (p - C.a i - C.g * θ - C.d * D))
      + Ef P lam i C.a - P.R * p)
    - P.gam / 2 * q ^ 2 * qUD P lam VB C i

/-- Market clearing (11) with optimal demands: at every state and every realization
`(m_t, θ_t, X_t, D_t) ∈ ℝ⁴`, there are maximizers of the informed and uninformed objectives at
the price (20) that clear the market. -/
def Clears (P : Params) (lam : State P → ℝ) (VB : State P → ℝ) (C : PriceCoeffs P) : Prop :=
  ∀ (i : State P) (mm θ X D : ℝ), ∃ qI qU : ℝ,
    IsMaxOn (objI P lam VB C i mm θ D (price C i mm θ X D)) Set.univ qI ∧
    IsMaxOn (objU P lam VB C i θ D (price C i mm θ X D)) Set.univ qU ∧
    lam i * qI + (1 - lam i) * qU = P.Xbar + X

/-- Self-consistency (26): `V_B(f) = b(f)² ϕ f σ_M² + g² (1 - ϕ) f σ_M² + c(f)² σ_X²`. -/
def SelfConsistent (P : Params) (VB : State P → ℝ) (C : PriceCoeffs P) : Prop :=
  ∀ i, VB i = C.b i ^ 2 * P.phi * grid P i * P.sigM ^ 2
    + C.g ^ 2 * (1 - P.phi) * grid P i * P.sigM ^ 2 + C.c i ^ 2 * P.sigX ^ 2

/-- A market equilibrium (pp. 12–13, 21–22) for the fraction informed `lam`: a positive
conjectured variance `V_B`, a linear price process (20) whose optimal demands clear the market,
and `V_B` self-consistent (26). -/
def MarketEquilibrium (P : Params) (lam : State P → ℝ) : Prop :=
  ∃ (VB : State P → ℝ) (C : PriceCoeffs P),
    (∀ i, 0 < VB i) ∧ Clears P lam VB C ∧ SelfConsistent P VB C

/-- `d = ρ / (R - ρ)`, (B.10). -/
noncomputable def dConst (P : Params) : ℝ := P.rho / (P.R - P.rho)

/-- `g = 1 / (R - ρ)`, (B.10). -/
noncomputable def gConst (P : Params) : ℝ := 1 / (P.R - P.rho)

/-- (B.13): `q^I_D(f) = (1 + d)² (1 - f) σ_M² + E[V_B(f_{t+1}) | f_t = f]`. -/
noncomputable def qID0 (P : Params) (lam VB : State P → ℝ) (i : State P) : ℝ :=
  (1 + dConst P) ^ 2 * (1 - grid P i) * P.sigM ^ 2 + Ef P lam i VB

/-- (B.14): `r(f) = λ(f) (1 + d) / (γ q^I_D(f))`. -/
noncomputable def r0 (P : Params) (lam VB : State P → ℝ) (i : State P) : ℝ :=
  lam i * (1 + dConst P) / (P.gam * qID0 P lam VB i)

/-- (B.15): `𝓡²(f) = r² f ϕ σ_M² / (r² f ϕ σ_M² + σ_X²)`. -/
noncomputable def R2rec (P : Params) (lam VB : State P → ℝ) (i : State P) : ℝ :=
  r0 P lam VB i ^ 2 * grid P i * P.phi * P.sigM ^ 2 /
    (r0 P lam VB i ^ 2 * grid P i * P.phi * P.sigM ^ 2 + P.sigX ^ 2)

/-- (B.16): `q^U_D(f) = q^I_D(f) + (1 + d)² f ϕ σ_M² (1 - 𝓡²(f))`. -/
noncomputable def qUD0 (P : Params) (lam VB : State P → ℝ) (i : State P) : ℝ :=
  qID0 P lam VB i + (1 + dConst P) ^ 2 * grid P i * P.phi * P.sigM ^ 2 * (1 - R2rec P lam VB i)

/-- (B.17): `b(f) = ((1 + d)/R) (λ q^U_D + (1 - λ) q^I_D 𝓡²) / (λ q^U_D + (1 - λ) q^I_D)`. -/
noncomputable def bRec (P : Params) (lam VB : State P → ℝ) (i : State P) : ℝ :=
  (1 + dConst P) / P.R *
    ((lam i * qUD0 P lam VB i + (1 - lam i) * qID0 P lam VB i * R2rec P lam VB i) /
      (lam i * qUD0 P lam VB i + (1 - lam i) * qID0 P lam VB i))

/-- (B.18): `c(f) = b(f)/r(f)` if `λ(f) > 0`, and `γ q^U_D(f)/R` if `λ(f) = 0`. -/
noncomputable def cRec (P : Params) (lam VB : State P → ℝ) (i : State P) : ℝ :=
  if 0 < lam i then bRec P lam VB i / r0 P lam VB i else P.gam * qUD0 P lam VB i / P.R

/-- The self-consistency map of p. 22: the right side of (26) evaluated at the coefficients
(B.10), (B.17), (B.18) produced from the conjecture `V_B`. -/
noncomputable def Tmap (P : Params) (lam VB : State P → ℝ) (i : State P) : ℝ :=
  bRec P lam VB i ^ 2 * P.phi * grid P i * P.sigM ^ 2
    + gConst P ^ 2 * (1 - P.phi) * grid P i * P.sigM ^ 2 + cRec P lam VB i ^ 2 * P.sigX ^ 2

end InfoRegimes.MarketEq


