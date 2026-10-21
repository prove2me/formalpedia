-- Prove2me | Definitions.Def_RiskPremiaDMP_Equivalence_Model
-- name    : RiskPremiaDMP_Equivalence_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:23.810885+00:00
-- url     : https://prove2.me/theorems/217fa854-46d4-4887-818f-dfb4af72cd14
-- title:
--   §2–§3, pp. 5–15 — DMP surplus PDEs with and without risk premia, generators L^P (5) and L^Q (20), parameter maps (21)–(27), productivity paths
-- statement:
--   This file sets up the two continuous-time search-and-matching (Diamond–Mortensen–Pissarides) economies of Mitra, Seo and Xu and the dictionary between them.
--
--   **Partial derivatives and generators.** For $F:\mathbb R^2\to\mathbb R$ write $\partial_1F,\partial_{11}F$ for the first and second partial derivatives in the first argument and $\partial_2F,\partial_{22}F$ for those in the second argument. The generator of the productivity process of the economy without risk premia, equation (5), is
--   $$\mathscr L^{\mathcal P}[\kappa_y,\sigma_y,\kappa_\mu,\sigma_\mu]F(y,\mu)=\kappa_y(\mu-y)\partial_1F+\tfrac12\sigma_y^2\partial_{11}F-\kappa_\mu\mu\,\partial_2F+\tfrac12\sigma_\mu^2\partial_{22}F,$$
--   and the risk-neutral generator of the economy with risk premia, equation (20), is
--   $$\mathscr L^{\mathcal Q}[\kappa_y,\sigma_y,\kappa_\eta,\bar\eta,\sigma_\eta]F(y,\eta)=-(\sigma_y\eta+\kappa_y y)\partial_1F+\tfrac12\sigma_y^2\partial_{11}F+\kappa_\eta(\bar\eta-\eta)\partial_2F+\tfrac12\sigma_\eta^2\partial_{22}F.$$
--
--   **Economy without risk premia (§2.1).** Parameters: risk-free rate $r_f$, separation rate $s$, bargaining power $\beta$, vacancy cost $c$, value of leisure $z$, and productivity parameters $\kappa_y,\sigma_y,\kappa_\mu,\sigma_\mu$. Standing assumptions: $\kappa_y>0$, $\kappa_\mu\ge0$, $\sigma_\mu\ge0$, $\beta\in(0,1)$. Given a vacancy-filling rate $q$, an *equilibrium* is a $C^2$ surplus $S(y,\mu)$ and a tightness $\theta(y,\mu)$ with, at every state,
--   $$(r_f+s)S=e^y-z-\frac{\beta c}{1-\beta}\theta+\mathscr L^{\mathcal P}S,\qquad c=(1-\beta)q(\theta)S\qquad(8).$$
--
--   **Economy with risk premia (§2.2).** Parameters: $r_f,s,\beta,c,z,\kappa_y,\sigma_y$ and the market-price-of-risk parameters $\kappa_\eta,\bar\eta,\sigma_\eta$. Standing assumptions: $\kappa_y>0$, $\sigma_y>0$, $\kappa_\eta>0$, $\sigma_\eta>0$, $\beta\in(0,1)$. An *equilibrium* is a $C^2$ surplus $S(y,\eta)$ and a tightness $\theta(y,\eta)$ solving (19), which is (8) with $\mathscr L^{\mathcal Q}$ in place of $\mathscr L^{\mathcal P}$.
--
--   **Dictionary (§3).** With the shift $a=\sigma_y\bar\eta/\kappa_y=-\mathbb E^{\mathcal Q}[y_t]$ (22), the state maps (21) are $y^{\mathcal Q}=y+a$ and $\mu^{\mathcal Q}=\sigma_y(\bar\eta-\eta)/\kappa_y$. The *artificial economy* has $z^{\mathcal Q}=e^az$, $c^{\mathcal Q}=e^ac$ (23), $\kappa^{\mathcal Q}_y=\kappa_y$, $\sigma^{\mathcal Q}_y=\sigma_y$, $\kappa^{\mathcal Q}_\mu=\kappa_\eta$, $\sigma^{\mathcal Q}_\mu=\sigma_\eta\sigma_y/\kappa_y$ (27), and the same $r_f,s,\beta$.
--
--   **Productivity paths.** The stochastic differential equations (1), (9), (12), (15) are written pathwise in integral form for $t\ge0$, driven by given paths $B$ through their increments $B_t-B_0$; for instance (9) reads $y_t=y_0-\int_0^t\kappa_yy_u\,du+\sigma_y(B^{y,\mathcal P}_t-B^{y,\mathcal P}_0)$. The path (16) is $B^{y,\mathcal Q}_t=\int_0^t\eta_u\,du+B^{y,\mathcal P}_t$.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** States are pairs of reals, functions are curried with productivity first, and partial derivatives are `deriv` of sections. The equilibrium predicates require $C^2$ regularity of the surplus, since `deriv` returns $0$ at non-differentiable points. The hypothesis $\sigma_y>0$ is added to the paper's standing assumptions: the map (21b) is invertible only if $\sigma_y\neq0$ (the paper's estimate is $\sigma_y=0.0179$). The vacancy-filling rate $q$ is an arbitrary function and the job-finding rate is $f(\theta)=\theta q(\theta)$. Equation (22) is not derived; its value is used as the shift. Probability measures, Brownian motion, Girsanov's theorem and the Feynman–Kac representation are not formalized.
-- source:
--   Mitra, Seo & Xu, High Discounts and Low Fundamental Surplus, FRB Atlanta Working Paper 2021-22 (Sept. 2021), pp. 5–15 (PDF 6–16), §2, §3, (1), (5), (8), (9), (12), (15), (16), (19)–(23), (27), Table 1

import Mathlib

namespace RiskPremiaDMP.Equivalence

/-- First partial derivative `∂₁F(y, m)` (in the first argument). -/
noncomputable def d1 (F : ℝ → ℝ → ℝ) (y m : ℝ) : ℝ := deriv (fun y' => F y' m) y

/-- Second partial derivative `∂₁₁F(y, m)` (twice in the first argument). -/
noncomputable def d11 (F : ℝ → ℝ → ℝ) (y m : ℝ) : ℝ :=
  deriv (fun y' => deriv (fun y'' => F y'' m) y') y

/-- First partial derivative `∂₂F(y, m)` (in the second argument). -/
noncomputable def d2 (F : ℝ → ℝ → ℝ) (y m : ℝ) : ℝ := deriv (fun m' => F y m') m

/-- Second partial derivative `∂₂₂F(y, m)` (twice in the second argument). -/
noncomputable def d22 (F : ℝ → ℝ → ℝ) (y m : ℝ) : ℝ :=
  deriv (fun m' => deriv (fun m'' => F y m'') m') m

/-- The generator `𝓛^𝒫[κy, σy, κμ, σμ]` of (5):
`κy(μ − y)∂₁F + ½σy²∂₁₁F − κμ μ ∂₂F + ½σμ²∂₂₂F`. -/
noncomputable def genP (κy σy κμ σμ : ℝ) (F : ℝ → ℝ → ℝ) (y μ : ℝ) : ℝ :=
  κy * (μ - y) * d1 F y μ + 1 / 2 * σy ^ 2 * d11 F y μ
    - κμ * μ * d2 F y μ + 1 / 2 * σμ ^ 2 * d22 F y μ

/-- The generator `𝓛^𝒬[κy, σy, κη, η̄, ση]` of (20):
`−(σy η + κy y)∂₁F + ½σy²∂₁₁F + κη(η̄ − η)∂₂F + ½ση²∂₂₂F`. -/
noncomputable def genQ (κy σy κη ηbar ση : ℝ) (F : ℝ → ℝ → ℝ) (y η : ℝ) : ℝ :=
  -(σy * η + κy * y) * d1 F y η + 1 / 2 * σy ^ 2 * d11 F y η
    + κη * (ηbar - η) * d2 F y η + 1 / 2 * ση ^ 2 * d22 F y η

/-- Parameters of the economy without risk premia (§2.1). -/
structure NoRPParams where
  rf : ℝ
  s : ℝ
  β : ℝ
  c : ℝ
  z : ℝ
  κy : ℝ
  σy : ℝ
  κμ : ℝ
  σμ : ℝ

/-- Standing assumptions of §2.1: `κy > 0`, `κμ ≥ 0`, `σμ ≥ 0`, `β ∈ (0, 1)`. -/
def NoRPParams.Standing (E : NoRPParams) : Prop :=
  0 < E.κy ∧ 0 ≤ E.κμ ∧ 0 ≤ E.σμ ∧ 0 < E.β ∧ E.β < 1

/-- Parameters of the economy with risk premia (§2.2). -/
structure RPParams where
  rf : ℝ
  s : ℝ
  β : ℝ
  c : ℝ
  z : ℝ
  κy : ℝ
  σy : ℝ
  κη : ℝ
  ηbar : ℝ
  ση : ℝ

/-- Standing assumptions of §2.2: `κy > 0`, `κη > 0`, `ση > 0`, `β ∈ (0, 1)`, and the added
`σy > 0` (the map (21b) is invertible only if `σy ≠ 0`). -/
def RPParams.Standing (P : RPParams) : Prop :=
  0 < P.κy ∧ 0 < P.σy ∧ 0 < P.κη ∧ 0 < P.ση ∧ 0 < P.β ∧ P.β < 1

/-- Equilibrium (8) of an economy without risk premia, with vacancy-filling rate `q`:
a C² surplus `S` and a tightness `θ` solving (8a)–(8b) at every state `(y, μ)`. -/
def IsEquilibriumNoRP (E : NoRPParams) (q : ℝ → ℝ) (S θ : ℝ → ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 (Function.uncurry S) ∧ ∀ y μ : ℝ,
    (E.rf + E.s) * S y μ
        = Real.exp y - E.z - E.β * E.c / (1 - E.β) * θ y μ + genP E.κy E.σy E.κμ E.σμ S y μ ∧
      E.c = (1 - E.β) * q (θ y μ) * S y μ

/-- Equilibrium (19) of the economy with risk premia, with vacancy-filling rate `q`:
a C² surplus `S` and a tightness `θ` solving (19a)–(19b) at every state `(y, η)`. -/
def IsEquilibriumRP (P : RPParams) (q : ℝ → ℝ) (S θ : ℝ → ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 (Function.uncurry S) ∧ ∀ y η : ℝ,
    (P.rf + P.s) * S y η
        = Real.exp y - P.z - P.β * P.c / (1 - P.β) * θ y η + genQ P.κy P.σy P.κη P.ηbar P.ση S y η ∧
      P.c = (1 - P.β) * q (θ y η) * S y η

/-- The shift `σy η̄ / κy`, the value of `−E^𝒬[y_t]` given by (22). -/
noncomputable def shift (P : RPParams) : ℝ := P.σy * P.ηbar / P.κy

/-- (21a): `y^𝒬 = y − E^𝒬[y_t] = y + σy η̄ / κy`. -/
noncomputable def toYQ (P : RPParams) (y : ℝ) : ℝ := y + shift P

/-- (21b): `μ^𝒬 = σy (η̄ − η) / κy`. -/
noncomputable def toMuQ (P : RPParams) (η : ℝ) : ℝ := P.σy * (P.ηbar - η) / P.κy

/-- The artificial economy without risk premia: (23) `z^𝒬 = e^{σy η̄/κy} z`,
`c^𝒬 = e^{σy η̄/κy} c`; (27) `κ^𝒬_y = κy`, `σ^𝒬_y = σy`, `κ^𝒬_μ = κη`, `σ^𝒬_μ = ση σy / κy`;
`rf`, `s`, `β` unchanged. -/
noncomputable def artificial (P : RPParams) : NoRPParams where
  rf := P.rf
  s := P.s
  β := P.β
  c := Real.exp (shift P) * P.c
  z := Real.exp (shift P) * P.z
  κy := P.κy
  σy := P.σy
  κμ := P.κη
  σμ := P.ση * P.σy / P.κy

/-- (1) in integral form along paths: for `t ≥ 0`,
`y_t = y_0 + ∫₀ᵗ κy(μ_u − y_u) du + σy (B^y_t − B^y_0)` and
`μ_t = μ_0 − ∫₀ᵗ κμ μ_u du + σμ (B^μ_t − B^μ_0)`. -/
def SolvesProductivity (E : NoRPParams) (y μ By Bμ : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t →
    y t = y 0 + (∫ u in (0 : ℝ)..t, E.κy * (μ u - y u)) + E.σy * (By t - By 0)) ∧
  (∀ t : ℝ, 0 ≤ t →
    μ t = μ 0 + (∫ u in (0 : ℝ)..t, -(E.κμ * μ u)) + E.σμ * (Bμ t - Bμ 0))

/-- (9) in integral form: `y_t = y_0 − ∫₀ᵗ κy y_u du + σy (B^{y,𝒫}_t − B^{y,𝒫}_0)` for `t ≥ 0`. -/
def SolvesPhysicalY (P : RPParams) (y BP : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    y t = y 0 + (∫ u in (0 : ℝ)..t, -(P.κy * y u)) + P.σy * (BP t - BP 0)

/-- (12) in integral form:
`η_t = η_0 + ∫₀ᵗ κη(η̄ − η_u) du + ση (B^{η,𝒫}_t − B^{η,𝒫}_0)` for `t ≥ 0`. -/
def SolvesMPR (P : RPParams) (η Bη : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    η t = η 0 + (∫ u in (0 : ℝ)..t, P.κη * (P.ηbar - η u)) + P.ση * (Bη t - Bη 0)

/-- (15) in integral form:
`y_t = y_0 + ∫₀ᵗ κy(−(σy/κy) η_u − y_u) du + σy (B^{y,𝒬}_t − B^{y,𝒬}_0)` for `t ≥ 0`. -/
def SolvesRiskNeutralY (P : RPParams) (y η BQ : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    y t = y 0 + (∫ u in (0 : ℝ)..t, P.κy * (-(P.σy / P.κy) * η u - y u))
      + P.σy * (BQ t - BQ 0)

/-- (16): `B^{y,𝒬}_t = ∫₀ᵗ η_u du + B^{y,𝒫}_t`. -/
noncomputable def riskNeutralBM (η BP : ℝ → ℝ) (t : ℝ) : ℝ := (∫ u in (0 : ℝ)..t, η u) + BP t

end RiskPremiaDMP.Equivalence


