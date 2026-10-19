-- Prove2me | Definitions.Def_OTCChain_Equilibrium_Model
-- name    : OTCChain_Equilibrium_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:21.893667+00:00
-- url     : https://prove2.me/theorems/aca6cd94-5ba4-494f-8369-85d969df6910
-- title:
--   §2, eqs. (1)–(19), Definition 1, pp. 6–13 — OTC search market with search cost: steady state, Bellman system, optimal cutoffs, intermediation equilibrium
-- statement:
--   The model of §2 of Shen, Wei and Yan, *Financial Intermediation Chains in an OTC Market*: a continuous-time over-the-counter market with search costs, in steady state.
--
--   **Data.** A continuum of investors of total mass $N$ trades an asset in supply $X$, with $0 < X < N$; each investor holds $0$ or $1$ unit. Investors meet trading partners at rate $\lambda$ times the partner population, discount at rate $r > 0$, pay a search cost $c \ge 0$ per unit of time while searching, and the buyer has bargaining power $\eta \in (0,1)$. An investor's type $\Delta \in [0,\bar\Delta]$ ($\bar\Delta > 0$) is redrawn at intensity $\kappa > 0$ from a probability density $f$ on $[0,\bar\Delta]$, with c.d.f. $F(\Delta) = \int_0^\Delta f$, and $\mathbf E[g(\Delta')] = \int_0^{\bar\Delta} g(x) f(x)\,dx$.
--
--   **Populations.** $\mu_b, \mu_s, \mu_n, \mu_h$ are the densities over types of buyers, sellers, inactive non-owners and inactive holders, with $N_b = \int_0^{\bar\Delta}\mu_b$ and $N_s = \int_0^{\bar\Delta}\mu_s$. For cutoffs $\Delta_b, \Delta_s$ they form a **steady state** if they are nonnegative and integrable on $[0,\bar\Delta]$ and
--
--   1. (12) $\mu_s + \mu_b + \mu_n + \mu_h = N f$ on $[0,\bar\Delta]$;
--   2. (13)–(14) on $(\Delta_s, \bar\Delta]$: $\mu_n = \mu_s = 0$ and $\kappa\mu_h = \kappa X f + \lambda N_s \mu_b$;
--   3. (15)–(16) on $[0, \Delta_b)$: $\mu_b = \mu_h = 0$ and $\kappa\mu_n = \kappa (N - X) f + \lambda N_b \mu_s$;
--   4. (17)–(18) on $(\Delta_b, \Delta_s)$: $\mu_n = \mu_h = 0$ and
--   $$\kappa\mu_s(\Delta) = \kappa X f(\Delta) - \lambda\mu_s(\Delta)\int_\Delta^{\bar\Delta}\mu_b(x)\,dx + \lambda\mu_b(\Delta)\int_0^\Delta \mu_s(x)\,dx;$$
--   5. (19) market clearing $\int_0^{\bar\Delta}(\mu_s + \mu_h) = X$.
--
--   **Values.** $V_h, V_s, V_n, V_b$ are the values of an inactive holder, a searching seller, an inactive non-owner and a searching buyer; $V(0,\Delta) = \max(V_n(\Delta), V_b(\Delta))$ (1), $V(1,\Delta) = \max(V_h(\Delta), V_s(\Delta))$ (2), the surplus of a meeting between a type-$x$ buyer and a type-$y$ seller is
--   $$S(x,y) = [V(1,x) + V(0,y)] - [V(0,x) + V(1,y)] \qquad (5)$$
--   and the price is $P(x,y) = V(1,x) - V(0,x) - \eta S(x,y)$ (6). The value functions solve the **Bellman system** (8)–(11) if they are bounded and measurable on $[0,\bar\Delta]$ and for every $\Delta \in [0,\bar\Delta]$
--   $$(\kappa+r)V_h(\Delta) = 1 + \Delta + \kappa\mathbf E[V(1,\Delta')],$$
--   $$(\kappa+r)V_s(\Delta) = 1 + \Delta - c + \lambda(1-\eta)\int_0^{\bar\Delta} S(x,\Delta)^+\mu_b(x)\,dx + \kappa\mathbf E[V(1,\Delta')],$$
--   $$(\kappa+r)V_n(\Delta) = \kappa\mathbf E[V(0,\Delta')],$$
--   $$(\kappa+r)V_b(\Delta) = -c + \lambda\eta\int_0^{\bar\Delta} S(\Delta,x)^+\mu_s(x)\,dx + \kappa\mathbf E[V(0,\Delta')].$$
--
--   **Optimality** of the decision rules (3)–(4) means $V_b \le V_n$ on $[0,\Delta_b)$, $V_n \le V_b$ on $(\Delta_b,\bar\Delta]$, $V_h \le V_s$ on $[0,\Delta_s)$ and $V_s \le V_h$ on $(\Delta_s,\bar\Delta]$.
--
--   **Definition 1.** A steady-state intermediation equilibrium is $(\Delta_b, \Delta_s, \mu, V)$ with $0 < \Delta_b < \Delta_s < \bar\Delta$, $\mu$ a steady state for these cutoffs, $V$ a solution of the Bellman system for $\mu$, and the rules (3)–(4) optimal under $V$; prices are then given by (6).
--
--   This is the object about which Theorem 1 asserts existence, uniqueness and closed forms.
--
--   **Formalization Note** Two printed slips are corrected: (9) is printed with $1 + y - c$ and (11) with $\mathbf E[\max\{V_b(\Delta), V_n\}]$; the derivation on p. 39 uses $1 + \Delta - c$ and $\mathbf E[\max\{V_b(\Delta'), V_n(\Delta')\}]$. Since a meeting trades iff the surplus is positive ((5)–(6)), the surplus enters (9) and (11) as $S^+ = \max(S,0)$ integrated over all partner types; under the paper's conjecture (7) this equals the printed $\int_\Delta^{\bar\Delta}$ and $\int_0^\Delta$, and (7) becomes a conclusion instead of an assumption. The Bellman equations are multiplied through by $\kappa + r > 0$. The positivity of $\kappa$ and $r$, nonnegativity and integrability of the densities and boundedness and measurability of the value functions are added so that the integrals are not Lean's junk value $0$. $\lambda$ is written `lam` and $\bar\Delta$ is `Δbar`.
-- source:
--   Shen, Wei & Yan, Financial Intermediation Chains in an OTC Market, MPRA Paper No. 74925 (version of October 29, 2016), pp. 6–13 (PDF 9–16), §2: model pp. 6–7, (1)–(4) p. 8–9, (5)–(11) p. 9 (PDF 12), (12)–(18) p. 12 (PDF 15), Definition 1 and (19) p. 13 (PDF 16); readings of (9), (11) from p. 39 (PDF 42)

import Mathlib

namespace OTCChain.Equilibrium

open MeasureTheory Set

/-- The primitive data of the OTC search market of Shen, Wei & Yan (§2, pp. 6–7): total investor
population `N`, asset supply `X`, meeting-rate constant `lam` (λ), type-change intensity `κ`,
bank (discount) rate `r`, buyer bargaining power `η`, search cost per unit of time `c`, upper end
`Δbar` (∆̄) of the type support `[0, ∆̄]`, and the type density `f` on `[0, ∆̄]`. -/
structure Params where
  N : ℝ
  X : ℝ
  lam : ℝ
  κ : ℝ
  r : ℝ
  η : ℝ
  c : ℝ
  Δbar : ℝ
  f : ℝ → ℝ

/-- The type c.d.f. `F(∆) = ∫₀^∆ f` (p. 7). -/
noncomputable def Params.F (M : Params) (Δ : ℝ) : ℝ := ∫ x in (0:ℝ)..Δ, M.f x

/-- The expectation `E[g(∆′)] = ∫₀^∆̄ g(x) f(x) dx` of a function of a fresh type draw `∆′ ∼ f`
(p. 9, below (11)). -/
noncomputable def Params.E (M : Params) (g : ℝ → ℝ) : ℝ := ∫ x in (0:ℝ)..M.Δbar, g x * M.f x

/-- Standing assumptions of §2 (pp. 6–9): `0 < X < N` (p. 6), `λ > 0` (p. 7), `κ > 0`, `r > 0`,
`η ∈ (0, 1)` (p. 9), `c ≥ 0` (p. 7), `∆̄ > 0`, and `f` a probability density on `[0, ∆̄]`
(nonnegative, integrable, total mass one). -/
def Params.Standing (M : Params) : Prop :=
  0 < M.X ∧ M.X < M.N ∧ 0 < M.lam ∧ 0 < M.κ ∧ 0 < M.r ∧ 0 < M.η ∧ M.η < 1 ∧ 0 ≤ M.c ∧
    0 < M.Δbar ∧ (∀ x ∈ Icc 0 M.Δbar, 0 ≤ M.f x) ∧ IntegrableOn M.f (Icc 0 M.Δbar) ∧
    ∫ x in (0:ℝ)..M.Δbar, M.f x = 1

/-- The densities over types of buyers `μb`, sellers `μs`, inactive non-owners `μn` and inactive
holders `μh` (p. 12). -/
structure Densities where
  μb : ℝ → ℝ
  μs : ℝ → ℝ
  μn : ℝ → ℝ
  μh : ℝ → ℝ

/-- The value functions (p. 8): `Vh` (inactive holder), `Vs` (searching seller), `Vn` (inactive
non-owner), `Vb` (searching buyer). -/
structure Values where
  Vh : ℝ → ℝ
  Vs : ℝ → ℝ
  Vn : ℝ → ℝ
  Vb : ℝ → ℝ

/-- Buyer population `N_b = ∫₀^∆̄ μb`. -/
noncomputable def Densities.Nb (M : Params) (μ : Densities) : ℝ := ∫ x in (0:ℝ)..M.Δbar, μ.μb x

/-- Seller population `N_s = ∫₀^∆̄ μs`. -/
noncomputable def Densities.Ns (M : Params) (μ : Densities) : ℝ := ∫ x in (0:ℝ)..M.Δbar, μ.μs x

/-- (1): `V(0, ∆) = max(Vn(∆), Vb(∆))`. -/
def Values.V0 (V : Values) (Δ : ℝ) : ℝ := max (V.Vn Δ) (V.Vb Δ)

/-- (2): `V(1, ∆) = max(Vh(∆), Vs(∆))`. -/
def Values.V1 (V : Values) (Δ : ℝ) : ℝ := max (V.Vh Δ) (V.Vs Δ)

/-- (5): the surplus when a type-`x` buyer meets a type-`y` seller,
`S(x, y) = [V(1, x) + V(0, y)] − [V(0, x) + V(1, y)]`. -/
def surplus (V : Values) (x y : ℝ) : ℝ := V.V1 x + V.V0 y - (V.V0 x + V.V1 y)

/-- (6): the negotiated price `P(x, y) = V(1, x) − V(0, x) − η S(x, y)` (it applies when
`S(x, y) > 0`, i.e. when the trade takes place). -/
def price (M : Params) (V : Values) (x y : ℝ) : ℝ := V.V1 x - V.V0 x - M.η * surplus V x y

/-- The steady state (12)–(19) for cutoffs `∆b`, `∆s` (pp. 12–13): the four densities are
nonnegative and integrable on `[0, ∆̄]`, and
* (12) `μs + μb + μn + μh = N f` on `[0, ∆̄]`;
* (13)–(14) on `(∆s, ∆̄]`: `μn = μs = 0`, `κ μh = κ X f + λ N_s μb`;
* (15)–(16) on `[0, ∆b)`: `μb = μh = 0`, `κ μn = κ (N − X) f + λ N_b μs`;
* (17)–(18) on `(∆b, ∆s)`: `μn = μh = 0`,
  `κ μs(∆) = κ X f(∆) − λ μs(∆) ∫_∆^∆̄ μb + λ μb(∆) ∫_0^∆ μs`;
* (19) market clearing `∫₀^∆̄ (μs + μh) = X`. -/
def IsSteadyState (M : Params) (Δb Δs : ℝ) (μ : Densities) : Prop :=
  (∀ x ∈ Icc 0 M.Δbar, 0 ≤ μ.μb x ∧ 0 ≤ μ.μs x ∧ 0 ≤ μ.μn x ∧ 0 ≤ μ.μh x) ∧
  IntegrableOn μ.μb (Icc 0 M.Δbar) ∧ IntegrableOn μ.μs (Icc 0 M.Δbar) ∧
  IntegrableOn μ.μn (Icc 0 M.Δbar) ∧ IntegrableOn μ.μh (Icc 0 M.Δbar) ∧
  (∀ Δ ∈ Icc 0 M.Δbar, μ.μs Δ + μ.μb Δ + μ.μn Δ + μ.μh Δ = M.N * M.f Δ) ∧
  (∀ Δ ∈ Ioc Δs M.Δbar, μ.μn Δ = 0 ∧ μ.μs Δ = 0 ∧
    M.κ * μ.μh Δ = M.κ * M.X * M.f Δ + M.lam * μ.Ns M * μ.μb Δ) ∧
  (∀ Δ ∈ Ico 0 Δb, μ.μb Δ = 0 ∧ μ.μh Δ = 0 ∧
    M.κ * μ.μn Δ = M.κ * (M.N - M.X) * M.f Δ + M.lam * μ.Nb M * μ.μs Δ) ∧
  (∀ Δ ∈ Ioo Δb Δs, μ.μn Δ = 0 ∧ μ.μh Δ = 0 ∧
    M.κ * μ.μs Δ = M.κ * M.X * M.f Δ - M.lam * μ.μs Δ * (∫ x in Δ..M.Δbar, μ.μb x)
      + M.lam * μ.μb Δ * (∫ x in (0:ℝ)..Δ, μ.μs x)) ∧
  (∫ x in (0:ℝ)..M.Δbar, (μ.μs x + μ.μh x)) = M.X

/-- The Bellman system (8)–(11) (p. 9), multiplied through by `κ + r`, for every `∆ ∈ [0, ∆̄]`,
with the four value functions bounded and a.e.-strongly measurable on `[0, ∆̄]`:
* (8)  `(κ + r) Vh(∆) = 1 + ∆ + κ E[V(1, ∆′)]`;
* (9)  `(κ + r) Vs(∆) = 1 + ∆ − c + λ(1 − η) ∫₀^∆̄ S(x, ∆)⁺ μb(x) dx + κ E[V(1, ∆′)]`;
* (10) `(κ + r) Vn(∆) = κ E[V(0, ∆′)]`;
* (11) `(κ + r) Vb(∆) = −c + λη ∫₀^∆̄ S(∆, x)⁺ μs(x) dx + κ E[V(0, ∆′)]`.
Corrected readings (disclosed): (9) is printed with `1 + y − c` and (11) with
`E[max{Vb(∆), Vn}]`; the derivation on p. 39 uses `1 + ∆ − c` and `E[max{Vb(∆′), Vn(∆′)}]`.
A meeting trades iff the surplus is positive ((5)–(6)), so the surplus enters as
`S⁺ = max(S, 0)` over all partner types; under (7) this is the printed `∫_∆^∆̄` / `∫_0^∆`. -/
def IsBellman (M : Params) (μ : Densities) (V : Values) : Prop :=
  (∃ B : ℝ, ∀ x ∈ Icc 0 M.Δbar,
    |V.Vh x| ≤ B ∧ |V.Vs x| ≤ B ∧ |V.Vn x| ≤ B ∧ |V.Vb x| ≤ B) ∧
  AEStronglyMeasurable V.Vh (volume.restrict (Icc 0 M.Δbar)) ∧
  AEStronglyMeasurable V.Vs (volume.restrict (Icc 0 M.Δbar)) ∧
  AEStronglyMeasurable V.Vn (volume.restrict (Icc 0 M.Δbar)) ∧
  AEStronglyMeasurable V.Vb (volume.restrict (Icc 0 M.Δbar)) ∧
  ∀ Δ ∈ Icc 0 M.Δbar,
    (M.κ + M.r) * V.Vh Δ = 1 + Δ + M.κ * M.E V.V1 ∧
    (M.κ + M.r) * V.Vs Δ = 1 + Δ - M.c
      + M.lam * (1 - M.η) * (∫ x in (0:ℝ)..M.Δbar, max (surplus V x Δ) 0 * μ.μb x)
      + M.κ * M.E V.V1 ∧
    (M.κ + M.r) * V.Vn Δ = M.κ * M.E V.V0 ∧
    (M.κ + M.r) * V.Vb Δ = -M.c
      + M.lam * M.η * (∫ x in (0:ℝ)..M.Δbar, max (surplus V Δ x) 0 * μ.μs x)
      + M.κ * M.E V.V0

/-- Optimality of the decision rules (3)–(4) given the value functions (pp. 8–9), via (1)–(2):
a non-owner stays out (`Vb ≤ Vn`) on `[0, ∆b)` and searches to buy (`Vn ≤ Vb`) on `(∆b, ∆̄]`;
an owner searches to sell (`Vh ≤ Vs`) on `[0, ∆s)` and stays out (`Vs ≤ Vh`) on `(∆s, ∆̄]`. -/
def IsOptimal (M : Params) (Δb Δs : ℝ) (V : Values) : Prop :=
  (∀ Δ ∈ Ico 0 Δb, V.Vb Δ ≤ V.Vn Δ) ∧ (∀ Δ ∈ Ioc Δb M.Δbar, V.Vn Δ ≤ V.Vb Δ) ∧
  (∀ Δ ∈ Ico 0 Δs, V.Vh Δ ≤ V.Vs Δ) ∧ (∀ Δ ∈ Ioc Δs M.Δbar, V.Vs Δ ≤ V.Vh Δ)

/-- Definition 1 (p. 13): a steady-state intermediation equilibrium consists of cutoffs
`0 < ∆b < ∆s < ∆̄`, densities `μ` satisfying (12)–(19), and value functions `V` solving
(8)–(11) under which the choices (3)–(4) are optimal. The prices are then given by (6)
(`price M V`). -/
def IsIntermEq (M : Params) (Δb Δs : ℝ) (μ : Densities) (V : Values) : Prop :=
  0 < Δb ∧ Δb < Δs ∧ Δs < M.Δbar ∧ IsSteadyState M Δb Δs μ ∧ IsBellman M μ V ∧
    IsOptimal M Δb Δs V

end OTCChain.Equilibrium


