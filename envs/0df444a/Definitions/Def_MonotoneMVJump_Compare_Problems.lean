-- Prove2me | Definitions.Def_MonotoneMVJump_Compare_Problems
-- name    : MonotoneMVJump_Compare_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:42.269251+00:00
-- url     : https://prove2.me/theorems/1c31cf5b-74e3-4855-a9cf-91fc9d803bf5
-- title:
--   §2–§4, pp. 5–7, 19–20 — wealth, admissible sets 𝒜 and ℬ, ℳ^t and Doléans-Dade measures, MV and MMV preferences, optimal values, Problems 1 and 3
-- statement:
--   This file defines the two portfolio problems and the preferences they compare.
--
--   **Wealth** ((6) = (28)). For a strategy $\pi$ (amount invested), the wealth on $[t,T]$ from $X_t=x$ is
--   $$\mathrm dX^\pi_s=\pi_s(\mu(Z_s)-r)\,\mathrm ds+\pi_s\sigma(Z_s)\,\mathrm dW^1_s+\pi_s\int_{\mathbb R}\gamma(Z_s,p)\,\tilde N(\mathrm ds,\mathrm dp).$$
--
--   **MV admissibility** (Definition 3): $\pi\in\mathcal B_{x,z,t}$ if $\pi$ is predictable and its wealth satisfies $\mathbb E[\sup_{t\le s\le T}|X^\pi_s|^2]<\infty$.
--
--   **Doléans-Dade measures** (pp. 5–6). $(\eta,\phi)=(\eta_1,\eta_2,\phi)\in\mathcal M^t$ if $\eta_1,\eta_2$ are predictable, $\phi_s(p)$ is predictable in $(s,\omega)$ and measurable in $p$, and the solution $\mathcal E$ of (5),
--   $$\mathrm d\mathcal E_s=\mathcal E_{s-}\Big[\eta_{1,s}\mathrm dW^1_s+\eta_{2,s}\mathrm dW^2_s+\int_{\mathbb R}\phi_s(p)\tilde N(\mathrm ds,\mathrm dp)\Big],\quad \mathcal E_t=1,$$
--   satisfies $\mathbb E[\mathcal E_T^2]<\infty$, $\mathbb E[\mathcal E_T]=1$, $\mathcal E_T\ge0$. Then $\mathbb Q^{\eta,\phi}=\mathcal E_T\cdot\mathbb P$, and the paper's $Y^{\eta,\phi}$ started at $y$ is $y\mathcal E$.
--
--   **MMV admissibility** (Definition 2): $\pi\in\mathcal A_{x,y,z,t}$ if $\pi$ is predictable and $\mathbb E^{\eta,\phi}[\sup_{t\le s\le T}|X^\pi_s|^2]<\infty$ for every $(\eta,\phi)\in\mathcal M^t$.
--
--   **Preferences.** For $\theta>0$:
--   1. MV: $U_\theta(X)=\mathbb E[X]-\frac\theta2\mathrm{Var}(X)$;
--   2. MMV over $\mathcal Q^t$: $V_\theta(X)=\inf_{(\eta,\phi)\in\mathcal M^t}\big\{\mathbb E^{\mathbb Q^{\eta,\phi}}[X]+\frac1{2\theta}(\mathbb E[\mathcal E_T^2]-1)\big\}$;
--   3. MMV over $\mathcal Q_0=\{\mathbb Q\ll\mathbb P:\mathbb E[(\mathrm d\mathbb Q/\mathrm d\mathbb P)^2]<\infty\}$: $V^0_\theta(X)=\inf_{\mathbb Q\in\mathcal Q_0}\big\{\mathbb E^{\mathbb Q}[X]+\frac1{2\theta}(\mathbb E[(\mathrm d\mathbb Q/\mathrm d\mathbb P)^2]-1)\big\}$.
--
--   **Optimal utilities.** From $(x,z,t)$:
--   $$\sup_{\pi\in\mathcal B_{x,z,t}}U_\theta(X^\pi_T),\qquad \sup_{\pi\in\mathcal A_{x,1/(2\theta),z,t}}V_\theta(X^\pi_T),\qquad \sup_{\pi\in\mathcal A_{x,1/(2\theta),z,t}}V^0_\theta(X^\pi_T).$$
--
--   **Problem 1** (7): $J^{\pi,\eta,\phi}(x,y,z,t)=\mathbb E^{\eta,\phi}[-X^\pi_T-Y^{\eta,\phi}_T]$ and $V(x,y,z,t)=\inf_{\pi\in\mathcal A}\sup_{(\eta,\phi)\in\mathcal M^t}J^{\pi,\eta,\phi}$. **Problem 3** (31): $J^\pi_D=\mathbb E[(X^\pi_T-D)^2]$ and $U_D(x,z,t)=\inf_{\pi\in\mathcal B}J^\pi_D$.
--
--   **Domain of monotonicity** (p. 27): $\mathcal G_\theta=\{f\in\mathcal L^2(\mathbb P): f-\mathbb E^{\mathbb P}[f]\le 1/\theta\ \text{a.s.}\}$.
--
--   **Formalization Note** Every infimum and supremum is taken in the extended reals. A strategy is paired with a wealth process $X$; since $X_T$ is a.s. determined by $\pi$, the values do not depend on the choice. "SDE (6) has a unique solution" is read as "the wealth exists". Because the Brownian integrals are $L^2$ Itô integrals, $\mathcal A$, $\mathcal B$ and $\mathcal M^t$ contain only strategies whose Brownian integrands lie in $L^2$; the strategies used in the paper all qualify. $\mathcal M^t$ is defined from the defining equation (5), not from formula (4). In $\mathcal M^t$ the printed "$\mathbb E[(Y_T)^2]\le+\infty$" is read as $<\infty$, and "$\mathbb E[Y_T]=1$" as $\mathbb E[Y_T/y]=1$, i.e. $\mathbb E[\mathcal E_T]=1$. The measures in $\mathcal Q_0$ are probability measures.
-- source:
--   Li, Liang & Pang, Comparison Between Mean-Variance and Monotone Mean-Variance Preferences Under Jump Diffusion and Stochastic Factor Model, arXiv:2211.14473v2, p. 5 (V_θ, 𝒬₀, 𝒬, ℳ), p. 6 ((5), ℳ^t, 𝒬^t), p. 7 ((6), Definition 2, Problem 1), p. 19 ((28), Definition 3, U_θ, Problem 2), p. 20 (Problem 3), p. 27 (𝒢_θ), p. 28 (V⁰_θ)

import Mathlib
import Definitions.Def_MonotoneMVJump_Compare_Market

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MonotoneMVJump.Compare

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

namespace Market

variable (M : Market Ω)

/-- `X = X^π` is the wealth (6) = (28) of the strategy `π` on `[t, T]` from `X_t = x`, along the
factor path `Z`:
`dX_s = π_s(μ(Z_s) − r) ds + π_s σ(Z_s) dW¹_s + π_s ∫_ℝ γ(Z_s, p) Ñ(ds, dp)`. -/
def IsWealth (t : ℝ≥0) (x : ℝ) (Z π X : ℝ≥0 → Ω → ℝ) : Prop :=
  M.IsJumpIto t x (fun u ω => π u ω * (M.μ (Z u ω) - M.r)) (fun u ω => π u ω * M.σ (Z u ω))
    (fun _ _ => 0) (fun u ω p => π u ω * M.γ (Z u ω) p) X

/-- `sup_{t ≤ s ≤ T} |X_s|²`, in `[0, ∞]`. -/
noncomputable def supSq (t : ℝ≥0) (X : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ (s : ℝ≥0) (_ : t ≤ s ∧ s ≤ M.T), ‖X s ω‖ₑ ^ 2

/-- Definition 3 (p. 19): `(π, X)` is an admissible pair for the MV problem from `(x, z, t)`
(`π ∈ ℬ_{x,z,t}` with wealth `X`): `π` is predictable, `X` is its wealth (28), and
`E_{x,z,t}[sup_{t≤s≤T} |X_s|²] < ∞`. -/
def AdmB (t : ℝ≥0) (x : ℝ) (Z π X : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyPredictable M.filt π ∧ M.IsWealth t x Z π X ∧ ∫⁻ ω, M.supSq t X ω ∂M.P < ⊤

/-- `Y` solves the Doléans-Dade equation (5) on `[t, T]` from `Y_t = y`:
`dY_s = Y_{s−}[η_{1,s} dW¹_s + η_{2,s} dW²_s + ∫_ℝ ϕ_s(p) Ñ(ds, dp)]`. -/
def SolvesDD (t : ℝ≥0) (y : ℝ) (η₁ η₂ : ℝ≥0 → Ω → ℝ) (ϕ : ℝ≥0 → Ω → ℝ → ℝ)
    (Y : ℝ≥0 → Ω → ℝ) : Prop :=
  M.IsJumpIto t y (fun _ _ => 0) (fun u ω => Y u ω * η₁ u ω) (fun u ω => Y u ω * η₂ u ω)
    (fun u ω p => Function.leftLim (fun v => Y v ω) u * ϕ u ω p) Y

/-- `(η, ϕ) ∈ ℳ^t` (p. 6) with stochastic exponential `ℰ`: `η₁, η₂` are predictable, `ϕ` is
measurable for (predictable σ-algebra) ⊗ (Borel sets of marks), `ℰ` solves (5) from `ℰ_t = 1`,
and `E[ℰ_T²] < ∞`, `E[ℰ_T] = 1`, `ℰ_T ≥ 0` a.s. (The solution of (5) from `y` is `y ℰ`.) -/
def InMt (t : ℝ≥0) (η₁ η₂ : ℝ≥0 → Ω → ℝ) (ϕ : ℝ≥0 → Ω → ℝ → ℝ) (E : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyPredictable M.filt η₁ ∧ IsStronglyPredictable M.filt η₂ ∧
    Measurable[MeasurableSpace.prod M.filt.predictable inferInstance]
      (fun q : (ℝ≥0 × Ω) × ℝ => ϕ q.1.1 q.1.2 q.2) ∧
    M.SolvesDD t 1 η₁ η₂ ϕ E ∧ ∫⁻ ω, ‖E M.T ω‖ₑ ^ 2 ∂M.P < ⊤ ∧
    ∫ ω, E M.T ω ∂M.P = 1 ∧ ∀ᵐ ω ∂M.P, 0 ≤ E M.T ω

/-- The Doléans-Dade measure `ℚ^{η,ϕ}` with `dℚ^{η,ϕ}/dℙ = ℰ_T`. -/
noncomputable def Qm (E : ℝ≥0 → Ω → ℝ) : Measure Ω :=
  M.P.withDensity fun ω => ENNReal.ofReal (E M.T ω)

/-- Definition 2 (p. 7): `(π, X)` is an admissible pair for the MMV problem (`π ∈ 𝒜_{x,y,z,t}`
with wealth `X`): `π` is predictable, `X` is its wealth (6), and
`E^{η,ϕ}[sup_{t≤s≤T} |X_s|²] < ∞` for every `(η, ϕ) ∈ ℳ^t`. -/
def AdmA (t : ℝ≥0) (x : ℝ) (Z π X : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyPredictable M.filt π ∧ M.IsWealth t x Z π X ∧
    ∀ (η₁ η₂ : ℝ≥0 → Ω → ℝ) (ϕ : ℝ≥0 → Ω → ℝ → ℝ) (E : ℝ≥0 → Ω → ℝ),
      M.InMt t η₁ η₂ ϕ E → ∫⁻ ω, M.supSq t X ω ∂(M.Qm E) < ⊤

/-- MV preference (p. 19): `U_θ(X) = E[X] − (θ/2) Var(X)` under `ℙ`. -/
noncomputable def mvU (θ : ℝ) (X : Ω → ℝ) : ℝ :=
  ∫ ω, X ω ∂M.P - θ / 2 * variance X M.P

/-- MMV preference over the Doléans-Dade measures `𝒬^t` (pp. 5–6):
`V^{𝒬^t}_θ(X) = inf_{(η,ϕ) ∈ ℳ^t} {E^{ℚ^{η,ϕ}}[X] + (1/(2θ))(E^ℙ[(dℚ^{η,ϕ}/dℙ)²] − 1)}`, in `EReal`. -/
noncomputable def mmvQt (t : ℝ≥0) (θ : ℝ) (X : Ω → ℝ) : EReal :=
  ⨅ (η₁ : ℝ≥0 → Ω → ℝ) (η₂ : ℝ≥0 → Ω → ℝ) (ϕ : ℝ≥0 → Ω → ℝ → ℝ) (E : ℝ≥0 → Ω → ℝ)
    (_ : M.InMt t η₁ η₂ ϕ E),
    (((∫ ω, X ω ∂M.Qm E) + 1 / (2 * θ) * ((∫ ω, E M.T ω ^ 2 ∂M.P) - 1) : ℝ) : EReal)

/-- MMV preference over `𝒬₀ = {ℚ ≪ ℙ : E^ℙ[(dℚ/dℙ)²] < ∞}` (p. 5, p. 28), `ℚ` ranging over
probability measures: `V⁰_θ(X) = inf_{ℚ ∈ 𝒬₀} {E^ℚ[X] + (1/(2θ))(E^ℙ[(dℚ/dℙ)²] − 1)}`, in
`EReal`. -/
noncomputable def mmvQ0 (θ : ℝ) (X : Ω → ℝ) : EReal :=
  ⨅ (Q : Measure Ω)
    (_ : IsProbabilityMeasure Q ∧ Q ≪ M.P ∧ ∫⁻ ω, Q.rnDeriv M.P ω ^ 2 ∂M.P < ⊤),
    (((∫ ω, X ω ∂Q) + 1 / (2 * θ) * ((∫⁻ ω, Q.rnDeriv M.P ω ^ 2 ∂M.P).toReal - 1) : ℝ) : EReal)

/-- The optimal MV utility from `(x, z, t)`: `sup_{π ∈ ℬ_{x,z,t}} U_θ(X^π_T)` (Problem 2, (29)),
in `EReal`. -/
noncomputable def mvValue (t : ℝ≥0) (θ x : ℝ) (Z : ℝ≥0 → Ω → ℝ) : EReal :=
  ⨆ (π : ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → ℝ) (_ : M.AdmB t x Z π X),
    ((M.mvU θ (X M.T) : ℝ) : EReal)

/-- The optimal MMV utility over `𝒬^t` from `(x, z, t)`:
`sup_{π ∈ 𝒜_{x,1/(2θ),z,t}} V^{𝒬^t}_θ(X^π_T)`, in `EReal`. -/
noncomputable def mmvValueQt (t : ℝ≥0) (θ x : ℝ) (Z : ℝ≥0 → Ω → ℝ) : EReal :=
  ⨆ (π : ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → ℝ) (_ : M.AdmA t x Z π X), M.mmvQt t θ (X M.T)

/-- The optimal MMV utility over `𝒬₀` from `(x, z, t)`:
`sup_{π ∈ 𝒜_{x,1/(2θ),z,t}} V⁰_θ(X^π_T)`, in `EReal`. -/
noncomputable def mmvValueQ0 (t : ℝ≥0) (θ x : ℝ) (Z : ℝ≥0 → Ω → ℝ) : EReal :=
  ⨆ (π : ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → ℝ) (_ : M.AdmA t x Z π X), M.mmvQ0 θ (X M.T)

/-- The objective of Problem 1 (p. 7): `J^{π,η,ϕ}(x, y, z, t) = E^{η,ϕ}[−X^π_T − Y^{η,ϕ}_T]` with
`Y^{η,ϕ} = y ℰ` and `ℚ^{η,ϕ} = ℰ_T · ℙ`. -/
noncomputable def J (y : ℝ) (X E : ℝ≥0 → Ω → ℝ) : ℝ :=
  ∫ ω, (-X M.T ω - y * E M.T ω) ∂M.Qm E

/-- The value of Problem 1 (7): `V(x, y, z, t) = inf_{π ∈ 𝒜} sup_{(η,ϕ) ∈ ℳ^t} J^{π,η,ϕ}`, in
`EReal`. -/
noncomputable def problem1Value (t : ℝ≥0) (x y : ℝ) (Z : ℝ≥0 → Ω → ℝ) : EReal :=
  ⨅ (π : ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → ℝ) (_ : M.AdmA t x Z π X),
    ⨆ (η₁ : ℝ≥0 → Ω → ℝ) (η₂ : ℝ≥0 → Ω → ℝ) (ϕ : ℝ≥0 → Ω → ℝ → ℝ) (E : ℝ≥0 → Ω → ℝ)
      (_ : M.InMt t η₁ η₂ ϕ E), ((M.J y X E : ℝ) : EReal)

/-- The objective of Problem 3 (p. 20): `J^π_D(x, z, t) = E[(X^π_T − D)²]` under `ℙ`. -/
noncomputable def JD (D : ℝ) (X : ℝ≥0 → Ω → ℝ) : ℝ :=
  ∫ ω, (X M.T ω - D) ^ 2 ∂M.P

/-- The value of Problem 3 (31): `U_D(x, z, t) = inf_{π ∈ ℬ_{x,z,t}} J^π_D(x, z, t)`, in
`EReal`. -/
noncomputable def problem3Value (t : ℝ≥0) (x D : ℝ) (Z : ℝ≥0 → Ω → ℝ) : EReal :=
  ⨅ (π : ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → ℝ) (_ : M.AdmB t x Z π X), ((M.JD D X : ℝ) : EReal)

end Market

/-- The domain of monotonicity of MV preferences (p. 27):
`𝒢_θ = {f ∈ ℒ²(ℙ) : f − E^ℙ[f] ≤ 1/θ ℙ-a.s.}`. -/
def InDomMono (P : Measure Ω) (θ : ℝ) (f : Ω → ℝ) : Prop :=
  MemLp f 2 P ∧ ∀ᵐ ω ∂P, f ω - ∫ ω', f ω' ∂P ≤ 1 / θ

end MonotoneMVJump.Compare


