-- Prove2me | Definitions.Def_CvitanicKaratzas92_Optimality_Problem
-- name    : CvitanicKaratzas92_Optimality_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T09:13:38.678469+00:00
-- url     : https://prove2.me/theorems/21616e5f-f7d3-4eee-b822-352f182d0324
-- title:
--   Sections 6–8 — $J$, $\mathcal A'(x)$, $V_0$, $V$, auxiliary markets $\mathcal M_\nu$, $\mathcal D'$, $\mathcal X_\nu$, $c_\nu$, $\xi_\nu$, $X_\nu$, $\tilde J$, standing assumptions
-- statement:
--   This definition collects the optimization problems of the paper on top of the market, the constraint set $K$ and the utilities $U_1,U_2$.
--
--   **The constrained problem** (Section 6). For $(\pi,c)\in\mathcal A_0(x)$ with wealth $X=X^{x,\pi,c}$,
--   $$J(x;\pi,c)=E\int_0^TU_1(t,c(t))\,dt+EU_2(X(T)). \tag{6.1}$$
--   $\mathcal A_0'(x)$ is the class of $(\pi,c)\in\mathcal A_0(x)$ with $E\int_0^TU_1^-(t,c(t))\,dt+EU_2^-(X(T))<\infty$ (6.2), and $V_0(x)=\sup_{(\pi,c)\in\mathcal A_0'(x)}J(x;\pi,c)$ (6.3). The constrained class is $\mathcal A'(x)=\{(\pi,c)\in\mathcal A_0'(x);\ \pi(t,\omega)\in K$ for $\ell\otimes P$-a.e. $(t,\omega)\}$ (6.4), with value $V(x)=\sup_{(\pi,c)\in\mathcal A'(x)}J(x;\pi,c)$ (6.5).
--
--   **The unconstrained solution** (Section 7). $\mathcal X_0(y)=E\big[\int_0^TH_0(t)I_1(t,yH_0(t))\,dt+H_0(T)I_2(yH_0(T))\big]$ (7.1); for $y=\mathcal Y_0(x)$, $\xi_0=I_2(yH_0(T))$ (7.2) and $c_0(t)=I_1(t,yH_0(t))$ (7.3).
--
--   **Auxiliary markets** (Section 8). $\mathcal H$ is the space of progressively measurable $\nu$ with $E\int_0^T\|\nu(t)\|^2dt<\infty$, and
--   $$\mathcal D=\Big\{\nu\in\mathcal H;\ E\int_0^T\delta(\nu(t))\,dt<\infty\Big\}. \tag{8.1}$$
--   For $\nu\in\mathcal D$ the market $\mathcal M_\nu$ has
--   $$\theta_\nu=\theta+\sigma^{-1}\nu,\quad \gamma_\nu(t)=\exp\Big[-\int_0^t\{r(s)+\delta(\nu(s))\}ds\Big],\quad Z_\nu(t)=\exp\Big[-\int_0^t\theta_\nu^*dW-\tfrac12\int_0^t\|\theta_\nu\|^2ds\Big],\quad H_\nu=\gamma_\nu Z_\nu \tag{8.5–8.8}$$
--   and wealth equation
--   $$dX_\nu=[\,rX_\nu-c\,]\,dt+X_\nu[\,\delta(\nu)+\pi^*\nu\,]\,dt+X_\nu\pi^*\sigma\,dW_0,\qquad X_\nu(0)=x. \tag{8.10}$$
--   $\mathcal A_\nu(x)$ is the class of pairs with $X_\nu^{x,\pi,c}(t)\ge0$ for all $t\le T$ a.s. (8.12); $\mathcal A_\nu'(x)$ adds the condition (6.2) with $X_\nu$; $V_\nu(x)=\sup_{\mathcal A_\nu'(x)}J(x;\pi,c)$ (8.13), $J$ evaluated with $X_\nu$. Further,
--   $$\mathcal X_\nu(y)=E\Big[\int_0^TH_\nu(t)I_1(t,yH_\nu(t))\,dt+H_\nu(T)I_2(yH_\nu(T))\Big],\quad 0<y<\infty, \tag{8.15}$$
--   $\mathcal D'=\{\nu\in\mathcal D;\ \mathcal X_\nu(y)<\infty\ \forall y\in(0,\infty)\}$ (8.16), and for $y=\mathcal Y_\nu(x)$ (the inverse of $\mathcal X_\nu$)
--   $$c_\nu(t)=I_1(t,yH_\nu(t)),\quad \xi_\nu=I_2(yH_\nu(T)),\quad X_\nu(t)=\frac1{H_\nu(t)}E\Big[\int_t^TH_\nu(s)c_\nu(s)\,ds+H_\nu(T)\xi_\nu\,\Big|\,\mathcal F_t\Big]. \tag{8.17–8.19}$$
--
--   **The dual functional** (12.1): $\tilde J(y;\nu)=E\big[\int_0^T\tilde U_1(t,yH_\nu(t))\,dt+\tilde U_2(yH_\nu(T))\big]$.
--
--   **Standing assumptions.** `Standing` bundles everything the paper assumes throughout: $P$ a complete probability measure; $T>0$; $W$ a standard Brownian motion with augmented filtration $\{\mathcal F_t\}$; $I$ an Itô-integral operator; (2.3)–(2.5), (2.7) and progressive measurability of $r,b,\sigma$; $K$ nonempty, closed, convex with (4.3)–(4.4); $U_1,U_2$ as in Section 6; and Assumption 6.2, $V_0(x)<\infty$ for all $x\in(0,\infty)$.
--
--   **Formalization Note** Expectations of utilities are extended reals: (positive parts) $-$ (negative parts), each a Lebesgue integral of a nonnegative function; this is the paper's value whenever the negative parts are finite, as on $\mathcal A_0'(x)$. A utility at $0$ is $U(0+)$. Classes are sets of triples $(\pi,c,X)$ with $X$ the wealth process. Suprema are taken in the extended reals. The paper prints (8.1) as "$\le\infty$"; this is read as "$<\infty$", the condition used in Remark 13.3, (A.36) and Section 16.2. $E\int\delta(\nu)\,dt$ is the expectation of the positive part, $\delta$ being bounded below by (4.4). In (8.6) and (8.10), $\delta(\nu)$ enters as a real number; for $\nu\in\mathcal D$ it is finite $\ell\otimes P$-a.e. $\mathcal Y_\nu(x)$ and $\mathcal Y_0(x)$ are not definitions: statements take a number $y>0$ with $\mathcal X_\nu(y)=x$. $X_\nu(t)$ uses Mathlib's conditional expectation, one version per $t$. Section 7's objects $H_0,\mathcal X_0$ are those of the original market, not of $\mathcal M_0$ (which agree only when $\delta(0)=0$).
-- source:
--   Cvitanić and Karatzas, Convex Duality in Constrained Portfolio Optimization, Ann. Appl. Probab. 2 (1992), pp. 773–778, (6.1)–(6.5), Assumption 6.2, (7.1)–(7.3), (8.1)–(8.19); p. 791, (12.1)

import Mathlib
import Definitions.Def_CvitanicKaratzas92_Optimality_Market
import Definitions.Def_CvitanicKaratzas92_Optimality_Utility

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CvitanicKaratzas92.Optimality

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
variable (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
  (W : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
  (I : (ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) → ℝ≥0 → Ω → ℝ)
  (M : Market Ω d) (K : Set (EuclideanSpace ℝ (Fin d)))
  (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ)

/-! ### Expected utility, the classes `𝒜₀'(x)`, `𝒜'(x)` and the values `V₀`, `V` (Section 6) -/

/-- `E∫₀ᵀ U₁⁺(t, c(t)) dt + E U₂⁺(ξ)`, with `U(0) := U(0+)` (see `uExt`). -/
noncomputable def utilPos (c : ℝ≥0 → Ω → ℝ) (ξ : Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ((∫⁻ s in Icc (0 : ℝ) T, (uExt (U1 s.toNNReal) (c s.toNNReal ω)).toENNReal) +
    (uExt U2 (ξ ω)).toENNReal) ∂P

/-- (6.2): `E∫₀ᵀ U₁⁻(t, c(t)) dt + E U₂⁻(ξ)`, with `U(0) := U(0+)` (see `uExt`). -/
noncomputable def utilNeg (c : ℝ≥0 → Ω → ℝ) (ξ : Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ((∫⁻ s in Icc (0 : ℝ) T, (-(uExt (U1 s.toNNReal) (c s.toNNReal ω))).toENNReal) +
    (-(uExt U2 (ξ ω))).toENNReal) ∂P

/-- `E[∫₀ᵀ U₁(t, c(t)) dt + U₂(ξ)]` in `[−∞, ∞]`, as (positive parts) − (negative parts); it is
the paper's expectation whenever the negative parts are finite. -/
noncomputable def expUtil (c : ℝ≥0 → Ω → ℝ) (ξ : Ω → ℝ) : EReal :=
  (utilPos P T U1 U2 c ξ : EReal) - (utilNeg P T U1 U2 c ξ : EReal)

/-- (6.1), p. 773: the total expected utility `J(x; π, c) = E∫₀ᵀ U₁(t, c(t)) dt + EU₂(X(T))` of a
triple `(π, c, X)`. -/
noncomputable def J (τ : Triple Ω d) : EReal :=
  expUtil P T U1 U2 τ.c (τ.X T)

/-- Definition 6.1 and (6.2), p. 773: `𝒜₀'(x)`, the triples of `𝒜₀(x)` with
`E∫₀ᵀ U₁⁻(t, c(t)) dt + EU₂⁻(X(T)) < ∞`. -/
def A0' (x : ℝ) : Set (Triple Ω d) :=
  {τ | τ ∈ A0 P 𝓕 T I M x ∧ utilNeg P T U1 U2 τ.c (τ.X T) < ⊤}

/-- Definition 6.3 and (6.4), p. 773: `𝒜'(x)`, the triples of `𝒜₀'(x)` with `π(t, ω) ∈ K` for
`ℓ ⊗ P`-a.e. `(t, ω)`. -/
def A' (x : ℝ) : Set (Triple Ω d) :=
  {τ | τ ∈ A0' P 𝓕 T I M U1 U2 x ∧ ∀ᵐ q ∂(lebP P T), τ.π q.1.toNNReal q.2 ∈ K}

/-- (6.3), p. 773: `V₀(x) = sup_{(π,c) ∈ 𝒜₀'(x)} J(x; π, c)`. -/
noncomputable def V0 (x : ℝ) : EReal :=
  ⨆ τ ∈ A0' P 𝓕 T I M U1 U2 x, J P T U1 U2 τ

/-- (6.5), p. 774: `V(x) = sup_{(π,c) ∈ 𝒜'(x)} J(x; π, c)`. -/
noncomputable def V (x : ℝ) : EReal :=
  ⨆ τ ∈ A' P 𝓕 T I M K U1 U2 x, J P T U1 U2 τ

/-! ### Section 7: the unconstrained problem in `𝓜` -/

/-- (7.1), p. 774: `𝒳₀(y) = E[∫₀ᵀ H₀(t) I₁(t, yH₀(t)) dt + H₀(T) I₂(yH₀(T))]`. -/
noncomputable def calX0 (y : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ((∫⁻ s in Icc (0 : ℝ) T, ENNReal.ofReal (H0 I M s.toNNReal ω *
      invMarginal (U1 s.toNNReal) (y * H0 I M s.toNNReal ω))) +
    ENNReal.ofReal (H0 I M T ω * invMarginal U2 (y * H0 I M T ω))) ∂P

/-- (7.3), p. 774: `c₀(t) = I₁(t, yH₀(t))`, with `y = 𝒴₀(x)` supplied by the caller. -/
noncomputable def c0 (y : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  invMarginal (U1 t) (y * H0 I M t ω)

/-- (7.2), p. 774: `ξ₀ = I₂(yH₀(T))`, with `y = 𝒴₀(x)` supplied by the caller. -/
noncomputable def xi0 (y : ℝ) (ω : Ω) : ℝ :=
  invMarginal U2 (y * H0 I M T ω)

/-! ### Section 8: the auxiliary markets `𝓜_ν` -/

/-- Section 8, p. 776: `ν ∈ ℋ` — progressively measurable with `E∫₀ᵀ ‖ν(t)‖² dt < ∞`. -/
def IsH (ν : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) : Prop :=
  IsStronglyProgressive 𝓕 ν ∧
    ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) T, ‖ν s.toNNReal ω‖ₑ ^ 2) ∂P < ∞

/-- (8.1), p. 776: `ν ∈ 𝒟` — `ν ∈ ℋ` and `E∫₀ᵀ δ(ν(t)) dt < ∞` (the positive part of `δ`, which is
bounded below by (4.4); the page prints `≤ ∞`, read as `< ∞`). -/
def IsD (ν : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) : Prop :=
  IsH P 𝓕 T ν ∧
    ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) T, (delta K (ν s.toNNReal ω)).toENNReal) ∂P < ∞

/-- (8.5), p. 777: `θ_ν(t) = θ(t) + σ⁻¹(t)ν(t)`. -/
noncomputable def thetaNu (ν : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (t : ℝ≥0) (ω : Ω) :
    EuclideanSpace ℝ (Fin d) :=
  theta M t ω + Matrix.toEuclideanLin (M.σ t ω)⁻¹ (ν t ω)

/-- (8.6), p. 777: `γ_ν(t) = exp(−∫₀ᵗ {r(s) + δ(ν(s))} ds)`. -/
noncomputable def gammaNu (ν : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (-∫ s in Icc (0 : ℝ) t, (M.r s.toNNReal ω + (delta K (ν s.toNNReal ω)).toReal))

/-- (8.7), p. 777: `Z_ν(t) = exp(−∫₀ᵗ θ_ν*(s) dW(s) − ½∫₀ᵗ ‖θ_ν(s)‖² ds)`. -/
noncomputable def ZNu (ν : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (-I (thetaNu M ν) t ω -
    (1 / 2) * ∫ s in Icc (0 : ℝ) t, ‖thetaNu M ν s.toNNReal ω‖ ^ 2)

/-- (8.8), p. 777: `H_ν(t) = γ_ν(t) Z_ν(t)`. -/
noncomputable def HNu (ν : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (t : ℝ≥0) (ω : Ω) : ℝ :=
  gammaNu M K ν t ω * ZNu I M ν t ω

/-- (8.10), p. 777: `X` is the wealth process of `(π, c)` from capital `x` in `𝓜_ν`:
`dX = [rX − c] dt + X[δ(ν) + π*ν] dt + Xπ*σ dW₀`, `X(0) = x`, in integral form with
`dW₀ = dW + θ dt`, both integrals existing. -/
def IsWealthNu (ν : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (x : ℝ)
    (π : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (c : ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ t, Measurable[𝓕 t] (X t)) ∧
  (∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Iic T)) ∧
  IsLocallySquareIntegrable 𝓕 P T (wealthIntegrand M π X) ∧
  (∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ =>
      M.r s.toNNReal ω * X s.toNNReal ω - c s.toNNReal ω +
        X s.toNNReal ω * ((delta K (ν s.toNNReal ω)).toReal +
          inner ℝ (π s.toNNReal ω) (ν s.toNNReal ω)) +
        X s.toNNReal ω * inner ℝ (Matrix.toEuclideanLin (M.σ s.toNNReal ω).transpose
          (π s.toNNReal ω)) (theta M s.toNNReal ω)) (Icc (0 : ℝ) T)) ∧
  ∀ t ≤ T, ∀ᵐ ω ∂P, X t ω = x +
    (∫ s in Icc (0 : ℝ) t,
      (M.r s.toNNReal ω * X s.toNNReal ω - c s.toNNReal ω +
        X s.toNNReal ω * ((delta K (ν s.toNNReal ω)).toReal +
          inner ℝ (π s.toNNReal ω) (ν s.toNNReal ω)) +
        X s.toNNReal ω * inner ℝ (Matrix.toEuclideanLin (M.σ s.toNNReal ω).transpose
          (π s.toNNReal ω)) (theta M s.toNNReal ω))) +
    I (wealthIntegrand M π X) t ω

/-- (8.12), p. 777: `𝒜_ν(x)` — portfolio, consumption, wealth in `𝓜_ν`, and `X_ν(t) ≥ 0` for all
`0 ≤ t ≤ T`, a.s. -/
def Anu (ν : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (x : ℝ) : Set (Triple Ω d) :=
  {τ | IsPortfolio 𝓕 P T τ.π ∧ IsConsumption 𝓕 P T τ.c ∧
    IsWealthNu P 𝓕 T I M K ν x τ.π τ.c τ.X ∧ ∀ᵐ ω ∂P, ∀ t ≤ T, 0 ≤ τ.X t ω}

/-- p. 777: `𝒜_ν'(x)` — the triples of `𝒜_ν(x)` with
`E∫₀ᵀ U₁⁻(t, c(t)) dt + EU₂⁻(X_ν(T)) < ∞`. -/
def Anu' (ν : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (x : ℝ) : Set (Triple Ω d) :=
  {τ | τ ∈ Anu P 𝓕 T I M K ν x ∧ utilNeg P T U1 U2 τ.c (τ.X T) < ⊤}

/-- (8.13), p. 777: `V_ν(x) = sup_{(π,c) ∈ 𝒜_ν'(x)} J(x; π, c)`, `J` computed with the wealth
`X_ν` of the triple. -/
noncomputable def Vnu (ν : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (x : ℝ) : EReal :=
  ⨆ τ ∈ Anu' P 𝓕 T I M K U1 U2 ν x, J P T U1 U2 τ

/-- (8.15), p. 778: `𝒳_ν(y) = E[∫₀ᵀ H_ν(t) I₁(t, yH_ν(t)) dt + H_ν(T) I₂(yH_ν(T))]`. -/
noncomputable def calX (ν : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (y : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ((∫⁻ s in Icc (0 : ℝ) T, ENNReal.ofReal (HNu I M K ν s.toNNReal ω *
      invMarginal (U1 s.toNNReal) (y * HNu I M K ν s.toNNReal ω))) +
    ENNReal.ofReal (HNu I M K ν T ω * invMarginal U2 (y * HNu I M K ν T ω))) ∂P

/-- (8.16), p. 778: `ν ∈ 𝒟'` — `ν ∈ 𝒟` and `𝒳_ν(y) < ∞` for every `y ∈ (0, ∞)`. -/
def IsD' (ν : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) : Prop :=
  IsD P 𝓕 T K ν ∧ ∀ y > 0, calX P T I M K U1 U2 ν y < ⊤

/-- (8.17), p. 778: `c_ν(t) = I₁(t, yH_ν(t))`, with `y = 𝒴_ν(x)` supplied by the caller. -/
noncomputable def cNu (ν : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (y : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  invMarginal (U1 t) (y * HNu I M K ν t ω)

/-- (8.18), p. 778: `ξ_ν = I₂(yH_ν(T))`, with `y = 𝒴_ν(x)` supplied by the caller. -/
noncomputable def xiNu (ν : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (y : ℝ) (ω : Ω) : ℝ :=
  invMarginal U2 (y * HNu I M K ν T ω)

/-- (8.19), p. 778: `X_ν(t) = (1/H_ν(t)) E[∫ₜᵀ H_ν(s)c_ν(s) ds + H_ν(T)ξ_ν | 𝓕_t]`. -/
noncomputable def XNu (ν : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (y : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  (1 / HNu I M K ν t ω) *
    condExp (𝓕 t) P (fun ω' =>
      (∫ s in Icc (t : ℝ) T, HNu I M K ν s.toNNReal ω' * cNu I M K U1 ν y s.toNNReal ω') +
        HNu I M K ν T ω' * xiNu T I M K U2 ν y ω') ω

/-! ### Section 12: the dual functional -/

/-- (12.1), p. 791: `J̃(y; ν) = E[∫₀ᵀ Ũ₁(t, yH_ν(t)) dt + Ũ₂(yH_ν(T))]` in `[−∞, ∞]`, as
(positive parts) − (negative parts). -/
noncomputable def Jtilde (y : ℝ) (ν : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) : EReal :=
  ((∫⁻ ω, ((∫⁻ s in Icc (0 : ℝ) T,
      ENNReal.ofReal (conj (U1 s.toNNReal) (y * HNu I M K ν s.toNNReal ω))) +
    ENNReal.ofReal (conj U2 (y * HNu I M K ν T ω))) ∂P : ℝ≥0∞) : EReal) -
  ((∫⁻ ω, ((∫⁻ s in Icc (0 : ℝ) T,
      ENNReal.ofReal (-conj (U1 s.toNNReal) (y * HNu I M K ν s.toNNReal ω))) +
    ENNReal.ofReal (-conj U2 (y * HNu I M K ν T ω))) ∂P : ℝ≥0∞) : EReal)

/-! ### Standing assumptions -/

/-- Every assumption the paper makes "throughout": a complete probability space (p. 769);
`0 < T`; `W` a standard `d`-dimensional Brownian motion and `𝓕` its augmented filtration
(p. 769); `I` an Itô-integral operator for `W`; the market assumptions (2.3)–(2.5), (2.7); `K`
nonempty, closed, convex with (4.3)–(4.4); `U₁, U₂` as in Section 6; Assumption 6.2,
`V₀(x) < ∞` for all `x > 0` (p. 774). -/
def Standing : Prop :=
  IsProbabilityMeasure P ∧ P.IsComplete ∧ 0 < T ∧
  EthierKurtz.IsStandardBrownian P W ∧ IsAugmentedBrownianFiltration P W 𝓕 ∧
  IsItoIntegralOperator P 𝓕 T W I ∧ Market.Standing P 𝓕 T M ∧ IsConstraintSet K ∧
  IsUtilityPair T U1 U2 ∧ ∀ x > 0, V0 P 𝓕 T I M U1 U2 x < ⊤

end CvitanicKaratzas92.Optimality


