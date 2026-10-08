-- Prove2me | Definitions.Def_TimeInconsLQ_MeanVariance_Market
-- name    : TimeInconsLQ_MeanVariance_Market
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T13:22:57.511111+00:00
-- url     : https://prove2.me/theorems/761e8603-b928-4ac0-9ae1-979c3f9bbbcd
-- title:
--   §5 — the complete market (5.2)–(5.3) as an LQ instance, Γ⁽¹⁾ and Γ, BMO martingales, the BSDEs (5.8) and (5.13), and the feedback (5.14)
-- statement:
--   This module defines the mean–variance problem of §5 of Hu, Jin and Zhou and the objects in its explicit equilibrium.
--
--   **The market.** A probability space with a standard $d$-dimensional Brownian motion $W$ and its filtration, a horizon $T>0$, an initial wealth $x_0\in\mathbb R$, a deterministic interest rate $r$ (measurable, bounded on $[0,T]$), a risk premium $\theta$ with values in $\mathbb R^d$, progressively measurable and essentially bounded on $[0,T]\times\Omega$ (it may be random), and weights $\mu_1\ge0$, $\mu_2\in\mathbb R$. The wealth under a strategy $u\in L^2_{\mathcal F}(0,T;\mathbb R^d)$ solves (5.2), $dX_s=r_sX_s\,ds+\theta_s'u_s\,ds+u_s'\,dW_s$, and the cost at time $t$ is (5.3)
--   $$J(t,x_t;u)=\tfrac12\mathrm{Var}_t(X_T)-(\mu_1x_t+\mu_2)E_t[X_T]=\tfrac12\big(E_t[X_T^2]-(E_t[X_T])^2\big)-(\mu_1x_t+\mu_2)E_t[X_T].$$
--   It is the instance $n=1$, $l=d$ of the LQ problem with $A=r$, $B=\theta$, $C^j=0$, $D^j=e_j'$, $b=\sigma^j=0$, $Q=R=0$, $G=h=1$; with these data the cost (2.3) is exactly (5.3).
--
--   **Deterministic functions** (p. 17): $\Gamma^{(1)}_t=\mu_1e^{\int_t^Tr_s\,ds}$ and $\Gamma_s=-\mu_2e^{\int_s^Tr_t\,dt}$.
--
--   **BMO** (p. 17). $Z\cdot W=\int_0^\cdot Z_s'\,dW_s$ is a *BMO martingale* if $Z\in L^2_{\mathcal F}(0,T;\mathbb R^d)$ and there is $C>0$ with $E\big[\int_\tau^T|Z_s|^2ds\,\big|\,\mathcal F_\tau\big]\le C$ for every stopping time $\tau\le T$.
--
--   **BSDE (5.8)**, for $(M,U)$ with values in $\mathbb R\times\mathbb R^d$:
--   $$dM_s=-\big(2r_sM_s-U_s'\theta_s+\Gamma^{(1)}_s|\theta_s|^2-M_s^{-1}|U_s|^2+\Gamma^{(1)}_sM_s^{-1}U_s'\theta_s\big)ds+U_s'\,dW_s,\qquad M_T=1 .$$
--   Its *solution class* (Proposition 5.1) is $(M,U)\in L^\infty_{\mathcal F}(0,T;\mathbb R)\times L^2_{\mathcal F}(0,T;\mathbb R^d)$ with $M\ge c$ for some constant $c>0$.
--
--   **BSDE (5.13)**, given $(M,U)$, for $(\Gamma^{(2)},\gamma^{(2)})$:
--   $$d\Gamma^{(2)}_t=-\Big[r_t\Gamma^{(2)}_t-\Big(\theta_t+\frac{U_t}{M_t}\Big)'\gamma^{(2)}_t-\Big(|\theta_t|^2+\frac{U_t'\theta_t}{M_t}\Big)\Gamma_t\Big]dt+(\gamma^{(2)}_t)'\,dW_t,\qquad\Gamma^{(2)}_T=-\mu_2,$$
--   with solution class $L^\infty_{\mathcal F}(0,T;\mathbb R)\times L^2_{\mathcal F}(0,T;\mathbb R^d)$ (Proposition 5.2).
--
--   **Feedback** (5.14): $u^*_s=\alpha_sX^*_s+\beta_s$ with
--   $$\alpha_s=\frac{\Gamma^{(1)}_s\theta_s-U_s}{M_s},\qquad\beta_s=-\frac{\Gamma_s\theta_s+\gamma^{(2)}_s}{M_s},$$
--   and the process (5.7) $k(s;t)=X^*_sU_s+M_su^*_s+\gamma^{(2)}_s$ (with $N=M$, $V=U$, $\gamma^{(1)}=0$).
--
--   **Formalization Note.** The paper starts from prices with drift $\mu$, volatility $\sigma$ ($\sigma\sigma'\succeq\varepsilon I$) and sets $\theta=\sigma^{-1}(\mu-r\mathbf 1)$, $u=\sigma'\pi$; every bounded progressive $\theta$ arises this way ($\sigma=I$, $\mu=\theta+r\mathbf 1$), so $\theta$ is taken as the primitive, as the paper does from (5.2) on. The BSDEs use Peng's `SolvesBSDE` with sign convention $-dp=F\,ds-\sum K\,dW$ (so $F$ is the bracket and $K=U$), one-dimensional ($\iota=$ `Fin 1`). $|\cdot|$ is the Euclidean norm, written as $z\cdot z$. "$M\ge c$" and essential boundedness are $ds\otimes dP$-a.e. on $[0,T]\times\Omega$. The BMO bound on the conditional expectation is written in integrated form, $E[\mathbf 1_A\int_\tau^T|Z|^2]\le C\,P(A)$ for all $A\in\mathcal F_\tau$, with lower integrals, which avoids Lean's junk value for non-integrable conditional expectations. $M^{-1}$ is $0$ in Lean where $M=0$; on the solution class $M\ge c>0$ a.e., so the junk value never enters an integral.
-- source:
--   Hu, Jin, Zhou, Time-Inconsistent Stochastic Linear–Quadratic Control, arXiv:1111.0818v1, §5: (5.1)–(5.3) p. 15, (5.7) p. 16, Γ⁽¹⁾, Γ, BMO and (5.8) p. 17, (5.13) p. 19, (5.14) p. 20

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_TimeInconsLQ_MeanVariance_Model

namespace TimeInconsLQ.MeanVariance

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

/-- §5, (5.2)–(5.3): the complete market of the mean–variance problem. A probability space with a
standard `d`-dimensional Brownian motion `W`, horizon `T > 0`, initial wealth `x₀`, a deterministic
interest rate `r`, a (random) risk premium `θ ∈ ℝᵈ`, and the weights `μ₁`, `μ₂` of (5.3). -/
structure Market (Ω : Type*) [MeasurableSpace Ω] (d : ℕ) where
  P : Measure Ω
  W : ℝ≥0 → Ω → Fin d → ℝ
  hW : Peng1990.SMP.IsStdBrownian P W
  T : ℝ≥0
  hT : 0 < T
  x₀ : ℝ
  r : ℝ≥0 → ℝ
  θ : ℝ≥0 → Ω → Fin d → ℝ
  μ₁ : ℝ
  μ₂ : ℝ

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `L^∞_𝓕(0, T; ℝ)`: progressively measurable and essentially bounded on `[0, T] × Ω`. -/
def LInfF (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0) (φ : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive 𝓕 φ ∧ EssBddOn P T φ

/-- `M ≥ c`: `M(s, ω) ≥ c` for `ds ⊗ dP`-almost every `(s, ω) ∈ [0, T] × Ω`. -/
def GeOn (P : Measure Ω) (T : ℝ≥0) (φ : ℝ≥0 → Ω → ℝ) (c : ℝ) : Prop :=
  ∀ᵐ q ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod P), c ≤ φ q.1.toNNReal q.2

/-- p. 17 (Kazamaki): `Z · W = ∫₀^· Z′_s dW_s` is a BMO martingale on `[0, T]`: `Z` is in
`L²_𝓕(0, T; ℝᵈ)` and there is a constant `C > 0` with `E[∫_τ^T |Z_s|² ds | 𝓕_τ] ≤ C` a.s. for every
stopping time `τ ≤ T`, written in integrated form: `E[1_A ∫_τ^T |Z_s|² ds] ≤ C · P(A)` for every
`A ∈ 𝓕_τ` (lower integrals; `|·|` the Euclidean norm). -/
def IsBMO {d : ℕ} (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (Z : ℝ≥0 → Ω → Fin d → ℝ) : Prop :=
  Peng1990.SMP.L2F 𝓕 P T Z ∧
  ∃ C : ℝ, 0 < C ∧ ∀ (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime 𝓕 τ),
    (∀ ω, τ ω ≤ (T : WithTop ℝ≥0)) → ∀ A : Set Ω, MeasurableSet[hτ.measurableSpace] A →
      ∫⁻ ω in A, ∫⁻ s in Set.Icc (((τ ω).untopD T : ℝ≥0) : ℝ) T,
          ENNReal.ofReal (Z s.toNNReal ω ⬝ᵥ Z s.toNNReal ω) ∂volume ∂P
        ≤ ENNReal.ofReal C * P A

namespace Market

variable {d : ℕ} (mk : Market Ω d)

/-- The filtration: the natural filtration of `W`. -/
noncomputable def filt : Filtration ℝ≥0 mΩ := Peng1990.SMP.brownianFiltration mk.hW

/-- §5 standing assumptions: `P` is a probability measure; the interest rate `r` is a measurable
function of time, bounded on `[0, T]`; the risk premium `θ` is progressively measurable and
essentially bounded on `[0, T] × Ω` (each coordinate); and `μ₁ ≥ 0`. -/
structure Standing : Prop where
  prob : IsProbabilityMeasure mk.P
  r_meas : Measurable mk.r
  r_bdd : ∃ K : ℝ, ∀ s ≤ mk.T, |mk.r s| ≤ K
  θ_prog : IsStronglyProgressive mk.filt mk.θ
  θ_bdd : ∀ j, EssBddOn mk.P mk.T (fun s ω => mk.θ s ω j)
  μ₁_nonneg : 0 ≤ mk.μ₁

/-- The mean–variance problem as the special case `n = 1`, `l = d` of the LQ problem (2.1)–(2.3):
`A = r`, `B = θ` (so `B′u = θ′u`), `Cʲ = 0`, `Dʲ = e_jᵀ` (so `Σⱼ Dʲu dWʲ = u′dW`), `b = 0`,
`σʲ = 0`, `Q = 0`, `R = 0`, `G = h = 1`, `μ₁`, `μ₂`. Its cost (2.3) is (5.3):
`½ Var_t(X_T) − (μ₁ x_t + μ₂) E_t[X_T]`. -/
noncomputable def mvData : Data Ω 1 d d where
  P := mk.P
  W := mk.W
  hW := mk.hW
  T := mk.T
  hT := mk.hT
  x₀ := fun _ => mk.x₀
  A := fun s => Matrix.of fun _ _ => mk.r s
  B := fun s ω => Matrix.of fun i _ => mk.θ s ω i
  C := fun _ _ _ => 0
  D := fun j _ _ => Matrix.of fun _ i => if i = j then 1 else 0
  b := fun _ _ => 0
  σ := fun _ _ _ => 0
  Q := fun _ _ => 0
  R := fun _ _ => 0
  G := 1
  h := 1
  μ₁ := Matrix.of fun _ _ => mk.μ₁
  μ₂ := fun _ => mk.μ₂

/-- `Γ⁽¹⁾_t = μ₁ e^{∫ₜᵀ r_s ds}` (p. 17). -/
noncomputable def Gam1 (t : ℝ≥0) : ℝ :=
  mk.μ₁ * Real.exp (∫ s in (t : ℝ)..(mk.T : ℝ), mk.r s.toNNReal)

/-- `Γ_s = −μ₂ e^{∫ₛᵀ r_t dt}` (p. 17). -/
noncomputable def Gam (s : ℝ≥0) : ℝ :=
  -mk.μ₂ * Real.exp (∫ v in (s : ℝ)..(mk.T : ℝ), mk.r v.toNNReal)

/-- The driver of the BSDE (5.8), as a function of the unknowns `(M, U)`:
`2 r_s M − U′θ_s + Γ⁽¹⁾_s |θ_s|² − M⁻¹ |U|² + Γ⁽¹⁾_s M⁻¹ U′θ_s`. -/
noncomputable def driver58 (s : ℝ≥0) (ω : Ω) (y : ℝ) (z : Fin d → ℝ) : ℝ :=
  2 * mk.r s * y - z ⬝ᵥ mk.θ s ω + mk.Gam1 s * (mk.θ s ω ⬝ᵥ mk.θ s ω)
    - y⁻¹ * (z ⬝ᵥ z) + mk.Gam1 s * y⁻¹ * (z ⬝ᵥ mk.θ s ω)

/-- `(M, U)` solves the BSDE (5.8) on `[0, T]`:
`dM_s = −(2r_sM_s − U′_sθ_s + Γ⁽¹⁾_s|θ_s|² − M_s⁻¹|U_s|² + Γ⁽¹⁾_sM_s⁻¹U′_sθ_s) ds + U′_s dW_s`,
`M_T = 1` (in Peng's `SolvesBSDE`, so `M ∈ L²_𝓕`, `U ∈ L²_𝓕(0, T; ℝᵈ)`). -/
def IsSol58 (M : ℝ≥0 → Ω → ℝ) (U : ℝ≥0 → Ω → Fin d → ℝ) : Prop :=
  Peng1990.SMP.SolvesBSDE mk.filt mk.P mk.T mk.W (fun _ _ => (1 : ℝ))
    (fun s ω y z _ => mk.driver58 s ω (y 0) (fun j => z j 0))
    (fun s ω (_ : Fin 1) => M s ω) (fun j s ω _ => U s ω j)

/-- The solution class of Proposition 5.1: `(M, U)` solves (5.8),
`(M, U) ∈ L^∞_𝓕(0, T; ℝ) × L²_𝓕(0, T; ℝᵈ)`, and `M ≥ c` for some constant `c > 0`. -/
def Class58 (M : ℝ≥0 → Ω → ℝ) (U : ℝ≥0 → Ω → Fin d → ℝ) : Prop :=
  mk.IsSol58 M U ∧ LInfF mk.filt mk.P mk.T M ∧ Peng1990.SMP.L2F mk.filt mk.P mk.T U ∧
    ∃ c : ℝ, 0 < c ∧ GeOn mk.P mk.T M c

/-- The driver of the BSDE (5.13), given `(M, U)`, as a function of the unknowns `(Γ⁽²⁾, γ⁽²⁾)`:
`r_t Γ⁽²⁾ − (θ_t + U_t/M_t)′ γ⁽²⁾ − (|θ_t|² + U′_tθ_t/M_t) Γ_t`. -/
noncomputable def driver513 (M : ℝ≥0 → Ω → ℝ) (U : ℝ≥0 → Ω → Fin d → ℝ) (s : ℝ≥0) (ω : Ω)
    (y : ℝ) (z : Fin d → ℝ) : ℝ :=
  mk.r s * y - (mk.θ s ω + (M s ω)⁻¹ • U s ω) ⬝ᵥ z
    - (mk.θ s ω ⬝ᵥ mk.θ s ω + (U s ω ⬝ᵥ mk.θ s ω) / M s ω) * mk.Gam s

/-- `(Γ⁽²⁾, γ⁽²⁾)` solves the BSDE (5.13) on `[0, T]`:
`dΓ⁽²⁾_t = −[r_tΓ⁽²⁾_t − (θ_t + U_t/M_t)′γ⁽²⁾_t − (|θ_t|² + U′_tθ_t/M_t)Γ_t] dt + (γ⁽²⁾_t)′ dW_t`,
`Γ⁽²⁾_T = −μ₂`. -/
def IsSol513 (M : ℝ≥0 → Ω → ℝ) (U : ℝ≥0 → Ω → Fin d → ℝ) (Γ2 : ℝ≥0 → Ω → ℝ)
    (γ2 : ℝ≥0 → Ω → Fin d → ℝ) : Prop :=
  Peng1990.SMP.SolvesBSDE mk.filt mk.P mk.T mk.W (fun _ _ => -mk.μ₂)
    (fun s ω y z _ => mk.driver513 M U s ω (y 0) (fun j => z j 0))
    (fun s ω (_ : Fin 1) => Γ2 s ω) (fun j s ω _ => γ2 s ω j)

/-- The solution class of Proposition 5.2: `(Γ⁽²⁾, γ⁽²⁾)` solves (5.13) and
`(Γ⁽²⁾, γ⁽²⁾) ∈ L^∞_𝓕(0, T; ℝ) × L²_𝓕(0, T; ℝᵈ)`. -/
def Class513 (M : ℝ≥0 → Ω → ℝ) (U : ℝ≥0 → Ω → Fin d → ℝ) (Γ2 : ℝ≥0 → Ω → ℝ)
    (γ2 : ℝ≥0 → Ω → Fin d → ℝ) : Prop :=
  mk.IsSol513 M U Γ2 γ2 ∧ LInfF mk.filt mk.P mk.T Γ2 ∧ Peng1990.SMP.L2F mk.filt mk.P mk.T γ2

/-- The feedback gain of (5.14): `α_s = (Γ⁽¹⁾_s θ_s − U_s) / M_s`. -/
noncomputable def alpha (M : ℝ≥0 → Ω → ℝ) (U : ℝ≥0 → Ω → Fin d → ℝ) : ℝ≥0 → Ω → Fin d → ℝ :=
  fun s ω => (M s ω)⁻¹ • (mk.Gam1 s • mk.θ s ω - U s ω)

/-- The feedback intercept of (5.14): `β_s = −(Γ_s θ_s + γ⁽²⁾_s) / M_s`. -/
noncomputable def beta (M : ℝ≥0 → Ω → ℝ) (γ2 : ℝ≥0 → Ω → Fin d → ℝ) : ℝ≥0 → Ω → Fin d → ℝ :=
  fun s ω => -((M s ω)⁻¹ • (mk.Gam s • mk.θ s ω + γ2 s ω))

/-- The feedback strategy (5.14) along a wealth process `X`: `u*_s = α_s X_s + β_s`. -/
noncomputable def uStar (M : ℝ≥0 → Ω → ℝ) (U : ℝ≥0 → Ω → Fin d → ℝ) (γ2 : ℝ≥0 → Ω → Fin d → ℝ)
    (X : ℝ≥0 → Ω → Fin 1 → ℝ) : ℝ≥0 → Ω → Fin d → ℝ :=
  fun s ω => X s ω 0 • mk.alpha M U s ω + mk.beta M γ2 s ω

/-- (5.7) with `N = M`, `V = U`, `γ⁽¹⁾ = 0`: `k(s; t) = X_s U_s + M_s u*_s + γ⁽²⁾_s`, written as the
family `(kʲ)_{j ≤ d}` of `ℝ¹`-valued processes used by the adjoint equation. -/
noncomputable def kStar (M : ℝ≥0 → Ω → ℝ) (U : ℝ≥0 → Ω → Fin d → ℝ) (γ2 : ℝ≥0 → Ω → Fin d → ℝ)
    (X : ℝ≥0 → Ω → Fin 1 → ℝ) : Fin d → ℝ≥0 → Ω → Fin 1 → ℝ :=
  fun j s ω _ => X s ω 0 * U s ω j + M s ω * mk.uStar M U γ2 X s ω j + γ2 s ω j

end Market

end TimeInconsLQ.MeanVariance


