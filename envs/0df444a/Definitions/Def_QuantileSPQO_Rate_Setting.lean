-- Prove2me | Definitions.Def_QuantileSPQO_Rate_Setting
-- name    : QuantileSPQO_Rate_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:07.831315+00:00
-- url     : https://prove2.me/theorems/4a957258-f1fc-4251-9faa-99782440dc92
-- title:
--   pp. 2–3, 9–13, 17 — black-box output law, cdf, density and quantile; Θ; Algorithm SPQO; assumptions A1–A3, B1–B3; step sizes; bias b_k
-- statement:
--   This file fixes the objects of Hu, Song and Fu's quantile optimization algorithm SPQO and the assumptions of its convergence analysis.
--
--   **Black box (pp. 2–3).** For every input $\theta\in\mathbb R^d$ the simulation output $Y(\theta)$ is a real random variable with law $\mu_\theta$, c.d.f. $F(y;\theta)=\mu_\theta((-\infty,y])$ and density $f(y;\theta)=\partial F(y;\theta)/\partial y$. A level $\varphi\in(0,1)$ is fixed, and $q(\theta)$ is the $\varphi$-quantile: $F(q(\theta);\theta)=\varphi$ for every $\theta$, and on $\Theta$ it is the unique solution $q$ of $F(q;\theta)=\varphi$. We write $\nabla_\theta F(y;\theta)$ for the gradient in $\theta$.
--
--   **Parameter set (p. 11).** $\Theta\subseteq\mathbb R^d$ is a nonempty compact convex set of the form $\Theta=\{\theta: h_j(\theta)\le 0,\ j=1,\dots,m\}$ with $h_j$ continuously differentiable and $\nabla h_j(\theta)\ne0$ whenever $h_j(\theta)=0$. $\Pi_\Theta$ is the Euclidean projection onto $\Theta$.
--
--   **Algorithm SPQO (p. 10).** With step sizes $\alpha_k,\beta_k,\gamma_k$, perturbation sizes $c_k$, $M_k=\max\{1,\|D_k\|/\sqrt d\}$ and $\bar c_k=c_k/M_k$,
--   $$
--   \begin{aligned}
--   q_{k+1}&=\Pi_I\big(q_k+\gamma_k(\varphi-I\{Y(\theta_k)\le q_k\})\big),\\
--   D_{k+1,i}&=D_{k,i}+\beta_k\,\frac{-I\{Y(\theta_k+\bar c_k\Delta_k)\le q_k+\bar c_kD_k^T\Delta_k\}+I\{Y(\theta_k-\bar c_k\Delta_k)\le q_k-\bar c_kD_k^T\Delta_k\}}{2\bar c_k\Delta_{k,i}},\\
--   \theta_{k+1}&=\Pi_\Theta(\theta_k-\alpha_kD_k),
--   \end{aligned}
--   $$
--   where $\Pi_I$ is the projection onto a nonempty closed interval $I\supseteq q(\Theta)$ (with $I=\mathbb R$ this is the paper's (20) verbatim). A *run* lives on a probability space $(\Omega,P)$ with a filtration $(\mathcal F_k)$: the initial values $\theta_0\in\Theta$, $q_0\in I$, $D_0$ are deterministic, $\theta_k,q_k,D_k$ are $\mathcal F_k$-measurable, $\Delta_k$ and the three outputs drawn at step $k$ are $\mathcal F_{k+1}$-measurable; given $\mathcal F_k$ the output $Y(\theta_k)$ has law $\mu_{\theta_k}$, and given $\mathcal F_k$ and $\Delta_k$ the outputs $Y(\theta_k\pm\bar c_k\Delta_k)$ have laws $\mu_{\theta_k\pm\bar c_k\Delta_k}$.
--
--   **Assumptions.**
--   1. **A1** (p. 12): there are $\delta>0$, $K$ and $\epsilon>0$, independent of $k$ and $\omega$, such that almost surely, for all $k$, on the ball of radius $\delta$ about $(q_k,\theta_k)$ the c.d.f. $F$ is three times continuously differentiable in $(y,\theta)$ with first and third derivatives bounded by $K$, and $f\ge\epsilon$.
--   2. **A2** (p. 12): each $\Delta_k$ has i.i.d. components with $P(\Delta_{k,i}=\pm1)=1/2$ and is independent of $\mathcal F_k$.
--   3. **A3** (pp. 12–13): (a) $\beta_k,c_k>0$, $c_k\to0$, $\sum\beta_k=\infty$, $\sum\beta_k^2/c_k^2<\infty$; (b) $\gamma_k>0$, $\sum\gamma_k=\infty$; (c) $\alpha_k>0$, $\sum\alpha_k=\infty$; (d) $\alpha_k=o(\gamma_k)$, $\gamma_k=o(\beta_k)$.
--   4. **Section 4 step sizes** (p. 17): $\alpha_k=a/(k+1)^{\alpha}$, $\beta_k=b/(k+1)^{\beta}$, $\gamma_k=r/(k+1)^{\gamma}$, $c_k=c/(k+1)^{\tau}$ with $a,b,r,c>0$ and $\alpha,\beta,\gamma,\tau\in(0,1)$.
--   5. **B1** (p. 17): constants $\varepsilon,C_f>0$ such that almost surely, for all $k$, $\varepsilon\le f(y;\theta_k)\le C_f$ for every $y$ between $q_k$ and $q(\theta_k)$.
--   6. **B2** (p. 17): $f$ is jointly continuous on $\mathbb R\times\Theta$, and there are $L_f,L_F>0$ with $|f(y_1;\theta)-f(y_2;\theta)|\le L_f|y_1-y_2|$ and $\|\nabla_\theta F(y_1;\theta)-\nabla_\theta F(y_2;\theta)\|\le L_F|y_1-y_2|$ for all $\theta\in\Theta$.
--   7. **B3** (p. 17): with $H(\theta)=\nabla^2_\theta q(\theta)$, a constant $\varrho>0$ such that almost surely, for all $k$ and all $\theta$ on the segment $[\theta_k,\theta^*]$, $v^TH(\theta)v\ge\varrho\|v\|^2$ for every $v$.
--
--   **Bias (Lemma 2, pp. 13–14).** For $q\in\mathbb R$ and $D,\theta\in\mathbb R^d$, with $M=\max\{1,\|D\|/\sqrt d\}$ and $\bar c=c_k/M$,
--   $$
--   b_k(q,D,\theta)=\frac{M}{2c_k}\cdot\frac1{2^d}\sum_{s\in\{\pm1\}^d}\Big(-F(q+\bar c\,D^Ts;\theta+\bar c s)+F(q-\bar c\,D^Ts;\theta-\bar c s)\Big)s+f(q;\theta)D+\nabla_\theta F(q;\theta).
--   $$
--
--   These are the hypotheses and quantities of Lemmas 1–5 and Theorems 1 and 3.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`. The black box is a family of laws `law : E d → Measure ℝ` rather than a family of random variables. The paper's $(20)$ is generalized by the truncation the paper itself recommends on p. 13 (D1): with $I=\mathbb R$ and $\Pi_I=\mathrm{id}$ the printed recursion is recovered, while without truncation no run can satisfy A1(b) or B1 (the iterate $q_k$ reaches every level with positive probability, and a density cannot exceed $\epsilon>0$ on all of $\mathbb R$). The filtration is general (the paper's $\mathcal F_k=\sigma\{D_0,q_0,\theta_0,\dots,D_k,q_k,\theta_k\}$ is too small to make $\Delta_k$ measurable; the full history of the run is an instance). The sampling model fixes only the conditional laws of the three outputs (D4), so independent sampling and common random numbers are both included; $\theta_0\in\Theta$ is assumed (D5). A1 adds the bound on first derivatives that the proofs use (pp. 35, 38) (D3); "for almost all $(q_k,\theta_k)$ pairs" is read as "almost surely, for all $k$" with deterministic radius and constants. The Section 4 step sizes use $k+1$ instead of $k$ because Lean indexes from $0$ (D2). B2's joint continuity is required on $\mathbb R\times\Theta$ (D7). B3 is stated as a quadratic-form bound, which for the symmetric Hessian of a $C^2$ function is equivalent to "smallest eigenvalue $\ge\varrho$" (Rayleigh–Ritz). The Hessian is the derivative of the gradient. The bias $b_k$ is defined as the explicit average over the $2^d$ sign vectors, which under A2 and the sampling model equals the paper's conditional expectation almost surely (using $1/\Delta_k=\Delta_k$, p. 14); no conditional expectation of a possibly non-integrable quantity appears.
-- source:
--   Hu, Song and Fu, Quantile Optimization via Multiple Timescale Local Search for Black-box Functions, arXiv:2308.07607v1, pp. 2–3 (problem (1)), p. 10 (Algorithm SPQO, (20)–(22)), p. 11 (setting, Θ, I_k^±), pp. 12–13 (A1–A3), p. 13 (Lemma 2, bias b_k), p. 17 (step sizes, B1–B3)

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto

namespace QuantileSPQO.Rate

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace ENNReal

/-- The parameter space `ℜ^d` with the Euclidean norm (p. 11). -/
abbrev E (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-! ### The parameter set Θ (p. 11) -/

/-- `Θ` is a nonempty compact convex set of the form `{θ : h_j(θ) ≤ 0, j = 1, …, m}` with each `h_j`
continuously differentiable and `∇h_j(θ) ≠ 0` whenever `h_j(θ) = 0` (arXiv:2308.07607v1, p. 11). -/
structure IsConstraintSet {d : ℕ} (Θ : Set (E d)) : Prop where
  isCompact : IsCompact Θ
  convex : Convex ℝ Θ
  nonempty : Θ.Nonempty
  constraints : ∃ (m : ℕ) (h : Fin m → E d → ℝ), (∀ j, ContDiff ℝ 1 (h j)) ∧
    (∀ j θ, h j θ = 0 → gradient (h j) θ ≠ 0) ∧ Θ = {θ | ∀ j, h j θ ≤ 0}

/-- `Pq` is the projection of `ℝ` onto the nonempty closed interval `I` (the truncation of the quantile
recursion (20) recommended on p. 13; `I = Set.univ`, `Pq = id` is the untruncated recursion). -/
structure IsIntervalProj (I : Set ℝ) (Pq : ℝ → ℝ) : Prop where
  isClosed : IsClosed I
  ordConnected : I.OrdConnected
  nonempty : I.Nonempty
  proj : ∀ x, Pq x ∈ I ∧ ∀ y ∈ I, |x - Pq x| ≤ |x - y|

/-! ### The black box (pp. 2–3) -/

/-- The black-box output: `law θ` is the law of the output `Y(θ)` at input `θ ∈ ℜ^d`, `dens y θ` is its
density `f(y;θ)`, `φ ∈ (0,1)` is the quantile level and `qf θ` is the `φ`-quantile `q(θ)`. -/
structure Model (d : ℕ) where
  law : E d → Measure ℝ
  dens : ℝ → E d → ℝ
  φ : ℝ
  qf : E d → ℝ

/-- The c.d.f. `F(y;θ) = P(Y(θ) ≤ y)`. -/
noncomputable def cdf {d : ℕ} (M : Model d) (y : ℝ) (θ : E d) : ℝ :=
  (M.law θ (Set.Iic y)).toReal

/-- The c.d.f. as a function of the pair `(y, θ)`. -/
noncomputable def cdfU {d : ℕ} (M : Model d) (p : ℝ × E d) : ℝ := cdf M p.1 p.2

/-- `∇_θ F(y;θ)`. -/
noncomputable def gradθ {d : ℕ} (M : Model d) (y : ℝ) (θ : E d) : E d :=
  gradient (fun θ' => cdf M y θ') θ

/-- The standing assumptions on the black box (pp. 2–3, 8): every `Y(θ)` has a probability law, the
c.d.f. has the density `f = ∂F/∂y`, `φ ∈ (0,1)`, `qf θ` is a `φ`-quantile of `Y(θ)` for every `θ`,
and on `Θ` it is the unique solution `q` of `F(q;θ) = φ`. -/
structure IsQuantileModel {d : ℕ} (M : Model d) (Θ : Set (E d)) : Prop where
  isProb : ∀ θ, IsProbabilityMeasure (M.law θ)
  hasDens : ∀ y θ, HasDerivAt (fun y' => cdf M y' θ) (M.dens y θ) y
  φ_pos : 0 < M.φ
  φ_lt_one : M.φ < 1
  quantile : ∀ θ, cdf M (M.qf θ) θ = M.φ
  quantile_unique : ∀ θ ∈ Θ, ∀ y, cdf M y θ = M.φ → y = M.qf θ

/-! ### Random directions (A2) -/

/-- The law on `ℜ^d` of a vector with i.i.d. components uniform on `{−1, 1}`. -/
noncomputable def rademacher (d : ℕ) : Measure (E d) :=
  (Measure.pi fun _ : Fin d => (2⁻¹ : ℝ≥0∞) • (Measure.dirac (1 : ℝ) + Measure.dirac (-1 : ℝ))).map
    (WithLp.toLp 2)

/-- The sign vector with entries `+1` where `b` is `true` and `−1` where `b` is `false`. -/
def signVec {d : ℕ} (b : Fin d → Bool) : E d :=
  WithLp.toLp 2 (fun i => if b i then (1 : ℝ) else -1)

/-! ### Algorithm SPQO (p. 10) -/

/-- `M_k = max{1, ‖D_k‖/√d}`. -/
noncomputable def mfac {d : ℕ} (D : E d) : ℝ := max 1 (‖D‖ / Real.sqrt d)

/-- The adaptive perturbation size `c̄_k = c_k / max{1, ‖D_k‖/√d}`. -/
noncomputable def cbar {d : ℕ} (c : ℕ → ℝ) (k : ℕ) (D : E d) : ℝ := c k / mfac D

/-- The sample paths of an SPQO run: iterates `θ_k, q_k, D_k`, directions `Δ_k`, and the three
outputs `Y(θ_k)`, `Y(θ_k + c̄_kΔ_k)`, `Y(θ_k − c̄_kΔ_k)` drawn at step `k`. -/
structure Run (Ω : Type*) (d : ℕ) where
  θ : ℕ → Ω → E d
  q : ℕ → Ω → ℝ
  D : ℕ → Ω → E d
  Δ : ℕ → Ω → E d
  Y0 : ℕ → Ω → ℝ
  Yp : ℕ → Ω → ℝ
  Ym : ℕ → Ω → ℝ

/-- `I_k^+ = I{Y(θ_k + c̄_kΔ_k) ≤ q_k + c̄_k D_k^T Δ_k}`. -/
noncomputable def Ip {Ω : Type*} {d : ℕ} (c : ℕ → ℝ) (R : Run Ω d) (k : ℕ) (ω : Ω) : ℝ :=
  if R.Yp k ω ≤ R.q k ω + cbar c k (R.D k ω) * ⟪R.D k ω, R.Δ k ω⟫ then 1 else 0

/-- `I_k^− = I{Y(θ_k − c̄_kΔ_k) ≤ q_k − c̄_k D_k^T Δ_k}`. -/
noncomputable def Im {Ω : Type*} {d : ℕ} (c : ℕ → ℝ) (R : Run Ω d) (k : ℕ) (ω : Ω) : ℝ :=
  if R.Ym k ω ≤ R.q k ω - cbar c k (R.D k ω) * ⟪R.D k ω, R.Δ k ω⟫ then 1 else 0

/-- `R` is a run of Algorithm SPQO (p. 10) on the probability space `(Ω, P)` with filtration `ℱ`:
deterministic initial values `θ_0 ∈ Θ`, `q_0 ∈ I`, `D_0`; the recursions (20) (with the quantile step
projected onto `I` by `Pq`), (21) and (22); adaptedness; and the sampling model: given the past and
`Δ_k`, the outputs `Y(θ_k ± c̄_kΔ_k)` have the laws of the black box at `θ_k ± c̄_kΔ_k`, and given the
past, `Y(θ_k)` has the law at `θ_k`. -/
structure IsSPQORun {Ω : Type*} {d : ℕ} [m0 : MeasurableSpace Ω] (P : Measure Ω)
    (ℱ : Filtration ℕ m0) (M : Model d) (Θ : Set (E d)) (Proj : E d → E d) (I : Set ℝ)
    (Pq : ℝ → ℝ) (α β γ c : ℕ → ℝ) (R : Run Ω d) : Prop where
  pqProj : IsIntervalProj I Pq
  quantiles_mem : M.qf '' Θ ⊆ I
  init : ∃ θ₀ ∈ Θ, ∃ q₀ ∈ I, ∃ D₀ : E d,
    ∀ ω, R.θ 0 ω = θ₀ ∧ R.q 0 ω = q₀ ∧ R.D 0 ω = D₀
  eq20 : ∀ k ω, R.q (k + 1) ω =
    Pq (R.q k ω + γ k * (M.φ - (if R.Y0 k ω ≤ R.q k ω then 1 else 0)))
  eq21 : ∀ k ω (i : Fin d), R.D (k + 1) ω i = R.D k ω i +
    β k * ((-Ip c R k ω + Im c R k ω) / (2 * cbar c k (R.D k ω) * R.Δ k ω i))
  eq22 : ∀ k ω, R.θ (k + 1) ω = Proj (R.θ k ω - α k • R.D k ω)
  adapted_θ : ∀ k, StronglyMeasurable[ℱ k] (R.θ k)
  adapted_q : ∀ k, StronglyMeasurable[ℱ k] (R.q k)
  adapted_D : ∀ k, StronglyMeasurable[ℱ k] (R.D k)
  meas_Δ : ∀ k, StronglyMeasurable[ℱ (k + 1)] (R.Δ k)
  meas_Y0 : ∀ k, StronglyMeasurable[ℱ (k + 1)] (R.Y0 k)
  meas_Yp : ∀ k, StronglyMeasurable[ℱ (k + 1)] (R.Yp k)
  meas_Ym : ∀ k, StronglyMeasurable[ℱ (k + 1)] (R.Ym k)
  sample0 : ∀ k (B : Set ℝ), MeasurableSet B →
    P[fun ω => B.indicator (fun _ => (1 : ℝ)) (R.Y0 k ω) | ℱ k] =ᵐ[P]
      fun ω => (M.law (R.θ k ω) B).toReal
  sampleP : ∀ k (B : Set ℝ), MeasurableSet B →
    P[fun ω => B.indicator (fun _ => (1 : ℝ)) (R.Yp k ω) |
        ℱ k ⊔ MeasurableSpace.comap (R.Δ k) inferInstance] =ᵐ[P]
      fun ω => (M.law (R.θ k ω + cbar c k (R.D k ω) • R.Δ k ω) B).toReal
  sampleM : ∀ k (B : Set ℝ), MeasurableSet B →
    P[fun ω => B.indicator (fun _ => (1 : ℝ)) (R.Ym k ω) |
        ℱ k ⊔ MeasurableSpace.comap (R.Δ k) inferInstance] =ᵐ[P]
      fun ω => (M.law (R.θ k ω - cbar c k (R.D k ω) • R.Δ k ω) B).toReal

/-! ### Assumptions A1–A3 (pp. 12–13) -/

/-- **A1** (p. 12), with the first-derivative bound used by the proofs (pp. 35, 38): there are a radius
`δ > 0` and constants `K`, `ε > 0`, independent of `k` and `ω`, such that almost surely, for every `k`,
on the ball of radius `δ` around `(q_k, θ_k)` the c.d.f. `F(y;θ)` is three times continuously
differentiable with first and third derivatives bounded by `K` (A1(a)), and `f(y;θ) ≥ ε` (A1(b)). -/
def A1 {Ω : Type*} {d : ℕ} [MeasurableSpace Ω] (P : Measure Ω) (M : Model d) (R : Run Ω d) : Prop :=
  ∃ δ > (0 : ℝ), ∃ K ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂P, ∀ k,
    ContDiffOn ℝ 3 (cdfU M) (Metric.ball (R.q k ω, R.θ k ω) δ) ∧
    ∀ p ∈ Metric.ball (R.q k ω, R.θ k ω) δ,
      ‖fderiv ℝ (cdfU M) p‖ ≤ K ∧ ‖iteratedFDeriv ℝ 3 (cdfU M) p‖ ≤ K ∧ ε ≤ M.dens p.1 p.2

/-- **A2** (p. 12): each `Δ_k` has i.i.d. components uniform on `{−1, 1}` (a common law for all `k`)
and is independent of `ℱ_k`. -/
def A2 {Ω : Type*} {d : ℕ} [m0 : MeasurableSpace Ω] (P : Measure Ω) (ℱ : Filtration ℕ m0)
    (R : Run Ω d) : Prop :=
  ∀ k, P.map (R.Δ k) = rademacher d ∧
    Indep (MeasurableSpace.comap (R.Δ k) inferInstance) (ℱ k) P

/-- **A3(a)** (p. 12): `β_k, c_k > 0`, `c_k → 0`, `∑ β_k = ∞`, `∑ β_k²/c_k² < ∞`. -/
def A3a (β c : ℕ → ℝ) : Prop :=
  (∀ k, 0 < β k ∧ 0 < c k) ∧ Tendsto c atTop (𝓝 0) ∧ ¬ Summable β ∧
    Summable (fun k => β k ^ 2 / c k ^ 2)

/-- **A3(b)** (p. 12): `γ_k > 0`, `∑ γ_k = ∞`. -/
def A3b (γ : ℕ → ℝ) : Prop := (∀ k, 0 < γ k) ∧ ¬ Summable γ

/-- **A3(c)** (p. 13): `α_k > 0`, `∑ α_k = ∞`. -/
def A3c (α : ℕ → ℝ) : Prop := (∀ k, 0 < α k) ∧ ¬ Summable α

/-- **A3(d)** (p. 13): `α_k = o(γ_k)`, `γ_k = o(β_k)`. -/
def A3d (α β γ : ℕ → ℝ) : Prop :=
  Tendsto (fun k => α k / γ k) atTop (𝓝 0) ∧ Tendsto (fun k => γ k / β k) atTop (𝓝 0)

/-! ### Section 4 (p. 17) -/

/-- The step- and perturbation-sizes of Section 4, indexed from `k = 0`:
`α_k = a/(k+1)^α`, `β_k = b/(k+1)^β`, `γ_k = r/(k+1)^γ`, `c_k = c/(k+1)^τ` with
`a, b, r, c > 0` and `α, β, γ, τ ∈ (0,1)`. -/
def PolySteps (α β γ c : ℕ → ℝ) : Prop :=
  ∃ a b r c₀ eα eβ eγ τ : ℝ, 0 < a ∧ 0 < b ∧ 0 < r ∧ 0 < c₀ ∧
    eα ∈ Set.Ioo (0 : ℝ) 1 ∧ eβ ∈ Set.Ioo (0 : ℝ) 1 ∧ eγ ∈ Set.Ioo (0 : ℝ) 1 ∧
    τ ∈ Set.Ioo (0 : ℝ) 1 ∧
    ∀ k : ℕ, α k = a / ((k : ℝ) + 1) ^ eα ∧ β k = b / ((k : ℝ) + 1) ^ eβ ∧
      γ k = r / ((k : ℝ) + 1) ^ eγ ∧ c k = c₀ / ((k : ℝ) + 1) ^ τ

/-- The Hessian `H(θ) = ∇²_θ q(θ)`, as the derivative of the gradient. -/
noncomputable def hess {d : ℕ} (g : E d → ℝ) (θ : E d) : E d →L[ℝ] E d :=
  fderiv ℝ (gradient g) θ

/-- **B1** (p. 17): constants `ε, C_f > 0` such that almost surely, for every `k`,
`ε ≤ f(y;θ_k) ≤ C_f` for all `y` between `q_k` and `q(θ_k)`. -/
def B1 {Ω : Type*} {d : ℕ} [MeasurableSpace Ω] (P : Measure Ω) (M : Model d) (R : Run Ω d) : Prop :=
  ∃ ε Cf : ℝ, 0 < ε ∧ 0 < Cf ∧ ∀ᵐ ω ∂P, ∀ k, ∀ y ∈ Set.uIcc (R.q k ω) (M.qf (R.θ k ω)),
    ε ≤ M.dens y (R.θ k ω) ∧ M.dens y (R.θ k ω) ≤ Cf

/-- **B2** (p. 17): `f` is jointly continuous on `ℝ × Θ`, and for all `θ ∈ Θ` both `f(·;θ)` and
`∇_θF(·;θ)` are Lipschitz in `y`, with constants `L_f, L_F > 0`. -/
def B2 {d : ℕ} (M : Model d) (Θ : Set (E d)) : Prop :=
  ContinuousOn (fun p : ℝ × E d => M.dens p.1 p.2) (Set.univ ×ˢ Θ) ∧
    ∃ Lf LF : ℝ, 0 < Lf ∧ 0 < LF ∧ ∀ θ ∈ Θ, ∀ y₁ y₂ : ℝ,
      |M.dens y₁ θ - M.dens y₂ θ| ≤ Lf * |y₁ - y₂| ∧
      ‖gradθ M y₁ θ - gradθ M y₂ θ‖ ≤ LF * |y₁ - y₂|

/-- **B3** (p. 17), in quadratic-form (Rayleigh–Ritz) form: a constant `ϱ > 0` such that almost surely,
for every `k` and every `θ` on the segment between `θ_k` and `θ*`, `⟪H(θ)v, v⟫ ≥ ϱ‖v‖²` for all `v`. -/
def B3 {Ω : Type*} {d : ℕ} [MeasurableSpace Ω] (P : Measure Ω) (M : Model d) (R : Run Ω d)
    (θstar : E d) : Prop :=
  ∃ ϱ > (0 : ℝ), ∀ᵐ ω ∂P, ∀ k, ∀ θ ∈ segment ℝ (R.θ k ω) θstar, ∀ v : E d,
    ϱ * ‖v‖ ^ 2 ≤ ⟪hess M.qf θ v, v⟫

/-! ### The bias of the SP gradient estimator (Lemma 2, p. 13) -/

/-- The bias `b_k(q, D, θ)` of Lemma 2, with the conditional expectation over `Δ_k` written as the
average over the `2^d` sign vectors `s` (under A2, `1/Δ_k = Δ_k`, p. 14):
`b_k = (M/(2c_k)) · 2^{−d} ∑_s (−F(q + c̄⟪D,s⟫; θ + c̄s) + F(q − c̄⟪D,s⟫; θ − c̄s)) s + f(q;θ) D + ∇_θF(q;θ)`
with `M = max{1, ‖D‖/√d}` and `c̄ = c_k/M`. -/
noncomputable def bias {d : ℕ} (M : Model d) (c : ℕ → ℝ) (k : ℕ) (q : ℝ) (D θ : E d) : E d :=
  (mfac D / (2 * c k)) • ((2 ^ d : ℝ)⁻¹ • ∑ b : Fin d → Bool,
      (-cdf M (q + cbar c k D * ⟪D, signVec b⟫) (θ + cbar c k D • signVec b) +
        cdf M (q - cbar c k D * ⟪D, signVec b⟫) (θ - cbar c k D • signVec b)) • signVec b) +
    M.dens q θ • D + gradθ M q θ

end QuantileSPQO.Rate


