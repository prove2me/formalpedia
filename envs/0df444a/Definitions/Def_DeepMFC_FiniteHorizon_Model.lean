-- Prove2me | Definitions.Def_DeepMFC_FiniteHorizon_Model
-- name    : DeepMFC_FiniteHorizon_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:15.180817+00:00
-- url     : https://prove2.me/theorems/af68c5b5-0d50-461e-96b6-aad03636d7e8
-- title:
--   §2–§3, pp. 4066–4072 — the MKV control problem (Problem 1), its N-agent version (Problem 3) and the Euler-scheme proxy (Problem 2)
-- statement:
--   This module fixes the objects of Carmona and Laurière's analysis of machine-learning methods for **mean field control** on a finite horizon.
--
--   **Measures.** For a probability measure $\mu$ on $\mathbb R^d$, $\mu\in\mathcal P_2(\mathbb R^d)$ (resp. $\mathcal P_4$) when $\int|x|^2\,d\mu<\infty$ (resp. $\int|x|^4\,d\mu<\infty$); $M_2(\mu)=(\int|x|^2\,d\mu(x))^{1/2}$, $\bar\mu=\int x\,d\mu(x)$ is the mean, $W_2$ is the 2-Wasserstein distance, and $\frac1N\sum_{i=1}^N\delta_{x_i}$ is the empirical measure of $x=(x_1,\dots,x_N)$.
--
--   **Data.** A horizon $T>0$, a drift $b(t,x,\mu,\alpha)\in\mathbb R^d$, an uncontrolled volatility $\sigma(t,x,\mu)\in\mathbb R^{d\times d}$, a running cost $f(t,x,\mu,\alpha)\in\mathbb R$, a terminal cost $g(x,\mu)\in\mathbb R$ and an initial law $\mu_0$; controls take values in $A=\mathbb R^k$. The Hamiltonian is $H(t,x,\mu,y,z,\alpha)=b\cdot y+\sigma\cdot z+f$ and the reduced Hamiltonian is $\tilde H(t,x,\mu,y,\alpha)=b\cdot y+f$, with $\sigma\cdot z=\sum_{ij}\sigma_{ij}z_{ij}$.
--
--   **Problem 1.** On a probability space carrying a $d$-dimensional Wiener process $W$ and an independent $X_0\sim\mu_0$, with the filtration $\mathcal F_t=\sigma(X_0,W_s:s\le t)$, an admissible control $\alpha\in\mathbb A=\mathbb H^{2,k}$ is a progressively measurable $\mathbb R^k$-valued process with $\mathbb E\int_0^T|\alpha_s|^2\,ds<\infty$. Its state solves
--   $$dX_t=b(t,X_t,\mathcal L(X_t),\alpha_t)\,dt+\sigma(t,X_t,\mathcal L(X_t))\,dW_t,\qquad(2.2)$$
--   and its cost is $J(\alpha)=\mathbb E\big[\int_0^Tf(t,X_t,\mathcal L(X_t),\alpha_t)\,dt+g(X_T,\mathcal L(X_T))\big]$ (2.1).
--
--   **Problem 3.** On a probability space carrying independent Wiener processes $W^1,\dots,W^N$ and i.i.d. $X^1_0,\dots,X^N_0\sim\mu_0$, all $2N$ of them mutually independent, a feedback function $v(t,x)$ drives
--   $$dX^i_t=b(t,X^i_t,\mu^N_t,v(t,X^i_t))\,dt+\sigma(t,X^i_t,\mu^N_t)\,dW^i_t,\qquad \mu^N_t=\frac1N\sum_{j=1}^N\delta_{X^j_t},\qquad(3.2)$$
--   with cost $J^N(v)=\frac1N\sum_{i=1}^N\mathbb E\big[\int_0^Tf(t,X^i_t,\mu^N_t,v(t,X^i_t))\,dt+g(X^i_T,\mu^N_T)\big]$ (3.1).
--
--   **Problem 2.** With $\Delta t=T/N_T$ and $t_n=n\Delta t$, the Euler scheme
--   $$\check X^i_{t_{n+1}}=\check X^i_{t_n}+b(t_n,\check X^i_{t_n},\check\mu_{t_n},\varphi(t_n,\check X^i_{t_n}))\Delta t+\sigma(t_n,\check X^i_{t_n},\check\mu_{t_n})\Delta\check W^i_n\qquad(2.13)$$
--   is driven by i.i.d. initial positions $\check X^i_0\sim\mu_0$ and i.i.d. increments $\Delta\check W^i_n\sim\mathcal N(0,\Delta t\,I_d)$, and its cost is
--   $$\check J^N(\varphi)=\mathbb E\Big[\frac1N\sum_{i=1}^N\Big(\Delta t\sum_{n=0}^{N_T-1}f(t_n,\check X^i_{t_n},\check\mu_{t_n},\varphi(t_n,\check X^i_{t_n}))+g(\check X^i_{t_{N_T}},\check\mu_{t_{N_T}})\Big)\Big].\qquad(2.12)$$
--
--   Finally, a feedback $v$ is *$L$-Lipschitz* when $(t,x)\mapsto v(t,x)$ is $L$-Lipschitz on $[0,T]\times\mathbb R^d$.
--
--   These are the three optimization problems compared by Theorem 3: the original McKean–Vlasov problem, its $N$-agent feedback version, and the computable discrete-time proxy.
--
--   **Formalization Note.** $\mathbb R^d$ is `Fin d → ℝ` with the sup norm; every statement of the paper is invariant under the choice of norm because every constant is existential. Time is `ℝ≥0` for processes, as in the published Itô substrate `Peng1990.SMP.Stochastic`, and the coefficients take real time. An SDE solution with random initial value is a process with continuous paths on $[0,T]$, starting at $X_0$, such that $X-X_0$ is a `Peng1990.SMP.IsItoProcess` for the natural (uncompleted) filtration of the initial data and the Wiener processes; this predicate includes progressive measurability, so the laws $\mathcal L(X_t)$ are well defined. Since $X_0$ (resp. the $X^i_0$) is independent of $W$ (resp. the $W^i$), the Wiener processes remain Wiener processes for these filtrations, which is the setting in which the Itô integrals are meant. The column $j$ of $\sigma$ multiplies $dW^j$. The empirical measure in (3.2) is pathwise (random), whereas Problem 1 uses the deterministic law. The Euler scheme is a deterministic map of the initial positions and the increments, and $\check J^N$ is its integral against $\mu_0^{\otimes N}\otimes\mathcal N(0,\Delta t\,I_d)^{\otimes N\times N_T}$, so it depends only on the laws, as in (2.12). The costs are Bochner integrals (value $0$ if not integrable); under the standing assumptions every cost that appears is integrable. $W_2$ is the published `WassersteinDRO.Duality.wassersteinDistance 2`, valued in $[0,\infty]$; it is used only between measures in $\mathcal P_2$, where it is finite. $\mu_0$ is a probability measure by definition of the data.
-- source:
--   Carmona, Laurière, Convergence analysis of machine learning algorithms for the numerical solution of mean field control and games: II—the finite horizon case, Ann. Appl. Probab. 32(6) (2022), https://doi.org/10.1214/21-AAP1715, pp. 4066–4072, Problems 1–3, (2.1)–(2.5), (2.12)–(2.13), (3.1)–(3.2)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DeepMFC.FiniteHorizon

/-! # The MKV control problem (Problem 1), its `N`-agent version (Problem 3) and the Euler
proxy (Problem 2)

Carmona, Laurière, *Convergence analysis of machine learning algorithms for the numerical solution
of mean field control and games: II — the finite horizon case*, Ann. Appl. Probab. 32(6) (2022),
§2–§3, pp. 4066–4072. -/

/-- The state space `ℝᵈ`, as `Fin d → ℝ` (sup norm; every statement of the paper is invariant
under the choice of norm because every constant is existential). -/
abbrev E (d : ℕ) := Fin d → ℝ

/-! ### Measures of order `p`, moments, Wasserstein distance, empirical measures (§2.1, p. 4067) -/

/-- `μ ∈ 𝒫₂(ℝᵈ)`: a probability measure with finite second moment. -/
def IsP2 {d : ℕ} (μ : Measure (E d)) : Prop :=
  IsProbabilityMeasure μ ∧ ∫⁻ x, ‖x‖ₑ ^ 2 ∂μ < ⊤

/-- `μ ∈ 𝒫₄(ℝᵈ)`: a probability measure with finite fourth moment. -/
def IsP4 {d : ℕ} (μ : Measure (E d)) : Prop :=
  IsProbabilityMeasure μ ∧ ∫⁻ x, ‖x‖ₑ ^ 4 ∂μ < ⊤

/-- The second moment `M₂(μ) = (∫ |x|² dμ(x))^{1/2}` of (2.3). -/
noncomputable def M2 {d : ℕ} (μ : Measure (E d)) : ℝ :=
  (∫ x, ‖x‖ ^ 2 ∂μ) ^ (1 / 2 : ℝ)

/-- The mean `μ̄ = ∫ x dμ(x)` of a measure. -/
noncomputable def mean {d : ℕ} (μ : Measure (E d)) : E d :=
  ∫ x, x ∂μ

/-- The 2-Wasserstein distance `W₂(μ, μ')` (the published coupling definition, in `[0, ∞]`). -/
noncomputable def W2 {d : ℕ} (μ μ' : Measure (E d)) : ℝ≥0∞ :=
  WassersteinDRO.Duality.wassersteinDistance 2 μ μ'

/-- The empirical measure `(1/N) Σᵢ δ_{xᵢ}` of `x = (x₁, …, x_N)`. -/
noncomputable def empirical {d N : ℕ} (x : Fin N → E d) : Measure (E d) :=
  (N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (x i)

/-- The Euclidean pairing `u · v = Σᵢ uᵢ vᵢ`. -/
def dot {n : ℕ} (u v : Fin n → ℝ) : ℝ :=
  ∑ i, u i * v i

/-- The pairing `σ · z = Σᵢⱼ σᵢⱼ zᵢⱼ` of two `d × d` matrices. -/
def mdot {d : ℕ} (σ z : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∑ i, ∑ j, σ i j * z i j

/-! ### The data of the problem (§2, p. 4066) -/

/-- The data of the MKV control problem: horizon `T > 0`, drift `b(t, x, μ, α) ∈ ℝᵈ`, uncontrolled
volatility `σ(t, x, μ) ∈ ℝ^{d×d}`, running cost `f(t, x, μ, α)`, terminal cost `g(x, μ)`, and the
initial law `μ₀`, a probability measure on `ℝᵈ`. The action set is `A = ℝᵏ` (p. 4069). -/
structure Model (d k : ℕ) where
  T : ℝ≥0
  hT : 0 < T
  b : ℝ → E d → Measure (E d) → (Fin k → ℝ) → E d
  σ : ℝ → E d → Measure (E d) → Matrix (Fin d) (Fin d) ℝ
  f : ℝ → E d → Measure (E d) → (Fin k → ℝ) → ℝ
  g : E d → Measure (E d) → ℝ
  μ0 : Measure (E d)
  hμ0 : IsProbabilityMeasure μ0

instance {d k : ℕ} (M : Model d k) : IsProbabilityMeasure M.μ0 := M.hμ0

/-- The Hamiltonian (2.4): `H(t, x, μ, y, z, α) = b(t, x, μ, α) · y + σ(t, x, μ) · z + f(t, x, μ, α)`. -/
noncomputable def Model.H {d k : ℕ} (M : Model d k) (t : ℝ) (x : E d) (μ : Measure (E d)) (y : E d)
    (z : Matrix (Fin d) (Fin d) ℝ) (a : Fin k → ℝ) : ℝ :=
  dot (M.b t x μ a) y + mdot (M.σ t x μ) z + M.f t x μ a

/-- The reduced Hamiltonian (2.5): `H̃(t, x, μ, y, α) = b(t, x, μ, α) · y + f(t, x, μ, α)`. -/
noncomputable def Model.Htilde {d k : ℕ} (M : Model d k) (t : ℝ) (x : E d) (μ : Measure (E d))
    (y : E d) (a : Fin k → ℝ) : ℝ :=
  dot (M.b t x μ a) y + M.f t x μ a

/-! ### Filtrations -/

/-- The natural filtration `t ↦ σ(Y(s) : s ≤ t)` of a process `Y` (intersected with the ambient
σ-algebra, which changes nothing when every `Y(s)` is measurable); uncompleted. -/
def filtOf {Ω : Type*} [mΩ : MeasurableSpace Ω] {β : Type*} [mβ : MeasurableSpace β]
    (Y : ℝ≥0 → Ω → β) : Filtration ℝ≥0 mΩ where
  seq t := (⨆ s ≤ t, MeasurableSpace.comap (Y s) mβ) ⊓ mΩ
  mono' _ _ hst :=
    inf_le_inf_right _ (iSup₂_le fun r hr => le_iSup₂_of_le r (hr.trans hst) le_rfl)
  le' _ := inf_le_right

/-! ### Problem 1 (p. 4066) -/

/-- The probability setting of Problem 1: a probability space carrying a standard `d`-dimensional
Wiener process `W` and an initial condition `X₀ ∼ μ₀` independent of `W`. -/
structure Setting1 {d k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (M : Model d k) (P : Measure Ω)
    (W : ℝ≥0 → Ω → E d) (X0 : Ω → E d) : Prop where
  prob : IsProbabilityMeasure P
  brownian : Peng1990.SMP.IsStdBrownian P W
  meas_X0 : Measurable X0
  law_X0 : P.map X0 = M.μ0
  indep : IndepFun X0 (fun ω t => W t ω) P

/-- The filtration `ℱ_t = σ(X₀, W_s : s ≤ t)` of Problem 1. -/
def filt1 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (W : ℝ≥0 → Ω → E d) (X0 : Ω → E d) :
    Filtration ℝ≥0 ‹MeasurableSpace Ω› :=
  filtOf (fun t ω => (X0 ω, W t ω))

/-- Admissible (open-loop) controls `𝔸 = ℍ^{2,k}`: `ℝᵏ`-valued progressively measurable processes
with `𝔼 ∫₀ᵀ |α_s|² ds < ∞`. -/
def Admissible {d k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (M : Model d k) (P : Measure Ω)
    (W : ℝ≥0 → Ω → E d) (X0 : Ω → E d) (α : ℝ≥0 → Ω → Fin k → ℝ) : Prop :=
  Peng1990.SMP.L2F (filt1 W X0) P M.T α

/-- `X` solves the McKean–Vlasov SDE (2.2) on `[0, T]` with control `α`:
`dX_t = b(t, X_t, ℒ(X_t), α_t) dt + σ(t, X_t, ℒ(X_t)) dW_t`, `X₀` given, where `ℒ(X_t)` is the law
`P.map (X t)`. The paths are continuous on `[0, T]`, and `X − X₀` is an Itô process for the
filtration of `(X₀, W)` (which includes progressive measurability, so the laws are meaningful). -/
structure Solves22 {d k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (M : Model d k) (P : Measure Ω)
    (W : ℝ≥0 → Ω → E d) (X0 : Ω → E d) (α : ℝ≥0 → Ω → Fin k → ℝ) (X : ℝ≥0 → Ω → E d) : Prop where
  init : ∀ ω, X 0 ω = X0 ω
  cont : ∀ ω, ContinuousOn (fun t => X t ω) (Set.Icc 0 M.T)
  sde : Peng1990.SMP.IsItoProcess (filt1 W X0) P M.T W 0
    (fun t ω => M.b t (X t ω) (P.map (X t)) (α t ω))
    (fun j t ω i => M.σ t (X t ω) (P.map (X t)) i j)
    (fun t ω => X t ω - X0 ω)

/-- The cost (2.1): `J(α) = 𝔼[∫₀ᵀ f(t, X_t, ℒ(X_t), α_t) dt + g(X_T, ℒ(X_T))]`, as a function of the
control `α` and the state `X` it generates. -/
noncomputable def J {d k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (M : Model d k) (P : Measure Ω)
    (α : ℝ≥0 → Ω → Fin k → ℝ) (X : ℝ≥0 → Ω → E d) : ℝ :=
  ∫ ω, ((∫ t in (0 : ℝ)..(M.T : ℝ),
      M.f t (X t.toNNReal ω) (P.map (X t.toNNReal)) (α t.toNNReal ω)) +
    M.g (X M.T ω) (P.map (X M.T))) ∂P

/-! ### Problem 3 (p. 4072) -/

/-- The σ-algebras generated by the `X₀ⁱ` (left summand) and by the `Wⁱ` (right summand). -/
abbrev noiseFam {d N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (W : Fin N → ℝ≥0 → Ω → E d)
    (X0 : Fin N → Ω → E d) : Fin N ⊕ Fin N → MeasurableSpace Ω
  | Sum.inl i => MeasurableSpace.comap (X0 i) inferInstance
  | Sum.inr i => MeasurableSpace.comap (fun ω t => W i t ω) inferInstance

/-- The probability setting of Problem 3 with `N` agents: independent standard `d`-dimensional
Wiener processes `W¹, …, Wᴺ`, initial conditions `X₀¹, …, X₀ᴺ` i.i.d. with law `μ₀`, and the `2N`
random elements `{X₀ⁱ} ∪ {Wⁱ}` mutually independent. -/
structure Setting3 {d k N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (M : Model d k) (P : Measure Ω)
    (W : Fin N → ℝ≥0 → Ω → E d) (X0 : Fin N → Ω → E d) : Prop where
  prob : IsProbabilityMeasure P
  brownian : ∀ i, Peng1990.SMP.IsStdBrownian P (W i)
  meas_X0 : ∀ i, Measurable (X0 i)
  law_X0 : ∀ i, P.map (X0 i) = M.μ0
  indep : iIndep (noiseFam W X0) P

/-- The filtration `ℱ_t = σ(X₀ⁱ, Wⁱ_s : i ≤ N, s ≤ t)` of Problem 3. -/
def filt3 {d N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (W : Fin N → ℝ≥0 → Ω → E d)
    (X0 : Fin N → Ω → E d) : Filtration ℝ≥0 ‹MeasurableSpace Ω› :=
  filtOf (fun t ω => ((fun i => X0 i ω), (fun i => W i t ω)))

/-- `X = (X¹, …, Xᴺ)` solves the `N`-agent system (3.2) on `[0, T]` with feedback function `v`:
`dXⁱ_t = b(t, Xⁱ_t, μᴺ_t, v(t, Xⁱ_t)) dt + σ(t, Xⁱ_t, μᴺ_t) dWⁱ_t`, `Xⁱ_0 = X₀ⁱ`, where
`μᴺ_t = (1/N) Σⱼ δ_{Xʲ_t}` is the (random, pathwise) empirical measure. -/
structure Solves32 {d k N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (M : Model d k) (P : Measure Ω)
    (W : Fin N → ℝ≥0 → Ω → E d) (X0 : Fin N → Ω → E d) (v : ℝ → E d → Fin k → ℝ)
    (X : Fin N → ℝ≥0 → Ω → E d) : Prop where
  init : ∀ i ω, X i 0 ω = X0 i ω
  cont : ∀ i ω, ContinuousOn (fun t => X i t ω) (Set.Icc 0 M.T)
  sde : ∀ i, Peng1990.SMP.IsItoProcess (filt3 W X0) P M.T (W i) 0
    (fun t ω => M.b t (X i t ω) (empirical (fun j => X j t ω)) (v t (X i t ω)))
    (fun j t ω l => M.σ t (X i t ω) (empirical (fun j' => X j' t ω)) l j)
    (fun t ω => X i t ω - X0 i ω)

/-- The `N`-agent cost (3.1):
`Jᴺ(v) = (1/N) Σᵢ 𝔼[∫₀ᵀ f(t, Xⁱ_t, μᴺ_t, v(t, Xⁱ_t)) dt + g(Xⁱ_T, μᴺ_T)]`. -/
noncomputable def JN {d k N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (M : Model d k) (P : Measure Ω)
    (v : ℝ → E d → Fin k → ℝ) (X : Fin N → ℝ≥0 → Ω → E d) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, ∫ ω, ((∫ t in (0 : ℝ)..(M.T : ℝ),
      M.f t (X i t.toNNReal ω) (empirical (fun j => X j t.toNNReal ω)) (v t (X i t.toNNReal ω))) +
    M.g (X i M.T ω) (empirical (fun j => X j M.T ω))) ∂P

/-! ### Problem 2 (p. 4070) -/

/-- The time step `Δt = T / N_T`. -/
noncomputable def Model.dt {d k : ℕ} (M : Model d k) (NT : ℕ) : ℝ≥0 :=
  M.T / (NT : ℝ≥0)

/-- The grid point `t_n = n Δt`. -/
noncomputable def Model.tg {d k : ℕ} (M : Model d k) (NT n : ℕ) : ℝ≥0 :=
  (n : ℝ≥0) * M.dt NT

/-- The Euler scheme (2.13) as a deterministic map of the initial positions `x₀ = (X̌ⁱ₀)ᵢ` and the
increments `w = (ΔW̌ⁱ_n)_{i,n}`: `X̌_0 = x₀` and
`X̌ⁱ_{n+1} = X̌ⁱ_n + b(t_n, X̌ⁱ_n, μ̌_n, φ(t_n, X̌ⁱ_n)) Δt + σ(t_n, X̌ⁱ_n, μ̌_n) ΔW̌ⁱ_n`,
with `μ̌_n = (1/N) Σᵢ δ_{X̌ⁱ_n}`. Only the steps `n < N_T` are used. -/
noncomputable def euler {d k N : ℕ} (M : Model d k) (NT : ℕ) (φ : ℝ → E d → Fin k → ℝ)
    (x0 : Fin N → E d) (w : Fin N → Fin NT → E d) : ℕ → Fin N → E d
  | 0 => x0
  | n + 1 => fun i =>
      euler M NT φ x0 w n i
        + ((M.dt NT : ℝ)) • M.b (M.tg NT n) (euler M NT φ x0 w n i)
            (empirical (euler M NT φ x0 w n)) (φ (M.tg NT n) (euler M NT φ x0 w n i))
        + (M.σ (M.tg NT n) (euler M NT φ x0 w n i) (empirical (euler M NT φ x0 w n))).mulVec
            (if h : n < NT then w i ⟨n, h⟩ else 0)

/-- The Gaussian law `𝒩(0, Δt I_d)` on `ℝᵈ`: `d` independent `𝒩(0, Δt)` coordinates. -/
noncomputable def gaussVec (d : ℕ) (v : ℝ≥0) : Measure (E d) :=
  Measure.pi fun _ : Fin d => gaussianReal 0 v

/-- The law of the inputs of Problem 2: `(X̌ⁱ₀)ᵢ` i.i.d. `μ₀`, independent of the increments
`(ΔW̌ⁱ_n)_{i,n}`, i.i.d. `𝒩(0, Δt I_d)`. -/
noncomputable def inputLaw {d k : ℕ} (M : Model d k) (N NT : ℕ) :
    Measure ((Fin N → E d) × (Fin N → Fin NT → E d)) :=
  (Measure.pi fun _ : Fin N => M.μ0).prod
    (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin NT => gaussVec d (M.dt NT))

/-- The integrand of (2.12):
`(1/N) Σᵢ (Δt Σ_{n<N_T} f(t_n, X̌ⁱ_n, μ̌_n, φ(t_n, X̌ⁱ_n)) + g(X̌ⁱ_{N_T}, μ̌_{N_T}))`. -/
noncomputable def costCheck {d k N : ℕ} (M : Model d k) (NT : ℕ) (φ : ℝ → E d → Fin k → ℝ)
    (p : (Fin N → E d) × (Fin N → Fin NT → E d)) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, ((M.dt NT : ℝ) * ∑ n ∈ Finset.range NT,
      M.f (M.tg NT n) (euler M NT φ p.1 p.2 n i) (empirical (euler M NT φ p.1 p.2 n))
        (φ (M.tg NT n) (euler M NT φ p.1 p.2 n i)) +
    M.g (euler M NT φ p.1 p.2 NT i) (empirical (euler M NT φ p.1 p.2 NT)))

/-- The cost (2.12) of Problem 2, `J̌ᴺ(φ)`: the expectation of `costCheck` under the input law. -/
noncomputable def Jcheck {d k : ℕ} (M : Model d k) (N NT : ℕ) (φ : ℝ → E d → Fin k → ℝ) : ℝ :=
  ∫ p, costCheck (N := N) M NT φ p ∂(inputLaw M N NT)

/-! ### Feedback functions -/

/-- A feedback function `v : [0, T] × ℝᵈ → ℝᵏ` is `L`-Lipschitz in `(t, x)` on `[0, T] × ℝᵈ`. -/
def FeedbackLip {d k : ℕ} (M : Model d k) (L : ℝ) (v : ℝ → E d → Fin k → ℝ) : Prop :=
  LipschitzOnWith (Real.toNNReal L) (fun p : ℝ × E d => v p.1 p.2)
    (Set.Icc (0 : ℝ) M.T ×ˢ Set.univ)

end DeepMFC.FiniteHorizon


