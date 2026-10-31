-- Prove2me | Definitions.Def_GraphonLabelGame_Model
-- name    : GraphonLabelGame_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:22:35.296984+00:00
-- url     : https://prove2.me/theorems/28e4537a-1855-4897-8611-4bcfee8ff051
-- title:
--   The $n$-player game, the graphon game in label-state form, $W$-equilibria and the errors $\epsilon^n_i$
-- statement:
--   This module encodes the two games of §3 and the quantities of §7.
--
--   1. **Model data and standing assumptions** (p.6). Dimensions $d\ge1$ and $d_0$, a horizon $T>0$, a compact metric action space $A$, and bounded continuous $b:[0,T]\times\mathbb R^d\times A\to\mathbb R^d$, $\sigma:[0,T]\times\mathbb R^d\to\mathbb R^{d\times d_0}$, $f:[0,T]\times\mathbb R^d\times\mathcal M_+(\mathbb R^d)\times A\to\mathbb R$, $g:\mathbb R^d\times\mathcal M_+(\mathbb R^d)\to\mathbb R$; $\sigma$ is Lipschitz, $\sigma\sigma^\top\ge c\,I$ for some $c>0$, and for each $(t,x,m)$ the set $\{(b(t,x,a),z):a\in A,\ z\le f(t,x,m,a)\}$ is convex (3.1). (Nondegeneracy forces $d_0\ge1$.)
--   2. **Brownian motions.** A family of independent $d_0$-dimensional $\mathbb F$-Brownian motions: standard Brownian motions, adapted, with increments independent of the past.
--   3. **Graphon game** (§3.2). For a control $\alpha\in\mathcal A_U$ (measurable $[0,T]\times[0,1]\times\mathbb R^d\to A$) and an initial law $\lambda$ of $(U,X_0)$, a solution of
--   $$dX_t=b(t,X_t,\alpha(t,U,X_t))\,dt+\sigma(t,X_t)\,dB_t,\qquad (U,X_0)\sim\lambda,\tag{3.4}$$
--   and, for a measure flow $\mu_\cdot$, the reward $J_W(\mu_\cdot,\alpha)=\mathbb E\big[\int_0^Tf(t,X_t,\mathsf W\mu_t(U),\alpha(t,U,X_t))\,dt+g(X_T,\mathsf W\mu_T(U))\big]$.
--   4. **$W$-equilibrium** (Definition 3.1). $\mu_\cdot\in C([0,T];\mathcal P_{\mathrm{Unif}}([0,1]\times\mathbb R^d))$ with a control $\alpha^*\in\mathcal A_U$ such that $\mu_t=\mathcal L(U,X^{\alpha^*}_t)$ for all $t$ and $J_W(\mu_\cdot,\alpha^*)=\sup_{\alpha\in\mathcal A_U}J_W(\mu_\cdot,\alpha)$.
--   5. **$n$-player game** (§3.1, §3.4). For a profile $(\alpha_1,\dots,\alpha_n)$ of controls $[0,T]\times(\mathbb R^d)^n\to A$ and labels $u^n$, the system $dX^i_t=b(t,X^i_t,\alpha_i(t,X_t))\,dt+\sigma(t,X^i_t)\,dB^i_t$ with independent $X^i_0\sim\lambda_{u_i}$; player $i$'s reward $J_i$ (3.3) uses $M^{n,i}_t=\frac1n\sum_j\xi_{ij}\delta_{X^j_t}$.
--   6. **The error** (p.11). With the profile $\alpha^{n,u_i}_i(t,x)=\alpha^*(t,u_i,x_i)$ (3.8),
--   $$\epsilon^n_i(u^n)=\sup_{\beta\in\mathcal A_n}J_i(\alpha^{n,u^n}_{-i},\beta)-J_i(\alpha^{n,u^n}).$$
--   7. The terms $\Delta^{n,i}_1,\Delta^{n,i}_2,\Delta^{n,i}_3$ of p.33, which compare rewards computed with the true $M^{n,u^n,i}_t$ and with the limiting $\mathsf W\mu_t(u_i)$.
--
--   **Formalization Note** Solutions are a relation: a structure bundling a probability space, a filtration, Brownian motions, continuous adapted states with the prescribed initial laws, and Itô integral processes (`Peng1990.SMP.IsItoIntegral`) such that the state equation holds a.s. at every $t\in[0,T]$. Under the standing assumptions solutions exist and are unique in law. $\epsilon^n_i$ is valued in $[0,\infty]$: it is the supremum, over $\beta$, over solutions of the deviated system and over solutions of the undeviated system, of the positive part of the reward difference. The version $u\mapsto\lambda_u$ is a Markov kernel $\kappa$, and $\lambda=\mathrm{Unif}[0,1]\otimes\kappa$. Time is $\mathbb R_{\ge0}$, read on $[0,T]$. "$\sigma$ is Lipschitz" is read as Lipschitz in $x$ uniformly in $t$.
-- source:
--   Lacker, Soret, A Label-State Formulation of Stochastic Graphon Games and Approximate Equilibria on Large Networks, arXiv:2204.09642v1, Standing assumptions p.6, §3.1 p.7 ((3.2), (3.3)), §3.2 p.8 ((3.4), J_W, Definition 3.1), §3.4 pp.10–11 ((3.8), εⁿᵢ), §5 p.21 (J^{u,m}_W), §7 pp.32–33 ((7.1)–(7.3), Δ^{n,i}_1,2,3)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_GraphonLabelGame_Kernel

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Matrix

namespace GraphonLabelGame

/-- The path space `C^d := C([0, T]; ℝᵈ)` with the supremum distance (p.4).

**Formalization Note** `ℝᵈ` is `Fin d → ℝ` (sup norm; same topology and Borel sets as the
Euclidean norm). The path space carries its Borel σ-algebra. -/
abbrev Path (d : ℕ) (T : ℝ≥0) := C(Set.Icc (0 : ℝ) (T : ℝ), Fin d → ℝ)

instance (d : ℕ) (T : ℝ≥0) : MeasurableSpace (Path d T) := borel _

instance (d : ℕ) (T : ℝ≥0) : BorelSpace (Path d T) := ⟨rfl⟩

/-- The value `x_s` of a path at time `s ∈ [0, T]`; times beyond `T` read `x_T`. -/
noncomputable def pathAt {d : ℕ} {T : ℝ≥0} (x : Path d T) (s : ℝ≥0) : Fin d → ℝ :=
  x (Set.projIcc (0 : ℝ) T T.coe_nonneg s)

/-- The data of the model (§3, p.6): dimensions `d, d₀`, horizon `T`, action space `A`, drift
`b : [0, T] × ℝᵈ × A → ℝᵈ`, volatility `σ : [0, T] × ℝᵈ → ℝ^{d×d₀}`, running reward
`f : [0, T] × ℝᵈ × M₊(ℝᵈ) × A → ℝ` and terminal reward `g : ℝᵈ × M₊(ℝᵈ) → ℝ`.

**Formalization Note** Time is `ℝ≥0` (the convention of `Peng1990_SMP_Stochastic`); only
`t ∈ [0, T]` ever enters. `M₊(ℝᵈ)` is `FiniteMeasure (Fin d → ℝ)` with the weak topology. -/
structure Data (d d₀ : ℕ) (A : Type*) where
  T : ℝ≥0
  b : ℝ≥0 → (Fin d → ℝ) → A → (Fin d → ℝ)
  σ : ℝ≥0 → (Fin d → ℝ) → Matrix (Fin d) (Fin d₀) ℝ
  f : ℝ≥0 → (Fin d → ℝ) → FiniteMeasure (Fin d → ℝ) → A → ℝ
  g : (Fin d → ℝ) → FiniteMeasure (Fin d → ℝ) → ℝ

/-- The **standing assumptions** of §3 (p.6): `d ≥ 1`, `T > 0`; `b, σ, f, g` bounded and
continuous (jointly, on `[0, T] × ⋯`); `σ` Lipschitz; `σσᵀ` uniformly nondegenerate; and the
convexity (3.1) of `{(b(t, x, a), z) : a ∈ A, z ≤ f(t, x, m, a)}` for every `(t, x, m)`.
(The action space `A` is a compact metric space; that is a typeclass assumption of each
statement.)

**Formalization Note** "σ is Lipschitz" is read as Lipschitz in `x`, uniformly in `t ∈ [0, T]`
(stated entrywise; equivalent to any matrix norm up to a constant). Nondegeneracy: there is
`c > 0` with `σσᵀ(t, x) − c·I` positive semidefinite for all `t ∈ [0, T]`, `x`. The paper's
`d₀ ∈ ℕ` (i.e. `d₀ ≥ 1`) is not repeated: it follows from nondegeneracy and `d ≥ 1`. -/
structure Data.Standing {d d₀ : ℕ} {A : Type*} [TopologicalSpace A] (D : Data d d₀ A) :
    Prop where
  one_le_d : 1 ≤ d
  T_pos : 0 < D.T
  b_cont : ContinuousOn (fun p : ℝ≥0 × (Fin d → ℝ) × A => D.b p.1 p.2.1 p.2.2)
    (Iic D.T ×ˢ univ)
  b_bdd : ∃ C : ℝ, ∀ t ≤ D.T, ∀ x a, ‖D.b t x a‖ ≤ C
  σ_cont : ContinuousOn (fun p : ℝ≥0 × (Fin d → ℝ) => D.σ p.1 p.2) (Iic D.T ×ˢ univ)
  σ_bdd : ∃ C : ℝ, ∀ t ≤ D.T, ∀ x j k, |D.σ t x j k| ≤ C
  f_cont : ContinuousOn
    (fun p : ℝ≥0 × (Fin d → ℝ) × FiniteMeasure (Fin d → ℝ) × A =>
      D.f p.1 p.2.1 p.2.2.1 p.2.2.2) (Iic D.T ×ˢ univ)
  f_bdd : ∃ C : ℝ, ∀ t ≤ D.T, ∀ x m a, |D.f t x m a| ≤ C
  g_cont : Continuous (fun p : (Fin d → ℝ) × FiniteMeasure (Fin d → ℝ) => D.g p.1 p.2)
  g_bdd : ∃ C : ℝ, ∀ x m, |D.g x m| ≤ C
  σ_lip : ∃ L : ℝ, ∀ t ≤ D.T, ∀ x y : Fin d → ℝ, ∀ j k,
    |D.σ t x j k - D.σ t y j k| ≤ L * dist x y
  nondeg : ∃ c : ℝ, 0 < c ∧ ∀ t ≤ D.T, ∀ x,
    (D.σ t x * (D.σ t x)ᵀ - c • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef
  convex : ∀ t ≤ D.T, ∀ x m,
    Convex ℝ {p : (Fin d → ℝ) × ℝ | ∃ a, p.1 = D.b t x a ∧ p.2 ≤ D.f t x m a}

/-- A family `(Bⁱ)_{i ∈ ι}` of independent `d₀`-dimensional `𝔽`-Brownian motions: each `Bⁱ` is
a standard Brownian motion (`Peng1990.SMP.IsStdBrownian`), the `Bⁱ` are mutually independent,
every `Bⁱ_t` is `𝓕_t`-measurable, and the joint increment `(Bⁱ_t − Bⁱ_s)_i` is independent of
`𝓕_s` for `s ≤ t`. For `ι` a singleton this is one `𝔽`-Brownian motion (§3.2, p.8); for
`ι = Fin n` it is "`B¹, …, Bⁿ` independent `d₀`-dimensional Brownian motions" (§3.1, p.7). -/
def IsFBMFamily {Ω : Type*} [mΩ : MeasurableSpace Ω] {ι : Type*} {d₀ : ℕ}
    (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (B : ι → ℝ≥0 → Ω → Fin d₀ → ℝ) : Prop :=
  (∀ i, Peng1990.SMP.IsStdBrownian P (B i)) ∧
  iIndepFun (fun i (ω : Ω) (t : ℝ≥0) => B i t ω) P ∧
  (∀ i t, Measurable[𝓕 t] (B i t)) ∧
  ∀ s t : ℝ≥0, s ≤ t →
    Indep (𝓕 s) (MeasurableSpace.comap (fun ω i => B i t ω - B i s ω) inferInstance) P

/-- `𝒜_U` (§3.2, p.8): measurable controls `α : [0, T] × [0, 1] × ℝᵈ → A`.

**Formalization Note** Controls are defined on `ℝ≥0 × ℝ × ℝᵈ`; only `t ∈ [0, T]` and
`u ∈ [0, 1]` enter. -/
def IsUControl {d : ℕ} {A : Type*} [MeasurableSpace A]
    (α : ℝ≥0 → ℝ → (Fin d → ℝ) → A) : Prop :=
  Measurable (fun p : ℝ≥0 × ℝ × (Fin d → ℝ) => α p.1 p.2.1 p.2.2)

/-- `𝒜₁` (§3.2, p.8; §5, p.21): measurable controls `α : [0, T] × ℝᵈ → A`. -/
def IsOneControl {d : ℕ} {A : Type*} [MeasurableSpace A]
    (α : ℝ≥0 → (Fin d → ℝ) → A) : Prop :=
  Measurable (fun p : ℝ≥0 × (Fin d → ℝ) => α p.1 p.2)

/-- `𝒜_n` (§3.1, p.7): measurable controls `β : [0, T] × (ℝᵈ)ⁿ → A`. -/
def IsNControl {d n : ℕ} {A : Type*} [MeasurableSpace A]
    (β : ℝ≥0 → (Fin n → Fin d → ℝ) → A) : Prop :=
  Measurable (fun p : ℝ≥0 × (Fin n → Fin d → ℝ) => β p.1 p.2)

/-- A solution of the graphon-game state equation (3.4), p.8, under a control `α`, with initial
law `λ` of `(U, X₀)`: a filtered probability space with an `𝔽`-Brownian motion `B`, an
`𝓕₀`-measurable label `U` and a continuous adapted state `X` with `(U, X₀) ∼ λ`, such that for
every `t ∈ [0, T]`, almost surely,
`Xₜ = X₀ + ∫₀ᵗ b(s, Xₛ, α(s, U, Xₛ)) ds + ∫₀ᵗ σ(s, Xₛ) dBₛ`
(componentwise; the stochastic integrals are Itô integrals in the sense of
`Peng1990.SMP.IsItoIntegral`).

**Formalization Note** "The unique solution" is encoded as a relation: statements quantify over
all solutions (they exist and are unique in law under the standing assumptions, [49] cited
p.8). `X` is measurable as a path-valued map (automatic for continuous adapted processes). -/
structure GSol {d d₀ : ℕ} {A : Type*} (D : Data d d₀ A)
    (α : ℝ≥0 → ℝ → (Fin d → ℝ) → A) (lam : Measure (ℝ × (Fin d → ℝ))) where
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  P : Measure Ω
  [isProb : IsProbabilityMeasure P]
  𝓕 : Filtration ℝ≥0 mΩ
  B : ℝ≥0 → Ω → Fin d₀ → ℝ
  hB : IsFBMFamily 𝓕 P (fun _ : Unit => B)
  U : Ω → ℝ
  X : Ω → Path d D.T
  measX : Measurable X
  measU : Measurable[𝓕 0] U
  adaptedX : ∀ t : ℝ≥0, Measurable[𝓕 t] (fun ω => pathAt (X ω) t)
  law0 : P.map (fun ω => (U ω, pathAt (X ω) 0)) = lam
  J : Fin d → Fin d₀ → ℝ≥0 → Ω → ℝ
  ito : ∀ j k, Peng1990.SMP.IsItoIntegral 𝓕 P D.T (fun s ω => B s ω k)
    (fun s ω => D.σ (min s D.T) (pathAt (X ω) s) j k) (J j k)
  eqn : ∀ t ≤ D.T, ∀ᵐ ω ∂P, ∀ j,
    pathAt (X ω) t j = pathAt (X ω) 0 j
      + (∫ s in Icc (0 : ℝ) t,
          D.b s.toNNReal (pathAt (X ω) s.toNNReal)
            (α s.toNNReal (U ω) (pathAt (X ω) s.toNNReal)) j)
      + ∑ k, J j k t ω

attribute [instance] GSol.mΩ GSol.isProb

/-- The graphon-game objective (p.8) on a solution `S` of (3.4), for a measure flow `μ·`:
`J_W(μ·, α) = E[∫₀ᵀ f(t, Xₜ, 𝐖μₜ(U), α(t, U, Xₜ)) dt + g(X_T, 𝐖μ_T(U))]`. -/
noncomputable def GSol.payoff {d d₀ : ℕ} {A : Type*} {D : Data d d₀ A}
    {α : ℝ≥0 → ℝ → (Fin d → ℝ) → A} {lam : Measure (ℝ × (Fin d → ℝ))} (S : GSol D α lam)
    (W : ℝ → ℝ → ℝ) (μ : ℝ≥0 → ProbabilityMeasure (ℝ × (Fin d → ℝ))) : ℝ :=
  ∫ ω, ((∫ s in Icc (0 : ℝ) D.T,
      D.f s.toNNReal (pathAt (S.X ω) s.toNNReal)
        (Wop W (μ s.toNNReal : Measure (ℝ × (Fin d → ℝ))) (S.U ω))
        (α s.toNNReal (S.U ω) (pathAt (S.X ω) s.toNNReal)))
    + D.g (pathAt (S.X ω) D.T) (Wop W (μ D.T : Measure (ℝ × (Fin d → ℝ))) (S.U ω))) ∂S.P

/-- A measure flow `μ· ∈ C([0, T]; P_Unif([0, 1] × ℝᵈ))` (p.8): continuous on `[0, T]` in the
weak topology, each `μₜ` with uniform first marginal. -/
def IsUnifFlow {d : ℕ} (T : ℝ≥0) (μ : ℝ≥0 → ProbabilityMeasure (ℝ × (Fin d → ℝ))) : Prop :=
  ContinuousOn μ (Iic T) ∧ ∀ t ≤ T, IsUnifFirst (μ t : Measure (ℝ × (Fin d → ℝ)))

/-- `μ·` is a (Markovian) `W`-equilibrium with equilibrium control `α*` (Definition 3.1, p.8):
`α* ∈ 𝒜_U`, `μ·` is a continuous `P_Unif`-valued flow, some solution `S*` of (3.4) under `α*`
has `μₜ = L(U, Xₜ)` for all `t ∈ [0, T]`, and `J_W(μ·, α*) = sup_{α ∈ 𝒜_U} J_W(μ·, α)`, i.e.
`J_W(S) ≤ J_W(S*)` for every `α ∈ 𝒜_U` and every solution `S` of (3.4) under `α`. -/
def IsWEquilibrium {d d₀ : ℕ} {A : Type*} [MeasurableSpace A] (D : Data d d₀ A)
    (W : ℝ → ℝ → ℝ) (lam : Measure (ℝ × (Fin d → ℝ)))
    (μ : ℝ≥0 → ProbabilityMeasure (ℝ × (Fin d → ℝ))) (αs : ℝ≥0 → ℝ → (Fin d → ℝ) → A) :
    Prop :=
  IsUControl αs ∧ IsUnifFlow D.T μ ∧
    ∃ Ss : GSol D αs lam,
      (∀ t ≤ D.T, Ss.P.map (fun ω => (Ss.U ω, pathAt (Ss.X ω) t)) =
        (μ t : Measure (ℝ × (Fin d → ℝ)))) ∧
      ∀ α, IsUControl α → ∀ S : GSol D α lam, S.payoff W μ ≤ Ss.payoff W μ

/-- The initial law `λ(du, dx) = du λᵤ(dx)` built from a version `κ : u ↦ λᵤ` of its
disintegration (p.4, p.11): `λ = Unif[0, 1] ⊗ κ`. -/
noncomputable def lamOf {d : ℕ} (κ : Kernel ℝ (Fin d → ℝ)) : Measure (ℝ × (Fin d → ℝ)) :=
  lebUnit ⊗ₘ κ

/-- A solution of the `n`-player state system (§3.1, p.7; (7.1)–(7.2), p.32) under the control
profile `α = (α₁, …, αₙ)`, with labels `uⁿ` and initial states `X^{n,i}_0 ∼ λ_{uᵢ}` drawn
independently (§3.4, p.10–11): a filtered probability space with independent `d₀`-dimensional
`𝔽`-Brownian motions `B¹, …, Bⁿ`, continuous adapted states with independent `𝓕₀`-measurable
initial values of laws `κ(uᵢ)`, and, for every `t ∈ [0, T]`, almost surely, for every `i`,
`X^i_t = X^i_0 + ∫₀ᵗ b(s, X^i_s, αᵢ(s, X_s)) ds + ∫₀ᵗ σ(s, X^i_s) dBⁱ_s`.

**Formalization Note** As for `GSol`, "the unique solution" is a relation. The version `κ` of
`u ↦ λᵤ` is fixed (p.11: "This definition makes sense only if we prespecify a version"). -/
structure NSol {d d₀ : ℕ} {A : Type*} (D : Data d d₀ A) (n : ℕ)
    (α : Fin n → ℝ≥0 → (Fin n → Fin d → ℝ) → A) (κ : Kernel ℝ (Fin d → ℝ))
    (u : Fin n → ℝ) where
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  P : Measure Ω
  [isProb : IsProbabilityMeasure P]
  𝓕 : Filtration ℝ≥0 mΩ
  B : Fin n → ℝ≥0 → Ω → Fin d₀ → ℝ
  hB : IsFBMFamily 𝓕 P B
  X : Ω → Fin n → Path d D.T
  measX : Measurable X
  adaptedX : ∀ i (t : ℝ≥0), Measurable[𝓕 t] (fun ω => pathAt (X ω i) t)
  law0 : ∀ i, P.map (fun ω => pathAt (X ω i) 0) = κ (u i)
  indep0 : iIndepFun (fun i ω => pathAt (X ω i) 0) P
  J : Fin n → Fin d → Fin d₀ → ℝ≥0 → Ω → ℝ
  ito : ∀ i j k, Peng1990.SMP.IsItoIntegral 𝓕 P D.T (fun s ω => B i s ω k)
    (fun s ω => D.σ (min s D.T) (pathAt (X ω i) s) j k) (J i j k)
  eqn : ∀ t ≤ D.T, ∀ᵐ ω ∂P, ∀ i j,
    pathAt (X ω i) t j = pathAt (X ω i) 0 j
      + (∫ s in Icc (0 : ℝ) t,
          D.b s.toNNReal (pathAt (X ω i) s.toNNReal)
            (α i s.toNNReal (fun k => pathAt (X ω k) s.toNNReal)) j)
      + ∑ k, J i j k t ω

attribute [instance] NSol.mΩ NSol.isProb

/-- Player `i`'s expected reward on an `n`-player solution `S` when the measure argument of
`f, g` at time `t` is `M(t, Xₜ)`:
`E[∫₀ᵀ f(t, X^i_t, M(t, Xₜ), αᵢ(t, Xₜ)) dt + g(X^i_T, M(T, X_T))]`, `αᵢ` the control `S` is
solved for. With `M = M^{n,i}` (3.2) this is `Jᵢ(α)` of (3.3), p.7; with `M ≡ 𝐖μₜ(uᵢ)` it is
the limiting reward appearing in `Δ^{n,i}_{1,2,3}` (p.33). -/
noncomputable def NSol.payoffM {d d₀ : ℕ} {A : Type*} {D : Data d d₀ A} {n : ℕ}
    {α : Fin n → ℝ≥0 → (Fin n → Fin d → ℝ) → A} {κ : Kernel ℝ (Fin d → ℝ)} {u : Fin n → ℝ}
    (S : NSol D n α κ u) (i : Fin n)
    (M : ℝ≥0 → (Fin n → Fin d → ℝ) → FiniteMeasure (Fin d → ℝ)) : ℝ :=
  ∫ ω, ((∫ s in Icc (0 : ℝ) D.T,
      D.f s.toNNReal (pathAt (S.X ω i) s.toNNReal)
        (M s.toNNReal (fun k => pathAt (S.X ω k) s.toNNReal))
        (α i s.toNNReal (fun k => pathAt (S.X ω k) s.toNNReal)))
    + D.g (pathAt (S.X ω i) D.T) (M D.T (fun k => pathAt (S.X ω k) D.T))) ∂S.P

/-- The neighborhood empirical measure flow `M^{n,i}_t = (1/n) Σⱼ ξᵢⱼ δ_{X^j_t}` of (3.2), p.7
((7.3), p.32), as a function of the state vector. -/
noncomputable def nbhdFlow {d n : ℕ} (ξ : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    ℝ≥0 → (Fin n → Fin d → ℝ) → FiniteMeasure (Fin d → ℝ) :=
  fun _ x => nbhdEmp ξ x i

/-- The limiting measure flow `t ↦ 𝐖μₜ(uᵢ)` substituted for `M^{n,i}_t` in `Δ^{n,i}` (p.33). -/
noncomputable def limitFlow {d n : ℕ} (W : ℝ → ℝ → ℝ)
    (μ : ℝ≥0 → ProbabilityMeasure (ℝ × (Fin d → ℝ))) (u : Fin n → ℝ) (i : Fin n) :
    ℝ≥0 → (Fin n → Fin d → ℝ) → FiniteMeasure (Fin d → ℝ) :=
  fun t _ => Wop W (μ t : Measure (ℝ × (Fin d → ℝ))) (u i)

/-- The profile (3.8), p.10: player `i` uses `α^{n,uᵢ}_i(t, x₁, …, xₙ) := α*(t, uᵢ, xᵢ)`. -/
def labelProfile {d n : ℕ} {A : Type*} (αs : ℝ≥0 → ℝ → (Fin d → ℝ) → A) (u : Fin n → ℝ) :
    Fin n → ℝ≥0 → (Fin n → Fin d → ℝ) → A :=
  fun i t x => αs t (u i) (x i)

/-- The error `εⁿᵢ(uⁿ) := sup_{β ∈ 𝒜ₙ} Jᵢ(α^{n,uⁿ}_{-i}, β) − Jᵢ(α^{n,uⁿ}) ∈ [0, ∞)` (p.11),
with the initial states drawn from the version `κ`.

**Formalization Note** Valued in `ℝ≥0∞`: the supremum runs over `β ∈ 𝒜ₙ`, over solutions `S'`
of the system in which player `i` uses `β`, and over solutions `S` of the undeviated system, of
`(Jᵢ(S') − Jᵢ(S))⁺`. Taking `β = αᵢ`, `S' = S` shows the printed difference is nonnegative, so
the positive part changes nothing when a solution exists (which the standing assumptions
guarantee). -/
noncomputable def eps {d d₀ : ℕ} {A : Type*} [MeasurableSpace A] (D : Data d d₀ A) {n : ℕ}
    (ξ : Matrix (Fin n) (Fin n) ℝ) (αs : ℝ≥0 → ℝ → (Fin d → ℝ) → A)
    (κ : Kernel ℝ (Fin d → ℝ)) (u : Fin n → ℝ) (i : Fin n) : ℝ≥0∞ :=
  ⨆ (β : ℝ≥0 → (Fin n → Fin d → ℝ) → A) (_ : IsNControl β)
    (S' : NSol D n (Function.update (labelProfile αs u) i β) κ u)
    (S : NSol D n (labelProfile αs u) κ u),
    ENNReal.ofReal (S'.payoffM i (nbhdFlow ξ i) - S.payoffM i (nbhdFlow ξ i))

/-- `Δ^{n,i}_1(β, uⁿ)` (p.33) on a solution `S'` of the system where player `i` deviates to `β`:
reward with the true `M^{n,uⁿ,i}` minus reward with the limiting `𝐖μₜ(uᵢ)`. -/
noncomputable def delta1 {d d₀ : ℕ} {A : Type*} {D : Data d d₀ A} {n : ℕ}
    {α : Fin n → ℝ≥0 → (Fin n → Fin d → ℝ) → A} {κ : Kernel ℝ (Fin d → ℝ)} {u : Fin n → ℝ}
    (W : ℝ → ℝ → ℝ) (μ : ℝ≥0 → ProbabilityMeasure (ℝ × (Fin d → ℝ)))
    (ξ : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (S' : NSol D n α κ u) : ℝ :=
  S'.payoffM i (nbhdFlow ξ i) - S'.payoffM i (limitFlow W μ u i)

/-- `Δ^{n,i}_2(β, uⁿ)` (p.33): limiting reward of the deviating player `i` (solution `S'`)
minus limiting reward of player `i` under `α*` (solution `S` of the undeviated system). -/
noncomputable def delta2 {d d₀ : ℕ} {A : Type*} {D : Data d d₀ A} {n : ℕ}
    {α α' : Fin n → ℝ≥0 → (Fin n → Fin d → ℝ) → A} {κ : Kernel ℝ (Fin d → ℝ)}
    {u : Fin n → ℝ} (W : ℝ → ℝ → ℝ) (μ : ℝ≥0 → ProbabilityMeasure (ℝ × (Fin d → ℝ)))
    (i : Fin n) (S' : NSol D n α' κ u) (S : NSol D n α κ u) : ℝ :=
  S'.payoffM i (limitFlow W μ u i) - S.payoffM i (limitFlow W μ u i)

/-- `Δ^{n,i}_3(uⁿ)` (p.33) on a solution `S` of the undeviated system: reward with the limiting
`𝐖μₜ(uᵢ)` minus reward with the true `M^{n,uⁿ,i}`. -/
noncomputable def delta3 {d d₀ : ℕ} {A : Type*} {D : Data d d₀ A} {n : ℕ}
    {α : Fin n → ℝ≥0 → (Fin n → Fin d → ℝ) → A} {κ : Kernel ℝ (Fin d → ℝ)} {u : Fin n → ℝ}
    (W : ℝ → ℝ → ℝ) (μ : ℝ≥0 → ProbabilityMeasure (ℝ × (Fin d → ℝ)))
    (ξ : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (S : NSol D n α κ u) : ℝ :=
  S.payoffM i (limitFlow W μ u i) - S.payoffM i (nbhdFlow ξ i)

end GraphonLabelGame


