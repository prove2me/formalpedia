-- Prove2me | Definitions.Def_TimeInconsLQ_MeanVariance_Model
-- name    : TimeInconsLQ_MeanVariance_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T13:22:08.487674+00:00
-- url     : https://prove2.me/theorems/630f5dd4-2be9-4505-bc0a-10c1006b6667
-- title:
--   §2 — the time-inconsistent stochastic LQ problem (2.1)–(2.4): data, standing assumptions, states, conditional cost, spike, open-loop equilibrium (Definition 2.1)
-- statement:
--   This module sets up the time-inconsistent stochastic linear–quadratic (LQ) problem of Hu, Jin and Zhou, §2.
--
--   **Data.** Fix integers $n,l,d\ge0$ (state, control and noise dimensions), a horizon $T>0$, and a probability space $(\Omega,\mathcal F,P)$ carrying a standard $d$-dimensional Brownian motion $W=(W^1,\dots,W^d)$ with its filtration $(\mathcal F_t)$. The coefficients are a deterministic $A:[0,T]\to\mathbb R^{n\times n}$; processes $B$ ($l\times n$), $C^j$ ($n\times n$), $D^j$ ($n\times l$), $b,\sigma^j$ ($\mathbb R^n$), $Q$ ($n\times n$), $R$ ($l\times l$); and constants $G,h,\mu_1\in\mathbb R^{n\times n}$, $\mu_2\in\mathbb R^n$, $x_0\in\mathbb R^n$.
--
--   **Standing assumptions** (pp. 3–4). $A$ is measurable and bounded on $[0,T]$; $B,C^j,D^j,Q,R$ are progressively measurable and essentially bounded on $[0,T]\times\Omega$; $b,\sigma^j\in L^2_{\mathcal F}(0,T;\mathbb R^n)$; $Q$ and $R$ are symmetric with $Q\succeq0$, $R\succeq0$ for $ds\otimes dP$-a.e. $(s,\omega)$; $G,h$ are symmetric and $G\succeq0$ ($h$ is not assumed semidefinite, and $\mu_1$ is arbitrary).
--
--   **States and controls.** A control is $u\in L^2_{\mathcal F}(0,T;\mathbb R^l)$. Its state process solves (2.1)
--   $$dX_s=[A_sX_s+B_s'u_s+b_s]\,ds+\sum_{j=1}^d[C^j_sX_s+D^j_su_s+\sigma^j_s]\,dW^j_s,\qquad X_0=x_0 .$$
--
--   **Cost** (2.3). For $t\in[0,T)$, an $\mathcal F_t$-measurable $x_t$ and a control $u$ with state $X$, with $E_t=E[\,\cdot\,|\mathcal F_t]$,
--   $$J(t,x_t;u)=\tfrac12E_t\!\int_t^T\!\big(\langle Q_sX_s,X_s\rangle+\langle R_su_s,u_s\rangle\big)ds+\tfrac12E_t\langle GX_T,X_T\rangle-\tfrac12\langle hE_t[X_T],E_t[X_T]\rangle-\langle\mu_1x_t+\mu_2,E_t[X_T]\rangle .$$
--
--   **Spike** (2.4): for $t\in[0,T)$, $\varepsilon>0$ and $v\in L^2_{\mathcal F_t}(\Omega;\mathbb R^l)$, $u^{t,\varepsilon,v}_s=u_s+v\,\mathbf 1_{s\in[t,t+\varepsilon)}$.
--
--   **Equilibrium** (Definition 2.1). An admissible $u^*$ with state $X^*$ is an *equilibrium* if for every $t\in[0,T)$ and $v\in L^2_{\mathcal F_t}(\Omega;\mathbb R^l)$
--   $$\liminf_{\varepsilon\downarrow0}\frac{J(t,X^*_t;u^{t,\varepsilon,v})-J(t,X^*_t;u^*)}{\varepsilon}\ge0\quad\text{a.s.}$$
--
--   **Closed loop** ($n=1$). For processes $\alpha,\beta$ with values in $\mathbb R^l$, $X$ is a *closed-loop solution* if it is a state process of the feedback control $u_s=\alpha_sX_s+\beta_s$.
--
--   These objects are shared by every statement of the mission; the mean–variance problem of §5 is the instance $n=1$ defined in the module `Market`.
--
--   **Formalization Note.** Stochastic integrals, SDEs and $L^2_{\mathcal F}$ are those of the published definition `Peng1990_SMP_Stochastic`. The filtration is the natural, uncompleted filtration of $W$; the paper uses its augmentation, but conditional expectations agree a.s. and every augmented-progressive process agrees $ds\otimes dP$-a.e. with a natural-progressive one, so no statement changes. The state from time $t$, $X^{t,X^*_t,u}$ of (2.2), is encoded through the full horizon: as the solution of (2.1) from $x_0$ for the control equal to $u^*$ on $[0,t)$ (the spike has this form); by pathwise uniqueness both agree on $[t,T]$. The paper writes $\lim_{\varepsilon\downarrow0}$; the limit need not exist, and the definition is stated with the lower limit (in $\overline{\mathbb R}$), along every sequence $\varepsilon_k\downarrow0$, almost surely for each sequence, for every state process of $u^*$ and of the spiked controls — a reading independent of the versions Lean picks for conditional expectations. "a.s., a.e." is read $ds\otimes dP$-a.e.; essential boundedness of matrices is entrywise. Every integrand in $J$ is integrable for an admissible control and its state, so the Lean conditional expectations are never junk.
-- source:
--   Hu, Jin, Zhou, Time-Inconsistent Stochastic Linear–Quadratic Control, arXiv:1111.0818v1, pp. 2–4, (2.1)–(2.4), Definition 2.1; closed-loop form as in (4.4) p. 9 and (5.14) p. 20

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_TimeInconsLQ_Sufficient_Model

namespace TimeInconsLQ.MeanVariance

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

/-- §2, (2.1)–(2.3): the data of the time-inconsistent stochastic LQ problem. A probability space
carrying a standard `d`-dimensional Brownian motion `W`, a horizon `T > 0`, an initial state
`x₀ ∈ ℝⁿ`; the deterministic drift matrix `A`; the random coefficients `B` (`l × n`, entering the
drift as `B′u`), `Cʲ` (`n × n`), `Dʲ` (`n × l`), `b`, `σʲ` (`ℝⁿ`); the running weights `Q`, `R`;
and the constants `G`, `h`, `μ₁` (`n × n`) and `μ₂ ∈ ℝⁿ` of the cost (2.3). -/
structure Data (Ω : Type*) [MeasurableSpace Ω] (n l d : ℕ) where
  P : Measure Ω
  W : ℝ≥0 → Ω → Fin d → ℝ
  hW : Peng1990.SMP.IsStdBrownian P W
  T : ℝ≥0
  hT : 0 < T
  x₀ : Fin n → ℝ
  A : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ
  B : ℝ≥0 → Ω → Matrix (Fin l) (Fin n) ℝ
  C : Fin d → ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ
  D : Fin d → ℝ≥0 → Ω → Matrix (Fin n) (Fin l) ℝ
  b : ℝ≥0 → Ω → Fin n → ℝ
  σ : Fin d → ℝ≥0 → Ω → Fin n → ℝ
  Q : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ
  R : ℝ≥0 → Ω → Matrix (Fin l) (Fin l) ℝ
  G : Matrix (Fin n) (Fin n) ℝ
  h : Matrix (Fin n) (Fin n) ℝ
  μ₁ : Matrix (Fin n) (Fin n) ℝ
  μ₂ : Fin n → ℝ

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A real process `φ` is essentially bounded on `[0, T] × Ω`: there is `K` with `|φ(s, ω)| ≤ K`
for `ds ⊗ dP`-almost every `(s, ω) ∈ [0, T] × Ω`. -/
def EssBddOn (P : Measure Ω) (T : ℝ≥0) (φ : ℝ≥0 → Ω → ℝ) : Prop :=
  ∃ K : ℝ, ∀ᵐ q ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod P), |φ q.1.toNNReal q.2| ≤ K

namespace Data

variable {n l d : ℕ} (M : Data Ω n l d)

/-- The filtration of the problem: the natural filtration of `W` (Peng's `brownianFiltration`). -/
noncomputable def filt : Filtration ℝ≥0 mΩ := Peng1990.SMP.brownianFiltration M.hW

/-- Standing assumptions of §2 (pp. 3–4): `P` is a probability measure; `A` is measurable and
bounded on `[0, T]`; `B, Cʲ, Dʲ, Q, R` are progressively measurable and essentially bounded on
`[0, T] × Ω` (entrywise); `b, σʲ ∈ L²_𝓕(0, T; ℝⁿ)`; `Q` and `R` are symmetric and positive
semidefinite `ds ⊗ dP`-a.e. on `[0, T] × Ω`; `G` and `h` are symmetric and `G ⪰ 0`. -/
structure Standing : Prop where
  prob : IsProbabilityMeasure M.P
  A_meas : ∀ i j, Measurable (fun s => M.A s i j)
  A_bdd : ∃ K : ℝ, ∀ s ≤ M.T, ∀ i j, |M.A s i j| ≤ K
  B_prog : IsStronglyProgressive M.filt M.B
  C_prog : ∀ j, IsStronglyProgressive M.filt (M.C j)
  D_prog : ∀ j, IsStronglyProgressive M.filt (M.D j)
  Q_prog : IsStronglyProgressive M.filt M.Q
  R_prog : IsStronglyProgressive M.filt M.R
  B_bdd : ∀ i j, EssBddOn M.P M.T (fun s ω => M.B s ω i j)
  C_bdd : ∀ k i j, EssBddOn M.P M.T (fun s ω => M.C k s ω i j)
  D_bdd : ∀ k i j, EssBddOn M.P M.T (fun s ω => M.D k s ω i j)
  Q_bdd : ∀ i j, EssBddOn M.P M.T (fun s ω => M.Q s ω i j)
  R_bdd : ∀ i j, EssBddOn M.P M.T (fun s ω => M.R s ω i j)
  b_L2 : Peng1990.SMP.L2F M.filt M.P M.T M.b
  σ_L2 : ∀ j, Peng1990.SMP.L2F M.filt M.P M.T (M.σ j)
  Q_psd : ∀ᵐ q ∂((volume.restrict (Set.Icc (0 : ℝ) M.T)).prod M.P),
    (M.Q q.1.toNNReal q.2).IsSymm ∧ (M.Q q.1.toNNReal q.2).PosSemidef
  R_psd : ∀ᵐ q ∂((volume.restrict (Set.Icc (0 : ℝ) M.T)).prod M.P),
    (M.R q.1.toNNReal q.2).IsSymm ∧ (M.R q.1.toNNReal q.2).PosSemidef
  G_symm : M.G.IsSymm
  h_symm : M.h.IsSymm
  G_psd : M.G.PosSemidef

/-- Admissible controls: `u ∈ L²_𝓕(0, T; ℝˡ)`. -/
def Admissible (u : ℝ≥0 → Ω → Fin l → ℝ) : Prop :=
  Peng1990.SMP.L2F M.filt M.P M.T u

/-- `X` is a state process of the control `u`: it solves (2.1),
`dX = [A X + B′u + b] ds + Σⱼ [Cʲ X + Dʲ u + σʲ] dWʲ`, `X₀ = x₀`, on `[0, T]`. -/
def IsState (u : ℝ≥0 → Ω → Fin l → ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  Peng1990.SMP.SolvesSDE M.filt M.P M.T M.W M.x₀
    (fun s ω x => M.A s *ᵥ x + (M.B s ω)ᵀ *ᵥ u s ω + M.b s ω)
    (fun j s ω x => M.C j s ω *ᵥ x + M.D j s ω *ᵥ u s ω + M.σ j s ω) X

/-- The componentwise conditional expectation `E_t[Y] = E[Y | 𝓕_t]` of an `ℝⁿ`-valued variable. -/
noncomputable def condVec (t : ℝ≥0) (Y : Ω → Fin n → ℝ) : Ω → Fin n → ℝ :=
  fun ω i => (M.P[fun ω' => Y ω' i | M.filt t]) ω

/-- The conditional cost (2.3) at time `t` with current state `x_t`, of the control `u` with state
process `X`:
`J(t, x_t; u) = ½ E_t ∫ₜᵀ (⟨Q X, X⟩ + ⟨R u, u⟩) ds + ½ E_t⟨G X_T, X_T⟩ − ½ ⟨h E_t X_T, E_t X_T⟩
  − ⟨μ₁ x_t + μ₂, E_t X_T⟩`. -/
noncomputable def cost (t : ℝ≥0) (xt : Ω → Fin n → ℝ) (u : ℝ≥0 → Ω → Fin l → ℝ)
    (X : ℝ≥0 → Ω → Fin n → ℝ) : Ω → ℝ :=
  fun ω =>
    (1 / 2) * (M.P[fun ω' => ∫ s in Set.Icc (t : ℝ) M.T,
        ((M.Q s.toNNReal ω' *ᵥ X s.toNNReal ω') ⬝ᵥ X s.toNNReal ω'
          + (M.R s.toNNReal ω' *ᵥ u s.toNNReal ω') ⬝ᵥ u s.toNNReal ω') | M.filt t]) ω
    + (1 / 2) * (M.P[fun ω' => (M.G *ᵥ X M.T ω') ⬝ᵥ X M.T ω' | M.filt t]) ω
    - (1 / 2) * ((M.h *ᵥ M.condVec t (X M.T) ω) ⬝ᵥ M.condVec t (X M.T) ω)
    - (M.μ₁ *ᵥ xt ω + M.μ₂) ⬝ᵥ M.condVec t (X M.T) ω

/-- Definition 2.1 (open-loop equilibrium). `u` is admissible, has a state process, and for every
state process `X` of `u`, every `t ∈ [0, T)`, every `v ∈ L²_{𝓕_t}(Ω; ℝˡ)`, every sequence
`εₖ ↓ 0` (`εₖ > 0`) and every choice of state processes `Xεₖ` of the spiked controls
`u^{t,εₖ,v}`, almost surely
`liminf_k [J(t, X_t; u^{t,εₖ,v}) − J(t, X_t; u)] / εₖ ≥ 0` (the lower limit taken in `EReal`). -/
def IsEquilibrium (u : ℝ≥0 → Ω → Fin l → ℝ) : Prop :=
  M.Admissible u ∧ (∃ X, M.IsState u X) ∧
  ∀ X, M.IsState u X → ∀ t : ℝ≥0, t < M.T →
    ∀ v : Ω → Fin l → ℝ, StronglyMeasurable[M.filt t] v → ∫⁻ ω, ‖v ω‖ₑ ^ 2 ∂M.P < ⊤ →
    ∀ εs : ℕ → ℝ, (∀ k, 0 < εs k) → Tendsto εs atTop (𝓝 0) →
    ∀ Xε : ℕ → ℝ≥0 → Ω → Fin n → ℝ, (∀ k, M.IsState (TimeInconsLQ.Sufficient.spike u t (εs k) v) (Xε k)) →
    ∀ᵐ ω ∂M.P, (0 : EReal) ≤ Filter.liminf (fun k =>
      (((M.cost t (X t) (TimeInconsLQ.Sufficient.spike u t (εs k) v) (Xε k) ω - M.cost t (X t) u X ω) / εs k : ℝ)
        : EReal)) atTop

end Data

/-- Closed-loop convention for `n = 1` (§4, §5): `X` solves the state equation (2.1) under the
linear feedback control `u_s = α_s X_s + β_s`. -/
def Data.IsClosedLoop {l d : ℕ} (M : Data Ω 1 l d) (α β : ℝ≥0 → Ω → Fin l → ℝ)
    (X : ℝ≥0 → Ω → Fin 1 → ℝ) : Prop :=
  M.IsState (fun s ω => X s ω 0 • α s ω + β s ω) X

end TimeInconsLQ.MeanVariance


