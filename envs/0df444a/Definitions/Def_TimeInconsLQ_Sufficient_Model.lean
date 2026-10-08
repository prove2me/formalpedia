-- Prove2me | Definitions.Def_TimeInconsLQ_Sufficient_Model
-- name    : TimeInconsLQ_Sufficient_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:07.013675+00:00
-- url     : https://prove2.me/theorems/caae0a36-2a93-45bb-9e00-6a8a997dde47
-- title:
--   §2 — the time-inconsistent stochastic LQ problem (2.1)–(2.4): data, standing assumptions, states, conditional cost, spike, open-loop equilibrium (Definition 2.1)
-- statement:
--   This file sets up the time-inconsistent stochastic linear–quadratic (LQ) control problem of Hu, Jin and Zhou.
--
--   **Data.** Fix a horizon $T>0$ and a probability space $(\Omega,\mathcal F,\mathbb P)$ carrying a standard $d$-dimensional Brownian motion $W=(W^1,\dots,W^d)$, with the filtration $(\mathcal F_t)$ it generates. The state lives in $\mathbb R^n$ and the control in $\mathbb R^l$. The coefficients are a deterministic matrix function $A_s\in\mathbb R^{n\times n}$, processes $B_s\in\mathbb R^{l\times n}$, $C^j_s\in\mathbb R^{n\times n}$, $D^j_s\in\mathbb R^{n\times l}$, $b_s,\sigma^j_s\in\mathbb R^n$, weights $Q_s\in\mathbb S^n$, $R_s\in\mathbb S^l$, and constants $G,h\in\mathbb S^n$, $\mu_1\in\mathbb R^{n\times n}$, $\mu_2\in\mathbb R^n$, together with an initial state $x_0\in\mathbb R^n$.
--
--   **Standing assumptions** (pp. 3–4). $A$ is measurable and bounded on $[0,T]$; $B,C^j,D^j,Q,R$ are progressively measurable and essentially bounded on $[0,T]\times\Omega$; $b,\sigma^j\in L^2_{\mathcal F}(0,T;\mathbb R^n)$; $Q$ and $R$ take symmetric values, and $Q\succeq0$, $R\succeq0$ for $ds\otimes d\mathbb P$-almost every $(s,\omega)$; $G$ and $h$ are symmetric and $G\succeq0$. No sign condition is imposed on $h$, and $\mu_1$ is arbitrary.
--
--   **Controls and states.** A control is a process $u\in L^2_{\mathcal F}(0,T;\mathbb R^l)$. Its state is a solution of
--
--   $$dX_s=[A_sX_s+B_s'u_s+b_s]\,ds+\sum_{j=1}^d[C^j_sX_s+D^j_su_s+\sigma^j_s]\,dW^j_s,\qquad X_0=x_0.\qquad(2.1)$$
--
--   **Cost.** For $t\in[0,T)$, an $\mathcal F_t$-measurable $x_t$ and a control $u$ with state $X$, writing $\mathbb E_t[\cdot]=\mathbb E[\cdot\mid\mathcal F_t]$,
--
--   $$J(t,x_t;u)=\tfrac12\mathbb E_t\!\int_t^T\big[\langle Q_sX_s,X_s\rangle+\langle R_su_s,u_s\rangle\big]ds+\tfrac12\mathbb E_t\langle GX_T,X_T\rangle-\tfrac12\langle h\,\mathbb E_t[X_T],\mathbb E_t[X_T]\rangle-\langle\mu_1x_t+\mu_2,\mathbb E_t[X_T]\rangle.\qquad(2.3)$$
--
--   The last two terms make the problem time-inconsistent.
--
--   **Spike variation** (2.4). For a control $u^*$, $t\in[0,T)$, $\varepsilon>0$ and $v\in L^2_{\mathcal F_t}(\Omega;\mathbb R^l)$, $u^{t,\varepsilon,v}_s=u^*_s+v\,\mathbf 1_{s\in[t,t+\varepsilon)}$.
--
--   **Equilibrium** (Definition 2.1). An admissible $u^*$ with state $X^*$ is an **equilibrium** if for every $t\in[0,T)$ and every $v\in L^2_{\mathcal F_t}(\Omega;\mathbb R^l)$
--
--   $$\liminf_{\varepsilon\downarrow0}\frac{J(t,X^*_t;u^{t,\varepsilon,v})-J(t,X^*_t;u^*)}{\varepsilon}\ge0\quad\text{a.s.}$$
--
--   These objects are shared by every statement of the mission; its goal (Theorem 3.2) gives a sufficient condition for $u^*$ to be an equilibrium.
--
--   **Formalization Note.** Stochastic integrals, SDE solutions, $L^2_{\mathcal F}$ and the Brownian motion are those of the published definition `Peng1990_SMP_Stochastic`. The filtration is the natural (uncompleted) filtration of $W$, not its augmentation; conditional expectations agree a.s. and every augmented-progressive process agrees $ds\otimes d\mathbb P$-a.e. with a natural-progressive one, so no statement changes. The paper's state $X^{t,x_t,u}$ from time $t$ (2.2) is encoded through the full horizon: the state of the control equal to $u^*$ on $[0,t)$ and to $u$ on $[t,T]$, which by pathwise uniqueness coincides with it on $[t,T]$; the spike already has this form. $\mathbb E_t$ of a vector is taken componentwise. Every conditional expectation in $J$ is applied to an integrable variable (bounded coefficients, $u\in L^2$, $\sup_{s\le T}\mathbb E|X_s|^2<\infty$), so Lean's junk value $0$ for non-integrable functions never arises. The paper writes $\lim_{\varepsilon\downarrow0}\dots\ge0$; the limit need not exist when $R$ is merely bounded measurable, and the proof of Theorem 3.2 only bounds the quotient from below, so the definition uses the lower limit, taken in $\overline{\mathbb R}$ (EReal) so that a sequence unbounded below gives $-\infty$, not a junk value. Because $J$ is defined only up to null sets, "$\varepsilon\downarrow0$, a.s." is read along every sequence $\varepsilon_k\downarrow0$, almost surely for each sequence, for every state $X^*$ of $u^*$ and every choice of states of the perturbed controls. "Essentially bounded" and "a.s., a.e." are read $ds\otimes d\mathbb P$-a.e. on $[0,T]\times\Omega$; norms of matrices are entrywise sup norms (equivalent to the paper's Frobenius norm for boundedness). The paper calls $B,C^j,D^j$ (and $Q,R$) "adapted"; they are taken progressively measurable, the standard reading needed for the time integrals in (2.1) and (2.3) and the convention of $L^2_{\mathcal F}$ in `Peng1990_SMP_Stochastic`. Progressive measurability, and the measurability of the deterministic $A$ (which the paper uses implicitly), are required on all of $\mathbb R_{\ge0}$; values after $T$ enter no object, so this restricts nothing.
-- source:
--   Hu, Jin, Zhou, Time-Inconsistent Stochastic Linear–Quadratic Control, arXiv:1111.0818v1, pp. 2–4, (2.1)–(2.4), Definition 2.1

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic

namespace TimeInconsLQ.Sufficient

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

/-- §2, (2.1)–(2.3): the data of the time-inconsistent stochastic LQ problem. `W` is a standard
`d`-dimensional Brownian motion on `(Ω, P)`, `T > 0` the horizon, `x₀ ∈ ℝⁿ` the initial state.
`A` is deterministic (`n × n`); `B` is `l × n` and enters the drift as `Bᵀ u`; `C j` is `n × n`,
`D j` is `n × l`; `b, σ j` are `ℝⁿ`-valued; `Q` (`n × n`) and `R` (`l × l`) weight the running
cost; `G, h, μ₁` are constant `n × n` matrices and `μ₂ ∈ ℝⁿ`. -/
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

variable {Ω : Type*} [MeasurableSpace Ω] {n l d : ℕ}

/-- The filtration `(𝓕ₜ)`: the natural (uncompleted) filtration of the Brownian motion `W`. -/
noncomputable def filt (M : Data Ω n l d) : Filtration ℝ≥0 ‹MeasurableSpace Ω› :=
  Peng1990.SMP.brownianFiltration M.hW

/-- A process is essentially bounded on `[0, T] × Ω`: for some constant `K`,
`‖f(s, ω)‖ ≤ K` for `ds ⊗ dP`-almost every `(s, ω) ∈ [0, T] × Ω`. -/
def EssBounded {E : Type*} [Norm E] (M : Data Ω n l d) (f : ℝ≥0 → Ω → E) : Prop :=
  ∃ K : ℝ, ∀ᵐ q ∂((volume.restrict (Set.Icc (0 : ℝ) M.T)).prod M.P), ‖f q.1.toNNReal q.2‖ ≤ K

/-- The standing assumptions of §2 (pp. 3–4): `P` is a probability measure; `A` is measurable and
bounded on `[0, T]`; `B, Cʲ, Dʲ, Q, R` are progressively measurable and essentially bounded;
`b, σʲ ∈ L²_𝓕(0, T; ℝⁿ)`; `Q, R` take symmetric values and `Q ⪰ 0`, `R ⪰ 0` `ds ⊗ dP`-a.e.;
`G, h` are symmetric and `G ⪰ 0` (`h` is not assumed semidefinite, `μ₁` is arbitrary). -/
structure Standing (M : Data Ω n l d) : Prop where
  prob : IsProbabilityMeasure M.P
  A_meas : Measurable (fun s => Matrix.of.symm (M.A s))
  A_bdd : ∃ K : ℝ, ∀ s ≤ M.T, ‖Matrix.of.symm (M.A s)‖ ≤ K
  B_prog : IsStronglyProgressive (filt M) M.B
  C_prog : ∀ j, IsStronglyProgressive (filt M) (M.C j)
  D_prog : ∀ j, IsStronglyProgressive (filt M) (M.D j)
  Q_prog : IsStronglyProgressive (filt M) M.Q
  R_prog : IsStronglyProgressive (filt M) M.R
  B_bdd : EssBounded M (fun s ω => Matrix.of.symm (M.B s ω))
  C_bdd : ∀ j, EssBounded M (fun s ω => Matrix.of.symm (M.C j s ω))
  D_bdd : ∀ j, EssBounded M (fun s ω => Matrix.of.symm (M.D j s ω))
  Q_bdd : EssBounded M (fun s ω => Matrix.of.symm (M.Q s ω))
  R_bdd : EssBounded M (fun s ω => Matrix.of.symm (M.R s ω))
  b_L2 : Peng1990.SMP.L2F (filt M) M.P M.T M.b
  σ_L2 : ∀ j, Peng1990.SMP.L2F (filt M) M.P M.T (M.σ j)
  Q_symm : ∀ s ≤ M.T, ∀ ω, (M.Q s ω).IsSymm
  R_symm : ∀ s ≤ M.T, ∀ ω, (M.R s ω).IsSymm
  Q_psd : ∀ᵐ q ∂((volume.restrict (Set.Icc (0 : ℝ) M.T)).prod M.P),
    (M.Q q.1.toNNReal q.2).PosSemidef
  R_psd : ∀ᵐ q ∂((volume.restrict (Set.Icc (0 : ℝ) M.T)).prod M.P),
    (M.R q.1.toNNReal q.2).PosSemidef
  G_symm : M.G.IsSymm
  h_symm : M.h.IsSymm
  G_psd : M.G.PosSemidef

/-- Admissible controls: `u ∈ L²_𝓕(0, T; ℝˡ)`. -/
def Admissible (M : Data Ω n l d) (u : ℝ≥0 → Ω → Fin l → ℝ) : Prop :=
  Peng1990.SMP.L2F (filt M) M.P M.T u

/-- `X` is a state process of the control `u`: it solves the state equation (2.1) on `[0, T]`,
`dX = [A X + Bᵀ u + b] ds + Σⱼ [Cʲ X + Dʲ u + σʲ] dWʲ`, `X₀ = x₀`. -/
def IsState (M : Data Ω n l d) (u : ℝ≥0 → Ω → Fin l → ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  Peng1990.SMP.SolvesSDE (filt M) M.P M.T M.W M.x₀
    (fun s ω x => M.A s *ᵥ x + (M.B s ω)ᵀ *ᵥ u s ω + M.b s ω)
    (fun j s ω x => M.C j s ω *ᵥ x + M.D j s ω *ᵥ u s ω + M.σ j s ω) X

/-- The componentwise conditional expectation `E_t[Y] = E[Y | 𝓕ₜ]` of a vector random variable. -/
noncomputable def condVec {ι : Type*} (M : Data Ω n l d) (t : ℝ≥0) (Y : Ω → ι → ℝ) :
    Ω → ι → ℝ :=
  fun ω i => condExp (filt M t) M.P (fun ω' => Y ω' i) ω

/-- The spike variation (2.4): `u^{t,ε,v}_s = u_s + v 1_{s ∈ [t, t+ε)}`. -/
noncomputable def spike (u : ℝ≥0 → Ω → Fin l → ℝ) (t : ℝ≥0) (ε : ℝ) (v : Ω → Fin l → ℝ) :
    ℝ≥0 → Ω → Fin l → ℝ :=
  fun s ω => u s ω + if t ≤ s ∧ (s : ℝ) < (t : ℝ) + ε then v ω else 0

/-- The conditional cost (2.3), `J(t, x_t; u)` evaluated along the state `X` of `u`:
`½ E_t ∫ₜᵀ [⟨Q X, X⟩ + ⟨R u, u⟩] ds + ½ E_t ⟨G X_T, X_T⟩ − ½ ⟨h E_t X_T, E_t X_T⟩
 − ⟨μ₁ x_t + μ₂, E_t X_T⟩`. -/
noncomputable def cost (M : Data Ω n l d) (t : ℝ≥0) (xt : Ω → Fin n → ℝ)
    (u : ℝ≥0 → Ω → Fin l → ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ) : Ω → ℝ :=
  fun ω =>
    (1 / 2 : ℝ) * condExp (filt M t) M.P (fun ω' => ∫ s in Set.Icc (t : ℝ) M.T,
        ((M.Q s.toNNReal ω' *ᵥ X s.toNNReal ω') ⬝ᵥ X s.toNNReal ω'
          + (M.R s.toNNReal ω' *ᵥ u s.toNNReal ω') ⬝ᵥ u s.toNNReal ω')) ω
    + (1 / 2 : ℝ) * condExp (filt M t) M.P (fun ω' => (M.G *ᵥ X M.T ω') ⬝ᵥ X M.T ω') ω
    - (1 / 2 : ℝ) * ((M.h *ᵥ condVec M t (X M.T) ω) ⬝ᵥ condVec M t (X M.T) ω)
    - (M.μ₁ *ᵥ xt ω + M.μ₂) ⬝ᵥ condVec M t (X M.T) ω

/-- Definition 2.1 (open-loop equilibrium). `u` is admissible, has a state process, and for every
state `X` of `u`, every `t ∈ [0, T)`, every `v ∈ L²_{𝓕ₜ}(Ω; ℝˡ)`, every sequence `εₖ ↓ 0` and every
choice of states `Xεₖ` of the spike variations `u^{t,εₖ,v}`, almost surely
`liminf_k [J(t, X_t; u^{t,εₖ,v}) − J(t, X_t; u)] / εₖ ≥ 0` (lower limit in `EReal`). -/
def IsEquilibrium (M : Data Ω n l d) (u : ℝ≥0 → Ω → Fin l → ℝ) : Prop :=
  Admissible M u ∧ (∃ X, IsState M u X) ∧
    ∀ X : ℝ≥0 → Ω → Fin n → ℝ, IsState M u X →
      ∀ t : ℝ≥0, t < M.T →
        ∀ v : Ω → Fin l → ℝ, StronglyMeasurable[filt M t] v →
          ∫⁻ ω, ‖v ω‖ₑ ^ 2 ∂M.P < ⊤ →
          ∀ εs : ℕ → ℝ, (∀ k, 0 < εs k) → Tendsto εs atTop (𝓝 0) →
            ∀ Xε : ℕ → ℝ≥0 → Ω → Fin n → ℝ, (∀ k, IsState M (spike u t (εs k) v) (Xε k)) →
              ∀ᵐ ω ∂M.P, 0 ≤ Filter.liminf (fun k =>
                (((cost M t (X t) (spike u t (εs k) v) (Xε k) ω - cost M t (X t) u X ω)
                  / εs k : ℝ) : EReal)) atTop

end TimeInconsLQ.Sufficient


