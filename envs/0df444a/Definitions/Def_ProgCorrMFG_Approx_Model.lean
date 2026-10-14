-- Prove2me | Definitions.Def_ProgCorrMFG_Approx_Model
-- name    : ProgCorrMFG_Approx_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:17:47.06109+00:00
-- url     : https://prove2.me/theorems/761913ea-1ab6-4bb2-abfc-8e66f79d26b1
-- title:
--   §2, (A1)–(A3), pp. 2–4, 9, 15 — the finite model: $\mathcal P(\mathcal X)$, dist, $\Psi$, $f$, $F$, assumptions, restricted and progressive strategies
-- statement:
--   This file sets up the data of the discrete-time, finite-state mean field game of Bonesini, Campi and Fischer.
--
--   **Spaces.** The time frame is $[\![0,T]\!]$ for a horizon $T\in\mathbb N$. The individual states lie in a finite nonempty set $\mathcal X$ and the actions in a finite nonempty set $\Gamma$, both with the discrete topology and σ-algebra. The noise space is $\mathcal Z=[0,1]$ with the uniform distribution $\nu$. The set $\mathcal P(\mathcal X)$ of probability measures on $\mathcal X$ carries the metric
--   $$\mathrm{dist}(\mu,\tilde\mu)=\frac12\sum_{x\in\mathcal X}|\mu(x)-\tilde\mu(x)|,$$
--   and a flow of measures is a vector $m=(m_t)_{t=0}^T\in\mathcal P(\mathcal X)^{T+1}$. For two flows, $\mathrm{dist}_T(\lambda,\lambda')=\sum_{t=0}^T\mathrm{dist}(\lambda_t,\lambda'_t)$.
--
--   **Model data.** A model consists of a system function $\Psi:[\![0,T-1]\!]\times\mathcal X\times\mathcal P(\mathcal X)\times\Gamma\times\mathcal Z\to\mathcal X$, a running cost $f:[\![0,T-1]\!]\times\mathcal X\times\mathcal P(\mathcal X)\times\Gamma\to\mathbb R$ and a terminal cost $F:\mathcal X\times\mathcal P(\mathcal X)\to\mathbb R$. The state of a player moves by $X_{t+1}=\Psi(t,X_t,\mu_t,u_t,\xi_{t+1})$.
--
--   **Assumptions.**
--   1. (A1) For all $t,x,m,u,y$: $\mathbb P(\Psi(t,x,m,u,Z)=y)>0$ for $Z\sim\nu$.
--   2. (A2) 1) There is a non-decreasing $w:[0,\infty)\to[0,1]$ with $w(s)\to0$ as $s\to0^+$ such that $\nu(\{z:\Psi(t,x,m,\gamma,z)\neq\Psi(t,x,\tilde m,\gamma,z)\})\le w(\mathrm{dist}(m,\tilde m))$; 2) for every $t$ and every probability measure $\tau$ on $\mathcal X\times\mathcal P(\mathcal X)\times\Gamma$, $\Psi(t,\cdot)$ is continuous at $\tau\otimes\nu$-almost every point.
--   3. (A3) $f$ and $F$ are Lipschitz with a common constant $L$.
--
--   **Strategies.** A restricted strategy is a map $\varphi:[\![0,T-1]\!]\times\mathcal X\to\Gamma$; their set is $\mathcal R$. A progressive feedback strategy $\varphi\in\widehat{\mathcal R}$ assigns to each time $t$ a Borel map $(x,m)\mapsto\varphi(t,x^{(t)},m^{(t)})\in\Gamma$ that depends only on the histories $x^{(t)}=(x_0,\dots,x_t)$ and $m^{(t)}=(m_0,\dots,m_t)$. Every restricted strategy is progressive through $\varphi\mapsto((t,x,m)\mapsto\varphi(t,x_t))$; this inclusion is the identity modification $\iota$ of Remark 4.2. The joint measurability of $\Psi$ and the measurability and boundedness of the costs are recorded as two further conditions.
--
--   **Formalization Note** $\mathcal P(\mathcal X)$ is the standard simplex `stdSimplex ℝ X` with the subspace topology and Borel σ-algebra of $\mathbb R^{\mathcal X}$; $\nu$ is `volume` on `unitInterval`. Times of actions and noises are `Fin T` (the noise $\xi_{t+1}$ has index $t$), times of states and flows are `Fin (T+1)`. A progressive strategy is stored as a function of the full state path and flow, constrained to be non-anticipative (`NonAnt`) and jointly measurable at each time. Because $\mathcal X$ and $\Gamma$ are discrete, continuity of $\Psi(t,\cdot)$ at $(x,m,\gamma,z)$ is written as local constancy of $\Psi(t,x,\cdot,\gamma,\cdot)$ near $(m,z)$. (A3) is stated in the measure argument, which is equivalent since time, $\mathcal X$ and $\Gamma$ are finite with the discrete metric. The modulus of (A2) is named `ω`.
-- source:
--   Bonesini, Campi & Fischer, Correlated Equilibria for Mean Field Games with Progressive Strategies, arXiv:2212.01656v1, pp. 2–4 (§2), p. 7 (Remark 4.2), p. 9 (A1), p. 15 (A2), (A3); dist_T as used on p. 21

import Mathlib

namespace ProgCorrMFG.Approx

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

/-- `𝒫(𝒳)` (§2, p. 3): the probability measures on the finite set `X`, represented as the standard
simplex `{p : X → ℝ | p ≥ 0, ∑ₓ p x = 1}`. It carries the subspace topology and the Borel σ-algebra
of `X → ℝ`; on the simplex these are the topology and σ-algebra of weak convergence (equivalently,
of `dist` below). -/
abbrev Meas (X : Type) [Fintype X] : Type := ↥(stdSimplex ℝ X)

/-- The metric `dist(μ, μ̃) := ½ ∑_{e ∈ E} |μ(e) − μ̃(e)|` on `𝒫(E)` (§2, p. 3). -/
noncomputable def distTV {X : Type} [Fintype X] (μ μ' : Meas X) : ℝ :=
  (1 / 2 : ℝ) * ∑ x, |(μ : X → ℝ) x - (μ' : X → ℝ) x|

/-- Flows of measures `m = (m_t)_{t=0}^T ∈ 𝒫(𝒳)^{T+1}`. -/
abbrev Flow (T : ℕ) (X : Type) [Fintype X] : Type := Fin (T + 1) → Meas X

/-- `dist_T(λ, λ') := ∑_{t=0}^T dist(λ_t, λ'_t)` on `𝒫(𝒳)^{T+1}` (used in the proof of Claim 6.4,
p. 21). -/
noncomputable def distT {T : ℕ} {X : Type} [Fintype X] (l l' : Flow T X) : ℝ :=
  ∑ t, distTV (l t) (l' t)

/-- The set `ℛ = {φ : ⟦0, T−1⟧ × 𝒳 → Γ}` of restricted strategies (§2, p. 3); time `t` is
`t : Fin T`. -/
abbrev Strat (T : ℕ) (X G : Type) : Type := Fin T → X → G

/-- The history `m^{(t+1)} = (m_0, …, m_{t+1})` of a `(T+1)`-vector, for `t ∈ ⟦0, T−1⟧`. -/
def histSucc {T : ℕ} {α : Type} (m : Fin (T + 1) → α) (t : Fin T) : Fin (t.1 + 2) → α :=
  fun s => m ⟨s.1, by have := s.2; have := t.2; omega⟩

/-- The model data of §2 (p. 3): the system function `Ψ : ⟦0,T−1⟧ × 𝒳 × 𝒫(𝒳) × Γ × 𝒵 → 𝒳`
(noise space `𝒵 = [0,1]`), the running cost `f : ⟦0,T−1⟧ × 𝒳 × 𝒫(𝒳) × Γ → ℝ` and the terminal
cost `F : 𝒳 × 𝒫(𝒳) → ℝ`. -/
structure Model (T : ℕ) (X G : Type) [Fintype X] where
  Ψ : Fin T → X → Meas X → G → I → X
  f : Fin T → X → Meas X → G → ℝ
  F : X → Meas X → ℝ

namespace Model

variable {T : ℕ} {X G : Type} [Fintype X] [MeasurableSpace X] [MeasurableSpace G]

/-- Joint Borel measurability of `Ψ(t, ·)` on `𝒳 × 𝒫(𝒳) × Γ × 𝒵`, for each `t`. Not stated in the
paper; it is needed for the states of a realization to be random variables. -/
def PsiMeasurable (M : Model T X G) : Prop :=
  ∀ t, Measurable (fun p : X × Meas X × G × I => M.Ψ t p.1 p.2.1 p.2.2.1 p.2.2.2)

/-- Assumption (A1) (p. 9): for all `t, m, x, y, u`, `ℙ(Ψ(t, x, m, u, Z) = y) > 0` for `Z ∼ ν`
uniform on `[0,1]`. -/
def A1 (M : Model T X G) : Prop :=
  ∀ (t : Fin T) (x : X) (m : Meas X) (u : G) (y : X),
    0 < (volume : Measure I) {z | M.Ψ t x m u z = y}

/-- Assumption (A2) (p. 15).
1) there is a non-decreasing `ω : [0,∞) → [0,1]` with `ω(s) → 0` as `s → 0⁺` such that
`ν{z : Ψ(t,x,m,γ,z) ≠ Ψ(t,x,m̃,γ,z)} ≤ ω(dist(m, m̃))`;
2) for every `t` and every probability measure `τ` on `𝒳 × 𝒫(𝒳) × Γ`, `Ψ(t, ·)` is continuous at
`τ ⊗ ν`-a.e. point of `𝒳 × 𝒫(𝒳) × Γ × 𝒵`. Since `𝒳`, `Γ` are discrete, continuity at `(x, m, γ, z)`
means that `Ψ(t, x, ·, γ, ·)` is constant on a neighbourhood of `(m, z)`. -/
def A2 (M : Model T X G) : Prop :=
  (∃ ω : ℝ → ℝ, MonotoneOn ω (Set.Ici 0) ∧ (∀ s, 0 ≤ s → 0 ≤ ω s ∧ ω s ≤ 1) ∧
      Tendsto ω (𝓝[>] 0) (𝓝 0) ∧
      ∀ (t : Fin T) (x : X) (g : G) (m m' : Meas X),
        (volume : Measure I) {z | M.Ψ t x m g z ≠ M.Ψ t x m' g z} ≤ ENNReal.ofReal (ω (distTV m m'))) ∧
  (∀ (t : Fin T) (τ : Measure (X × Meas X × G)), IsProbabilityMeasure τ →
      ∀ᵐ p ∂(τ.prod (volume : Measure I)),
        ∀ᶠ q in 𝓝 (p.1.2.1, p.2), M.Ψ t p.1.1 q.1 p.1.2.2 q.2 = M.Ψ t p.1.1 p.1.2.1 p.1.2.2 p.2)

/-- Assumption (A3) (p. 15): `f` and `F` are Lipschitz with one constant `L`. As `𝒳`, `Γ` and time
are finite with the discrete metric, this is stated in the measure argument, with respect to `dist`. -/
def A3 (M : Model T X G) : Prop :=
  ∃ L : ℝ, (∀ (t : Fin T) (x : X) (g : G) (m m' : Meas X),
      |M.f t x m g - M.f t x m' g| ≤ L * distTV m m') ∧
    ∀ (x : X) (m m' : Meas X), |M.F x m - M.F x m'| ≤ L * distTV m m'

/-- The costs are Borel measurable and bounded in the measure argument: the standing convention
under which the expected costs (3.3), (4.2), (5.3) are well defined. Implied by (A3). -/
def CostsRegular (M : Model T X G) : Prop :=
  (∀ (t : Fin T) (x : X) (g : G), Measurable (fun m : Meas X => M.f t x m g)) ∧
  (∀ x : X, Measurable (fun m : Meas X => M.F x m)) ∧
  ∃ C : ℝ, (∀ t x m g, |M.f t x m g| ≤ C) ∧ ∀ x m, |M.F x m| ≤ C

end Model

/-- Non-anticipativity at time `t`: `g(x, m)` depends only on the histories `x^{(t)}`, `m^{(t)}`. -/
def NonAnt {T : ℕ} {α β γ : Type} (t : Fin T) (g : (Fin (T + 1) → α) → (Fin (T + 1) → β) → γ) : Prop :=
  ∀ x x' m m', (∀ s : Fin (T + 1), s ≤ t.castSucc → x s = x' s ∧ m s = m' s) → g x m = g x' m'

/-- The time-`t` component `ℰ̂_t` of a progressive feedback strategy of the mean field game: a
Borel map `(x, m) ↦ φ(t, x^{(t)}, m^{(t)}) ∈ Γ` of state path and flow that depends only on the
histories up to `t`. -/
def Comp (T : ℕ) (X G : Type) [Fintype X] [MeasurableSpace X] [MeasurableSpace G] (t : Fin T) : Type :=
  {g : (Fin (T + 1) → X) → Flow T X → G //
    NonAnt t g ∧ Measurable (fun p : (Fin (T + 1) → X) × Flow T X => g p.1 p.2)}

/-- `ℛ̂` (p. 3): progressive feedback strategies, `φ(t, ·)` a Borel function of
`(x^{(t)}, m^{(t)})`, for `t ∈ ⟦0, T−1⟧`. -/
abbrev Prog (T : ℕ) (X G : Type) [Fintype X] [MeasurableSpace X] [MeasurableSpace G] : Type :=
  (t : Fin T) → Comp T X G t

/-- The inclusion `ℛ ⊂ ℛ̂`, which is also the identity modification `ι ∈ 𝒟̂` of Remark 4.2:
`ι ∘ φ(t, x^{(t)}, m^{(t)}) = φ(t, x_t)`. -/
def iotaMFG {T : ℕ} {X G : Type} [Fintype X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [MeasurableSpace G] (φ : Strat T X G) : Prog T X G :=
  fun t => ⟨fun x _ => φ t (x t.castSucc),
    fun x x' m m' h => by simp only [(h t.castSucc le_rfl).1],
    (Measurable.of_discrete (f := φ t)).comp ((measurable_pi_apply t.castSucc).comp measurable_fst)⟩

end ProgCorrMFG.Approx


