-- Prove2me | Definitions.Def_MFGLiquidation_Nash_Players
-- name    : MFGLiquidation_Nash_Players
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:16.789871+00:00
-- url     : https://prove2.me/theorems/5f3bfaed-0cfa-4410-9524-df3e1483eeed
-- title:
--   The N-player liquidation game: players (W⁰, Wⁱ, 𝒳ⁱ), Assumption 3.1, the costs J^{N,i} of (1.4), the sets 𝒜ⁱ, and I₁, I₂
-- statement:
--   The $N$-player portfolio liquidation game of §1.2 (pp. 3–4) and §3.
--
--   **Players.** One probability space $(\Omega,\mathcal G,\mathbb P)$ carries a one-dimensional Brownian motion $W^0$ (common noise), for each player $i$ a $k=(m-1)$-dimensional Brownian motion $W^i$ (private noise) and an initial portfolio $\mathcal X^i$. Player $i$ uses the Brownian motion $\widetilde W^i=(W^0,W^i)$ and the filtration $\mathbb F^i$, $\mathcal F^i_t=\sigma(\mathcal X^i,W^0_s,W^i_s,\ s\le t)$ (1.6), augmented. The standing setting: $W^0$ and every coordinate of every $W^i$ are real Brownian motions; $W^0$, all coordinates of all $W^i$, and all $\mathcal X^i$ are mutually independent; the $\mathcal X^i$ are measurable with common law $\nu$.
--
--   **Assumption 3.1.** There are nonnegative, bounded, jointly measurable deterministic functionals $\kappa,\eta,\lambda$ such that
--   $$\kappa^i_t=\kappa(t,\mathcal X^i,W^i_{\cdot\wedge t},W^0_{\cdot\wedge t}),\quad \eta^i_t=\eta(t,\mathcal X^i,W^i_{\cdot\wedge t},W^0_{\cdot\wedge t}),\quad \lambda^i_t=\lambda(t,\mathcal X^i,W^i_{\cdot\wedge t},W^0_{\cdot\wedge t}).$$
--   Player $i$'s single-player data is $(T,\widetilde W^i,\mathcal X^i,\kappa^i,\lambda^i,\eta^i)$.
--
--   **Costs (1.4).** For a strategy profile $\vec\xi=(\xi^1,\dots,\xi^N)$ and $X^i_t=\mathcal X^i-\int_0^t\xi^i_s\,ds$,
--   $$J^{N,i}(\vec\xi)=\mathbb E\Big[\int_0^T\Big(\frac{\kappa^i_t}{N}\sum_{j=1}^N\xi^j_tX^i_t+\eta^i_t(\xi^i_t)^2+\lambda^i_t(X^i_t)^2\Big)dt\ \Big|\ \mathcal X^i\Big].$$
--   Given a solution $(X^i,Y^i,Z^i)$ of (2.3) for player $i$'s data, $\xi^{*,i}_t=Y^i_t/(2\eta^i_t)$ is player $i$'s mean-field strategy (2.2).
--
--   **Admissible sets of Theorem 3.3.** For a positive function $M$,
--   $$\mathcal A^i=\Big\{\xi\in\mathcal A_{\mathbb F^i}(\mathcal X^i):\ \mathbb E\Big[\int_0^T|\xi_t|^2dt\ \Big|\ \mathcal X^i\Big]\le M(\mathcal X^i)\Big\}.$$
--
--   **The differences $I_1,I_2$** (proof of Theorem 3.3, p. 23), for player $i$, a deviation $\xi$ with state $X^\xi$, a process $\mu$ and $X^{*,i}=\mathcal X^i-\int_0^\cdot\xi^{*,i}$:
--   $$I_1=\mathbb E\Big[\int_0^T\Big(\kappa^i_t\Big(\frac1N\sum_{j\ne i}\xi^{*,j}_t+\frac1N\xi_t\Big)X^\xi_t+\eta^i_t\xi_t^2+\lambda^i_t(X^\xi_t)^2\Big)dt\,\Big|\,\mathcal X^i\Big]-\mathbb E\Big[\int_0^T\big(\kappa^i_t\mu_tX^\xi_t+\eta^i_t\xi_t^2+\lambda^i_t(X^\xi_t)^2\big)dt\,\Big|\,\mathcal X^i\Big],$$
--   $$I_2=\mathbb E\Big[\int_0^T\big(\kappa^i_t\mu_tX^{*,i}_t+\eta^i_t(\xi^{*,i}_t)^2+\lambda^i_t(X^{*,i}_t)^2\big)dt\,\Big|\,\mathcal X^i\Big]-\mathbb E\Big[\int_0^T\Big(\kappa^i_t\frac1N\sum_{j=1}^N\xi^{*,j}_tX^{*,i}_t+\eta^i_t(\xi^{*,i}_t)^2+\lambda^i_t(X^{*,i}_t)^2\Big)dt\,\Big|\,\mathcal X^i\Big].$$
--
--   These definitions carry the $N$-player game in which the paper's approximate Nash property (Theorem 3.3) is stated.
--
--   **Formalization Note.** Players are indexed by $\mathbb N$; the $N$-player game uses players $i<N$, the paper's $1,\dots,N$ shifted by one, and only $\xi^j$ with $j<N$ enter $J^{N,i}$. The mutual independence is stated for the family of random paths $(W^0,\ \text{constant path }\mathcal X^i,\ \text{coordinates of }W^i)$, each a random element of $\mathbb R^{\mathbb R_{\ge0}}$ with the product σ-algebra. The structure also records, as a field, that each player's data satisfies the single-player standing setting (a consequence of the other fields). Conditioning on $\mathcal X^i=x^i$ is encoded as conditioning on $\sigma(\mathcal X^i)$, so an a.s. statement is a statement for $\nu$-a.e. $x^i$. The measurability of the functionals is joint in $(t,x,w,w^0)$ for the product σ-algebras on the path spaces. $I_1$ and $I_2$ are written for a general player $i$ (the paper writes them for player 1).
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, pp. 3–4, §1.2, (1.4)–(1.6); p. 21, Assumption 3.1; p. 22, (3.1) and the set 𝒜ⁱ of Theorem 3.3; p. 23, I₁ + I₂ in the proof of Theorem 3.3

import Mathlib
import Definitions.Def_MFGLiquidation_Nash_Setting
import Definitions.Def_MFGLiquidation_Nash_Game

open MeasureTheory ProbabilityTheory Filter Topology Peng1990.SMP
open scoped ENNReal NNReal

namespace MFGLiquidation.Nash

/-- The population of the `N`-player liquidation game (§1.2, pp. 3–4, and Assumption 3.1), on a
single probability space carrying every player. Players are indexed by `ℕ`; the `N`-player game
uses players `i < N` (the paper's `1, …, N`, shifted by one).
* `W0` — the common one-dimensional noise `W⁰`;
* `Wp i` — player `i`'s private `k = (m − 1)`-dimensional noise `W^i`;
* `Xs i` — player `i`'s initial portfolio `𝒳^i`;
* `κf, ηf, lamf` — the deterministic functionals `κ, η, λ` of Assumption 3.1, evaluated at
  `(t, 𝒳^i, W^i_{·∧t}, W⁰_{·∧t})`. -/
structure Population (Ω : Type*) [MeasurableSpace Ω] (k : ℕ) where
  T : ℝ≥0
  W0 : ℝ≥0 → Ω → ℝ
  Wp : ℕ → ℝ≥0 → Ω → Fin k → ℝ
  Xs : ℕ → Ω → ℝ
  κf : ℝ≥0 → ℝ → (ℝ≥0 → Fin k → ℝ) → (ℝ≥0 → ℝ) → ℝ
  ηf : ℝ≥0 → ℝ → (ℝ≥0 → Fin k → ℝ) → (ℝ≥0 → ℝ) → ℝ
  lamf : ℝ≥0 → ℝ → (ℝ≥0 → Fin k → ℝ) → (ℝ≥0 → ℝ) → ℝ

namespace Population

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ}

/-- Player `i`'s Brownian motion `W̃^i = (W⁰, W^i)` (coordinate `0` is `W⁰`). -/
def Wt (Pop : Population Ω k) (i : ℕ) (t : ℝ≥0) (ω : Ω) : Fin (k + 1) → ℝ :=
  Fin.cons (Pop.W0 t ω) (Pop.Wp i t ω)

/-- Player `i`'s coefficient `f(t, 𝒳^i, W^i_{·∧t}, W⁰_{·∧t})` built from a functional `f`
(Assumption 3.1), with the stopped paths `s ↦ W^i_{s∧t}`, `s ↦ W⁰_{s∧t}`. -/
def coeff (Pop : Population Ω k)
    (f : ℝ≥0 → ℝ → (ℝ≥0 → Fin k → ℝ) → (ℝ≥0 → ℝ) → ℝ) (i : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  f t (Pop.Xs i ω) (fun s => Pop.Wp i (min s t) ω) (fun s => Pop.W0 (min s t) ω)

/-- Player `i`'s single-player data `(T, W̃^i, 𝒳^i, κ^i, λ^i, η^i)`. -/
def player (Pop : Population Ω k) (i : ℕ) : Data Ω k where
  T := Pop.T
  W := Pop.Wt i
  𝒳 := Pop.Xs i
  κ := Pop.coeff Pop.κf i
  lam := Pop.coeff Pop.lamf i
  η := Pop.coeff Pop.ηf i

/-- The primitive random elements, all as random paths `ℝ≥0 → ℝ`: `none ↦ W⁰`,
`inl i ↦` the constant path `𝒳^i`, `inr (i, j) ↦` the `j`-th coordinate of `W^i`. -/
def noise (Pop : Population Ω k) : Option (ℕ ⊕ (ℕ × Fin k)) → Ω → ℝ≥0 → ℝ
  | none => fun ω t => Pop.W0 t ω
  | some (Sum.inl i) => fun ω _ => Pop.Xs i ω
  | some (Sum.inr (i, j)) => fun ω t => Pop.Wp i t ω j

/-- The probabilistic setting of the `N`-player game (p. 3): `T > 0`; `W⁰` and every coordinate
of every `W^i` are real Brownian motions; `W⁰`, the coordinates of the `W^i` and the `𝒳^i` are
mutually independent; the `𝒳^i` are measurable with common law `ν`. The last field records the
consequence that each player's data satisfies the single-player standing setting. -/
structure Standing (Pop : Population Ω k) (P : Measure Ω) (ν : Measure ℝ) : Prop where
  T_pos : 0 < Pop.T
  W0_meas : ∀ t, Measurable (Pop.W0 t)
  Wp_meas : ∀ i t, Measurable (Pop.Wp i t)
  W0_brownian : IsBrownianReal Pop.W0 P
  Wp_brownian : ∀ i (j : Fin k), IsBrownianReal (fun t ω => Pop.Wp i t ω j) P
  Xs_meas : ∀ i, Measurable (Pop.Xs i)
  Xs_law : ∀ i, P.map (Pop.Xs i) = ν
  indep : iIndepFun Pop.noise P
  player : ∀ i, (Pop.player i).Standing P

/-- Assumption 3.1: `κ, η, λ` are nonnegative, bounded and jointly measurable deterministic
functionals of `(t, x, w, w⁰)` (product σ-algebras on the path spaces). -/
structure Assumption31 (Pop : Population Ω k) : Prop where
  κf_meas : Measurable fun p : ℝ≥0 × ℝ × (ℝ≥0 → Fin k → ℝ) × (ℝ≥0 → ℝ) =>
    Pop.κf p.1 p.2.1 p.2.2.1 p.2.2.2
  ηf_meas : Measurable fun p : ℝ≥0 × ℝ × (ℝ≥0 → Fin k → ℝ) × (ℝ≥0 → ℝ) =>
    Pop.ηf p.1 p.2.1 p.2.2.1 p.2.2.2
  lamf_meas : Measurable fun p : ℝ≥0 × ℝ × (ℝ≥0 → Fin k → ℝ) × (ℝ≥0 → ℝ) =>
    Pop.lamf p.1 p.2.1 p.2.2.1 p.2.2.2
  κf_bdd : ∃ c : ℝ, ∀ t x w w0, 0 ≤ Pop.κf t x w w0 ∧ Pop.κf t x w w0 ≤ c
  ηf_bdd : ∃ c : ℝ, ∀ t x w w0, 0 ≤ Pop.ηf t x w w0 ∧ Pop.ηf t x w w0 ≤ c
  lamf_bdd : ∃ c : ℝ, ∀ t x w w0, 0 ≤ Pop.lamf t x w w0 ∧ Pop.lamf t x w w0 ≤ c

/-- `ξ^{*,i}_t = Y^i_t / (2 η^i_t)`, player `i`'s optimal control (2.2) built from a solution
`(X^i, Y^i, Z^i)` of the FBSDE (2.3) for player `i`'s data. -/
noncomputable def xiStar (Pop : Population Ω k) (Yp : ℕ → ℝ≥0 → Ω → ℝ) (i : ℕ) (t : ℝ≥0)
    (ω : Ω) : ℝ :=
  Yp i t ω / (2 * (Pop.player i).η t ω)

/-- Player `i`'s conditional cost (1.4) in the `N`-player game, for a strategy profile
`ξs` (only `ξs j`, `j < N`, enter):
`J^{N,i}(ξ⃗) = E[∫_0^T (κ^i_t (1/N) Σ_{j<N} ξ^j_t X^i_t + η^i_t (ξ^i_t)² + λ^i_t (X^i_t)²) dt | 𝒳^i]`,
with `X^i = 𝒳^i − ∫_0^· ξ^i`. -/
noncomputable def costN (Pop : Population Ω k) (P : Measure Ω) (N i : ℕ)
    (ξs : ℕ → ℝ≥0 → Ω → ℝ) : Ω → ℝ :=
  P[fun ω => ∫ s in Set.Icc (0 : ℝ) Pop.T,
      ((Pop.player i).κ s.toNNReal ω * ((1 / (N : ℝ)) * ∑ j ∈ Finset.range N, ξs j s.toNNReal ω)
          * stateOf (Pop.player i) (ξs i) s.toNNReal ω
        + (Pop.player i).η s.toNNReal ω * ξs i s.toNNReal ω ^ 2
        + (Pop.player i).lam s.toNNReal ω * stateOf (Pop.player i) (ξs i) s.toNNReal ω ^ 2)
    | MeasurableSpace.comap (Pop.Xs i) inferInstance]

/-- Player `i`'s admissible set `𝒜^i` of Theorem 3.3: `ξ ∈ 𝒜_{𝔽^i}(𝒳^i)` and
`E[∫_0^T |ξ_t|² dt | 𝒳^i] ≤ M(𝒳^i)` a.s. -/
def AdmN {Pop : Population Ω k} {P : Measure Ω} {ν : Measure ℝ} (hstd : Pop.Standing P ν)
    (M : ℝ → ℝ) (i : ℕ) (ξ : ℝ≥0 → Ω → ℝ) : Prop :=
  IsAdmissible (hstd.player i) ξ ∧
    P[fun ω => ∫ s in Set.Icc (0 : ℝ) Pop.T, ξ s.toNNReal ω ^ 2
      | MeasurableSpace.comap (Pop.Xs i) inferInstance] ≤ᵐ[P] fun ω => M (Pop.Xs i ω)

/-- `I₁` of the proof of Theorem 3.3 (p. 23), for player `i` deviating to `ξ`:
the conditional cost with the others' average `(1/N)(Σ_{j ≠ i} ξ^{*,j} + ξ)` minus the
conditional cost with the mean-field term `μ`, both along `X^ξ`. -/
noncomputable def I1 (Pop : Population Ω k) (P : Measure Ω) (N i : ℕ) (μ : ℝ≥0 → Ω → ℝ)
    (Yp : ℕ → ℝ≥0 → Ω → ℝ) (ξ : ℝ≥0 → Ω → ℝ) : Ω → ℝ :=
  P[fun ω => ∫ s in Set.Icc (0 : ℝ) Pop.T,
      ((Pop.player i).κ s.toNNReal ω
          * ((1 / (N : ℝ)) * ∑ j ∈ (Finset.range N).erase i, Pop.xiStar Yp j s.toNNReal ω
            + (1 / (N : ℝ)) * ξ s.toNNReal ω)
          * stateOf (Pop.player i) ξ s.toNNReal ω
        + (Pop.player i).η s.toNNReal ω * ξ s.toNNReal ω ^ 2
        + (Pop.player i).lam s.toNNReal ω * stateOf (Pop.player i) ξ s.toNNReal ω ^ 2)
    | MeasurableSpace.comap (Pop.Xs i) inferInstance]
  - P[fun ω => ∫ s in Set.Icc (0 : ℝ) Pop.T,
      ((Pop.player i).κ s.toNNReal ω * μ s.toNNReal ω * stateOf (Pop.player i) ξ s.toNNReal ω
        + (Pop.player i).η s.toNNReal ω * ξ s.toNNReal ω ^ 2
        + (Pop.player i).lam s.toNNReal ω * stateOf (Pop.player i) ξ s.toNNReal ω ^ 2)
    | MeasurableSpace.comap (Pop.Xs i) inferInstance]

/-- `I₂` of the proof of Theorem 3.3 (p. 23), for player `i`: the conditional cost of
`ξ^{*,i}` with the mean-field term `μ` minus its conditional cost with the empirical average
`(1/N) Σ_{j<N} ξ^{*,j}`, both along `X^{*,i} = 𝒳^i − ∫_0^· ξ^{*,i}`. -/
noncomputable def I2 (Pop : Population Ω k) (P : Measure Ω) (N i : ℕ) (μ : ℝ≥0 → Ω → ℝ)
    (Yp : ℕ → ℝ≥0 → Ω → ℝ) : Ω → ℝ :=
  P[fun ω => ∫ s in Set.Icc (0 : ℝ) Pop.T,
      ((Pop.player i).κ s.toNNReal ω * μ s.toNNReal ω
          * stateOf (Pop.player i) (Pop.xiStar Yp i) s.toNNReal ω
        + (Pop.player i).η s.toNNReal ω * Pop.xiStar Yp i s.toNNReal ω ^ 2
        + (Pop.player i).lam s.toNNReal ω
          * stateOf (Pop.player i) (Pop.xiStar Yp i) s.toNNReal ω ^ 2)
    | MeasurableSpace.comap (Pop.Xs i) inferInstance]
  - P[fun ω => ∫ s in Set.Icc (0 : ℝ) Pop.T,
      ((Pop.player i).κ s.toNNReal ω
          * ((1 / (N : ℝ)) * ∑ j ∈ Finset.range N, Pop.xiStar Yp j s.toNNReal ω)
          * stateOf (Pop.player i) (Pop.xiStar Yp i) s.toNNReal ω
        + (Pop.player i).η s.toNNReal ω * Pop.xiStar Yp i s.toNNReal ω ^ 2
        + (Pop.player i).lam s.toNNReal ω
          * stateOf (Pop.player i) (Pop.xiStar Yp i) s.toNNReal ω ^ 2)
    | MeasurableSpace.comap (Pop.Xs i) inferInstance]

end Population

end MFGLiquidation.Nash


