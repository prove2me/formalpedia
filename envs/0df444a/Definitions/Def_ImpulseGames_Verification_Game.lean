-- Prove2me | Definitions.Def_ImpulseGames_Verification_Game
-- name    : ImpulseGames_Verification_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T02:42:40.063508+00:00
-- url     : https://prove2.me/theorems/977fc70f-451a-42ab-8a18-2f810aef1eba
-- title:
--   Two-player impulse game: data of Section 2, strategies (Def. 2.1), controlled process (Def. 2.2), payoffs (2.6), $\Phi_x$ (Def. 2.5), Nash equilibrium (Def. 2.6)
-- statement:
--   This file sets up the general two-player nonzero-sum stochastic differential game with impulse controls of Aïd, Basei, Callegaro, Campi and Vargiolu (Section 2).
--
--   **Underlying diffusion.** Fix a probability space $(\Omega,\mathcal F,\mathbb P)$ with a filtration $\{\mathcal F_t\}_{t\ge0}$ satisfying the usual conditions (right-continuity and $\mathbb P$-completeness), and a $k$-dimensional $\{\mathcal F_t\}$-Brownian motion $W$: a standard Brownian motion with independent coordinates, adapted, with increments $W_t-W_s$ independent of $\mathcal F_s$. The coefficients $b:\mathbb R^d\to\mathbb R^d$ and $\sigma:\mathbb R^d\to\mathbb R^{d\times k}$ are globally Lipschitz. A process $Y$ **solves (2.1) from a random time $\tau$ with initial value $\zeta$** if its paths are continuous on $[\tau,\infty)$, $Y_s\mathbf 1_{\{\tau\le s\}}$ is $\mathcal F_s$-measurable, $Y_\tau=\zeta$ on $\{\tau<\infty\}$, and for each $s$, almost surely on $\{\tau\le s\}$,
--   $$
--   Y_s=\zeta+\int_0^s \mathbf 1_{\{u>\tau\}}\,b(Y_u)\,du+\int_0^s \mathbf 1_{\{u>\tau\}}\,\sigma(Y_u)\,dW_u ,
--   $$
--   the stochastic integrals being Itô integrals (limits of left-point sums of adapted step integrands).
--
--   **Game data.** Two players $i\in\{1,2\}$; $j$ denotes the opponent. $S\subseteq\mathbb R^d$ is open; $Z_i\subseteq\mathbb R^{l_i}$ is nonempty; $\Gamma^i:S\times Z_i\to S$ is continuous (an intervention with impulse $\delta$ moves the state from $y$ to $\Gamma^i(y,\delta)$); $\rho_i>0$; the running payoff $f_i$ is continuous on $S$, the terminal payoff $h_i$ continuous on $\partial S$, the intervention cost $\phi_i$ continuous on $S\times Z_i$ and the gain $\psi_i$ from the opponent's interventions continuous on $S\times Z_j$.
--
--   **Strategies (Definition 2.1).** A strategy for player $i$ is a pair $\varphi_i=(\mathcal C_i,\xi_i)$ with $\mathcal C_i\subseteq S$ open and $\xi_i:S\to Z_i$ continuous: player $i$ intervenes when the state leaves $\mathcal C_i$, with impulse $\xi_i(y)$ at the state $y$.
--
--   **Controlled process (Definition 2.2).** Given $x\in S$, set $\tilde\tau_0=0$, $x_0=x$, $\tilde X^0=Y^{0,x}$, $\alpha^S_0=\infty$, and for $k\ge1$, with $\alpha^O_k=\inf\{s>\tilde\tau_{k-1}:\tilde X^{k-1}_s\notin O\}$ ($\inf\emptyset=\infty$),
--   $$
--   \tilde\tau_k=\alpha^{\mathcal C_1}_k\wedge\alpha^{\mathcal C_2}_k,\quad m_k=\begin{cases}1,&\alpha^{\mathcal C_1}_k\le\alpha^{\mathcal C_2}_k\\2,&\text{otherwise}\end{cases},\quad x_k=\Gamma^{m_k}\big(\tilde X^{k-1}_{\tilde\tau_k},\xi_{m_k}(\tilde X^{k-1}_{\tilde\tau_k})\big)\mathbf 1_{\{\tilde\tau_k<\infty\}},
--   $$
--   $$
--   \tilde X^k=\tilde X^{k-1}\mathbf 1_{[0,\tilde\tau_k[}+Y^{\tilde\tau_k,x_k}\mathbf 1_{[\tilde\tau_k,\infty[},
--   $$
--   so player 1 has priority on ties. Let $\bar k\in\mathbb N\cup\{\infty\}$ be the largest $k$ with $\tilde\tau_h<\alpha^S_h$ for all $h\le k$. The construction is admissible only if the $\tilde\tau_k$ do not accumulate before the exit: on $\{\bar k=\infty\}$, $\lim_k\tilde\tau_k=\sup_k\alpha^S_k$. Then $X=\tilde X^{\bar k}$ (with $\tilde X^\infty=\lim_k\tilde X^k$), $\tau_S=\alpha^S_{\bar k+1}$ if $\bar k<\infty$ and $\tau_S=\sup_k\alpha^S_k$ otherwise. The $n$-th intervention of player $i$ is the $\eta(i,n)$-th intervention overall; it happens at $\tau_{i,n}=\tilde\tau_{\eta(i,n)}$ with impulse $\delta_{i,n}=\xi_i(X_{(\tau_{i,n})^-})$, where $X_{(\tau_{i,n})^-}=\tilde X^{\eta(i,n)-1}_{\tilde\tau_{\eta(i,n)}}$ is the state just before it; beyond the last one, $(\tau_{i,n},\delta_{i,n})=(\tau_S,0)$ as in (2.3). A **realization** is a family of diffusion pieces $Y^{\tilde\tau_k,x_k}$, each solving (2.1) from $(\tilde\tau_k,x_k)$ while the game is running.
--
--   **Payoffs (Definition 2.4).** With $e^{-\rho\cdot\infty}=0$,
--   $$
--   J^i(x;\varphi_1,\varphi_2)=\mathbb E\Big[\int_0^{\tau_S}e^{-\rho_is}f_i(X_s)\,ds+\sum_{\tau_{i,n}<\tau_S}e^{-\rho_i\tau_{i,n}}\phi_i(X_{(\tau_{i,n})^-},\delta_{i,n})+\sum_{\tau_{j,n}<\tau_S}e^{-\rho_i\tau_{j,n}}\psi_i(X_{(\tau_{j,n})^-},\delta_{j,n})+e^{-\rho_i\tau_S}h_i(X_{\tau_S})\mathbf 1_{\{\tau_S<\infty\}}\Big].
--   $$
--
--   **Admissible pairs (Definition 2.5).** $(\varphi_1,\varphi_2)\in\Phi_x$ if both are strategies and some realization satisfies: (2.7) the four random variables $\int_0^{\tau_S}e^{-\rho_is}|f_i|(X_s)ds$, $e^{-\rho_i\tau_S}|h_i|(X_{\tau_S})$, $\sum_{\tau_{i,n}<\tau_S}e^{-\rho_i\tau_{i,n}}|\phi_i|(X_{(\tau_{i,n})^-},\delta_{i,n})$ and $\sum_{\tau_{j,n}<\tau_S}e^{-\rho_i\tau_{j,n}}|\psi_i|(X_{(\tau_{j,n})^-},\delta_{j,n})$ are in $L^1$; (2.8) $\mathbb E[\|X\|_\infty^p]<\infty$ for all $p\in\mathbb N$, with $\|X\|_\infty=\sup_{0\le s\le\tau_S}|X_s|$; (2.9) $\tau_{i,n}\to\tau_S$ a.s.; and the payoff in (2.6) is well defined.
--
--   **Nash equilibrium (Definition 2.6).** $(\varphi_1^*,\varphi_2^*)\in\Phi_x$ is a Nash equilibrium if $J^1(x;\varphi_1^*,\varphi_2^*)\ge J^1(x;\varphi_1,\varphi_2^*)$ for every strategy $\varphi_1$ with $(\varphi_1,\varphi_2^*)\in\Phi_x$, and symmetrically for player 2.
--
--   These definitions are the model on which the verification theorem (Theorem 3.3) and its milestones are stated.
--
--   **Formalization Note.** The usual conditions and the $\{\mathcal F_t\}$-Brownian motion are the published `You2015.Shared.UsualConditions` and `You2015.Shared.IsFBrownian` ($W$ takes values in `Fin k → ℝ`); the Itô integral is the published `EthierKurtz.HasBrownianItoIntegral`. Players are `Player.one`, `Player.two`; the cost $\phi_i$ is `cost i`, the gain $\psi_i$ is `gain i`. The construction is pathwise (`stage`), given the sample paths of the diffusion pieces; times live in $[0,\infty]$ (`ℝ≥0∞`). Deviations: the Lemma 2.3 pathology at $\{\bar k=\infty,\tau_S<\infty\}$ is excluded from $\Phi_x$ (almost surely, $\bar k=\infty$ forces $\tau_S=\infty$), because the paper defines $\tilde X^\infty$ only on $[0,\tau_S[$, so $X_{\tau_S}$ and the payoff are undefined there. Index corrections: the paper writes $\tau_S=\alpha^S_{\bar k}$, which for $\bar k=0$ gives $\alpha^S_0=\infty$; the exit time of $X=\tilde X^{\bar k}$ is $\alpha^S_{\bar k+1}$, which is also the paper's own $\inf\{s\ge0:X_s\notin S\}$. The fourth variable of (2.7) is printed with $\tau_{i,k},\delta_{i,k}$; $\psi_i$ is defined on $S\times Z_j$, so it is read with $\tau_{j,k},\delta_{j,k}$ as in (2.6). The supremum in (2.8) is over $[0,\tau_S]$: after $\tau_S$ the paper's $X$ continues as an uncontrolled diffusion, and a supremum over all $t\ge0$ would make $\Phi_x$ empty for Brownian motion in a bounded domain, contrary to the paper's remark after Definition 2.5. Admissibility uses one realization and Nash quantifies over every admissible realization; under Lipschitz coefficients strong uniqueness makes realizations, and hence payoffs, almost surely equal. Integrability of each payoff random variable is required, which the paper asserts follows from (2.7). $\bar k$ is the end of the initial segment of steps before the exit, the paper's intended reading of $\sup\{k:\tilde\tau_k<\alpha^S_k\}$.
-- source:
--   Aïd et al. (2020), Math. Oper. Res. 45(1), accepted manuscript, Section 2: (2.1), Definitions 2.1, 2.2, 2.4, 2.5, 2.6, (2.3), (2.6)–(2.9) (pp. 4–7)

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_You2015_Shared_Basis

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ImpulseGames.Verification

noncomputable section
open Classical

/-- The two players; `Player.one` is the paper's player 1, who has priority. -/
inductive Player
  | one
  | two
  deriving DecidableEq

/-- The opponent `j ≠ i`. -/
def Player.other : Player → Player
  | .one => .two
  | .two => .one

/-- The state space `ℝ^d` with the Euclidean norm. -/
abbrev State (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Data of the two-player impulse game of Section 2: drift `b`, diffusion `σ` (a `d × k`
matrix), the open domain `S`, impulse sets `Z i ⊆ ℝ^{l i}`, impulse maps `Γ i`, discount rates
`ρ i`, running payoffs `f i`, terminal payoffs `h i` (only used on `∂S`), intervention costs
`cost i : S × Z_i → ℝ` (the paper's `ϕ_i`) and gains `gain i : S × Z_j → ℝ` (the paper's `ψ_i`). -/
structure Game (d k : ℕ) where
  b : State d → State d
  σ : State d → Matrix (Fin d) (Fin k) ℝ
  S : Set (State d)
  l : Player → ℕ
  Z : (i : Player) → Set (EuclideanSpace ℝ (Fin (l i)))
  Γ : (i : Player) → State d → EuclideanSpace ℝ (Fin (l i)) → State d
  ρ : Player → ℝ
  f : Player → State d → ℝ
  h : Player → State d → ℝ
  cost : (i : Player) → State d → EuclideanSpace ℝ (Fin (l i)) → ℝ
  gain : (i : Player) → State d → EuclideanSpace ℝ (Fin (l i.other)) → ℝ

variable {d k : ℕ}

/-- The impulse space `ℝ^{l_i}` of player `i`. -/
abbrev Game.Imp (G : Game d k) (i : Player) := EuclideanSpace ℝ (Fin (G.l i))

/-- The standing assumptions of Section 2 (pp. 4, 6): `b`, `σ` globally Lipschitz; `S` open;
`Z_i` nonempty; `Γ_i : S × Z_i → S` continuous; `ρ_i > 0`; `f_i` continuous on `S`, `h_i`
continuous on `∂S`, `ϕ_i` continuous on `S × Z_i`, `ψ_i` continuous on `S × Z_j`. -/
def Game.Standing (G : Game d k) : Prop :=
  (∃ K : ℝ≥0, LipschitzWith K G.b ∧ ∀ p q, LipschitzWith K (fun y => G.σ y p q)) ∧
  IsOpen G.S ∧
  (∀ i, (G.Z i).Nonempty) ∧
  (∀ i, ContinuousOn (fun z : State d × G.Imp i => G.Γ i z.1 z.2) (G.S ×ˢ G.Z i)) ∧
  (∀ i, ∀ y ∈ G.S, ∀ z ∈ G.Z i, G.Γ i y z ∈ G.S) ∧
  (∀ i, 0 < G.ρ i) ∧
  (∀ i, ContinuousOn (G.f i) G.S) ∧
  (∀ i, ContinuousOn (G.h i) (frontier G.S)) ∧
  (∀ i, ContinuousOn (fun z : State d × G.Imp i => G.cost i z.1 z.2) (G.S ×ˢ G.Z i)) ∧
  (∀ i, ContinuousOn (fun z : State d × G.Imp i.other => G.gain i z.1 z.2)
    (G.S ×ˢ G.Z i.other))

/-- The stochastic basis of Section 2 (p. 4): `P` is a probability measure, the filtration `𝔽`
satisfies the usual conditions (right-continuity, `P`-completeness), and `W` is a
`k`-dimensional `𝔽`-Brownian motion (independent standard Brownian coordinates, `𝔽`-adapted,
increments independent of the past), as in `You2015.Shared`. -/
def IsBrownianBasis {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    (𝔽 : Filtration ℝ≥0 m) (W : ℝ≥0 → Ω → (Fin k → ℝ)) : Prop :=
  IsProbabilityMeasure P ∧ You2015.Shared.UsualConditions P 𝔽 ∧
  You2015.Shared.IsFBrownian P 𝔽 W

/-- `Y` is a solution of (2.1), `dY_s = b(Y_s) ds + σ(Y_s) dW_s` for `s ≥ τ`, with initial
condition `Y_τ = ζ` (on `{τ < ∞}`), where `τ` is a random time in `[0, ∞]`: `Y` has continuous
paths on `[τ, ∞)`, `Y_s 1_{τ ≤ s}` is `𝔽_s`-measurable, `Y_τ = ζ`, and for each `s`, almost
surely on `{τ ≤ s}`,
`Y_s = ζ + ∫_0^s 1_{u > τ} b(Y_u) du + ∑_q ∫_0^s 1_{u > τ} σ_{·q}(Y_u) dW^q_u`,
the stochastic integrals being Itô integrals in the sense of
`EthierKurtz.HasBrownianItoIntegral`. -/
def SolvesFrom {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω) (𝔽 : Filtration ℝ≥0 m)
    (W : ℝ≥0 → Ω → (Fin k → ℝ)) (b : State d → State d)
    (σ : State d → Matrix (Fin d) (Fin k) ℝ) (τ : Ω → ℝ≥0∞) (ζ : Ω → State d)
    (Y : ℝ≥0 → Ω → State d) : Prop :=
  (∀ ω, ContinuousOn (fun s => Y s ω) {s : ℝ≥0 | τ ω ≤ (s : ℝ≥0∞)}) ∧
  (∀ s : ℝ≥0, Measurable[𝔽 s] (fun ω => if τ ω ≤ (s : ℝ≥0∞) then Y s ω else 0)) ∧
  (∀ ω, τ ω < ⊤ → Y (τ ω).toNNReal ω = ζ ω) ∧
  ∃ J : Fin d → Fin k → ℝ≥0 → Ω → ℝ,
    (∀ p q, EthierKurtz.HasBrownianItoIntegral P 𝔽 (fun t ω => W t ω q)
      (fun u ω => if τ ω < (u : ℝ≥0∞) then σ (Y u ω) p q else 0) (J p q)) ∧
    ∀ s : ℝ≥0, ∀ᵐ ω ∂P, τ ω ≤ (s : ℝ≥0∞) → ∀ p,
      Y s ω p = ζ ω p
        + (∫ u in (0 : ℝ)..(s : ℝ),
            if τ ω < ENNReal.ofReal u then b (Y u.toNNReal ω) p else 0)
        + ∑ q, J p q s ω

/-- Definition 2.1: a strategy for player `i` is a pair `(C, ξ)` with `C` an open subset of `S`
and `ξ` a continuous function from `S` to `Z_i`. -/
def IsStrategy (G : Game d k) (i : Player) (C : Set (State d)) (ξ : State d → G.Imp i) :
    Prop :=
  IsOpen C ∧ C ⊆ G.S ∧ (∀ y ∈ G.S, ξ y ∈ G.Z i) ∧ ContinuousOn ξ G.S

/-- A pair of (candidate) strategies `φ_i = (C_i, ξ_i)`, `i = 1, 2`, as data. -/
structure Profile (G : Game d k) where
  C : Player → Set (State d)
  ξ : (i : Player) → State d → G.Imp i

/-- Replace player `i`'s strategy by `(Ci, ξi)`. -/
def Profile.update {G : Game d k} (π : Profile G) (i : Player) (Ci : Set (State d))
    (ξi : State d → G.Imp i) : Profile G :=
  ⟨Function.update π.C i Ci, Function.update π.ξ i ξi⟩

/-- The exit time `inf {s > t₀ : y_s ∉ O}` of a path `y` from `O` after time `t₀`, in
`[0, ∞]` (`inf ∅ = ∞`). -/
def exitAfter (y : ℝ≥0 → State d) (t₀ : ℝ≥0∞) (O : Set (State d)) : ℝ≥0∞ :=
  ⨅ (s : ℝ≥0) (_ : t₀ < (s : ℝ≥0∞) ∧ y s ∉ O), (s : ℝ≥0∞)

/-- One step of the construction of Definition 2.2, pathwise:
`path = X̃^k`, `time = τ̃_k`, `exitS = α^S_k`, `mover = m_k`,
`pre = X̃^{k-1}_{τ̃_k}` (the state just before the `k`-th intervention), `post = x_k`. -/
structure Stage (d : ℕ) where
  path : ℝ≥0 → State d
  time : ℝ≥0∞
  exitS : ℝ≥0∞
  mover : Player
  pre : State d
  post : State d

/-- The inductive construction of Definition 2.2 along one sample path, given the paths
`y n = Y^{τ̃_n, x_n}` of the diffusion pieces: `τ̃_0 = 0`, `x_0 = x`, `X̃^0 = y 0`,
`α^S_0 = ∞`, and for `n ≥ 1`
`α^O_n = inf {s > τ̃_{n-1} : X̃^{n-1}_s ∉ O}`, `τ̃_n = α^{C_1}_n ∧ α^{C_2}_n`,
`m_n = 1` if `α^{C_1}_n ≤ α^{C_2}_n` and `2` otherwise,
`x_n = Γ^{m_n}(X̃^{n-1}_{τ̃_n}, ξ_{m_n}(X̃^{n-1}_{τ̃_n})) 1_{τ̃_n < ∞}`,
`X̃^n = X̃^{n-1} 1_{[0, τ̃_n[} + y n 1_{[τ̃_n, ∞[}`. -/
def stage (G : Game d k) (x : State d) (π : Profile G) (y : ℕ → ℝ≥0 → State d) :
    ℕ → Stage d
  | 0 => ⟨y 0, 0, ⊤, .one, x, x⟩
  | n + 1 =>
    let Q := stage G x π y n
    let a₁ := exitAfter Q.path Q.time (π.C .one)
    let a₂ := exitAfter Q.path Q.time (π.C .two)
    let τ := min a₁ a₂
    let m : Player := if a₁ ≤ a₂ then .one else .two
    let pre := Q.path τ.toNNReal
    { path := fun s => if (s : ℝ≥0∞) < τ then Q.path s else y (n + 1) s
      time := τ
      exitS := exitAfter Q.path Q.time G.S
      mover := m
      pre := pre
      post := if τ < ⊤ then G.Γ m pre (π.ξ m pre) else 0 }

section Path

variable (G : Game d k) (x : State d) (π : Profile G) (y : ℕ → ℝ≥0 → State d)

/-- Steps `0, …, n` all happen before the exit from `S`: `τ̃_h < α^S_h` for `h ≤ n`. -/
def alive (n : ℕ) : Prop :=
  ∀ h ≤ n, (stage G x π y h).time < (stage G x π y h).exitS

/-- `k̄ = sup {k : τ̃_h < α^S_h for all h ≤ k}` in `ℕ ∪ {∞}`. -/
def kbar : ℕ∞ := ⨆ (n : ℕ) (_ : alive G x π y n), (n : ℕ∞)

/-- The exit time `τ_S`: `α^S_{k̄+1}`, the exit time of `X̃^{k̄}` from `S` after `τ̃_{k̄}`, if
`k̄ < ∞`, and `α^S_∞ = sup_k α^S_k` if `k̄ = ∞`. -/
def exitTime : ℝ≥0∞ :=
  if kbar G x π y = ⊤ then ⨆ n, (stage G x π y n).exitS
  else (stage G x π y ((kbar G x π y).toNat + 1)).exitS

/-- The controlled process `X = X̃^{k̄}` (with `X̃^∞ = lim_k X̃^k`). -/
def ctrl (s : ℝ≥0) : State d :=
  if kbar G x π y = ⊤ then limUnder atTop (fun n => (stage G x π y n).path s)
  else (stage G x π y (kbar G x π y).toNat).path s

/-- `∑_{1 ≤ h ≤ l} 1_{m_h = i}`. -/
def count (i : Player) (l : ℕ) : ℕ :=
  ((Finset.Icc 1 l).filter (fun h => (stage G x π y h).mover = i)).card

/-- `k̄_i`, the number of interventions of player `i` before the end of the game. -/
def kbarI (i : Player) : ℕ∞ :=
  ⨆ (l : ℕ) (_ : (l : ℕ∞) ≤ kbar G x π y), (count G x π y i l : ℕ∞)

/-- `η(i, n) = min {l : ∑_{1 ≤ h ≤ l} 1_{m_h = i} = n}`, the index of the `n`-th intervention
of player `i`. -/
def eta (i : Player) (n : ℕ) : ℕ := sInf {l | count G x π y i l = n}

/-- The intervention time `τ_{i,n}` of (2.3): `τ̃_{η(i,n)}` if `n ≤ k̄_i`, `τ_S` otherwise. -/
def interTime (i : Player) (n : ℕ) : ℝ≥0∞ :=
  if (n : ℕ∞) ≤ kbarI G x π y i then (stage G x π y (eta G x π y i n)).time
  else exitTime G x π y

/-- The state `X_{(τ_{i,n})^-} = X̃^{η(i,n)-1}_{τ̃_{η(i,n)}}` just before the `n`-th
intervention of player `i`. -/
def preState (i : Player) (n : ℕ) : State d := (stage G x π y (eta G x π y i n)).pre

/-- The impulse `δ_{i,n}` of (2.3): `ξ_i(X_{(τ_{i,n})^-})` if `n ≤ k̄_i`, `0` otherwise. -/
def impulse (i : Player) (n : ℕ) : G.Imp i :=
  if (n : ℕ∞) ≤ kbarI G x π y i then π.ξ i (preState G x π y i n) else 0

/-- The intervention times before the end of the game, `{τ_{i,n} : n ≥ 1, τ_{i,n} < τ_S}`. -/
def interventionTimes : Set ℝ≥0∞ :=
  {t | ∃ i n, 1 ≤ n ∧ interTime G x π y i n < exitTime G x π y ∧ t = interTime G x π y i n}

/-- Discount factor `e^{-ρ t}`, with `e^{-ρ ∞} = 0`. -/
def disc (ρ : ℝ) (t : ℝ≥0∞) : ℝ := if t = ⊤ then 0 else Real.exp (-ρ * t.toReal)

/-- The time set `[0, τ)` as a subset of `ℝ`. -/
def before (t : ℝ≥0∞) : Set ℝ := {s | 0 ≤ s ∧ ENNReal.ofReal s < t}

/-- Pathwise payoff of player `i`, the random variable inside the expectation in (2.6):
`∫_0^{τ_S} e^{-ρ_i s} f_i(X_s) ds + ∑_{τ_{i,n} < τ_S} e^{-ρ_i τ_{i,n}} ϕ_i(X_{(τ_{i,n})^-}, δ_{i,n})
 + ∑_{τ_{j,n} < τ_S} e^{-ρ_i τ_{j,n}} ψ_i(X_{(τ_{j,n})^-}, δ_{j,n})
 + e^{-ρ_i τ_S} h_i(X_{τ_S}) 1_{τ_S < ∞}`. -/
def pathPayoff (i : Player) : ℝ :=
  (∫ s in before (exitTime G x π y),
      Real.exp (-G.ρ i * s) * G.f i (ctrl G x π y s.toNNReal))
  + (∑' n : ℕ, if 1 ≤ n ∧ interTime G x π y i n < exitTime G x π y then
      disc (G.ρ i) (interTime G x π y i n) *
        G.cost i (preState G x π y i n) (impulse G x π y i n) else 0)
  + (∑' n : ℕ, if 1 ≤ n ∧ interTime G x π y i.other n < exitTime G x π y then
      disc (G.ρ i) (interTime G x π y i.other n) *
        G.gain i (preState G x π y i.other n) (impulse G x π y i.other n) else 0)
  + (if exitTime G x π y < ⊤ then
      disc (G.ρ i) (exitTime G x π y) * G.h i (ctrl G x π y (exitTime G x π y).toNNReal)
    else 0)

/-- The four nonnegative random variables of (2.7) for player `i`, pathwise, valued in
`[0, ∞]`. -/
def runningAbs (i : Player) : ℝ≥0∞ :=
  ∫⁻ s in before (exitTime G x π y),
    ENNReal.ofReal (Real.exp (-G.ρ i * s) * |G.f i (ctrl G x π y s.toNNReal)|)

def terminalAbs (i : Player) : ℝ≥0∞ :=
  ENNReal.ofReal (disc (G.ρ i) (exitTime G x π y) *
    |G.h i (ctrl G x π y (exitTime G x π y).toNNReal)|)

def costAbs (i : Player) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal (if 1 ≤ n ∧ interTime G x π y i n < exitTime G x π y then
    disc (G.ρ i) (interTime G x π y i n) *
      |G.cost i (preState G x π y i n) (impulse G x π y i n)| else 0)

def gainAbs (i : Player) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal (if 1 ≤ n ∧ interTime G x π y i.other n < exitTime G x π y then
    disc (G.ρ i) (interTime G x π y i.other n) *
      |G.gain i (preState G x π y i.other n) (impulse G x π y i.other n)| else 0)

/-- `‖X‖_∞ = sup_{0 ≤ s ≤ τ_S} |X_s|` (times `s < ∞`). -/
def supNorm : ℝ≥0∞ :=
  ⨆ (s : ℝ≥0) (_ : (s : ℝ≥0∞) ≤ exitTime G x π y), (‖ctrl G x π y s‖₊ : ℝ≥0∞)

end Path

/-- The sample path `ω ↦ (n, s) ↦ Y n s ω` of the family of diffusion pieces. -/
def pathOf {Ω : Type*} (Y : ℕ → ℝ≥0 → Ω → State d) (ω : Ω) : ℕ → ℝ≥0 → State d :=
  fun n s => Y n s ω

section Random

variable {Ω : Type*} [m : MeasurableSpace Ω]

/-- `Y` realizes Definition 2.2 for the initial state `x` and the strategies `π`: the `n`-th
piece `Y n` solves (2.1) from time `τ̃_n` with initial value `x_n` while the game is running
(steps `0, …, n` before the exit from `S`; otherwise nothing is required of it), and the
intervention times do not accumulate before the exit: on `{k̄ = ∞}`,
`lim_k τ̃_k = α^S_∞ = sup_k α^S_k`. -/
def IsRealization (P : Measure Ω) (𝔽 : Filtration ℝ≥0 m)
    (W : ℝ≥0 → Ω → (Fin k → ℝ)) (G : Game d k) (x : State d) (π : Profile G)
    (Y : ℕ → ℝ≥0 → Ω → State d) : Prop :=
  (∀ n, SolvesFrom P 𝔽 W G.b G.σ
    (fun ω => if alive G x π (pathOf Y ω) n then (stage G x π (pathOf Y ω) n).time else ⊤)
    (fun ω => (stage G x π (pathOf Y ω) n).post) (Y n)) ∧
  (∀ ω, kbar G x π (pathOf Y ω) = ⊤ →
    Tendsto (fun n => (stage G x π (pathOf Y ω) n).time) atTop
      (𝓝 (⨆ n, (stage G x π (pathOf Y ω) n).exitS)))

/-- A `[0, ∞]`-valued random variable is in `L¹(Ω)`. -/
def InL1 (P : Measure Ω) (F : Ω → ℝ≥0∞) : Prop :=
  AEMeasurable F P ∧ ∫⁻ ω, F ω ∂P < ⊤

/-- Definition 2.5: the pair `π` is `x`-admissible, witnessed by the realization `Y`:
both components are strategies, `Y` realizes Definition 2.2, (2.7) the four random variables
are in `L¹` for each player, (2.8) `E[‖X‖_∞^p] < ∞` for every `p ∈ ℕ`, (2.9)
`τ_{i,n} → τ_S` a.s., and (2.6) is well defined: almost surely the interventions do not
accumulate at a finite exit time (on `{k̄ = ∞}`, `τ_S = ∞`; the paper defines `X̃^∞` only on
`[0, τ_S[`, so `X_{τ_S}` would be undefined), and the payoff random variable of each player is
integrable. -/
def IsAdmissible (P : Measure Ω) (𝔽 : Filtration ℝ≥0 m)
    (W : ℝ≥0 → Ω → (Fin k → ℝ)) (G : Game d k) (x : State d) (π : Profile G)
    (Y : ℕ → ℝ≥0 → Ω → State d) : Prop :=
  (∀ i, IsStrategy G i (π.C i) (π.ξ i)) ∧
  IsRealization P 𝔽 W G x π Y ∧
  (∀ i, InL1 P (fun ω => runningAbs G x π (pathOf Y ω) i) ∧
    InL1 P (fun ω => terminalAbs G x π (pathOf Y ω) i) ∧
    InL1 P (fun ω => costAbs G x π (pathOf Y ω) i) ∧
    InL1 P (fun ω => gainAbs G x π (pathOf Y ω) i)) ∧
  (∀ p : ℕ, ∫⁻ ω, supNorm G x π (pathOf Y ω) ^ p ∂P < ⊤) ∧
  (∀ i, ∀ᵐ ω ∂P, Tendsto (fun n => interTime G x π (pathOf Y ω) i n) atTop
    (𝓝 (exitTime G x π (pathOf Y ω)))) ∧
  (∀ᵐ ω ∂P, kbar G x π (pathOf Y ω) = ⊤ → exitTime G x π (pathOf Y ω) = ⊤) ∧
  (∀ i, Integrable (fun ω => pathPayoff G x π (pathOf Y ω) i) P)

/-- `π ∈ Φ_x`. -/
def InPhi (P : Measure Ω) (𝔽 : Filtration ℝ≥0 m) (W : ℝ≥0 → Ω → (Fin k → ℝ))
    (G : Game d k) (x : State d) (π : Profile G) : Prop :=
  ∃ Y, IsAdmissible P 𝔽 W G x π Y

/-- The payoff `J^i(x; φ_1, φ_2)` of (2.6), computed on the realization `Y`. -/
def payoff (P : Measure Ω) (G : Game d k) (x : State d) (π : Profile G)
    (Y : ℕ → ℝ≥0 → Ω → State d) (i : Player) : ℝ :=
  ∫ ω, pathPayoff G x π (pathOf Y ω) i ∂P

/-- Definition 2.6: `π ∈ Φ_x` is a Nash equilibrium: for each player `i` and every strategy
`(Ci, ξi)` of player `i` such that the deviation is in `Φ_x`, `J^i` of the deviation is at most
`J^i(x; π)` (each payoff computed on any admissible realization). -/
def IsNash (P : Measure Ω) (𝔽 : Filtration ℝ≥0 m) (W : ℝ≥0 → Ω → (Fin k → ℝ))
    (G : Game d k) (x : State d) (π : Profile G) : Prop :=
  InPhi P 𝔽 W G x π ∧
  ∀ (i : Player) (Ci : Set (State d)) (ξi : State d → G.Imp i)
    (Y Y' : ℕ → ℝ≥0 → Ω → State d),
    IsAdmissible P 𝔽 W G x (π.update i Ci ξi) Y → IsAdmissible P 𝔽 W G x π Y' →
    payoff P G x (π.update i Ci ξi) Y i ≤ payoff P G x π Y' i

end Random

end

end ImpulseGames.Verification


