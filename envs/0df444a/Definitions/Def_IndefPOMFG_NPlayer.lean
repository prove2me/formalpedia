-- Prove2me | Definitions.Def_IndefPOMFG_NPlayer
-- name    : IndefPOMFG_NPlayer
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:12:31.501136+00:00
-- url     : https://prove2.me/theorems/69a2132c-dfce-406c-89fa-1c52bc95ea0c
-- title:
--   The N-player system (2)–(4), (6)–(7), strategy sets 𝒰^{i,0}_c, 𝒰ⁱ_c and the cost 𝒥_i (5)
-- statement:
--   For a control profile $u=(u^1,\dots,u^N)$, the state of agent $i$ solves
--
--   $$dx^i_t=\{A_tx^i_t+B_tu^i_t+\bar A_tx^{(N)}_t+\bar B_tu^{(N)}_t+b_t\}dt+\sigma_tdW^i_t+\{D_tx^i_t+F_tu^i_t+\bar D_tx^{(N)}_t+\bar F_tu^{(N)}_t+\bar b_t\}dW^0_t+\bar\sigma_td\bar W^i_t,\quad x^i_0=x,$$
--
--   where $x^{(N)}=\frac1N\sum_jx^j$ and $u^{(N)}=\frac1N\sum_ju^j$; agent $i$ observes $dy^i_t=\{G_tx^i_t+H_tu^i_t+\bar G_tx^{(N)}_t+\bar H_tu^{(N)}_t+\tilde b_t\}dt+\tilde\sigma_td\bar W^i_t$, $y^i_0=0$, and all agents observe $d\theta_t=(I_t\theta_t+\check b_t)dt+\check\sigma_tdW^0_t$, $\theta_0=0$. The control-free system (6)–(7) is the same with $u=0$ and $b=\bar b=\tilde b=0$.
--
--   The observation filtrations are $\mathcal F^{y}_t=\sigma\{y^j_s,\theta_s;\ j\le N,\ s\le t\}$ and $\mathcal F^{y^0}_t=\sigma\{y^{j,0}_s,\theta_s;\ j\le N,\ s\le t\}$. A control $u^i$ belongs to $\mathscr U^{i,0}_c$ if it is $\mathcal F^{y^0}$-adapted with $\mathbb E\sup_{t\le T}|u^i_t|^2<\infty$, and to the **admissible centralized strategy set** $\mathscr U^i_c$ (Definition 3.1) if moreover it is $\mathcal F^y$-adapted.
--
--   The cost of agent $i$ is
--
--   $$\mathcal J_i(u^i,u^{-i})=\tfrac12\mathbb E\Big[\int_0^T\big\{\langle Q_t(x^i_t-\alpha_1x^{(N)}_t)+2q_t,x^i_t-\alpha_1x^{(N)}_t\rangle+\langle R_t(u^i_t-\beta_1u^{(N)}_t)+2r_t,u^i_t-\beta_1u^{(N)}_t\rangle+2\langle S_t(u^i_t-\beta_2u^{(N)}_t),x^i_t-\alpha_2x^{(N)}_t\rangle\big\}dt+\langle L_T(x^i_T-\alpha_3x^{(N)}_T)+2l_T,x^i_T-\alpha_3x^{(N)}_T\rangle\Big].$$
--
--   **Formalization Note** Equations are solved in the strong sense of `Peng1990.SMP.SolvesSDE` for the full filtration; the cost is written once (`quadCost`) for state, control and mean terms, and is reused for the limiting cost (16).
-- source:
--   Chen, Nie & Wu, Indefinite Linear-Quadratic Partially Observed Mean-Field Game, arXiv:2508.01568v1, (2)–(5) p.3, (6)–(7) and Definition 3.1 p.6

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_IndefPOMFG_Coeffs
import Definitions.Def_IndefPOMFG_Space

open MeasureTheory Set Peng1990.SMP
open scoped NNReal ENNReal Matrix

set_option warn.classDefReducibility false

namespace IndefPOMFG

variable {n m d N : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The average `z⁽ᴺ⁾ = (1/N) ∑ⱼ zʲ` of a family of `N` processes (p.3). -/
noncomputable def avg {k : ℕ} (z : Fin N → ℝ≥0 → Ω → Fin k → ℝ) : ℝ≥0 → Ω → Fin k → ℝ :=
  fun s ω => (N : ℝ)⁻¹ • ∑ j, z j s ω

/-- `θ` is the common observation (4), p.3: `dθ_t = (I_t θ_t + b̌_t) dt + σ̌_t dW⁰_t`, `θ_0 = 0`
(a scalar process, stored as `Fin 1 → ℝ`). -/
def IsTheta (c : Coeffs n m d) (Sp : Space N d Ω) (θ : ℝ≥0 → Ω → Fin 1 → ℝ) : Prop :=
  SolvesSDE Sp.filt Sp.P c.T Sp.B 0 (fun s _ z => c.I s • z + fun _ => c.bc s)
    (w0Diff (fun s _ _ => fun _ => c.σc s)) θ

/-- `𝓕^θ_t = σ{θ_s; 0 ≤ s ≤ t}` (p.6), null-set augmented. -/
def obsTheta (Sp : Space N d Ω) (θ : ℝ≥0 → Ω → Fin 1 → ℝ) : ℝ≥0 → MeasurableSpace Ω :=
  obsSigma Sp.P θ

/-- The `N`-player system with control profile `u = (u¹, …, uᴺ)` and affine terms `b, b̄, b̃`:
for every agent `i`, `xⁱ` solves
`dxⁱ = {A xⁱ + B uⁱ + Ā x⁽ᴺ⁾ + B̄ u⁽ᴺ⁾ + b} dt + σ dWⁱ + {D xⁱ + F uⁱ + D̄ x⁽ᴺ⁾ + F̄ u⁽ᴺ⁾ + b̄} dW⁰ + σ̄ dW̄ⁱ`,
`xⁱ_0 = x`, and `yⁱ` solves
`dyⁱ = {G xⁱ + H uⁱ + Ḡ x⁽ᴺ⁾ + H̄ u⁽ᴺ⁾ + b̃} dt + σ̃ dW̄ⁱ`, `yⁱ_0 = 0`.
With `b, b̄, b̃` the model's this is (2)–(3) (p.3); with `u = 0` and `b = b̄ = b̃ = 0` it is
(6)–(7) (p.6).

**Formalization Note** Solutions are strong solutions in the sense of
`Peng1990.SMP.SolvesSDE` for the full filtration `𝓕`; the system is solved jointly (each
equation sees the averages of the given family). -/
def IsNSys (c : Coeffs n m d) (Sp : Space N d Ω) (u : Fin N → ℝ≥0 → Ω → Fin m → ℝ)
    (b bb bt : ℝ≥0 → Fin n → ℝ) (x y : Fin N → ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  ∀ i, SolvesSDE Sp.filt Sp.P c.T Sp.B c.x
      (fun s ω z => c.A s *ᵥ z + c.B s *ᵥ u i s ω + c.Ab s *ᵥ avg x s ω +
        c.Bb s *ᵥ avg u s ω + b s)
      (agentDiff i (fun s ω z => c.D s *ᵥ z + c.F s *ᵥ u i s ω + c.Db s *ᵥ avg x s ω +
          c.Fb s *ᵥ avg u s ω + bb s)
        (fun s _ => c.σ s) (fun s _ => c.σb s)) (x i) ∧
    SolvesSDE Sp.filt Sp.P c.T Sp.B 0
      (fun s ω _ => c.G s *ᵥ x i s ω + c.H s *ᵥ u i s ω + c.Gb s *ᵥ avg x s ω +
        c.Hb s *ᵥ avg u s ω + bt s)
      (agentDiff i (fun _ _ _ => 0) (fun _ _ => 0) (fun s _ => c.σt s)) (y i)

/-- `(x, y)` solves the state equations (2) and observation equations (3) of the `N`-player
system under the profile `u` (p.3). -/
def IsNState (c : Coeffs n m d) (Sp : Space N d Ω) (u : Fin N → ℝ≥0 → Ω → Fin m → ℝ)
    (x y : Fin N → ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  IsNSys c Sp u c.b c.bb c.bt x y

/-- `(x⁰, y⁰) = (x^{i,0}, y^{i,0})ᵢ` solves the control-free system (6)–(7) (p.6). -/
def IsNState0 (c : Coeffs n m d) (Sp : Space N d Ω) (x y : Fin N → ℝ≥0 → Ω → Fin n → ℝ) :
    Prop :=
  IsNSys c Sp 0 0 0 0 x y

/-- The observation filtration `σ{yʲ_s, θ_s; 1 ≤ j ≤ N, 0 ≤ s ≤ t}` of a family `y` (null-set
augmented): `𝓕^y_t = ⋁ᵢ 𝓕^{yⁱ}_t` for the observations (3), and `𝓕^{y⁰}_t` for (7) (p.6). -/
def obsN (Sp : Space N d Ω) (θ : ℝ≥0 → Ω → Fin 1 → ℝ) (y : Fin N → ℝ≥0 → Ω → Fin n → ℝ) :
    ℝ≥0 → MeasurableSpace Ω :=
  obsSigma Sp.P (fun s ω => ((fun j => y j s ω), θ s ω))

/-- `u ∈ 𝒰^{i,0}_c` (p.6): `u` is an `𝓕^{y⁰}`-adapted `ℝᵐ`-valued control (an `L²_𝓕` process) with
`E[sup_{0 ≤ t ≤ T} |u_t|²] < ∞`; `y0` is the family `(y^{j,0})ⱼ` of (7). -/
def InUc0 (c : Coeffs n m d) (Sp : Space N d Ω) (θ : ℝ≥0 → Ω → Fin 1 → ℝ)
    (y0 : Fin N → ℝ≥0 → Ω → Fin n → ℝ) (u : ℝ≥0 → Ω → Fin m → ℝ) : Prop :=
  IsCtrl Sp c.T u ∧ AdaptedOn (obsN Sp θ y0) c.T u

/-- `u ∈ 𝒰ⁱ_c`, Definition 3.1 (p.6): `u ∈ 𝒰^{i,0}_c` and `u` is `𝓕^y`-adapted, where `y` is the
family of observations (3) generated by the profile in which `u` is played (passed as `y`). -/
def InUc (c : Coeffs n m d) (Sp : Space N d Ω) (θ : ℝ≥0 → Ω → Fin 1 → ℝ)
    (y0 y : Fin N → ℝ≥0 → Ω → Fin n → ℝ) (u : ℝ≥0 → Ω → Fin m → ℝ) : Prop :=
  InUc0 c Sp θ y0 u ∧ AdaptedOn (obsN Sp θ y) c.T u

/-- The running cost of (5) and (16) at time `t`, state `X`, control `u`, and mean terms `xm, um`:
`⟨Q(X − α₁xm) + 2q, X − α₁xm⟩ + ⟨R(u − β₁um) + 2r, u − β₁um⟩ + 2⟨S(u − β₂um), X − α₂xm⟩`. -/
def costRate (c : Coeffs n m d) (t : ℝ≥0) (X : Fin n → ℝ) (u : Fin m → ℝ) (xm : Fin n → ℝ)
    (um : Fin m → ℝ) : ℝ :=
  (c.Q t *ᵥ (X - c.α₁ • xm) + (2 : ℝ) • c.q t) ⬝ᵥ (X - c.α₁ • xm)
    + (c.R t *ᵥ (u - c.β₁ • um) + (2 : ℝ) • c.r t) ⬝ᵥ (u - c.β₁ • um)
    + 2 * ((c.S t *ᵥ (u - c.β₂ • um)) ⬝ᵥ (X - c.α₂ • xm))

/-- The terminal cost of (5) and (16): `⟨L_T(X − α₃xm) + 2l_T, X − α₃xm⟩`. -/
def termCost (c : Coeffs n m d) (X xm : Fin n → ℝ) : ℝ :=
  (c.LT *ᵥ (X - c.α₃ • xm) + (2 : ℝ) • c.lT) ⬝ᵥ (X - c.α₃ • xm)

/-- The quadratic cost `½ E[∫₀ᵀ costRate dt + termCost]` along a state `X`, control `u` and mean
terms `(xm, um)`. With `(xm, um) = (x⁽ᴺ⁾, u⁽ᴺ⁾)` it is the `N`-player cost (5); with
`(xm, um) = (x⁰, u⁰)` it is the limiting cost (16).

**Formalization Note** Bochner integrals; the integrand is integrable for every admissible
control and solution (bounded weights, square-integrable processes). -/
noncomputable def quadCost (c : Coeffs n m d) (P : Measure Ω) (X : ℝ≥0 → Ω → Fin n → ℝ)
    (u : ℝ≥0 → Ω → Fin m → ℝ) (xm : ℝ≥0 → Ω → Fin n → ℝ) (um : ℝ≥0 → Ω → Fin m → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ ω, ((∫ s in Icc (0 : ℝ) c.T,
      costRate c s.toNNReal (X s.toNNReal ω) (u s.toNNReal ω) (xm s.toNNReal ω)
        (um s.toNNReal ω)) + termCost c (X c.T ω) (xm c.T ω)) ∂P

/-- The cost functional `𝒥_i(uⁱ, u⁻ⁱ)` of agent `i` (5), p.3, along the states `x` of the profile
`u`. -/
noncomputable def NCost (c : Coeffs n m d) (P : Measure Ω) (x : Fin N → ℝ≥0 → Ω → Fin n → ℝ)
    (u : Fin N → ℝ≥0 → Ω → Fin m → ℝ) (i : Fin N) : ℝ :=
  quadCost c P (x i) (u i) (avg x) (avg u)

end IndefPOMFG


