-- Prove2me | Definitions.Def_IndefPOMFG_Limiting
-- name    : IndefPOMFG_Limiting
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:13:20.927169+00:00
-- url     : https://prove2.me/theorems/d3dc9a10-6297-43e7-8ce6-07bbaf3116fa
-- title:
--   The limiting control problem (MFD): (10)–(21), 𝒰^{i,0}_d, 𝒰ⁱ_d, optimality, Hamiltonian system (22) (corrected: (11), (18))
-- statement:
--   Fix an $\mathcal F^\theta$-adapted square-integrable **mean-field pair** $(x^0,u^0)$. The limiting state and observation of agent $i$ under a control $u$ are
--
--   $$dX^i_t=(A_tX^i_t+B_tu_t+\bar A_tx^0_t+\bar B_tu^0_t+b_t)dt+\sigma_tdW^i_t+(D_tX^i_t+F_tu_t+\bar D_tx^0_t+\bar F_tu^0_t+\bar b_t)dW^0_t+\bar\sigma_td\bar W^i_t,\quad X^i_0=x,$$
--
--   $$dY^i_t=(G_tX^i_t+H_tu_t+\bar G_tx^0_t+\bar H_tu^0_t+\tilde b_t)dt+\tilde\sigma_td\bar W^i_t,\quad Y^i_0=0.$$
--
--   The control-free processes (12)–(13) use $x^{0,0}$, the solution of $dx^{0,0}=(A+\bar A)x^{0,0}dt+(D+\bar D)x^{0,0}dW^0$, $x^{0,0}_0=x$. A control is in $\mathscr U^{i,0}_d$ if it is $\mathcal F^{Y^{i,0}}$-adapted with $\mathbb E\sup|u|^2<\infty$, and in $\mathscr U^i_d$ (Definition 4.1) if moreover it is $\mathcal F^{Y^i}$-adapted for its own observation $Y^i$. The limiting cost $J_i(u)$ is (16), the cost (5) with $(x^{(N)},u^{(N)})$ replaced by $(x^0,u^0)$; $\bar u$ is **optimal for Problem (MFD)** if $\bar u\in\mathscr U^i_d$ and $J_i(\bar u)\le J_i(v)$ for all $v\in\mathscr U^i_d$.
--
--   The module also defines the homogeneous state (20) and cost $J^0_i$, the adjoint BSDE (21)
--
--   $$d\varphi^i_t=-\{A_t^\top\varphi^i_t+D_t^\top\eta^i_t+Q_t(\bar X^i_t-\alpha_1x^0_t)+S_t(\bar u^i_t-\beta_2u^0_t)+q_t\}dt+\eta^i_tdW^0_t+\zeta^i_tdW^i_t+\vartheta^i_td\bar W^i_t,\ \ \varphi^i_T=L_T(\bar X^i_T-\alpha_3x^0_T)+l_T,$$
--
--   the stationarity condition (18) $B_t^\top\mathbb E[\varphi^i_t|\mathcal F^{\bar Y^i}_t]+F_t^\top\mathbb E[\eta^i_t|\mathcal F^{\bar Y^i}_t]+S_t^\top\mathbb E[\bar X^i_t-\alpha_2x^0_t|\mathcal F^{\bar Y^i}_t]+R_t(\bar u^i_t-\beta_1u^0_t)+r_t=0$, and the Hamiltonian system (22).
--
--   **Formalization Note** Two printed formulas are ill-typed for $m\ne n$ and are corrected: (11) prints $\bar H_tx^0_t+\bar G_tu^0_t$ (here $\bar G_tx^0_t+\bar H_tu^0_t$), and (18)/(22) print $S_t$ where $S_t^\top$ is needed (as in the proof on p.9 and in (29)). $x^{0,0}$ is not defined in the paper; any $\mathcal F^\theta$-adapted choice gives the same $\mathcal F^{Y^{i,0}}$. (18) is required for a.e. $t$, almost surely.
-- source:
--   Chen, Nie & Wu, Indefinite Linear-Quadratic Partially Observed Mean-Field Game, arXiv:2508.01568v1, (10)–(17), Lemma 4.2 context, Definition 4.1, Problem (MFD) pp.7–8; Proposition 4.4 (18)–(21) p.9; (22) p.10

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_IndefPOMFG_Coeffs
import Definitions.Def_IndefPOMFG_Space
import Definitions.Def_IndefPOMFG_NPlayer

open MeasureTheory Set Peng1990.SMP
open scoped NNReal ENNReal Matrix

set_option warn.classDefReducibility false

namespace IndefPOMFG

variable {n m d N : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- A mean-field parameter `(x⁰, u⁰)` of the limiting problem (p.7: "some `𝓕^θ`-adapted process
pair"): both are `𝓕^θ`-adapted on `[0, T]`, progressively measurable, and
`E[sup_{0≤t≤T} |x⁰_t|²], E[sup_{0≤t≤T} |u⁰_t|²] < ∞`.

**Formalization Note** The square-integrability makes the limiting cost (16) finite; the pair
actually used, (38) and (59), satisfies it (p.23). -/
def IsMFParam (c : Coeffs n m d) (Sp : Space N d Ω) (θ : ℝ≥0 → Ω → Fin 1 → ℝ)
    (x0 : ℝ≥0 → Ω → Fin n → ℝ) (u0 : ℝ≥0 → Ω → Fin m → ℝ) : Prop :=
  IsStronglyProgressive Sp.filt x0 ∧ IsStronglyProgressive Sp.filt u0 ∧
    AdaptedOn (obsTheta Sp θ) c.T x0 ∧ AdaptedOn (obsTheta Sp θ) c.T u0 ∧
    supSq Sp c.T x0 < ⊤ ∧ supSq Sp c.T u0 < ⊤

/-- The limiting state (10) and limiting observation (11) of agent `i` under the control `u`
and the mean-field parameter `(x⁰, u⁰)` (p.7):
`dXⁱ = (A Xⁱ + B u + Ā x⁰ + B̄ u⁰ + b) dt + σ dWⁱ + (D Xⁱ + F u + D̄ x⁰ + F̄ u⁰ + b̄) dW⁰ + σ̄ dW̄ⁱ`,
`Xⁱ_0 = x`, and `dYⁱ = (G Xⁱ + H u + Ḡ x⁰ + H̄ u⁰ + b̃) dt + σ̃ dW̄ⁱ`, `Yⁱ_0 = 0`.

**Formalization Note** (11) is printed with `H̄_t x⁰_t + Ḡ_t u⁰_t`, which is ill-typed for
`m ≠ n` (`H̄ ∈ ℝ^{n×m}`, `x⁰ ∈ ℝⁿ`); it is corrected to `Ḡ x⁰ + H̄ u⁰`, the pattern of (3), (13),
(15). -/
def IsLimState (c : Coeffs n m d) (Sp : Space N d Ω) (i : Fin N) (x0 : ℝ≥0 → Ω → Fin n → ℝ)
    (u0 u : ℝ≥0 → Ω → Fin m → ℝ) (X Y : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  SolvesSDE Sp.filt Sp.P c.T Sp.B c.x
      (fun s ω z => c.A s *ᵥ z + c.B s *ᵥ u s ω + c.Ab s *ᵥ x0 s ω + c.Bb s *ᵥ u0 s ω + c.b s)
      (agentDiff i (fun s ω z => c.D s *ᵥ z + c.F s *ᵥ u s ω + c.Db s *ᵥ x0 s ω +
          c.Fb s *ᵥ u0 s ω + c.bb s)
        (fun s _ => c.σ s) (fun s _ => c.σb s)) X ∧
    SolvesSDE Sp.filt Sp.P c.T Sp.B 0
      (fun s ω _ => c.G s *ᵥ X s ω + c.H s *ᵥ u s ω + c.Gb s *ᵥ x0 s ω + c.Hb s *ᵥ u0 s ω +
        c.bt s)
      (agentDiff i (fun _ _ _ => 0) (fun _ _ => 0) (fun s _ => c.σt s)) Y

/-- The process `x^{0,0}` of (12)–(13), which the paper does not define (p.7 says only that
`x⁽ᴺ⁾₀` is approximated by `x^{0,0}`): read as the conditional-mean limit of (6),
`dx^{0,0} = (A + Ā) x^{0,0} dt + (D + D̄) x^{0,0} dW⁰`, `x^{0,0}_0 = x`.

**Formalization Note** Any `𝓕^θ`-adapted choice gives the same filtration `𝓕^{Y^{i,0}}`, the only
place `x^{0,0}` enters. -/
def IsX00 (c : Coeffs n m d) (Sp : Space N d Ω) (x00 : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  SolvesSDE Sp.filt Sp.P c.T Sp.B c.x (fun s _ z => (c.A s + c.Ab s) *ᵥ z)
    (w0Diff (fun s _ z => (c.D s + c.Db s) *ᵥ z)) x00

/-- The control-free limiting state (12) and observation (13) of agent `i` (p.7):
`dX^{i,0} = (A X^{i,0} + Ā x^{0,0}) dt + (D X^{i,0} + D̄ x^{0,0}) dW⁰ + σ dWⁱ + σ̄ dW̄ⁱ`,
`X^{i,0}_0 = x`; `dY^{i,0} = (G X^{i,0} + Ḡ x^{0,0}) dt + σ̃ dW̄ⁱ`, `Y^{i,0}_0 = 0`. -/
def IsLimState0 (c : Coeffs n m d) (Sp : Space N d Ω) (i : Fin N)
    (x00 X0 Y0 : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  SolvesSDE Sp.filt Sp.P c.T Sp.B c.x (fun s ω z => c.A s *ᵥ z + c.Ab s *ᵥ x00 s ω)
      (agentDiff i (fun s ω z => c.D s *ᵥ z + c.Db s *ᵥ x00 s ω)
        (fun s _ => c.σ s) (fun s _ => c.σb s)) X0 ∧
    SolvesSDE Sp.filt Sp.P c.T Sp.B 0 (fun s ω _ => c.G s *ᵥ X0 s ω + c.Gb s *ᵥ x00 s ω)
      (agentDiff i (fun _ _ _ => 0) (fun _ _ => 0) (fun s _ => c.σt s)) Y0

/-- `σ{Y_s, θ_s; 0 ≤ s ≤ t}` (null-set augmented): `𝓕^{Yⁱ}`, `𝓕^{Y^{i,0}}`, `𝓕^{Ȳⁱ}` (p.8). -/
def obsOne (Sp : Space N d Ω) (θ : ℝ≥0 → Ω → Fin 1 → ℝ) (Y : ℝ≥0 → Ω → Fin n → ℝ) :
    ℝ≥0 → MeasurableSpace Ω :=
  obsSigma Sp.P (fun s ω => (Y s ω, θ s ω))

/-- `u ∈ 𝒰^{i,0}_d` (p.8): an `𝓕^{Y^{i,0}}`-adapted `ℝᵐ`-valued control (an `L²_𝓕` process) with
`E[sup_{0≤t≤T} |u_t|²] < ∞`; `Y0` is `Y^{i,0}` of (13). -/
def InUd0 (c : Coeffs n m d) (Sp : Space N d Ω) (θ : ℝ≥0 → Ω → Fin 1 → ℝ)
    (Y0 : ℝ≥0 → Ω → Fin n → ℝ) (u : ℝ≥0 → Ω → Fin m → ℝ) : Prop :=
  IsCtrl Sp c.T u ∧ AdaptedOn (obsOne Sp θ Y0) c.T u

/-- `u ∈ 𝒰ⁱ_d`, Definition 4.1 (p.8): `u ∈ 𝒰^{i,0}_d` and `u` is `𝓕^{Yⁱ}`-adapted, where `Yⁱ` is the
limiting observation (11) generated by `u` (every solution of (10)–(11) under `u`). -/
def InUd (c : Coeffs n m d) (Sp : Space N d Ω) (i : Fin N) (x0 : ℝ≥0 → Ω → Fin n → ℝ)
    (u0 : ℝ≥0 → Ω → Fin m → ℝ) (θ : ℝ≥0 → Ω → Fin 1 → ℝ) (Y0 : ℝ≥0 → Ω → Fin n → ℝ)
    (u : ℝ≥0 → Ω → Fin m → ℝ) : Prop :=
  InUd0 c Sp θ Y0 u ∧
    ∀ X Y, IsLimState c Sp i x0 u0 u X Y → AdaptedOn (obsOne Sp θ Y) c.T u

/-- `ū` is an optimal control of Problem (MFD) (p.8) for agent `i` and parameter `(x⁰, u⁰)`:
`ū ∈ 𝒰ⁱ_d` and `J_i(ū) ≤ J_i(v)` for every `v ∈ 𝒰ⁱ_d`, where `J_i` is the limiting cost (16)
evaluated along the solutions of (10). -/
def IsLimOptimal (c : Coeffs n m d) (Sp : Space N d Ω) (i : Fin N)
    (x0 : ℝ≥0 → Ω → Fin n → ℝ) (u0 : ℝ≥0 → Ω → Fin m → ℝ) (θ : ℝ≥0 → Ω → Fin 1 → ℝ)
    (Y0 : ℝ≥0 → Ω → Fin n → ℝ) (ub : ℝ≥0 → Ω → Fin m → ℝ) : Prop :=
  InUd c Sp i x0 u0 θ Y0 ub ∧
    ∀ v, InUd c Sp i x0 u0 θ Y0 v → ∀ Xb Yb X Y, IsLimState c Sp i x0 u0 ub Xb Yb →
      IsLimState c Sp i x0 u0 v X Y → quadCost c Sp.P Xb ub x0 u0 ≤ quadCost c Sp.P X v x0 u0

/-- `inf_{u ∈ 𝒰} J_i(u)` over a class `𝒰` of controls (given by `adm`), in `[−∞, +∞]`; `J_i` is (16)
along the solutions of (10). -/
noncomputable def limInf (c : Coeffs n m d) (Sp : Space N d Ω) (i : Fin N)
    (x0 : ℝ≥0 → Ω → Fin n → ℝ) (u0 : ℝ≥0 → Ω → Fin m → ℝ)
    (adm : (ℝ≥0 → Ω → Fin m → ℝ) → Prop) : EReal :=
  ⨅ (u : ℝ≥0 → Ω → Fin m → ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ) (Y : ℝ≥0 → Ω → Fin n → ℝ)
    (_ : adm u ∧ IsLimState c Sp i x0 u0 u X Y), ((quadCost c Sp.P X u x0 u0 : ℝ) : EReal)

/-- The homogeneous state (20) (p.9), also `𝕏ⁱ` of App. D (p.24):
`dX̃ = (A X̃ + B v) dt + (D X̃ + F v) dW⁰`, `X̃_0 = 0`. -/
def IsHomState (c : Coeffs n m d) (Sp : Space N d Ω) (v : ℝ≥0 → Ω → Fin m → ℝ)
    (X : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  SolvesSDE Sp.filt Sp.P c.T Sp.B 0 (fun s ω z => c.A s *ᵥ z + c.B s *ᵥ v s ω)
    (w0Diff (fun s ω z => c.D s *ᵥ z + c.F s *ᵥ v s ω)) X

/-- The homogeneous cost `J⁰_i(v) = ½ E[∫₀ᵀ {⟨Q X̃, X̃⟩ + ⟨R v, v⟩ + 2⟨S v, X̃⟩} dt + ⟨L_T X̃_T, X̃_T⟩]`
(App. D, p.24); twice it is the left side of the convexity condition (19). -/
noncomputable def homCost (c : Coeffs n m d) (P : Measure Ω) (X : ℝ≥0 → Ω → Fin n → ℝ)
    (v : ℝ≥0 → Ω → Fin m → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ ω, ((∫ s in Icc (0 : ℝ) c.T,
      ((c.Q s.toNNReal *ᵥ X s.toNNReal ω) ⬝ᵥ X s.toNNReal ω
        + (c.R s.toNNReal *ᵥ v s.toNNReal ω) ⬝ᵥ v s.toNNReal ω
        + 2 * ((c.S s.toNNReal *ᵥ v s.toNNReal ω) ⬝ᵥ X s.toNNReal ω)))
      + (c.LT *ᵥ X c.T ω) ⬝ᵥ X c.T ω) ∂P

/-- The martingale integrands `(η, ζ, ϑ)` of the adjoint BSDE written against all Brownian
coordinates: `η` on `W⁰`, the columns of `ζ` on `Wⁱ`, those of `ϑ` on `W̄ⁱ`, `0` elsewhere. -/
def adjK (i : Fin N) (η : ℝ≥0 → Ω → Fin n → ℝ) (ζ ϑ : ℝ≥0 → Ω → Matrix (Fin n) (Fin d) ℝ) :
    Fin (nK N d) → ℝ≥0 → Ω → Fin n → ℝ :=
  fun a s ω => agentDiff i (fun s ω _ => η s ω) ζ ϑ a s ω 0

/-- `(φ, η, ζ, ϑ) ∈ 𝕄_𝓕` solves the adjoint BSDE (21) (p.9) of agent `i` along `(X̄, ū)`:
`dφ = −{Aᵀφ + Dᵀη + Q(X̄ − α₁x⁰) + S(ū − β₂u⁰) + q} dt + η dW⁰ + ζ dWⁱ + ϑ dW̄ⁱ`,
`φ_T = L_T(X̄_T − α₃x⁰_T) + l_T`, in the sense of `Peng1990.SMP.SolvesBSDE`. -/
def IsAdjoint (c : Coeffs n m d) (Sp : Space N d Ω) (i : Fin N) (x0 : ℝ≥0 → Ω → Fin n → ℝ)
    (u0 : ℝ≥0 → Ω → Fin m → ℝ) (Xb : ℝ≥0 → Ω → Fin n → ℝ) (ub : ℝ≥0 → Ω → Fin m → ℝ)
    (φ η : ℝ≥0 → Ω → Fin n → ℝ) (ζ ϑ : ℝ≥0 → Ω → Matrix (Fin n) (Fin d) ℝ) : Prop :=
  SolvesBSDE Sp.filt Sp.P c.T Sp.B (fun ω => c.LT *ᵥ (Xb c.T ω - c.α₃ • x0 c.T ω) + c.lT)
    (fun s ω p K => (c.A s)ᵀ *ᵥ p + (c.D s)ᵀ *ᵥ K (idxEquiv N d (Sum.inl ())) +
      c.Q s *ᵥ (Xb s ω - c.α₁ • x0 s ω) + c.S s *ᵥ (ub s ω - c.β₂ • u0 s ω) + c.q s)
    φ (adjK i η ζ ϑ)

/-- The stationarity condition (18) (p.9), for almost every `t ∈ [0, T]`, almost surely:
`Bᵀ E[φ_t | 𝓕^{Ȳ}_t] + Fᵀ E[η_t | 𝓕^{Ȳ}_t] + Sᵀ E[X̄_t − α₂x⁰_t | 𝓕^{Ȳ}_t] + R(ū_t − β₁u⁰_t) + r_t = 0`.

**Formalization Note** (18) and the third line of (22) print `S_t E[X̄ⁱ_t − α₂x⁰_t | 𝓕^{Ȳⁱ}_t]`,
ill-typed for `m ≠ n` (`S ∈ ℝ^{n×m}`); the proof on p.9 and (29) have `Sᵀ`, used here. -/
def Stationary (c : Coeffs n m d) (Sp : Space N d Ω) (θ : ℝ≥0 → Ω → Fin 1 → ℝ)
    (x0 : ℝ≥0 → Ω → Fin n → ℝ) (u0 : ℝ≥0 → Ω → Fin m → ℝ) (Xb Yb : ℝ≥0 → Ω → Fin n → ℝ)
    (ub : ℝ≥0 → Ω → Fin m → ℝ) (φ η : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) c.T)), ∀ᵐ ω ∂Sp.P,
    (c.B s.toNNReal)ᵀ *ᵥ (condExp (obsOne Sp θ Yb s.toNNReal) Sp.P (φ s.toNNReal) ω)
      + (c.F s.toNNReal)ᵀ *ᵥ (condExp (obsOne Sp θ Yb s.toNNReal) Sp.P (η s.toNNReal) ω)
      + (c.S s.toNNReal)ᵀ *ᵥ (condExp (obsOne Sp θ Yb s.toNNReal) Sp.P
          (fun ω' => Xb s.toNNReal ω' - c.α₂ • x0 s.toNNReal ω') ω)
      + c.R s.toNNReal *ᵥ (ub s.toNNReal ω - c.β₁ • u0 s.toNNReal ω) + c.r s.toNNReal = 0

/-- `(X̄, ū, φ, η, ζ, ϑ)` solves the Hamiltonian system (22) (p.10) of agent `i`, with `Ȳ` the
observation (11) of `ū`: (10) with `ū`, the adjoint BSDE (21), and the stationarity condition
(18) (with `Sᵀ`, as in `Stationary`). -/
def IsHamiltonian (c : Coeffs n m d) (Sp : Space N d Ω) (i : Fin N) (θ : ℝ≥0 → Ω → Fin 1 → ℝ)
    (x0 : ℝ≥0 → Ω → Fin n → ℝ) (u0 : ℝ≥0 → Ω → Fin m → ℝ) (Xb Yb : ℝ≥0 → Ω → Fin n → ℝ)
    (ub : ℝ≥0 → Ω → Fin m → ℝ) (φ η : ℝ≥0 → Ω → Fin n → ℝ)
    (ζ ϑ : ℝ≥0 → Ω → Matrix (Fin n) (Fin d) ℝ) : Prop :=
  IsLimState c Sp i x0 u0 ub Xb Yb ∧ IsAdjoint c Sp i x0 u0 Xb ub φ η ζ ϑ ∧
    Stationary c Sp θ x0 u0 Xb Yb ub φ η

end IndefPOMFG


