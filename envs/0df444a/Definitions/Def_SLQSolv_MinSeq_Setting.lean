-- Prove2me | Definitions.Def_SLQSolv_MinSeq_Setting
-- name    : SLQSolv_MinSeq_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T09:18:31.843098+00:00
-- url     : https://prove2.me/theorems/539dc5b3-93f8-46dd-8e5c-ee67f3a12daf
-- title:
--   §§1–2, (H1)–(H2), Definition 2.1, pp. 2274–2278 — Problem (SLQ): state equation, cost, value function, finiteness, open- and closed-loop optimality
-- statement:
--   Fix a horizon $T>0$ and a complete probability space $(\Omega,\mathcal F,\mathbb P)$ carrying a standard one-dimensional Brownian motion $W$, with $\mathbb F=\{\mathcal F_t\}$ the natural filtration of $W$ augmented by the $\mathbb P$-null sets. **Problem (SLQ)** is the control of the linear state equation
--
--   $$
--   dX(s)=\big[A X+B u+b\big]ds+\big[C X+D u+\sigma\big]dW(s),\quad s\in[t,T],\qquad X(t)=x,
--   $$
--
--   with the quadratic cost
--
--   $$
--   J(t,x;u)=\mathbb E\Big[\langle GX(T),X(T)\rangle+2\langle g,X(T)\rangle+\int_t^T\Big(\langle QX,X\rangle+2\langle SX,u\rangle+\langle Ru,u\rangle+2\langle q,X\rangle+2\langle\rho,u\rangle\Big)ds\Big]
--   $$
--
--   over the admissible controls $\mathcal U[t,T]$: $\mathbb F$-progressively measurable $\mathbb R^m$-valued processes with $\mathbb E\int_t^T|u|^2ds<\infty$. The coefficients $A,C\in\mathbb R^{n\times n}$, $B,D\in\mathbb R^{n\times m}$ are deterministic functions of time, and the weights $Q,S,R,G$ are deterministic, with $Q,R,G$ symmetric. Assumption **(H1)** asks $A\in L^1$, $B,C\in L^2$, $D\in L^\infty$ on $[0,T]$, $b\in L^2_{\mathbb F}(\Omega;L^1(0,T;\mathbb R^n))$ and $\sigma\in L^2_{\mathbb F}(0,T;\mathbb R^n)$. Assumption **(H2)** asks $Q\in L^1$, $S\in L^2$, $R\in L^\infty$, $q\in L^2_{\mathbb F}(\Omega;L^1)$, $\rho\in L^2_{\mathbb F}$ and $g$ square integrable and $\mathcal F_T$-measurable. No sign condition is placed on $G,Q,R$.
--
--   The **value function** is $V(t,x)=\inf_{u\in\mathcal U[t,T]}J(t,x;u)\in[-\infty,\infty)$. Problem (SLQ)$^0$ is the problem with $b,\sigma,g,q,\rho=0$; its cost and value are written $J^0$ and $V^0$. Following Definition 2.1, the problem is **finite at $(t,x)$** if $V(t,x)>-\infty$, finite at $t$ if this holds for all $x$, and **finite** if it holds for all $(t,x)\in[0,T]\times\mathbb R^n$. A control $u^*$ is **open-loop optimal** at $(t,x)$ if $J(t,x;u^*)\le J(t,x;u)$ for all $u\in\mathcal U[t,T]$; a pair $(\Theta^*,v^*)\in L^2(t,T;\mathbb R^{m\times n})\times\mathcal U[t,T]$ is a **closed-loop optimal strategy** on $[t,T]$ if, for every $x$, the control $\Theta^*X^*+v^*$ along the solution $X^*$ of the closed-loop system beats every $u\in\mathcal U[t,T]$. Unique solvability means that any two optimal controls (strategies) coincide almost everywhere. The file also records the uniform convexity condition (4.2), $J^0(t,0;u)\ge\lambda\,\mathbb E\int_t^T|u|^2ds$ for some $\lambda>0$, the nonnegativity condition (5.6), $J^0(t,0;u)\ge0$, and the data with $R$ replaced by $R+\varepsilon I$.
--
--   These are the objects every result of the paper is stated in.
--
--   **Formalization Note** The probability basis is a probability space carrying a one-dimensional standard Brownian motion $W$ with its augmented natural filtration $\mathbb F$. Vectors are `Fin k → ℝ`, matrices `Matrix (Fin k) (Fin l) ℝ`, time is `ℝ≥0`, and the Euclidean inner product $\langle a,b\rangle$ is the dot product. The state from $(t,x)$ is a solution from time $0$ of the published SDE notion whose coefficients are switched on at $t$, so $X\equiv x$ on $[0,t]$; it is required to have a.s. continuous paths and $\mathbb E\sup_{s\le T}|X(s)|^2<\infty$. The cost is evaluated along a chosen solution (`state`), which is unique by [23, Proposition 2.1]. $V$ is an infimum in `EReal`, so $V=-\infty$ is `⊥` and finiteness is `⊥ < V`. The $L^p$ conditions on matrix coefficients are entrywise. Controls are processes on all of $[0,\infty)$; values before $t$ enter nothing.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), §1, (1.1)–(1.3), §2, (H1)–(H2), Definition 2.1, pp. 2274–2278; (4.2), p. 2284; (5.6), p. 2294

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Setting

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Matrix

namespace SLQSolv.MinSeq

open Peng1990.SMP ReflectedBSDE.Existence

/-- §1, p. 2274: a probability space `(Ω, 𝓕, P)` carrying a standard one-dimensional Brownian motion
`W` (Mathlib's `IsBrownianReal` through the published `Peng1990.SMP.IsStdBrownian`, `d = 1`). -/
structure Basis (Ω : Type*) [MeasurableSpace Ω] where
  P : Measure Ω
  W : ℝ≥0 → Ω → Fin 1 → ℝ
  prob : IsProbabilityMeasure P
  hW : IsStdBrownian P W

/-- The data of Problem (SLQ), (1.1)–(1.2), pp. 2274–2275: horizon `T`, deterministic coefficients
`A, C` (`n × n`), `B, D` (`n × m`), weights `Q` (`n × n`), `S` (`m × n`), `R` (`m × m`), `G` (`n × n`),
and random inhomogeneous terms `b, σ, q` (`ℝⁿ`-valued processes), `ρ` (`ℝᵐ`-valued), `g` (`ℝⁿ`-valued). -/
structure Data (Ω : Type*) (n m : ℕ) where
  T : ℝ≥0
  A : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ
  B : ℝ≥0 → Matrix (Fin n) (Fin m) ℝ
  C : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ
  D : ℝ≥0 → Matrix (Fin n) (Fin m) ℝ
  b : ℝ≥0 → Ω → Fin n → ℝ
  σ : ℝ≥0 → Ω → Fin n → ℝ
  Q : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ
  S : ℝ≥0 → Matrix (Fin m) (Fin n) ℝ
  R : ℝ≥0 → Matrix (Fin m) (Fin m) ℝ
  q : ℝ≥0 → Ω → Fin n → ℝ
  ρ : ℝ≥0 → Ω → Fin m → ℝ
  G : Matrix (Fin n) (Fin n) ℝ
  g : Ω → Fin n → ℝ

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {n m : ℕ}

/-- `𝔽 = {𝓕ₜ}`: the natural filtration of `W` augmented by all the `P`-null sets (p. 2274). -/
noncomputable abbrev filt (Bs : Basis Ω) : Filtration ℝ≥0 mΩ :=
  augmentedFiltration Bs.P Bs.hW

/-- `M(·) ∈ Lᵖ(a, b; ℝ^{k×l})`, read entrywise (equivalent to the Frobenius norm of p. 2277). -/
def MatLpOn {k l : ℕ} (p : ℝ≥0∞) (a b : ℝ≥0) (M : ℝ≥0 → Matrix (Fin k) (Fin l) ℝ) : Prop :=
  ∀ i j, MemLp (fun s : ℝ => M s.toNNReal i j) p (volume.restrict (Icc (a : ℝ) b))

/-- `φ ∈ L²_𝔽(Ω; L¹(0, T; ℝᵏ))` (p. 2277): progressively measurable with `E(∫₀ᵀ |φ(s)| ds)² < ∞`. -/
def L2L1 {k : ℕ} (Bs : Basis Ω) (T : ℝ≥0) (φ : ℝ≥0 → Ω → Fin k → ℝ) : Prop :=
  IsStronglyProgressive (filt Bs) φ ∧
    ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) T, ‖φ s.toNNReal ω‖ₑ) ^ 2 ∂Bs.P < ⊤

/-- (H1), p. 2277, with the fixed horizon `T > 0`: `A ∈ L¹`, `B ∈ L²`, `C ∈ L²`, `D ∈ L^∞`,
`b ∈ L²_𝔽(Ω; L¹(0, T; ℝⁿ))`, `σ ∈ L²_𝔽(0, T; ℝⁿ)`. -/
structure H1 (Bs : Basis Ω) (d : Data Ω n m) : Prop where
  T_pos : 0 < d.T
  A : MatLpOn 1 0 d.T d.A
  B : MatLpOn 2 0 d.T d.B
  C : MatLpOn 2 0 d.T d.C
  D : MatLpOn ⊤ 0 d.T d.D
  b : L2L1 Bs d.T d.b
  σ : L2F (filt Bs) Bs.P d.T d.σ

/-- (H2), p. 2278: `Q ∈ L¹(0, T; 𝕊ⁿ)`, `S ∈ L²`, `R ∈ L^∞(0, T; 𝕊ᵐ)`, `q ∈ L²_𝔽(Ω; L¹(0, T; ℝⁿ))`,
`ρ ∈ L²_𝔽(0, T; ℝᵐ)`, `G ∈ 𝕊ⁿ`, `g ∈ L²_{𝓕_T}(Ω; ℝⁿ)`. No sign condition on `G, Q, R`. -/
structure H2 (Bs : Basis Ω) (d : Data Ω n m) : Prop where
  Q : MatLpOn 1 0 d.T d.Q
  S : MatLpOn 2 0 d.T d.S
  R : MatLpOn ⊤ 0 d.T d.R
  Q_symm : ∀ s, (d.Q s).IsSymm
  R_symm : ∀ s, (d.R s).IsSymm
  q : L2L1 Bs d.T d.q
  ρ : L2F (filt Bs) Bs.P d.T d.ρ
  G_symm : d.G.IsSymm
  g_meas : StronglyMeasurable[filt Bs d.T] d.g
  g_sq : ∫⁻ ω, ‖d.g ω‖ₑ ^ 2 ∂Bs.P < ⊤

/-- The admissible controls `𝒰[t, T]` (p. 2274): `𝔽`-progressively measurable `ℝᵐ`-valued `u` with
`E ∫ₜᵀ |u(s)|² ds < ∞`. Values before `t` enter no object. -/
def Adm (Bs : Basis Ω) (d : Data Ω n m) (t : ℝ≥0) (u : ℝ≥0 → Ω → Fin m → ℝ) : Prop :=
  IsStronglyProgressive (filt Bs) u ∧
    ∫⁻ ω, ∫⁻ s in Icc (t : ℝ) d.T, ‖u s.toNNReal ω‖ₑ ^ 2 ∂volume ∂Bs.P < ⊤

/-- `X` is a strong solution of the state equation (1.1) on `[t, T]` with `X(t) = x`:
`dX = (AX + Bu + b) ds + (CX + Du + σ) dW`. Encoded from time `0` with coefficients switched on at
`t` (so `X = x` on `[0, t]`), with a.s. continuous paths and `E sup_{s ≤ T} |X(s)|² < ∞`. -/
def IsState (Bs : Basis Ω) (d : Data Ω n m) (t : ℝ≥0) (x : Fin n → ℝ)
    (u : ℝ≥0 → Ω → Fin m → ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  SolvesSDE (filt Bs) Bs.P d.T Bs.W x
      (fun s ω y => if t ≤ s then d.A s *ᵥ y + d.B s *ᵥ u s ω + d.b s ω else 0)
      (fun _ s ω y => if t ≤ s then d.C s *ᵥ y + d.D s *ᵥ u s ω + d.σ s ω else 0) X ∧
    (∀ᵐ ω ∂Bs.P, ContinuousOn (fun s => X s ω) (Icc 0 d.T)) ∧
    ∫⁻ ω, ⨆ s ∈ Iic d.T, ‖X s ω‖ₑ ^ 2 ∂Bs.P < ⊤

open Classical in
/-- `X(· ; t, x, u)`: the state of `u` from `(t, x)`, chosen among the solutions of (1.1)
(unique by [23, Proposition 2.1], p. 2278); `0` if there is none. -/
noncomputable def state (Bs : Basis Ω) (d : Data Ω n m) (t : ℝ≥0) (x : Fin n → ℝ)
    (u : ℝ≥0 → Ω → Fin m → ℝ) : ℝ≥0 → Ω → Fin n → ℝ :=
  if h : ∃ X, IsState Bs d t x u X then h.choose else 0

/-- The cost (1.2) along a state process `X`:
`E[⟨G X(T), X(T)⟩ + 2⟨g, X(T)⟩ + ∫ₜᵀ (⟨QX, X⟩ + 2⟨SX, u⟩ + ⟨Ru, u⟩ + 2⟨q, X⟩ + 2⟨ρ, u⟩) ds]`,
the block form of (1.2) written out (`⟨SᵀU, X⟩ = ⟨SX, U⟩`). -/
noncomputable def costAlong (Bs : Basis Ω) (d : Data Ω n m) (t : ℝ≥0)
    (u : ℝ≥0 → Ω → Fin m → ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ) : ℝ :=
  ∫ ω, ((d.G *ᵥ X d.T ω) ⬝ᵥ X d.T ω + 2 * (d.g ω ⬝ᵥ X d.T ω)
    + ∫ s in Icc (t : ℝ) d.T,
        ((d.Q s.toNNReal *ᵥ X s.toNNReal ω) ⬝ᵥ X s.toNNReal ω
          + 2 * ((d.S s.toNNReal *ᵥ X s.toNNReal ω) ⬝ᵥ u s.toNNReal ω)
          + (d.R s.toNNReal *ᵥ u s.toNNReal ω) ⬝ᵥ u s.toNNReal ω
          + 2 * (d.q s.toNNReal ω ⬝ᵥ X s.toNNReal ω)
          + 2 * (d.ρ s.toNNReal ω ⬝ᵥ u s.toNNReal ω))) ∂Bs.P

/-- The cost functional `J(t, x; u(·))` of (1.2). -/
noncomputable def J (Bs : Basis Ω) (d : Data Ω n m) (t : ℝ≥0) (x : Fin n → ℝ)
    (u : ℝ≥0 → Ω → Fin m → ℝ) : ℝ :=
  costAlong Bs d t u (state Bs d t x u)

/-- The data of Problem (SLQ)⁰ (p. 2275): `b, σ, g, q, ρ = 0`. -/
def Data.hom (d : Data Ω n m) : Data Ω n m :=
  { d with b := 0, σ := 0, q := 0, ρ := 0, g := 0 }

/-- `J⁰(t, x; u(·))`, the cost of Problem (SLQ)⁰. -/
noncomputable def J0 (Bs : Basis Ω) (d : Data Ω n m) (t : ℝ≥0) (x : Fin n → ℝ)
    (u : ℝ≥0 → Ω → Fin m → ℝ) : ℝ :=
  J Bs d.hom t x u

/-- The value function (1.3), `V(t, x) = inf_{u ∈ 𝒰[t, T]} J(t, x; u)`, in `[−∞, ∞)`. -/
noncomputable def V (Bs : Basis Ω) (d : Data Ω n m) (t : ℝ≥0) (x : Fin n → ℝ) : EReal :=
  ⨅ u : {u // Adm Bs d t u}, ((J Bs d t x u.1 : ℝ) : EReal)

/-- `V⁰(t, x)`, the value function of Problem (SLQ)⁰. -/
noncomputable def V0 (Bs : Basis Ω) (d : Data Ω n m) (t : ℝ≥0) (x : Fin n → ℝ) : EReal :=
  V Bs d.hom t x

/-- `E ∫ₜᵀ |u(s)|² ds` with the Euclidean norm `|u|² = u ⬝ᵥ u`. -/
noncomputable def sqNorm (Bs : Basis Ω) (d : Data Ω n m) (t : ℝ≥0)
    (u : ℝ≥0 → Ω → Fin m → ℝ) : ℝ :=
  ∫ ω, ∫ s in Icc (t : ℝ) d.T, u s.toNNReal ω ⬝ᵥ u s.toNNReal ω ∂volume ∂Bs.P

/-- Definition 2.1(i): finite at `(t, x)`, (2.1) `V(t, x) > −∞`. -/
def IsFiniteAt (Bs : Basis Ω) (d : Data Ω n m) (t : ℝ≥0) (x : Fin n → ℝ) : Prop :=
  ⊥ < V Bs d t x

/-- Definition 2.1(i): finite at `t`. -/
def IsFiniteAtTime (Bs : Basis Ω) (d : Data Ω n m) (t : ℝ≥0) : Prop :=
  ∀ x, IsFiniteAt Bs d t x

/-- Definition 2.1(i): finite, (2.1) for all `(t, x) ∈ [0, T] × ℝⁿ`. -/
def IsFinite (Bs : Basis Ω) (d : Data Ω n m) : Prop :=
  ∀ t ≤ d.T, IsFiniteAtTime Bs d t

/-- Definition 2.1(ii), (2.2): `u` is an open-loop optimal control for `(t, x)`. -/
def IsOpenLoopOptimal (Bs : Basis Ω) (d : Data Ω n m) (t : ℝ≥0) (x : Fin n → ℝ)
    (u : ℝ≥0 → Ω → Fin m → ℝ) : Prop :=
  Adm Bs d t u ∧ ∀ v, Adm Bs d t v → J Bs d t x u ≤ J Bs d t x v

/-- Open-loop solvable at `(t, x)`. -/
def OpenLoopSolvableAt (Bs : Basis Ω) (d : Data Ω n m) (t : ℝ≥0) (x : Fin n → ℝ) : Prop :=
  ∃ u, IsOpenLoopOptimal Bs d t x u

/-- Two processes agree `ds ⊗ dP`-a.e. on `[t, T] × Ω` (equality in `𝒰[t, T]`). -/
def AEEqOn {k : ℕ} (Bs : Basis Ω) (t T : ℝ≥0) (u v : ℝ≥0 → Ω → Fin k → ℝ) : Prop :=
  ∀ᵐ q ∂((volume.restrict (Icc (t : ℝ) T)).prod Bs.P), u q.1.toNNReal q.2 = v q.1.toNNReal q.2

/-- Uniquely open-loop solvable at `(t, x)`: an open-loop optimal control exists and any two agree
as elements of `𝒰[t, T]`. -/
def UniquelyOpenLoopSolvableAt (Bs : Basis Ω) (d : Data Ω n m) (t : ℝ≥0) (x : Fin n → ℝ) :
    Prop :=
  OpenLoopSolvableAt Bs d t x ∧
    ∀ u v, IsOpenLoopOptimal Bs d t x u → IsOpenLoopOptimal Bs d t x v → AEEqOn Bs t d.T u v

/-- (Uniquely) open-loop solvable on `[0, T) × ℝⁿ`. -/
def OpenLoopSolvable (Bs : Basis Ω) (d : Data Ω n m) : Prop :=
  ∀ t < d.T, ∀ x, OpenLoopSolvableAt Bs d t x

def UniquelyOpenLoopSolvable (Bs : Basis Ω) (d : Data Ω n m) : Prop :=
  ∀ t < d.T, ∀ x, UniquelyOpenLoopSolvableAt Bs d t x

/-- `X` solves the closed-loop system (2.4) of `(Θ, v)` from `(t, x)`: the state equation with the
control `ΘX + v`. -/
def IsClosedLoopState (Bs : Basis Ω) (d : Data Ω n m) (t : ℝ≥0)
    (Θ : ℝ≥0 → Matrix (Fin m) (Fin n) ℝ) (v : ℝ≥0 → Ω → Fin m → ℝ) (x : Fin n → ℝ)
    (X : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  IsState Bs d t x (fun s ω => Θ s *ᵥ X s ω + v s ω) X

/-- Definition 2.1(iii), (2.3): `(Θ, v) ∈ L²(t, T; ℝ^{m×n}) × 𝒰[t, T]` is a closed-loop optimal
strategy on `[t, T]`: for every `x` the closed-loop system (2.4) has a solution, and for every
solution `X*` and every `u ∈ 𝒰[t, T]`, `J(t, x; ΘX* + v) ≤ J(t, x; u)`. -/
def IsClosedLoopOptimal (Bs : Basis Ω) (d : Data Ω n m) (t : ℝ≥0)
    (Θ : ℝ≥0 → Matrix (Fin m) (Fin n) ℝ) (v : ℝ≥0 → Ω → Fin m → ℝ) : Prop :=
  MatLpOn 2 t d.T Θ ∧ Adm Bs d t v ∧
    ∀ x, (∃ X, IsClosedLoopState Bs d t Θ v x X) ∧
      ∀ X, IsClosedLoopState Bs d t Θ v x X →
        ∀ u, Adm Bs d t u → J Bs d t x (fun s ω => Θ s *ᵥ X s ω + v s ω) ≤ J Bs d t x u

/-- Closed-loop solvable on `[t, T]`. -/
def ClosedLoopSolvableOn (Bs : Basis Ω) (d : Data Ω n m) (t : ℝ≥0) : Prop :=
  ∃ Θ v, IsClosedLoopOptimal Bs d t Θ v

/-- Closed-loop solvable: on every `[t, T]`, `t ∈ [0, T)`. -/
def ClosedLoopSolvable (Bs : Basis Ω) (d : Data Ω n m) : Prop :=
  ∀ t < d.T, ClosedLoopSolvableOn Bs d t

/-- Uniquely closed-loop solvable: on every `[t, T]` a closed-loop optimal strategy exists and any two
agree (`Θ` a.e. on `[t, T]`, `v` in `𝒰[t, T]`). -/
def UniquelyClosedLoopSolvable (Bs : Basis Ω) (d : Data Ω n m) : Prop :=
  ∀ t < d.T, ClosedLoopSolvableOn Bs d t ∧
    ∀ Θ₁ v₁ Θ₂ v₂, IsClosedLoopOptimal Bs d t Θ₁ v₁ → IsClosedLoopOptimal Bs d t Θ₂ v₂ →
      (∀ᵐ s ∂(volume.restrict (Icc (t : ℝ) d.T)), Θ₁ s.toNNReal = Θ₂ s.toNNReal) ∧
        AEEqOn Bs t d.T v₁ v₂

/-- (4.2)/(3.7) at time `t`: `u ↦ J⁰(t, 0; u)` is uniformly convex,
`J⁰(t, 0; u) ≥ λ E ∫ₜᵀ |u|² ds` for all `u ∈ 𝒰[t, T]`, for some `λ > 0`. -/
def IsUnifConvex (Bs : Basis Ω) (d : Data Ω n m) (t : ℝ≥0) : Prop :=
  ∃ lam : ℝ, 0 < lam ∧ ∀ u, Adm Bs d t u → lam * sqNorm Bs d t u ≤ J0 Bs d t 0 u

/-- (5.6) at time `t`: `J⁰(t, 0; u) ≥ 0` for all `u ∈ 𝒰[t, T]`. -/
def IsNonnegJ0 (Bs : Basis Ω) (d : Data Ω n m) (t : ℝ≥0) : Prop :=
  ∀ u, Adm Bs d t u → 0 ≤ J0 Bs d t 0 u

/-- The data with `R` replaced by `R + εI` (Problem (SLQ)⁰_ε of p. 2294 when applied to `d.hom`). -/
def Data.addR (d : Data Ω n m) (ε : ℝ) : Data Ω n m :=
  { d with R := fun s => d.R s + ε • (1 : Matrix (Fin m) (Fin m) ℝ) }

end SLQSolv.MinSeq


