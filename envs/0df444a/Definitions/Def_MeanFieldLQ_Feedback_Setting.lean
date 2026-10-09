-- Prove2me | Definitions.Def_MeanFieldLQ_Feedback_Setting
-- name    : MeanFieldLQ_Feedback_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T05:34:51.41699+00:00
-- url     : https://prove2.me/theorems/e680b01a-b98b-434c-8ddb-bd8210e6c7dd
-- title:
--   §1–§3, pp. 2809–2820 — Problem (MF-LQ): (H1)–(H2), the mean-field state equation (1.1), the cost (1.2), optimal pairs, the MF-BSDE (3.1) and the MF-FBSDE (3.3)
-- statement:
--   This file sets up Problem (MF-LQ) of Yong (2013).
--
--   **Stochastic basis.** $(\Omega,\mathcal F,\mathbb P)$ is a complete probability space carrying a one-dimensional standard Brownian motion $W$, and $\mathbb F=\{\mathcal F_t\}_{t\ge0}$ is the natural filtration of $W$ augmented by all the $\mathbb P$-null sets. $T>0$ is the horizon, and $\mathcal U[0,T]=L^2_{\mathbb F}(0,T;\mathbb R^m)$ is the set of $\mathbb F$-progressively measurable $u$ with $\mathbb E\int_0^T|u(s)|^2\,ds<\infty$ (the **admissible controls**).
--
--   **Data.** Deterministic matrix-valued functions $A,\bar A,C,\bar C$ ($n\times n$), $B,\bar B,D,\bar D$ ($n\times m$), weights $Q,\bar Q$ ($n\times n$), $R,\bar R$ ($m\times m$) and matrices $G,\bar G$ ($n\times n$).
--
--   1. **(H1)**: $A,\bar A,C,\bar C\in L^\infty(0,T;\mathbb R^{n\times n})$ and $B,\bar B,D,\bar D\in L^\infty(0,T;\mathbb R^{n\times m})$.
--   2. **(H2)**: $Q,\bar Q\in L^\infty(0,T;\mathcal S^n)$, $R,\bar R\in L^\infty(0,T;\mathcal S^m)$, $G,\bar G\in\mathcal S^n$, and for some $\delta>0$ and all $s\in[0,T]$
--   $$Q(s)\ge0,\quad Q(s)+\bar Q(s)\ge0,\quad R(s)\ge\delta I,\quad R(s)+\bar R(s)\ge\delta I,\quad G\ge0,\quad G+\bar G\ge0 .$$
--   Nothing is assumed on the sign of $\bar Q$, $\bar R$, $\bar G$ alone.
--
--   **State equation (1.1).** For $x\in\mathbb R^n$ and $u\in\mathcal U[0,T]$, the state $X$ solves
--   $$dX=\big(AX+\bar A\,\mathbb E[X]+Bu+\bar B\,\mathbb E[u]\big)ds+\big(CX+\bar C\,\mathbb E[X]+Du+\bar D\,\mathbb E[u]\big)dW,\qquad X(0)=x,$$
--   on $[0,T]$, where $\mathbb E[X(s)]$ is the expectation of the solution itself. The space $\widehat{\mathcal X}[0,T]$ consists of processes with continuous paths and $\mathbb E\sup_{s\in[0,T]}|X(s)|^2<\infty$.
--
--   **Cost (1.2).**
--   $$J(x;u)=\mathbb E\Big\{\int_0^T\big[\langle QX,X\rangle+\langle\bar Q\,\mathbb E[X],\mathbb E[X]\rangle+\langle Ru,u\rangle+\langle\bar R\,\mathbb E[u],\mathbb E[u]\rangle\big]ds+\langle GX(T),X(T)\rangle+\langle\bar G\,\mathbb E[X(T)],\mathbb E[X(T)]\rangle\Big\}.$$
--   A pair $(X^*,u^*)$ is an **optimal pair** for $x$ if $u^*$ is admissible, $X^*$ is its state, and $J(x;u^*)\le J(x;u)$ for every admissible $u$.
--
--   **MF-BSDE (3.1) and MF-FBSDE (3.3).** Given $X^*$, $(Y,Z)$ is an adapted solution of
--   $$dY=-\big(A^TY+\bar A^T\mathbb E[Y]+C^TZ+\bar C^T\mathbb E[Z]+QX^*+\bar Q\,\mathbb E[X^*]\big)ds+Z\,dW,\qquad Y(T)=GX^*(T)+\bar G\,\mathbb E[X^*(T)],$$
--   and the **stationarity condition (3.2)** reads $Ru^*+\bar R\,\mathbb E[u^*]+B^TY+\bar B^T\mathbb E[Y]+D^TZ+\bar D^T\mathbb E[Z]=0$. A 4-tuple $(X^*,u^*,Y,Z)$ solves the MF-FBSDE (3.3) when $u^*$ is admissible, $X^*$ is its state, $(Y,Z)$ solves (3.1) and (3.2) holds.
--
--   These objects are shared by every statement of the mission: well-posedness of the state equation, the optimality system, and the Riccati feedback of Theorem 4.1.
--
--   **Formalization Note.** States are `Fin n → ℝ`, time is `ℝ≥0`, and $\mathbb E[\cdot]$ is a Bochner integral. Stochastic integrals, SDE and BSDE solutions and $L^2_{\mathbb F}$ come from the published `Peng1990.SMP.Stochastic`; $\mathbb F$ is `ReflectedBSDE.Existence.augmentedFiltration`. The SDE solution class requires progressive measurability and $\sup_{t\le T}\mathbb E|X(t)|^2<\infty$, and the identity holds at each $t\in[0,T]$ almost surely. $L^\infty$ coefficients are read as measurable functions on $[0,\infty)$ with an entrywise bound on $[0,T]$, which is a bounded representative. Matrix inequalities are `PosSemidef`, and $M\ge\delta I$ is `(M - δ • 1).PosSemidef`. The equality of controls and of $Z$-components is $ds\otimes d\mathbb P$-a.e. on $[0,T]\times\Omega$, so (3.2) is required $ds\otimes d\mathbb P$-a.e.
-- source:
--   Yong, Linear-Quadratic Optimal Control Problems for Mean-Field Stochastic Differential Equations, SIAM J. Control Optim. 51(4) (2013), pp. 2809–2820, (1.1), (1.2), Problem (MF-LQ), (H1) (2.1), (H2) (2.2)–(2.3), 𝒳̂[0, T] p. 2813, (3.1), (3.2), (3.3)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Setting

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal ENNReal

namespace MeanFieldLQ.Feedback

open Peng1990.SMP

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A matrix-valued deterministic coefficient `M : [0, ∞) → ℝ^{a×b}` is measurable and bounded
on `[0, T]` (entrywise bound; equivalent to a bound in any matrix norm): the bounded-representative
reading of `M(·) ∈ L^∞(0, T; ℝ^{a×b})`. -/
def IsBddMeas {a b : ℕ} (T : ℝ≥0) (M : ℝ≥0 → Matrix (Fin a) (Fin b) ℝ) : Prop :=
  Measurable (fun s => Matrix.of.symm (M s)) ∧ ∃ K : ℝ, ∀ s ≤ T, ∀ i j, |M s i j| ≤ K

/-- The data of Problem (MF-LQ) (p. 2809–2810): coefficients `A, Ā, C, C̄` (`n × n`),
`B, B̄, D, D̄` (`n × m`) of the state equation (1.1), weights `Q, Q̄` (`n × n`), `R, R̄`
(`m × m`) and terminal weights `G, Ḡ` (`n × n`) of the cost (1.2). -/
structure Data (n m : ℕ) where
  A : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ
  Abar : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ
  B : ℝ≥0 → Matrix (Fin n) (Fin m) ℝ
  Bbar : ℝ≥0 → Matrix (Fin n) (Fin m) ℝ
  C : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ
  Cbar : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ
  D : ℝ≥0 → Matrix (Fin n) (Fin m) ℝ
  Dbar : ℝ≥0 → Matrix (Fin n) (Fin m) ℝ
  Q : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ
  Qbar : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ
  R : ℝ≥0 → Matrix (Fin m) (Fin m) ℝ
  Rbar : ℝ≥0 → Matrix (Fin m) (Fin m) ℝ
  G : Matrix (Fin n) (Fin n) ℝ
  Gbar : Matrix (Fin n) (Fin n) ℝ

/-- Hypothesis (H1), (2.1), p. 2814: `A, Ā, C, C̄ ∈ L^∞(0, T; ℝ^{n×n})` and
`B, B̄, D, D̄ ∈ L^∞(0, T; ℝ^{n×m})`. -/
structure H1 {n m : ℕ} (T : ℝ≥0) (d : Data n m) : Prop where
  A : IsBddMeas T d.A
  Abar : IsBddMeas T d.Abar
  C : IsBddMeas T d.C
  Cbar : IsBddMeas T d.Cbar
  B : IsBddMeas T d.B
  Bbar : IsBddMeas T d.Bbar
  D : IsBddMeas T d.D
  Dbar : IsBddMeas T d.Dbar

/-- Hypothesis (H2), (2.2)–(2.3), p. 2814, with the constant `δ > 0`:
`Q, Q̄ ∈ L^∞(0, T; 𝒮ⁿ)`, `R, R̄ ∈ L^∞(0, T; 𝒮ᵐ)`, `G, Ḡ ∈ 𝒮ⁿ`, and for `s ∈ [0, T]`
`Q(s) ≥ 0`, `Q(s) + Q̄(s) ≥ 0`, `R(s) ≥ δI`, `R(s) + R̄(s) ≥ δI`, `G ≥ 0`, `G + Ḡ ≥ 0`.
Nothing is assumed on the sign of `Q̄`, `R̄`, `Ḡ` alone. -/
structure H2 {n m : ℕ} (T : ℝ≥0) (δ : ℝ) (d : Data n m) : Prop where
  Q : IsBddMeas T d.Q
  Qbar : IsBddMeas T d.Qbar
  R : IsBddMeas T d.R
  Rbar : IsBddMeas T d.Rbar
  Q_symm : ∀ s ≤ T, (d.Q s).IsSymm
  Qbar_symm : ∀ s ≤ T, (d.Qbar s).IsSymm
  R_symm : ∀ s ≤ T, (d.R s).IsSymm
  Rbar_symm : ∀ s ≤ T, (d.Rbar s).IsSymm
  G_symm : d.G.IsSymm
  Gbar_symm : d.Gbar.IsSymm
  delta_pos : 0 < δ
  Q_psd : ∀ s ≤ T, (d.Q s).PosSemidef
  QQbar_psd : ∀ s ≤ T, (d.Q s + d.Qbar s).PosSemidef
  R_ge : ∀ s ≤ T, (d.R s - δ • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef
  RRbar_ge : ∀ s ≤ T, (d.R s + d.Rbar s - δ • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef
  G_psd : d.G.PosSemidef
  GGbar_psd : (d.G + d.Gbar).PosSemidef

/-- The filtration `𝔽` of the paper (p. 2809): the natural filtration of `W` augmented by all the
`μ`-null sets. -/
noncomputable abbrev filt (μ : Measure Ω) {W : ℝ≥0 → Ω → Fin 1 → ℝ} (hW : IsStdBrownian μ W) :
    Filtration ℝ≥0 mΩ :=
  ReflectedBSDE.Existence.augmentedFiltration μ hW

/-- The mean `𝔼[X(s)] = ∫ X(s, ω) dP(ω)` of a vector-valued process at time `s`. -/
noncomputable def mean {ι : Type*} [Fintype ι] (μ : Measure Ω) (X : ℝ≥0 → Ω → ι → ℝ)
    (s : ℝ≥0) : ι → ℝ :=
  ∫ ω, X s ω ∂μ

/-- Two processes agree `ds ⊗ dP`-almost everywhere on `[0, T] × Ω`; this is the equality of
elements of `L²_𝔽(0, T)` (controls, the `Z`-component of a BSDE). -/
def AEEqOn {E : Type*} (μ : Measure Ω) (T : ℝ≥0) (u v : ℝ≥0 → Ω → E) : Prop :=
  ∀ᵐ q ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod μ), u q.1.toNNReal q.2 = v q.1.toNNReal q.2

/-- The state equation (1.1), p. 2809: `X` solves on `[0, T]`
`dX = (A X + Ā 𝔼[X] + B u + B̄ 𝔼[u]) ds + (C X + C̄ 𝔼[X] + D u + D̄ 𝔼[u]) dW`, `X(0) = x`,
where `𝔼[X(s)]` is the mean of the solution `X` itself and `𝔼[u(s)]` that of the control. -/
def IsState {n m : ℕ} (μ : Measure Ω) {W : ℝ≥0 → Ω → Fin 1 → ℝ} (hW : IsStdBrownian μ W)
    (T : ℝ≥0) (d : Data n m) (x : Fin n → ℝ) (u : ℝ≥0 → Ω → Fin m → ℝ)
    (X : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  SolvesSDE (filt μ hW) μ T W x
    (fun s ω y => d.A s *ᵥ y + d.Abar s *ᵥ mean μ X s + d.B s *ᵥ u s ω
      + d.Bbar s *ᵥ mean μ u s)
    (fun _ s ω y => d.C s *ᵥ y + d.Cbar s *ᵥ mean μ X s + d.D s *ᵥ u s ω
      + d.Dbar s *ᵥ mean μ u s)
    X

/-- Membership in `𝒳̂[0, T]` (p. 2813): almost every path is continuous on `[0, T]` and
`𝔼[sup_{s ∈ [0, T]} |X(s)|²] < ∞`. -/
def InXhat {n : ℕ} (μ : Measure Ω) (T : ℝ≥0) (X : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  (∀ᵐ ω ∂μ, ContinuousOn (fun s => X s ω) (Set.Icc 0 T)) ∧
    ∫⁻ ω, ⨆ s ∈ Set.Icc 0 T, ‖X s ω‖ₑ ^ 2 ∂μ < ⊤

/-- The cost functional (1.2), p. 2810, evaluated on a control `u` and a process `X` (its state):
`𝔼{∫₀ᵀ [⟨QX, X⟩ + ⟨Q̄𝔼[X], 𝔼[X]⟩ + ⟨Ru, u⟩ + ⟨R̄𝔼[u], 𝔼[u]⟩] ds + ⟨GX(T), X(T)⟩
+ ⟨Ḡ𝔼[X(T)], 𝔼[X(T)]⟩}`. -/
noncomputable def cost {n m : ℕ} (μ : Measure Ω) (T : ℝ≥0) (d : Data n m)
    (u : ℝ≥0 → Ω → Fin m → ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ) : ℝ :=
  (∫ ω, (∫ s in Set.Icc (0 : ℝ) T,
      ((d.Q s.toNNReal *ᵥ X s.toNNReal ω) ⬝ᵥ X s.toNNReal ω
        + (d.Qbar s.toNNReal *ᵥ mean μ X s.toNNReal) ⬝ᵥ mean μ X s.toNNReal
        + (d.R s.toNNReal *ᵥ u s.toNNReal ω) ⬝ᵥ u s.toNNReal ω
        + (d.Rbar s.toNNReal *ᵥ mean μ u s.toNNReal) ⬝ᵥ mean μ u s.toNNReal)) ∂μ)
  + ∫ ω, ((d.G *ᵥ X T ω) ⬝ᵥ X T ω + (d.Gbar *ᵥ mean μ X T) ⬝ᵥ mean μ X T) ∂μ

/-- An optimal pair of Problem (MF-LQ) for the initial state `x` (p. 2810): `u* ∈ 𝒰[0, T]`,
`X*` is its state, and `J(x; u*) ≤ J(x; u)` for every admissible control `u` with state `X`. -/
def IsOptimalPair {n m : ℕ} (μ : Measure Ω) {W : ℝ≥0 → Ω → Fin 1 → ℝ}
    (hW : IsStdBrownian μ W) (T : ℝ≥0) (d : Data n m) (x : Fin n → ℝ)
    (u : ℝ≥0 → Ω → Fin m → ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  L2F (filt μ hW) μ T u ∧ IsState μ hW T d x u X ∧
    ∀ (v : ℝ≥0 → Ω → Fin m → ℝ) (Y : ℝ≥0 → Ω → Fin n → ℝ),
      L2F (filt μ hW) μ T v → IsState μ hW T d x v Y → cost μ T d u X ≤ cost μ T d v Y

/-- The mean-field BSDE (3.1), p. 2819, driven by the state `X`:
`dY = −(AᵀY + Āᵀ𝔼[Y] + CᵀZ + C̄ᵀ𝔼[Z] + QX + Q̄𝔼[X]) ds + Z dW`, `Y(T) = GX(T) + Ḡ𝔼[X(T)]`;
`(Y, Z)` is an adapted solution (both in `L²_𝔽(0, T; ℝⁿ)`). -/
def IsMFBSDE {n m : ℕ} (μ : Measure Ω) {W : ℝ≥0 → Ω → Fin 1 → ℝ} (hW : IsStdBrownian μ W)
    (T : ℝ≥0) (d : Data n m) (X Y Z : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  SolvesBSDE (filt μ hW) μ T W (fun ω => d.G *ᵥ X T ω + d.Gbar *ᵥ mean μ X T)
    (fun s ω y k => (d.A s)ᵀ *ᵥ y + (d.Abar s)ᵀ *ᵥ mean μ Y s + (d.C s)ᵀ *ᵥ k 0
      + (d.Cbar s)ᵀ *ᵥ mean μ Z s + d.Q s *ᵥ X s ω + d.Qbar s *ᵥ mean μ X s)
    Y (fun _ => Z)

/-- The stationarity condition (3.2), p. 2819:
`Ru + R̄𝔼[u] + BᵀY + B̄ᵀ𝔼[Y] + DᵀZ + D̄ᵀ𝔼[Z] = 0` for `ds ⊗ dP`-a.e. `(s, ω) ∈ [0, T] × Ω`. -/
def Stationary {n m : ℕ} (μ : Measure Ω) (T : ℝ≥0) (d : Data n m)
    (u : ℝ≥0 → Ω → Fin m → ℝ) (Y Z : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  ∀ᵐ q ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod μ),
    d.R q.1.toNNReal *ᵥ u q.1.toNNReal q.2 + d.Rbar q.1.toNNReal *ᵥ mean μ u q.1.toNNReal
      + (d.B q.1.toNNReal)ᵀ *ᵥ Y q.1.toNNReal q.2
      + (d.Bbar q.1.toNNReal)ᵀ *ᵥ mean μ Y q.1.toNNReal
      + (d.D q.1.toNNReal)ᵀ *ᵥ Z q.1.toNNReal q.2
      + (d.Dbar q.1.toNNReal)ᵀ *ᵥ mean μ Z q.1.toNNReal = 0

/-- An adapted solution `(X*, u*, Y, Z)` of the MF-FBSDE (3.3), p. 2820: `u* ∈ 𝒰[0, T]`, `X*` is
the state of `(x, u*)` (forward equation of (3.3)), `(Y, Z)` solves the MF-BSDE (3.1) driven by
`X*`, and the coupling (3.2) holds. -/
def IsFBSDESol {n m : ℕ} (μ : Measure Ω) {W : ℝ≥0 → Ω → Fin 1 → ℝ} (hW : IsStdBrownian μ W)
    (T : ℝ≥0) (d : Data n m) (x : Fin n → ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ)
    (u : ℝ≥0 → Ω → Fin m → ℝ) (Y Z : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  L2F (filt μ hW) μ T u ∧ IsState μ hW T d x u X ∧ IsMFBSDE μ hW T d X Y Z ∧
    Stationary μ T d u Y Z

end MeanFieldLQ.Feedback


