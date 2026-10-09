-- Prove2me | Definitions.Def_ImpulsiveISS_AvgDwell_Setting
-- name    : ImpulsiveISS_AvgDwell_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T18:30:40.159858+00:00
-- url     : https://prove2.me/theorems/d6dc80b9-97f3-4680-8555-b49dda95b92e
-- title:
--   §§2–3: impulsive flow, inputs, trajectory, comparison classes, upper Dini derivative, and generalized average dwell time
-- statement:
--   The state and input spaces $X$ and $U$ are real Banach spaces. An impulsive system has a continuous-part transition map $\phi_c(t,x,u)$, starting at time zero, and a jump map $J(x,\xi)$. The transition map starts from $x$, obeys the time-shifted cocycle law, is continuous in time for admissible inputs, and fixes zero under zero input; $J(0,0)=0$. Admissible inputs are bounded, piecewise right-continuous functions on $[0,\infty)$, with a left limit at each positive time. Impulse times form a strictly increasing sequence tending to infinity, with the first time strictly positive. The trajectory flows between impulse times and applies $J$ to the pre-jump state and left input limit at each impulse. The count $N(t,s)$ includes impulses in $(s,t]$.
--
--   The comparison classes $\mathcal L$ and $\mathcal{KL}$ have their meanings from Definition 1. The Lie derivative is the extended-real upper-right Dini derivative of $t\mapsto V(\phi_c(t,x,u))$ at zero. A **max-form exponential ISS-Lyapunov function** is continuous, sandwiched between two $\mathcal K_\infty$ functions of $\|x\|$, and satisfies
--   $$V(x)\ge\gamma(\|\xi\|)\Longrightarrow \dot V_u(x)\le-cV(x),\qquad V(J(x,\xi))\le\max\{e^{-d}V(x),\gamma(\|\xi\|)\}.$$
--   The second inequality holds for every state and jump input. The generalized dwell-time class $S[h]$ consists of sequences with $-dN(t,s)-c(t-s)\le\log h(t-s)$ for all $t\ge s\ge0$. Uniform ISS means one pair of comparison functions bounds every trajectory for every sequence in the class.
--
--   These objects provide a reusable transition-map formulation of the paper's stability statements.
--
--   **Formalization Note** Time starts at $0$, and the first impulse is strictly later. The model records $(\phi_c,J)$ rather than the generator and mild-solution machinery. The input norm is represented by an arbitrary uniform bound $M$, avoiding an undefined supremum. The Dini derivative takes values in extended reals. The real supremum of $h$ is used only under the stated positive, bounded domination hypothesis.
-- source:
--   Dashkovskiy and Mironchenko, Input-to-state stability of nonlinear impulsive systems, arXiv:1212.5481v1, pp. 3–6, 11, §2, Definitions 1–2, Definition 4, (3.3)–(3.6), Proposition 3.2, (3.29)

import Mathlib
import Definitions.Def_SmallGainISS_Lyapunov_Gains
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_DiniDerivative
import Definitions.Def_ImpulsiveISS_FixedDwell_Setting

open scoped NNReal
open Filter Topology

namespace ImpulsiveISS.AvgDwell

open SmallGainISS.Lyapunov
open ProcessingNetworks.LyapunovCriteria

/-- Local name for the shared impulsive-system structure. -/
abbrev System (X U : Type*) := ImpulsiveISS.FixedDwell.System X U

/-- Local name for the shared standing system assumptions. -/
abbrev IsImpulsiveSystem {X U : Type*} [NormedAddCommGroup X] [NormedAddCommGroup U]
    (S : System X U) : Prop := ImpulsiveISS.FixedDwell.IsImpulsiveSystem S

/-- Local name for the shared impulse-sequence conditions. -/
abbrev IsImpulseSeq (τ : ℕ → ℝ) : Prop := ImpulsiveISS.FixedDwell.IsImpulseSeq τ

/-- The number of impulse times in the left-open, right-closed interval `(s,t]`. -/
noncomputable def count (τ : ℕ → ℝ) (t s : ℝ) : ℕ :=
  Nat.card {k : ℕ // s < τ k ∧ τ k ≤ t}

/-- The starting time of the `k`-th flow piece. -/
def epoch (τ : ℕ → ℝ) : ℕ → ℝ :=
  Nat.rec 0 (fun k _ => τ k)

/-- State immediately after the first `k` impulses. -/
noncomputable def post {X U : Type*} [NormedAddCommGroup U] (S : ImpulsiveISS.FixedDwell.System X U)
    (τ : ℕ → ℝ) (x₀ : X) (u : ℝ → U) : ℕ → X :=
  Nat.rec x₀ (fun k x =>
    S.jump (S.flow (τ k - epoch τ k) x (ImpulsiveISS.FixedDwell.shift u (epoch τ k)))
      (Function.leftLim u (τ k)))

/-- The right-continuous impulsive trajectory assembled from flow pieces and jumps. -/
noncomputable def traj {X U : Type*} [NormedAddCommGroup U] (S : ImpulsiveISS.FixedDwell.System X U)
    (τ : ℕ → ℝ) (x₀ : X) (u : ℝ → U) (t : ℝ) : X :=
  let k := count τ t 0
  S.flow (t - epoch τ k) (post S τ x₀ u k) (ImpulsiveISS.FixedDwell.shift u (epoch τ k))

/-- Proposition 3.2's exponential ISS-Lyapunov conditions in max form. -/
def IsExpLyapunov {X U : Type*} [NormedAddCommGroup X]
    [NormedAddCommGroup U] (S : ImpulsiveISS.FixedDwell.System X U) (V : X → ℝ≥0)
    (ψ₁ ψ₂ γ : ℝ≥0 → ℝ≥0) (c d : ℝ) : Prop :=
  Continuous V ∧ IsKInf ψ₁ ∧ IsKInf ψ₂ ∧ IsKInf γ ∧
  (∀ x, ψ₁ ‖x‖₊ ≤ V x ∧ V x ≤ ψ₂ ‖x‖₊) ∧
  (∀ x ξ u, ImpulsiveISS.FixedDwell.IsPCInput u → u 0 = ξ → γ ‖ξ‖₊ ≤ V x →
    ImpulsiveISS.FixedDwell.lieDeriv S V x u ≤ (((-c * (V x : ℝ)) : ℝ) : EReal)) ∧
  ∀ x ξ, V (S.jump x ξ) ≤
    max ((Real.toNNReal (Real.exp (-d))) * V x) (γ ‖ξ‖₊)

/-- The generalized average dwell-time class `S[h]` of (3.29). -/
def IsGADT (τ : ℕ → ℝ) (c d : ℝ) (h : ℝ≥0 → ℝ) : Prop :=
  ImpulsiveISS.FixedDwell.IsImpulseSeq τ ∧
    ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      -(d * (count τ t s : ℝ)) - c * (t - s) ≤
        Real.log (h (t - s).toNNReal)

/-- Definition 2, uniformly over a class of impulse sequences. -/
def UniformISS {X U : Type*} [NormedAddCommGroup X]
    [NormedAddCommGroup U] (S : ImpulsiveISS.FixedDwell.System X U)
    (C : (ℕ → ℝ) → Prop) : Prop :=
  ∃ β γ, ImpulsiveISS.FixedDwell.IsKL β ∧ IsKInf γ ∧
    ∀ τ, C τ → ∀ x₀ u, ImpulsiveISS.FixedDwell.IsPCInput u →
      ∀ M : ℝ≥0, (∀ t : ℝ, 0 ≤ t → ‖u t‖₊ ≤ M) →
        ∀ t : ℝ, 0 ≤ t →
          ‖traj S τ x₀ u t‖₊ ≤ β ‖x₀‖₊ t.toNNReal + γ M

/-- The finite constant `C_λ = sup_{r ≥ 0} h(r)` of the proof of Theorem 5. -/
noncomputable def height (h : ℝ≥0 → ℝ) : ℝ :=
  sSup (Set.range h)

end ImpulsiveISS.AvgDwell


