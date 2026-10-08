-- Prove2me | Definitions.Def_WhittFLT_TimeReversal_Reversal
-- name    : WhittFLT_TimeReversal_Reversal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:56:52.250718+00:00
-- url     : https://prove2.me/theorems/041c020a-e268-4401-8c2e-10e9699b2a3b
-- title:
--   The endpoint-constrained path space and time-reversal maps
-- statement:
--   Let $D$ consist of càdlàg paths $x:[0,1]\to S$ with $x(1)=x(1-)$, where $S$ is an additive metric group with identity $0$. Let $D_\theta$ be the subset with $x(0)=0$. The reverse-time path and its version starting at the identity are
--
--   $$
--   R(x)(t)=\begin{cases}x((1-t)-),&0\le t<1,\\x(0),&t=1,\end{cases}
--   \qquad r(x)(t)=R(x)(t)-x(1).
--   $$
--
--   For a time change $\lambda$ of $[0,1]$, its reflected time change is $(-r)(\lambda)(t)=1-\lambda(1-t)$. These definitions are the objects in Whitt's time-reversal theorem.
--
--   **Formalization Note** Paths are total real-indexed functions but all claims concern $[0,1]$. The left-limit operator is used for $R$, rather than the value $x(1-t)$. The endpoint condition is part of $D$, and the translation-invariance assumption appears in the theorems. The expression for $(-r)(\lambda)$ follows from $\lambda(1)=1$: reversing $\lambda$, subtracting its terminal value, and negating gives $1-\lambda(1-t)$.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), §8, p. 83 and proof of Theorem 8.1, p. 84; https://doi.org/10.1287/moor.5.1.67

import Mathlib
import Definitions.Def_WhittFLT_Composition_SkorohodD

namespace WhittFLT.TimeReversal

open Set Filter Topology

variable {S : Type*} [AddCommGroup S] [MetricSpace S]

/-- §8, p. 83: `x ∈ D` means a càdlàg path on `[0, 1]` continuous from the left at `1`. -/
def InD (x : ℝ → S) : Prop := WhittFLT.Composition.IsCadlagOn (Icc 0 1) x ∧ Function.leftLim x 1 = x 1

/-- §8, p. 83: `x ∈ D_θ` additionally starts at the group identity. -/
def InDθ (x : ℝ → S) : Prop := InD x ∧ x 0 = 0

/-- §8, p. 83: `R(x)(t) = x((1 − t)−)` for `0 ≤ t < 1` and `R(x)(1) = x(0)`. -/
noncomputable def revTime (x : ℝ → S) (t : ℝ) : S :=
  if t < 1 then Function.leftLim x (1 - t) else x 0

/-- §8, p. 83: reverse time and shift the starting value to the identity. -/
noncomputable def revTime0 (x : ℝ → S) (t : ℝ) : S := revTime x t - x 1

/-- §8, proof of Theorem 8.1, p. 84: the reflected time change `(-r)(λ)`. -/
def negRev (l : ℝ → ℝ) (t : ℝ) : ℝ := 1 - l (1 - t)

end WhittFLT.TimeReversal


