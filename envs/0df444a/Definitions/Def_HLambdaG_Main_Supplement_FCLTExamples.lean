-- Prove2me | Definitions.Def_HLambdaG_Main_Supplement_FCLTExamples
-- name    : HLambdaG_Main_Supplement_FCLTExamples
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:59:32.790183+00:00
-- url     : https://prove2.me/theorems/c525e6f5-bed1-4b00-a7c2-7b9c822386e2
-- title:
--   §5, pp. 643–644 — deterministic counterexample data and compact convergence for Theorems 7–8
-- statement:
--   This auxiliary bundle defines the explicit deterministic witnesses used to refute Theorems 7 and 8, rather than introducing a general stochastic-process model. Uniform convergence on bounded time intervals is expressed with epsilon bounds (no real supremum). Diffusion scaling is exactly (27), with centering rate one:
--   $$
--   \operatorname{diffusion}(f)_n(t)=\frac{f(nt)-nt}{\sqrt n}.
--   $$
--   For Theorem 7, put $T(s)=s+\sqrt s$, $B(t)=((\sqrt{1+4t}-1)/2)^2$, $F(s,t)=\min(s,B(t))^2$ and $H(t)=B(t)^2/t$. For Theorem 8 put $T_k=k$, $S_k=\sqrt k+1$ and $f_k(v)=2k1_{[k+\sqrt k,k+\sqrt k+1]}(v)$. The bundle defines the integrated $F_k$, and the exact averages $G,H$ from (1).
--
--   **Formalization Note** These are counterexample objects, not replacements for the source's general definitions. Customer 0 has zero cost. Real division at zero only fixes endpoint values; all limits are at infinity. Deterministic paths can be random elements on a singleton probability space. Uniform convergence to the displayed continuous paths implies the source's J₁ convergence, for either a product or joint vector topology.
-- source:
--   Glynn and Whitt, Oper. Res. 37 (1989), pp. 643–644, §5 displays (27)–(30), (33)–(34); explicit counterexamples developed during moderation

import Mathlib

open scoped NNReal

namespace HLambdaG.Main.Supplement

open Filter Topology MeasureTheory

/-- Uniform convergence on every bounded time interval, stated without a possibly junk real supremum.
For these deterministic paths the continuous limits also give J₁ weak convergence on a one-point
probability space. This predicate records convergence of the explicit counterexamples, not a
replacement definition of stochastic weak convergence. -/
def CompactConvergence (f : ℕ → ℝ≥0 → ℝ) (g : ℝ≥0 → ℝ) : Prop :=
  ∀ a : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
    ∀ t : ℝ≥0, t ≤ a → |f n t - g t| < ε

/-- Scaling (27), with centering rate one. Index zero is irrelevant to convergence at infinity. -/
noncomputable def diffusion (f : ℝ≥0 → ℝ) (n : ℕ) (t : ℝ≥0) : ℝ :=
  (f ((n : ℝ≥0) * t) - (n : ℝ) * t) / Real.sqrt n

/-- The time change T(s) = s + √s in the counterexample to Theorem 7. -/
noncomputable def curvedT (s : ℝ≥0) : ℝ := s + Real.sqrt s

/-- The inverse of curvedT: the positive solution b + √b = t. -/
noncomputable def curvedS (t : ℝ≥0) : ℝ := ((Real.sqrt (1 + 4 * (t : ℝ)) - 1) / 2) ^ 2

/-- A continuous cumulative input with finite margins s² and curvedS(t)². -/
noncomputable def curvedF (s t : ℝ≥0) : ℝ := (min (s : ℝ) (curvedS t)) ^ 2

/-- The source's time AVERAGE H(t), exactly as (1) defines it. -/
noncomputable def curvedH (t : ℝ≥0) : ℝ := (curvedS t) ^ 2 / (t : ℝ)

/-- A cost rate of total mass 2k, supported in [k + √k, k + √k + 1], k ≥ 1.
The 0th rate is zero. No stochastic randomness is needed. -/
noncomputable def delayedRate (k : ℕ) (t : ℝ) : ℝ :=
  if (k : ℝ) + Real.sqrt k ≤ t ∧ t ≤ (k : ℝ) + Real.sqrt k + 1 then 2 * k else 0

/-- The integral of delayedRate from time 0 to t. -/
noncomputable def delayedF (k : ℕ) (t : ℝ≥0) : ℝ :=
  2 * k * min 1 (max 0 ((t : ℝ) - k - Real.sqrt k))

/-- The customer average G(s) from (1), for F_k(∞) = 2k. -/
noncomputable def delayedG (s : ℝ≥0) : ℝ :=
  (∑ k ∈ Finset.Icc 1 ⌊s⌋₊, (2 * k : ℝ)) / (s : ℝ)

/-- The time average H(t) from (1). Customers k > t contribute zero. -/
noncomputable def delayedH (t : ℝ≥0) : ℝ :=
  (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, delayedF k t) / (t : ℝ)

/-- The arrival time change T₁(s) = T_[s], with T_k = k. -/
noncomputable def integerT (s : ℝ≥0) : ℝ := ⌊s⌋₊

end HLambdaG.Main.Supplement


