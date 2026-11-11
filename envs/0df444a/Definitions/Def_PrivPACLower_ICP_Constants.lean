-- Prove2me | Definitions.Def_PrivPACLower_ICP_Constants
-- name    : PrivPACLower_ICP_Constants
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T13:46:19.477042+00:00
-- url     : https://prove2.me/theorems/9af6cff8-8ed7-45bf-9656-b42d537dfcb1
-- title:
--   The explicit lower-bound constant from the proof of Theorem 1
-- statement:
--   For the fixed accuracy parameter $\alpha_0$, set
--
--   $$\bar\alpha=\frac{\alpha_0}{64e},\qquad\eta=\frac{\bar\alpha}{2},\qquad T=\min\{t\in\mathbb N:t>0,\ t\text{ odd},\ t\ge72\ln(1/\eta)\}.$$
--
--   The proof's constant, with $C=101$, is
--
--   $$c(\alpha_0)=\min\left\{\frac{\bar\alpha}{69120T},\frac{\alpha_0}{576(10\cdot101+4\alpha_0)}\right\}.$$
--
--   It depends only on $\alpha_0$, independently of the classes, packing, sample size, privacy and learner accuracy parameters. For $0<\alpha_0\le1/4$ it is strictly positive.
--
--   **Formalization Note** $T$ is the natural-number infimum of the displayed set. That set is nonempty for every finite real threshold because positive odd integers are unbounded. This infimum cannot use the empty-set default. Logarithms are natural logarithms and $e=\exp(1)$.
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 16–18, Proof of Theorem 1, Parameters and Step 3. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP

noncomputable def alphaBar (α₀ : ℝ) : ℝ := α₀ / (64 * Real.exp 1)
noncomputable def confidence (α₀ : ℝ) : ℝ := alphaBar α₀ / 2

/-- The least positive odd integer meeting the proof's logarithmic threshold.
The set is nonempty for every real threshold, so sInf on Nat is legitimate here. -/
noncomputable def amplificationCount (α₀ : ℝ) : ℕ :=
  sInf {T : ℕ | 0 < T ∧ Odd T ∧ 72 * Real.log (1 / confidence α₀) ≤ (T : ℝ)}

noncomputable def lowerConstant (α₀ : ℝ) : ℝ :=
  min (alphaBar α₀ / (69120 * (amplificationCount α₀ : ℝ)))
    (α₀ / (576 * (10 * 101 + 4 * α₀)))

end PrivPACLower.ICP


