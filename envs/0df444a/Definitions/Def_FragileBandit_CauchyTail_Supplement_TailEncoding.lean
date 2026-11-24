-- Prove2me | Definitions.Def_FragileBandit_CauchyTail_Supplement_TailEncoding
-- name    : FragileBandit_CauchyTail_Supplement_TailEncoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:02:39.7538+00:00
-- url     : https://prove2.me/theorems/abdb2fc1-af7b-4b28-8fac-2e44d09fed06
-- title:
--   The uniform power-form tail lower bound and the window B_γ(T) of (23)
-- statement:
--   For a horizon $T$ and $0<\gamma<1$, the window in (23) is
--
--   $$B_\gamma(T)=[(\log T)^{1+\gamma},(1-\gamma)T].$$
--
--   For a family of tail probabilities $q_T(x)$ and an exponent $c\in[0,+\infty]$, `UniformTailLower q c` means that for every $\gamma\in(0,1)$ and every real $b$ with $c<b$, eventually in $T$,
--
--   $$x^{-b}\le q_T(x)\qquad\text{for all }x\in B_\gamma(T).$$
--
--   This is the uniform logarithmic lower bound with exponent $-c$ in (23). When $c=+\infty$ the requirement is vacuous, as is the source lower bound. For finite $c$, zero tail probability violates the requirement on the eventually nonempty window.
--
--   **Formalization Note** Horizons are natural numbers, thresholds are real, and probabilities and exponents lie in the extended nonnegative reals. The window has $x>1$ eventually; values of the real logarithm and real power at small horizons have no effect on the asymptotic property. No divergence outside the published family's mean domain is defined in this file.
-- source:
--   Fan and Glynn, The Fragility of Optimized Bandit Algorithms, arXiv:2109.13595v8, p.21, Theorem 3 (window B_γ(T) of (23)); p.20, Definition 4 (22); pp.7–8, (1)–(3)

import Mathlib
import Definitions.Def_FragileBandit_CauchyTail_Setting

set_option autoImplicit false

namespace FragileBandit.CauchyTail.Supplement

open MeasureTheory ProbabilityTheory Filter BanditAlgorithm
open scoped ENNReal Topology

/-- The polylogarithmic-to-linear window `B_γ(T) = [(log T)^{1+γ}, (1-γ)T]` of (23). -/
def tailWindow (γ : ℝ) (T : ℕ) : Set ℝ :=
  Set.Icc ((Real.log T) ^ (1 + γ)) ((1 - γ) * T)

/-- Power encoding of a uniform logarithmic tail lower bound with exponent −c.
For c = +∞ this is vacuous, as is the printed lower bound. -/
def UniformTailLower (q : ℕ → ℝ → ℝ≥0∞) (c : ℝ≥0∞) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 1 → ∀ b : ℝ, c < ENNReal.ofReal b →
    ∀ᶠ T : ℕ in atTop, ∀ x ∈ tailWindow γ T,
      ENNReal.ofReal (x ^ (-b)) ≤ q T x

end FragileBandit.CauchyTail.Supplement


