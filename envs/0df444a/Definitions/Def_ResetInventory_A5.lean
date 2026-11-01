-- Prove2me | Definitions.Def_ResetInventory_A5
-- name    : ResetInventory_A5
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:19:49.676046+00:00
-- url     : https://prove2.me/theorems/1db72685-3b1f-4d43-a308-e147db4b4d3d
-- title:
--   Assumption 5: bounded Lipschitz demand density
-- statement:
--   **Assumption 5.** The demands $w_n$ are i.i.d., and the density of $w_n$ is a function $f$ such that
--
--   1. $f$ is a probability density on $\mathbb R$: $f\ge0$, $f$ is measurable and $\int_{\mathbb R}f(w)\,dw=1$;
--   2. $f(w)=0$ for all $w<0$;
--   3. $f$ is Lipschitz continuous on $[0,\infty)$ with a non-negative constant $L$: $|f(w)-f(w')|\le L|w-w'|$ for $w,w'\ge0$;
--   4. $|f(w)|\le P$ for all $w\ge0$, with a non-negative constant $P$.
--
--   Demand is thus non-negative, with a density supported on $[0,\infty)$ that is bounded and Lipschitz there; exponential, gamma and truncated normal demands qualify. A jump of $f$ at $0$ is allowed.
--
--   **Formalization Note** "Density" is a probability density with respect to Lebesgue measure (the published definition `FDivToolkit.IsDensity`). The paper uses that $f$ is non-negative and integrates to one in the proof of Proposition 2. The i.i.d. clause has no separate content here, since the mission uses the demand only through one-period expectations $\int\varphi(w)f(w)\,dw$.
-- source:
--   Lee, Mintz, Aswani, Shen, Yang, Optimal Policy for Inventory Management with Periodic and Controlled Resets, arXiv:2209.03571v1, Assumption 5, p.16; proof of Proposition 2, (A.7), p.31

import Mathlib
import Definitions.Def_FDivToolkit_IsDensity

namespace ResetInventory

/-- **Assumption 5 (A5)** of Lee, Mintz, Aswani, Shen, Yang, *Optimal Policy for Inventory
Management with Periodic and Controlled Resets*, arXiv:2209.03571v1, p.16: the demands `w_n` are
i.i.d. with a density `f` that vanishes on `(-∞, 0)`, is Lipschitz continuous on `[0, ∞)` with a
non-negative constant `L`, and is bounded by a non-negative constant `P` on `[0, ∞)`.

**Formalization Note** "Density" is a probability density with respect to Lebesgue measure
(`FDivToolkit.IsDensity`: non-negative, measurable, total integral `1`); the proof of
Proposition 2 (p.31) uses that `f` is non-negative and integrates to one. The i.i.d. clause has no
separate content here, because the mission uses the demand only through expectations
`∫ φ(w) f(w) dw` of a single period. -/
def A5 (f : ℝ → ℝ) (L P : ℝ) : Prop :=
  FDivToolkit.IsDensity f ∧
  (∀ w : ℝ, w < 0 → f w = 0) ∧
  0 ≤ L ∧ 0 ≤ P ∧
  (∀ w : ℝ, 0 ≤ w → ∀ w' : ℝ, 0 ≤ w' → |f w - f w'| ≤ L * |w - w'|) ∧
  (∀ w : ℝ, 0 ≤ w → |f w| ≤ P)

end ResetInventory


