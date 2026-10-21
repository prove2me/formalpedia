-- Prove2me | Definitions.Def_YeIPA_Asymptotic_Order
-- name    : YeIPA_Asymptotic_Order
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:57:28.660775+00:00
-- url     : https://prove2.me/theorems/2feaad66-4f58-49d5-9c1c-f37a40a35bd2
-- title:
--   Order of convergence of a sequence (Definition 1.1) and quadratic convergence (Definition 1.2)
-- statement:
--   Let $\{r^k\}_{k\ge0}$ be a real sequence. Write
--   $$L(p)=\limsup_{k\to\infty}\frac{|r^{k+1}|}{|r^k|^p}\in[0,+\infty]\qquad(p\ge0).$$
--   1. **Order of convergence** (Definition 1.1, p. 33): the supremum of the nonnegative numbers $p$ satisfying $0\le L(p)<\infty$.
--   2. **Quadratic convergence** (Definition 1.2, p. 33): $\{r^k\}$ converges quadratically to zero if $r^k\to0$ and $L(2)<\infty$.
--
--   The book defines both for sequences converging to zero; §7.1.1 (p. 210) restates them in terms of the limit superior so that they apply to any sequence, with $0/0$ regarded as a finite number.
--
--   **Formalization Note** Limits superior and the supremum are taken in `EReal`, so $L(p)=+\infty$ is $\top$ rather than a junk real value, and an order of convergence equal to $+\infty$ is representable. $|r^k|^p$ is the real power `Real.rpow`; with Lean's convention $t/0=0$ a term with $r^k=0$ contributes $0$, which is a finite value as the book's convention asks. The order is defined for every sequence; the convergence hypothesis $r^k\to0$ is placed in the theorems that use it.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 33, Definitions 1.1 and 1.2; p. 210, §7.1.1

import Mathlib

namespace YeIPA.Asymptotic

/-!
# Order of convergence of a real sequence and quadratic convergence

Ye, *Interior Point Algorithms: Theory and Analysis*, Wiley 1997, Definitions 1.1 and 1.2
(p. 33), restated for arbitrary sequences in §7.1.1 (p. 210). Limits superior and inferior
are taken in `EReal`, so that a limit superior equal to `+∞` is `⊤` and not a junk real.
-/

/-- `limsup_{k→∞} |r^{k+1}| / |r^k|^p`, computed in `EReal`. The real power `|r^k|^p` is
`Real.rpow`; with Lean's `x / 0 = 0` a term with `r^k = 0` contributes `0`, the "0/0 is
regarded as a finite number" convention of p. 210. -/
noncomputable def ratioLimsup (r : ℕ → ℝ) (p : ℝ) : EReal :=
  Filter.limsup (fun k => ((|r (k + 1)| / |r k| ^ p : ℝ) : EReal)) Filter.atTop

/-- The order of convergence of `{rᵏ}` (Definition 1.1, p. 33): the supremum (in `EReal`)
of the nonnegative numbers `p` with `0 ≤ limsup_{k→∞} |r^{k+1}| / |r^k|^p < ∞`. -/
noncomputable def orderOfConvergence (r : ℕ → ℝ) : EReal :=
  sSup {q : EReal | ∃ p : ℝ, 0 ≤ p ∧ q = (p : EReal) ∧ 0 ≤ ratioLimsup r p ∧
    ratioLimsup r p < ⊤}

/-- `{rᵏ}` converges quadratically to zero (Definition 1.2, p. 33): `rᵏ → 0` and
`limsup_{k→∞} |r^{k+1}| / |r^k|² < ∞`. -/
def ConvergesQuadratically (r : ℕ → ℝ) : Prop :=
  Filter.Tendsto r Filter.atTop (nhds 0) ∧ ratioLimsup r 2 < ⊤

end YeIPA.Asymptotic


