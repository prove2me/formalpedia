-- Prove2me | Definitions.Def_GevreyGibbsSep_InGevrey
-- name    : GevreyGibbsSep_InGevrey
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:36:59.797512+00:00
-- url     : https://prove2.me/theorems/766e0f92-921a-487b-92c9-8db256bc8db7
-- title:
--   Definition A.1 — Gevrey class $G^s(C,r)$
-- statement:
--   For $s\ge1$ and $r,C>0$, a function $f$ is in the **$s$-Gevrey class** $G^s(C,r)$ if it is $2\pi$-periodic and $C^\infty$ and
--   $$|\partial^af(x)|\le (a!)^s\,C\,r^{-\|a\|_1}\qquad\text{for all }a\in\mathbb N^d\text{ and all }x .$$
--   Unlike Definition 1, the value ($a=0$) is constrained as well.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Definition A.1, Eq. (A5), p.20

import Mathlib
import Definitions.Def_GevreyGibbsSep_IsPeriodicSmooth
import Definitions.Def_GevreyGibbsSep_partialDeriv

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- Definition A.1 (s-Gevrey function), arXiv:2608.24527 (sha256 d4fd40eb…), Eq. (A5), p.20:
`f ∈ G^s(C, r)` iff `f` is `2π`-periodic and `C^∞` and `|∂^a f(x)| ≤ (a!)^s C r^{−‖a‖₁}` for all
`a ∈ ℕ^d` (including `a = 0`) and all `x`. -/
def InGevrey {d : ℕ} (s C r : ℝ) (f : (Fin d → ℝ) → ℝ) : Prop :=
  IsPeriodicSmooth f ∧ ∀ (a : Fin d → ℕ) (x : Fin d → ℝ),
    |partialDeriv a f x| ≤ ((∏ i, (a i).factorial : ℕ) : ℝ) ^ s * C * (r ^ (∑ i, a i))⁻¹

end GevreyGibbsSep


