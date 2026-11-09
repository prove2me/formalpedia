-- Prove2me | Definitions.Def_GevreyGibbsSep_partialDeriv
-- name    : GevreyGibbsSep_partialDeriv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:36:07.35084+00:00
-- url     : https://prove2.me/theorems/2957c77a-10b3-4ca1-ad51-467a602b4dff
-- title:
--   Multi-index derivative $\partial^a f$
-- statement:
--   For a multi-index $a=(a_1,\dots,a_d)\in\mathbb N^d$ the paper writes
--   $$\partial^a=\prod_j\Big(\frac{\partial}{\partial x_j}\Big)^{a_j},\qquad a!=\prod_j a_j!,\qquad \|a\|_1=\sum_j a_j .$$
--   This item is $\partial^a f$: $a_j$ partial derivatives in each coordinate $x_j$.
--
--   **Formalization Note** The derivatives are applied in one fixed coordinate order; for $C^\infty$ functions the order does not matter.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Section II, p.5

import Mathlib
import Definitions.Def_GevreyGibbsSep_iterPartial

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- The multi-index derivative `∂^a f = ∏_j (∂/∂x_j)^{a_j} f` for `a ∈ ℕ^d`
(arXiv:2608.24527 (sha256 d4fd40eb…), Section II, p.5).

**Formalization Note** The derivatives are applied in one fixed coordinate order; for the `C^∞`
functions to which it is applied the order is irrelevant. -/
noncomputable def partialDeriv {d : ℕ} (a : Fin d → ℕ) (f : (Fin d → ℝ) → ℝ) :
    (Fin d → ℝ) → ℝ :=
  iterPartial ((List.finRange d).flatMap (fun i => List.replicate (a i) i)) f

end GevreyGibbsSep


