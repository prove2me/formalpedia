-- Prove2me | Definitions.Def_GevreyGibbsSep_gibbs
-- name    : GevreyGibbsSep_gibbs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:36:50.649104+00:00
-- url     : https://prove2.me/theorems/15cbb5a0-a12e-48eb-ba05-4d1064151ade
-- title:
--   Definition B.1 — Gibbs state $p=e^{-V}/Z_V$ on $\mathbb T^d$
-- statement:
--   The **Gibbs state** with scaled potential $V=\beta E$ is the distribution on $\mathbb T^d$ with density
--   $$p=\frac{e^{-V}}{Z_V},\qquad Z_V=\int_{[0,2\pi)^d}e^{-V(x)}\,dx,$$
--   that is $p(A)=\int_A p(x)\,dx$ for measurable $A\subseteq[0,2\pi)^d$.
--
--   **Formalization Note** The measure is the push-forward to the torus of Lebesgue measure on $[0,2\pi)^d$ with density $e^{-V}/Z_V$. The argument is the scaled potential $\beta E$.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Definition B.1, Eq. (B1), p.34; Eq. (1), p.5

import Mathlib
import Definitions.Def_GevreyGibbsSep_Torus
import Definitions.Def_GevreyGibbsSep_toTorus
import Definitions.Def_GevreyGibbsSep_periodCube
import Definitions.Def_GevreyGibbsSep_partitionFn

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- Definition B.1 (Gibbs state on `T^d`), arXiv:2608.24527 (sha256 d4fd40eb…), Eq. (B1), p.34:
the distribution on `T^d` with density `p = e^{−V}/Z_V`, i.e. `p(A) = ∫_A e^{−V}/Z_V dx` for
`A ⊆ [0, 2π)^d`.

**Formalization Note** The scaled potential `V = βE` is the argument. The measure is the
push-forward to the torus of Lebesgue measure on `[0, 2π)^d` with density `e^{−V}/Z_V`. -/
noncomputable def gibbs {d : ℕ} (V : (Fin d → ℝ) → ℝ) : Measure (Torus d) :=
  Measure.map toTorus ((volume.restrict (periodCube d)).withDensity
    (fun x => ENNReal.ofReal (Real.exp (- V x) / partitionFn V)))

end GevreyGibbsSep


