-- Prove2me | Definitions.Def_LevyExtrema_SBA_IsCPPWithDrift
-- name    : LevyExtrema_SBA_IsCPPWithDrift
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:39:19.985985+00:00
-- url     : https://prove2.me/theorems/f14082d3-6527-4202-98c3-fd3ad0034e8d
-- title:
--   Compound Poisson with drift: $\sigma=0$ and $\nu(\mathbb R)<\infty$
-- statement:
--   A Lévy process with generating triplet $(\sigma^2,\nu,b)$ is **compound Poisson with drift** when it has no Gaussian component and finitely many jumps on compact time intervals, that is,
--
--   $$\sigma=0\quad\text{and}\quad \nu(\mathbb R)<\infty,$$
--
--   with an arbitrary drift. Theorem 1 and Theorem 2 of the paper assume that $X$ is *not* of this kind.
--
--   **Formalization Note** The property is stated on the triplet. It is different from the reused predicate `Triplet.DriftlessCP`, which also forces the drift to vanish; the pure drift ($\nu=0$, $\sigma=0$) is compound Poisson with drift.
-- source:
--   González Cázares, Mijatović, Uribe Bravo, Geometrically Convergent Simulation of the Extrema of Lévy Processes, arXiv:1810.11039v3, Theorem 1, p. 3; §4, p. 17

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy

open MeasureTheory

namespace LevyExtrema.SBA

open SingCtrlLevy.Barrier

/-- **Compound Poisson with drift.**
González Cázares, Mijatović, Uribe Bravo, arXiv:1810.11039v3, §1.1, p. 3 (Theorem 1: "Assume the
Lévy process X is not compound Poisson with drift") and §4, p. 17. A Lévy process with generating
triplet (σ², ν, b) is compound Poisson with drift exactly when it has no Gaussian part and a
finite Lévy measure; the drift is arbitrary.

`IsCPPWithDrift Tr := Tr.σ = 0 ∧ ν(ℝ) < ∞`.

**Formalization Note.** Stated on the triplet (`SingCtrlLevy.Barrier.Triplet`, whose `σ` is the
Gaussian coefficient, `σ²` the paper's σ²). This is *not* `Triplet.DriftlessCP` of the reused
module, which additionally forces the drift to vanish. The pure drift (ν = 0, σ = 0) is included,
as it is compound Poisson with zero intensity plus drift. -/
def IsCPPWithDrift (Tr : Triplet) : Prop :=
  Tr.σ = 0 ∧ Tr.levyMeasure Set.univ < ⊤

end LevyExtrema.SBA


