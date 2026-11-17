-- Prove2me | Definitions.Def_ThinShellSampling_Supplement_indicatorPot
-- name    : ThinShellSampling_Supplement_indicatorPot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:37:05.859996+00:00
-- url     : https://prove2.me/theorems/e3fade91-757d-4b3b-aac3-96eb53dc1dff
-- title:
--   Indicator potential $V_{\mathcal K}$ of a set: membership oracle and uniform distribution
-- statement:
--   For a set $\mathcal K\subseteq\mathbb R^n$ the **indicator potential** is
--
--   $$
--   V_{\mathcal K}(x)=\begin{cases}0,&x\in\mathcal K,\\+\infty,&x\notin\mathcal K.\end{cases}
--   $$
--
--   An evaluation oracle for $V_{\mathcal K}$ is exactly a **membership oracle** for $\mathcal K$ (a query at $x$ returns a finite value iff $x\in\mathcal K$), and $\pi\propto e^{-V_{\mathcal K}}$ is the **uniform distribution** on $\mathcal K$ whenever $0<\mathrm{vol}(\mathcal K)<\infty$, in particular for a convex body containing the unit ball.
--
--   This lets the uniform-sampling results (Theorems 1.1 and 1.5) use the published logconcave machinery: the target, its moments $R,L,\Lambda$ and the oracle-program model.
--
--   **Formalization Note** The target is `piOf (indicatorPot K)`, the published normalized density $e^{-V}/\int e^{-V}$.
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), Theorem 1.1, p.3 (PDF p.5); Theorem 1.5, p.4 (PDF p.6); §1.1, p.5 (PDF p.7): "For the uniform distribution on a convex body K ⊂ ℝⁿ, this corresponds to B(0, 1) ⊆ K"

import Mathlib
import Definitions.Def_ThinShellSampling_piOf

set_option autoImplicit false

namespace ThinShellSampling.Supplement

open MeasureTheory

open Classical in
/-- **The indicator potential of a set** `K ⊆ ℝⁿ`: `V_K(x) = 0` for `x ∈ K` and `V_K(x) = +∞`
otherwise. Its evaluation oracle is the membership oracle of `K` (a query at `x` answers `x ∈ K` iff
the value is not `⊤`), and `piOf (indicatorPot K)` is the uniform distribution on `K`.

Kook, Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with
Sesteric Complexity from a Cold Start*, STOC 2027 submission (manuscript sha256 25a041a9…),
Theorem 1.1, p.3 (PDF p.5): "Let `π` be the uniform distribution over a convex body `K ⊂ ℝⁿ` given
by a membership oracle"; §1.1, p.5 (PDF p.7): "For the uniform distribution on a convex body
`K ⊂ ℝⁿ`, this corresponds to `B(0, 1) ⊆ K`".

**Formalization Note.** `piOf (indicatorPot K)` has density `1_K / vol(K)`; for a convex body
(compact, convex, containing the unit ball) `0 < vol(K) < ∞`, so it is the uniform probability
measure on `K`. -/
noncomputable def indicatorPot {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) :
    EuclideanSpace ℝ (Fin n) → WithTop ℝ :=
  fun x => if x ∈ K then 0 else ⊤

end ThinShellSampling.Supplement


