-- Prove2me | Definitions.Def_OnlineDiscUniv_empMeas
-- name    : OnlineDiscUniv_empMeas
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:09.548426+00:00
-- url     : https://prove2.me/theorems/becf522f-b323-4679-95a1-6427ac141627
-- title:
--   Path space $C([0,1],\mathbb R^2)$, linear interpolation of mesh values, and empirical measures of paths
-- statement:
--   The path space $\mathcal C^2=C([0,1],\mathbb R)^2$ of pairs of continuous paths carries its Borel $\sigma$-algebra. For values $x_0,\dots,x_N\in\mathbb R^2$ the **linearly interpolated path** through $(k/N,x_k)$ is
--   $$
--   t\mapsto\sum_{k=0}^N\max\big(0,1-|Nt-k|\big)\,x_k ,
--   $$
--   and the **empirical measure** of $M$ paths $w_1,\dots,w_M$ is $\frac1M\sum_{i=1}^M\delta_{w_i}$, a probability measure on $\mathcal C^2$.
--
--   These build the random empirical measure $\widehat\nu_N$ of §5.1.
--
--   **Formalization Note** A pair of paths in $C([0,1],\mathbb R)^2$ is encoded as one path in $C([0,1],\mathbb R^2)$ (the spaces are canonically homeomorphic). The Borel instance is scoped to the namespace. For $M=0$, outside the paper's regime, the empirical measure is set to the point mass at the zero path.
-- source:
--   Jo, Lee, Exact Universality of Online Discrepancy, arXiv:2610.00103 (artifact sha256 cb190f127dea2c038b4a22a4787862f82356a983593dfdc3dc3fe3c7c8264ad5), §5.1, (5.1), pp.23–24 (PDF pp.24–25)

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace OnlineDiscUniv

/-- The Borel σ-algebra on the path space `C([0,1], ℝ²)` (Jo–Lee, arXiv:2610.00103, artifact
sha256 cb190f12…, §5.1, printed pp.23–24, PDF pp.24–25: "the Borel probability measures on a
metric space `E`").

**Formalization Note** The pair of paths `(A, B) ∈ C² = C([0,1], ℝ)²` of the paper is encoded as
one path in `C([0,1], ℝ × ℝ)`; the two spaces are canonically homeomorphic (uniform topology).
The instance is scoped to the namespace `OnlineDiscUniv`. -/
scoped instance pathMeasurableSpace : MeasurableSpace C(unitInterval, ℝ × ℝ) := borel _

scoped instance pathBorelSpace : BorelSpace C(unitInterval, ℝ × ℝ) := ⟨rfl⟩

/-- The piecewise linear path through the points `(k/N, x_k)`, `k = 0, …, N` (Jo–Lee,
arXiv:2610.00103, (5.1), p.23, PDF p.24: "linearly interpolated between mesh points").

**Formalization Note** Written as `∑_{k=0}^{N} max(0, 1 − |N t − k|) · x_k`, which for `N ≥ 1` is
exactly the linear interpolation of the values `x_k` at the mesh points `k/N` (for `N = 0` it is
the constant `x_0`). -/
noncomputable def hatPath (N : ℕ) (x : ℕ → ℝ × ℝ) : C(unitInterval, ℝ × ℝ) where
  toFun t := ∑ k ∈ Finset.range (N + 1), max 0 (1 - |(N : ℝ) * (t : ℝ) - k|) • x k
  continuous_toFun := by fun_prop

/-- The empirical measure `(1/M) ∑_{i=1}^{M} δ_{w_i}` of `M` paths, as a probability measure on
`C([0,1], ℝ²)` (Jo–Lee, arXiv:2610.00103, §5.1, p.23, PDF p.24).

**Formalization Note** It is the image of the uniform law on `Fin M` under `i ↦ w_i`. For `M = 0`
(not a case of the paper, where `M/N → α > 0`) it is set to the point mass at the zero path. -/
noncomputable def empMeas {M : ℕ} (w : Fin M → C(unitInterval, ℝ × ℝ)) :
    ProbabilityMeasure C(unitInterval, ℝ × ℝ) :=
  if h : M = 0 then ⟨Measure.dirac 0, inferInstance⟩ else
    haveI : NeZero M := ⟨h⟩
    ⟨(ProbabilityTheory.uniformOn (Set.univ : Set (Fin M))).map w,
      Measure.isProbabilityMeasure_map (Measurable.of_discrete).aemeasurable⟩

end OnlineDiscUniv


