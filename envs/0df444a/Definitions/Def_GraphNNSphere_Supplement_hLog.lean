-- Prove2me | Definitions.Def_GraphNNSphere_Supplement_hLog
-- name    : GraphNNSphere_Supplement_hLog
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:44:22.303847+00:00
-- url     : https://prove2.me/theorems/6ffe3c69-cefd-4056-9fe1-9d53369a35cd
-- title:
--   Logarithmic-regime rates $R(g,\nu)$, $X(g,\nu)$, $h(g,\nu)$
-- statement:
--   In the logarithmic regime $d=\lfloor c\log n\rfloor$ write $\lambda=1/c$ and, for a region where $f$ has level $e^{\mu d}$, $\nu=\lambda+\mu$. For $0\le g<\nu$ define
--
--   $$R(g,\nu)=\arcsin e^{g-\nu},\qquad X(g,\nu)=\frac{e^{2g}}{1+\cos R(g,\nu)},\qquad h(g,\nu)=\frac12\log\frac{1+X(g,\nu)}2 .$$
--
--   $R(g,\nu)$ is the limiting radius of a cap containing $e^{gd}$ points in expectation at that density level, and $h(g,\nu)$ is the permitted density variation in the sufficient condition of Theorem 4.4.
--
--   **Formalization Note** This two-argument $h$ is distinct from the dense-regime $h(\gamma)$ of (11).
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §4.4, p.42

import Mathlib

namespace GraphNNSphere

namespace Supplement

/-- `R(g, ν) = arcsin e^{g-ν}`, the limiting radius of a cap containing `e^{gd}` points in
expectation at density level `e^{μd}`, `ν = λ + μ`, in the logarithmic regime
(Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §4.4, p.42). -/
noncomputable def Rlog (g ν : ℝ) : ℝ := Real.arcsin (Real.exp (g - ν))

/-- `X(g, ν) = e^{2g}/(1 + cos R(g, ν))` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §4.4, p.42). -/
noncomputable def Xlog (g ν : ℝ) : ℝ := Real.exp (2 * g) / (1 + Real.cos (Rlog g ν))

/-- The permitted density variation of the logarithmic regime,
`h(g, ν) = ½ log((1 + X(g, ν))/2)` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §4.4, p.42).

**Formalization Note** This two-argument `h` is distinct from the dense-regime `h(γ)` of (11),
`hDense`. -/
noncomputable def hLog (g ν : ℝ) : ℝ := Real.log ((1 + Xlog g ν) / 2) / 2

end Supplement

end GraphNNSphere


