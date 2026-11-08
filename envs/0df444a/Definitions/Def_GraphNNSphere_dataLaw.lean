-- Prove2me | Definitions.Def_GraphNNSphere_dataLaw
-- name    : GraphNNSphere_dataLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:39:41.984871+00:00
-- url     : https://prove2.me/theorems/5a489b97-a0d9-4a16-8d06-d054e00b179c
-- title:
--   Law of the uniform sample $D_n$
-- statement:
--   The law of the sample $D_n=(X_1,\dots,X_n)$ of $n$ independent uniform points of $S^{d-1}$, that is, the product measure $\sigma_{d-1}^{\otimes n}$. This is the paper's model with sampling density $f\equiv1$.
--
--   **Formalization Note** A sample is a map from the labels `Fin n` to the sphere.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.2

import Mathlib
import Definitions.Def_GraphNNSphere_unif

open MeasureTheory

namespace GraphNNSphere

/-- The law of the uniform sample `D_n = (X_1, …, X_n)`: `n` independent points with common
distribution `σ_{d-1}` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*,
STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.2, with `f ≡ 1`).

**Formalization Note** A sample is a map `Fin n → Sph d`. The indices are the data labels. -/
noncomputable def dataLaw (n d : ℕ) : Measure (Fin n → Sph d) :=
  Measure.pi (fun _ => unif d)

end GraphNNSphere


