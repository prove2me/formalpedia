-- Prove2me | Definitions.Def_GraphNNSphere_Supplement_sampleLaw
-- name    : GraphNNSphere_Supplement_sampleLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:41:54.545315+00:00
-- url     : https://prove2.me/theorems/a563ca2f-33a4-4482-9f9c-2d9c174cad26
-- title:
--   Nonuniform sampling law $P=f\,d\sigma_{d-1}$ and the sample law
-- statement:
--   A **sampling density** on $S^{d-1}$ is a measurable function $f\ge 0$ with $\int f\,d\sigma_{d-1}=1$, where $\sigma_{d-1}$ is normalized surface measure. It defines the sampling distribution
--
--   $$P(A)=\int_A f\,d\sigma_{d-1}$$
--
--   for measurable $A\subseteq S^{d-1}$, and the sample $D_n=(X_1,\dots,X_n)$ consists of $n$ independent points with common law $P$. For $f\equiv 1$ this is the uniform model of the base mission.
--
--   These objects carry the nonuniform results of Section 4 (Theorems 4.1, 4.3, 4.4, 4.6, 4.8).
--
--   **Formalization Note** The density is real valued and required to be nonnegative at every point, which restricts no law (every density has such a version). The sample is a map from the labels $\{1,\dots,n\}$ to the sphere, with the product law.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.2

import Mathlib
import Definitions.Def_GraphNNSphere_unif

open MeasureTheory

namespace GraphNNSphere

namespace Supplement

/-- `f` is a sampling density on `S^{d-1}`: a measurable nonnegative function with
`∫ f dσ_{d-1} = 1` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.2).

**Formalization Note** The density is real valued and nonnegative at every point. A density is
determined only up to null sets, and every density has such a representative, so this restricts
no law. -/
def IsDensity (d : ℕ) (f : Sph d → ℝ) : Prop :=
  Measurable f ∧ (∀ x, 0 ≤ f x) ∧ Integrable f (unif d) ∧ ∫ x, f x ∂(unif d) = 1

/-- The sampling distribution `P = f dσ_{d-1}`, so that `P(A) = ∫_A f dσ_{d-1}`
(Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.2). -/
noncomputable def sampleLaw (d : ℕ) (f : Sph d → ℝ) : Measure (Sph d) :=
  (unif d).withDensity (fun x => ENNReal.ofReal (f x))

instance (d : ℕ) (f : Sph d → ℝ) : SigmaFinite (sampleLaw d f) := by
  unfold sampleLaw; infer_instance

/-- The law of the sample `D_n = (X_1, …, X_n)` of `n` independent points with common
distribution `P = f dσ_{d-1}` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.2).

**Formalization Note** A sample is a map `Fin n → Sph d`, as in the base mission's `dataLaw`,
which is the case `f ≡ 1`. -/
noncomputable def dataLawF (n d : ℕ) (f : Sph d → ℝ) : Measure (Fin n → Sph d) :=
  Measure.pi (fun _ => sampleLaw d f)

end Supplement

end GraphNNSphere


