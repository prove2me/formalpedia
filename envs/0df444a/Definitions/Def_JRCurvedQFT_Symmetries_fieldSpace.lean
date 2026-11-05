-- Prove2me | Definitions.Def_JRCurvedQFT_Symmetries_fieldSpace
-- name    : JRCurvedQFT_Symmetries_fieldSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:03:57.5332+00:00
-- url     : https://prove2.me/theorems/7dbf60fc-fc10-4e95-89b7-24f9faf4ffbe
-- title:
--   The field space $\mathcal E$
-- statement:
--   The **field space** $\mathcal E$ is the closure in $L^2(P;\mathbb C)$ of the complex span of all monomials, a complex Hilbert space. In the paper's setting the span is dense in $L^2(S',\mu)$, so that $\mathcal E=L^2(S',\mu)$.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries, arXiv:0704.0052v1, §2.1, p. 3

import Mathlib
import Definitions.Def_JRCurvedQFT_Symmetries_monomial

open scoped Manifold ContDiff ENNReal Topology InnerProductSpace
open Bundle MeasureTheory

namespace JRCurvedQFT.Symmetries

variable {d : ℕ} {M : Type} [EMetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) M]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The **field space** `E`, the closure in the complex `L²(P)` of the span of all monomials.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries*, arXiv:0704.0052v1, §2.1, p. 3: "the monomials ... are all elements of E, and ... their span is dense in E".

**Formalization Note** Reading 4: the paper takes `E = L²(S′, µ)` with this span dense, so there
`fieldSpace Φ` is all of `L²`. -/
noncomputable def fieldSpace (Φ : EuclideanField (d := d) M P) : Submodule ℂ (Lp ℂ 2 P) :=
  (Submodule.span ℂ (Set.range fun x : (Σ n : ℕ, Fin n → testFunctions (d := d) M) =>
    monomial Φ x.2)).topologicalClosure

/-- `E` is a Hilbert space. -/
noncomputable instance (Φ : EuclideanField (d := d) M P) : CompleteSpace (fieldSpace Φ) :=
  inferInstanceAs (CompleteSpace (Submodule.topologicalClosure _))

/-- A monomial as a vector of `E`. -/
noncomputable def fieldMonomial (Φ : EuclideanField (d := d) M P) {n : ℕ}
    (f : Fin n → testFunctions (d := d) M) : fieldSpace Φ :=
  ⟨monomial Φ f, Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨n, f⟩, rfl⟩)⟩

end JRCurvedQFT.Symmetries


