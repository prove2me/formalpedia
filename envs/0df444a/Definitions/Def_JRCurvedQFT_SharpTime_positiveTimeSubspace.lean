-- Prove2me | Definitions.Def_JRCurvedQFT_SharpTime_positiveTimeSubspace
-- name    : JRCurvedQFT_SharpTime_positiveTimeSubspace
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:37:37.798102+00:00
-- url     : https://prove2.me/theorems/db7f832a-ef33-47fa-bd82-fa8f8894544d
-- title:
--   Positive-time subspace $\mathcal E_+=\mathcal E_{\Omega_+}$
-- statement:
--   The **positive-time subspace** is $\mathcal E_+=\mathcal E_{\Omega_+}$, the standard domain of the open half $\Omega_+=\{t>0\}$: the closed span of $e^{i\Phi(g)}$ over real test functions $g$ supported in $\Omega_+$.
--
--   Time-zero vectors are not in it by support; their membership is clause (i) of Theorem 4.4.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, p. 5

import Mathlib
import Definitions.Def_JRCurvedQFT_SharpTime_standardDomain
import Definitions.Def_JRCurvedQFT_SharpTime_StaticStructure

open scoped Manifold ContDiff ENNReal Topology
open Bundle MeasureTheory

namespace JRCurvedQFT.SharpTime

variable {d : ℕ} {M : Type} [EMetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]

/-- The **positive-time subspace** `ℰ₊ = ℰ_{Ω₊}`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, p. 5: "Of particular importance for Euclidean field theory is the positive-time subspace
ℰ₊ := ℰ_{Ω₊}, where the notation Ω₊ refers to the decomposition (1.1)."

**Formalization Note** `Ω₊ = {t > 0}` is open; time-zero vectors are not in it by support. -/
noncomputable def positiveTimeSubspace [MeasurableSpace M] (S : StaticStructure (d := d) M)
    (μ : Measure M) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (Φ : ((M → ℝ) → ℝ) → Ω → ℝ) : Submodule ℂ (Lp ℂ 2 P) :=
  standardDomain (d := d) μ P Φ S.positiveTime

end JRCurvedQFT.SharpTime


