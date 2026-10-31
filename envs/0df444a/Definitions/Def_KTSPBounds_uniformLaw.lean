-- Prove2me | Definitions.Def_KTSPBounds_uniformLaw
-- name    : KTSPBounds_uniformLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:37:12.216991+00:00
-- url     : https://prove2.me/theorems/43ce6300-007d-46ce-8c3c-4167e5d7b1ac
-- title:
--   The uniform law on a set $\mathcal K\subset\mathbb R^2$
-- statement:
--   The uniform law on a set $\mathcal K \subset \mathbb R^2$ of positive finite area $\mathcal A_{\mathcal K}$ is
--
--   $$
--   \mu_{\mathcal K}(B) = \frac{|B \cap \mathcal K|}{\mathcal A_{\mathcal K}},
--   $$
--
--   where $|\cdot|$ is Lebesgue measure.
--
--   This is the law of each vertex in Theorem 2 and Lemma 2.
--
--   **Formalization Note** The definition is `ProbabilityTheory.cond volume K`, the normalized restriction of Lebesgue measure, and not `ProbabilityTheory.uniformOn`, which normalizes counting measure. Every theorem assumes `IsCompact K` and `0 < volume K`, under which it is a probability measure.
-- source:
--   Blanchard, Jacquillat, Jaillet, Probabilistic bounds on the k-Traveling Salesman Problem and the Traveling Repairman Problem, arXiv:2211.11063v1, Theorem 2 and Lemma 2, p.9

import Mathlib
import Definitions.Def_KTSPBounds_Plane

open MeasureTheory

namespace KTSPBounds

/-- The uniform law on `K ⊆ ℝ²` ("uniformly on a compact 𝒦 ⊂ ℝ²", Theorem 2 and Lemma 2, p.9),
Blanchard, Jacquillat, Jaillet, arXiv:2211.11063v1: Lebesgue measure restricted to `K` and normalized by the area of `K`.

**Formalization Note.** `ProbabilityTheory.cond volume K` is `(volume K)⁻¹ • volume.restrict K`.
This is a probability measure exactly when `0 < volume K < ∞`, which every theorem of this mission
gets from `IsCompact K` and `0 < volume K`. It is not `ProbabilityTheory.uniformOn`, which
normalizes the counting measure. -/
noncomputable def uniformLaw (K : Set Plane) : Measure Plane :=
  ProbabilityTheory.cond volume K

end KTSPBounds


