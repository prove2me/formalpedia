-- Prove2me | Definitions.Def_QPSpinParisi_IsParisiPath
-- name    : QPSpinParisi_IsParisiPath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:18:52.249637+00:00
-- url     : https://prove2.me/theorems/ea3a2b3c-7092-45e4-9d3c-3fbd18e4ba44
-- title:
--   A solution of the SDE of Lemma 3.7
-- statement:
--   A process $X$ on $[0,1)$ solves $dX_t=\zeta(t)\gamma(t)\nabla\Phi(t,X_t)\,dt+\sqrt{\zeta(t)}\,dB_t$, $X_0=0$, when it is adapted with continuous paths and, for each $t<1$, almost surely,
--   $$X_t=\int_0^t\sqrt{\zeta(r)}\,dB_r+\int_0^t\zeta(r)\gamma(r)\nabla\Phi(r,X_r)\,dr.$$
--
--   **Formalization Note** Continuity is asked of every path, which a solution can always arrange since the filtration is completed. This keeps the integrands of the Itô relations in Lemma 3.7 measurable in time for every outcome.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Lemma 3.7, p.23 (PDF p.23)

import Mathlib
import Definitions.Def_QPSpinParisi_gradPsi
import Definitions.Def_QPSpinParisi_BrownianNoise_filt
import Definitions.Def_QPSpinParisi_BrownianNoise_noise

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- `X` solves `dX_t = ζ(t) γ(t) ∇Φ(t, X_t) dt + √ζ(t) dB_t`, `X₀ = 0`, on `[0, 1)` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Lemma 3.7, p.23, PDF p.23), in integral
form: `X` is adapted, every path is continuous on `[0,1)`, and for each `t < 1`, almost surely,
`X_t = ∫₀ᵗ √ζ dB + ∫₀ᵗ ζ γ ∇Φ(r, X_r) dr`.

**Formalization Note** Continuity is asked of every path, and a solution has such a version since the filtration is completed. This
makes the integrands in the Itô relations of `lemma_3_7` measurable in time for every `ω`, as that relation asks. -/
def IsParisiPath {c : ℕ → ℝ} (W : BrownianNoise c) (γ : Ico (0 : ℝ) 1 → ℝ) (X : ℝ≥0 → W.Ω → E3) : Prop :=
  (∀ t : ℝ≥0, t < 1 → StronglyMeasurable[W.filt t] (X t)) ∧
  (∀ ω, ContinuousOn (fun t => X t ω) (Iio 1)) ∧
  ∀ t : ℝ≥0, t < 1 → ∀ᵐ ω ∂W.P, X t ω = W.noise t ω +
    ∫ r in (0 : ℝ)..t, (zeta c r * gamHat γ r) • gradPsi W γ r (X r.toNNReal ω)

end QPSpinParisi


