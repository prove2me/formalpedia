-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_roMeasure
-- name    : QAdvFew_PoQOracle_roMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:47:55.014146+00:00
-- url     : https://prove2.me/theorems/5f8f32d3-383c-45a9-af55-13062e96aac7
-- title:
--   Law of the random oracle
-- statement:
--   The law of a random oracle $\mathrm{RO}=\{\mathrm{RO}_t:\{0,1\}^t\to\{0,1\}\}$: independent fair bits $\mathrm{RO}_t(u)$.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §4.1, p. 21 (PDF p. 23)

import Mathlib

open MeasureTheory

namespace QAdvFew.PoQOracle

/-- The law of a random oracle `RO = {RO_t : {0,1}^t → {0,1}}` (Goldin, Lombardi, Morimae, *Quantum
Advantage has Few Complexity Implications*, arXiv:2611.05303v1, §4.1, p. 21 (PDF p. 23): "Let
`RO_t : {0,1}^t → {0,1}` be a random oracle"): independent fair bits `RO_t(u)`. -/
noncomputable def roMeasure : Measure ((Σ t : ℕ, Fin t → Bool) → Bool) :=
  Measure.infinitePi fun _ : (Σ t : ℕ, Fin t → Bool) => (PMF.uniformOfFintype Bool).toMeasure

end QAdvFew.PoQOracle


