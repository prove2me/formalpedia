-- Prove2me | Definitions.Def_FoundationsML_Boosting_PhiRho
-- name    : FoundationsML_Boosting_PhiRho
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:07:26.242587+00:00
-- url     : https://prove2.me/theorems/dd1aba23-020b-4f56-a0cb-dc63c170d390
-- title:
--   The rho-margin loss function (Definition 5.5, restated)
-- statement:
--   **Definition 5.5, p. 92, PDF p. 109 (restated locally for this chapter).** For $\rho>0$,
--   $\Phi_\rho(x)=\min(1,\max(0,1-x/\rho))$.
--
--   **Formalization Note.** Byte-identical to chunk `05-svm`'s own copy; restated because a
--   draft item cannot import another chunk's draft module.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 92, Definition 5.5 (PDF p. 109)

import Mathlib

namespace FoundationsML.Boosting

/-- The `ρ`-margin loss function `Φ_ρ` (Mohri, Rostamizadeh & Talwalkar, *Foundations of
Machine Learning*, 2nd ed., MIT Press 2018, Definition 5.5, p. 92, PDF p. 109, restated locally
for this chapter since drafts cannot import another chunk's draft module):
`Φ_ρ(x) = min(1, max(0, 1 − x/ρ))`. -/
noncomputable def PhiRho (ρ : ℝ) (x : ℝ) : ℝ := min 1 (max 0 (1 - x / ρ))

end FoundationsML.Boosting


