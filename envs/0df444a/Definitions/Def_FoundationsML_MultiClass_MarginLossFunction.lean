-- Prove2me | Definitions.Def_FoundationsML_MultiClass_MarginLossFunction
-- name    : FoundationsML_MultiClass_MarginLossFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:28:31.465247+00:00
-- url     : https://prove2.me/theorems/d6829926-81a4-42ef-ab3f-f1557470d92b
-- title:
--   Margin loss function Φ_ρ (Definition 5.5, restated)
-- statement:
--   **Definition 5.5, referenced p. 215, PDF p. 232.** $\Phi_\rho(x) = 1$ if $x\le0$,
--   $1-x/\rho$ if $0\le x\le\rho$, and $0$ if $x\ge\rho$. Restated locally in this chunk's
--   `MultiClass` namespace since a draft module cannot import chunk `05-svm`'s own copy.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, Definition 5.5 (referenced p. 215, PDF p. 232)

import Mathlib

namespace FoundationsML.MultiClass

/-- The margin loss function `Φ_ρ` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, Definition 5.5, referenced at p. 215, PDF p. 232, and
restated locally here since a draft module cannot import chunk `05-svm`'s own draft copy):
`Φ_ρ(x) = 1` if `x ≤ 0`, `1 − x/ρ` if `0 ≤ x ≤ ρ`, and `0` if `x ≥ ρ`. -/
noncomputable def MarginLossFunction (ρ : ℝ) (x : ℝ) : ℝ :=
  if x ≤ 0 then 1 else if x ≤ ρ then 1 - x / ρ else 0

end FoundationsML.MultiClass


