-- Prove2me | Definitions.Def_FoundationsML_Ranking_MarginLossFunction
-- name    : FoundationsML_Ranking_MarginLossFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:36:41.047303+00:00
-- url     : https://prove2.me/theorems/987697c4-3e19-43ca-a4c3-643d8c7411ad
-- title:
--   Margin loss function Φ_ρ (Definition 5.5, restated)
-- statement:
--   **Definition 5.5, referenced p. 241, PDF p. 258.** $\Phi_\rho(x) = 1$ if $x\le0$,
--   $1-x/\rho$ if $0\le x\le\rho$, and $0$ if $x\ge\rho$. Restated locally in this chunk's
--   `Ranking` namespace since a draft module cannot import chunk `05-svm`'s own copy.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, Definition 5.5 (referenced p. 241, PDF p. 258)

import Mathlib

namespace FoundationsML.Ranking

/-- The margin loss function `Φ_ρ` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, Definition 5.5, referenced at p. 241, PDF p. 258, and
restated locally here since a draft module cannot import chunk `05-svm`'s own draft copy):
`Φ_ρ(x) = 1` if `x ≤ 0`, `1 − x/ρ` if `0 ≤ x ≤ ρ`, and `0` if `x ≥ ρ`. -/
noncomputable def MarginLossFunction (ρ : ℝ) (x : ℝ) : ℝ :=
  if x ≤ 0 then 1 else if x ≤ ρ then 1 - x / ρ else 0

end FoundationsML.Ranking


