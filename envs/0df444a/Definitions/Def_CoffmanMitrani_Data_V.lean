-- Prove2me | Definitions.Def_CoffmanMitrani_Data_V
-- name    : CoffmanMitrani_Data_V
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:02:53.860683+00:00
-- url     : https://prove2.me/theorems/09a42bf3-ed80-4ac0-b3dc-4ff6d2aa7bf8
-- title:
--   The constant $V = \sum_i \lambda_i/\mu_i^2$
-- statement:
--   The constant appearing in Kleinrock's conservation law (1) is
--   $$V = \sum_{i=1}^M \frac{\lambda_i}{\mu_i^2}.$$
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 813, eq. (1)

import Mathlib
import Definitions.Def_CoffmanMitrani_Data

namespace CoffmanMitrani

/-- **The constant `V` of the conservation law.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 813, eq. (1): "where V = Σ_{i=1}^M (λi/μi²)."

`D.V = Σ_i λi / μi²`. -/
noncomputable def Data.V (D : Data) : ℝ := ∑ i, D.lam i / D.mu i ^ 2

end CoffmanMitrani


