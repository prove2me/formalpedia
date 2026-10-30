-- Prove2me | Definitions.Def_CoffmanMitrani_Data_rho
-- name    : CoffmanMitrani_Data_rho
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:02:22.41907+00:00
-- url     : https://prove2.me/theorems/5fcb41d9-80ae-4be9-a3d4-2e5b0049229e
-- title:
--   Traffic intensity $\rho_i = \lambda_i/\mu_i$
-- statement:
--   For a model instance and a class $i$, the traffic intensity of class $i$ is
--   $$\rho_i = \frac{\lambda_i}{\mu_i}.$$
--   The total traffic intensity is $\rho = \rho_1 + \dots + \rho_M$.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 811

import Mathlib
import Definitions.Def_CoffmanMitrani_Data

namespace CoffmanMitrani

/-- **Traffic intensity of class `i`.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 811: "The traffic intensity for class i is ρi = λi/μi and the total traffic intensity
is ρ = ρ1 + ρ2 + ··· + ρM."

`D.rho i = λi / μi`; the total intensity `ρ` is written `∑ i, D.rho i` wherever it is used. -/
noncomputable def Data.rho (D : Data) (i : Fin D.M) : ℝ := D.lam i / D.mu i

end CoffmanMitrani


