-- Prove2me | Definitions.Def_FarmerInfoProvision_Shock
-- name    : FarmerInfoProvision_Shock
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:34:48.681742+00:00
-- url     : https://prove2.me/theorems/e722e96d-d9b6-4185-ab93-f371052f0b59
-- title:
--   Index set of the model's independent shocks
-- statement:
--   The model has one demand shock $u$, one public-signal noise $\epsilon_r$, and one private-signal noise $\epsilon_i$ for each farmer $i=1,\dots,n$. The type $\mathrm{Shock}(n)$ indexes these $n+2$ shocks.
--
--   **Formalization Note** Farmers are indexed by $\{0,\dots,n-1\}$ in Lean.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), §3, pp. 8–9

import Mathlib

namespace FarmerInfoProvision

/-- **The index set of the independent Gaussian shocks of the model.**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), §3, pp. 8–9: the demand shock "`u ∼ N(0, σ_u²)`" (p. 8), the
private-signal noises "`ϵ_i ∼ N(0, σ_f²)`, `∀i`" (p. 8) and the public-signal noise
"`ϵ_r ∼ N(0, σ_r²)` … independent of `u` and all `{ϵ_i}`'s" (p. 9).

`Shock n` has one element `demand` (for `u`), one element `publicNoise` (for `ϵ_r`) and one
element `privateNoise i` for each farmer `i : Fin n` (for `ϵ_i`).

**Formalization Note.** Farmers are indexed by `Fin n`, i.e. `0, …, n − 1` for the paper's
`1, …, n`. -/
inductive Shock (n : ℕ) where
  | demand
  | publicNoise
  | privateNoise (i : Fin n)
  deriving DecidableEq, Fintype

end FarmerInfoProvision


