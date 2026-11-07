-- Prove2me | Definitions.Def_ChoresEFX_Lambda
-- name    : ChoresEFX_Lambda
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:07:13.435065+00:00
-- url     : https://prove2.me/theorems/830962df-9e7a-48a7-acca-8bc70dbea462
-- title:
--   The approximation-factor budget $\Lambda_k(t)$
-- statement:
--   The budget of Lemma A.1 is
--
--   $$\Lambda_1(t)=\frac{(1+t)(3/2+2t)}{1/2-2t},\qquad \Lambda_k(t)=(1+t)\left(1+\frac{1+t}{\rho}\right)\quad(k\ge2),$$
--
--   where $\rho=\rho_k(t)=1-t-(1+2t)/(k+1)$.
--
--   It is the factor for which the output of packet decomposition satisfies the hypotheses of the reallocation lemma.
--
--   **Formalization Note** For $0<t\le1/100$ no denominator vanishes.
-- source:
--   Qin, Fang, Li, Liu, Chen, Polynomial-Time Approximate EFX for Chores via Flow and Matching, STOC 2027 submission (manuscript sha256 b26d14cf…), Lemma A.1, p.19

import Mathlib
import Definitions.Def_ChoresEFX_IsCappedPriceStructure

namespace ChoresEFX

/-- **The approximation-factor budget** `Λ_k(t)`, Lemma A.1, p.19.

Qin, Fang, Li, Liu, Chen, *Polynomial-Time Approximate EFX for Chores via Flow and Matching*, STOC 2027
submission (manuscript sha256 b26d14cf…): `Λ_1(t) = (1 + t)(3/2 + 2t)/(1/2 − 2t)` and, for `k ≥ 2`,
`Λ_k(t) = (1 + t)(1 + (1 + t)/ρ)` with `ρ = ρ_k(t)`.

**Formalization Note.** For `0 < t ≤ 1/100` no denominator vanishes: `1/2 − 2t > 0`, and `ρ_k(t) > 0`
for `k ≥ 2`. -/
noncomputable def Lambda (k : ℕ) (t : ℝ) : ℝ :=
  if k = 1 then (1 + t) * (3 / 2 + 2 * t) / (1 / 2 - 2 * t)
  else (1 + t) * (1 + (1 + t) / rhoParam k t)

end ChoresEFX


