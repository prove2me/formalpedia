-- Prove2me | Definitions.Def_FairFacilityLoc_tau
-- name    : FairFacilityLoc_tau
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:11:04.133613+00:00
-- url     : https://prove2.me/theorems/a1ae23c2-f93b-4c8f-8984-0f8421f78a01
-- title:
--   The threshold $\tau_d$
-- statement:
--   $$\tau_1=1,\qquad\tau_2=\frac1{\sqrt2},\qquad\tau_3=\frac{25-\sqrt{157}}{18}.$$
--
--   These are the values computed in Lemma 3.22.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), Lemma 3.22, p.41 (PDF p.43)

import Mathlib

namespace FairFacilityLoc

/-- **The threshold `τ_d`** (Yan, Zhou, manuscript, sha256 642a1268…, Lemma 3.22, p.41, PDF p.43): `τ₁ = 1`,
`τ₂ = 1/√2`, `τ₃ = (25 − √157)/18`.

**Formalization Note.** Every statement using it has `d ∈ {1, 2, 3}`; the last branch is `d = 3` there. -/
noncomputable def tau (d : ℕ) : ℝ :=
  if d = 1 then 1 else if d = 2 then 1 / √2 else (25 - √157) / 18

end FairFacilityLoc


