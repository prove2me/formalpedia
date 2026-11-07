-- Prove2me | Definitions.Def_GeoSemialgCSP_valDord
-- name    : GeoSemialgCSP_valDord
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:51:14.565437+00:00
-- url     : https://prove2.me/theorems/bed5c0cd-4aba-45ee-9050-fc2f6690f78d
-- title:
--   Value of an ordinary solution on $(D_R)_P$
-- statement:
--   For an assignment $\phi:[M]^R\to\mathbb R^d$ of points to the variables of the test,
--   $$\mathrm{val}(\phi,(D_R)_P)=\mathbb E_{(\tilde Z_1,\dots,\tilde Z_k)\sim D_R}\,P\bigl(\phi(\tilde Z_1),\dots,\phi(\tilde Z_k)\bigr).$$
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3, p.7 (PDF p.8); Lemma 4.4, p.12 (PDF p.13)

import Mathlib
import Definitions.Def_GeoSemialgCSP_E
import Definitions.Def_GeoSemialgCSP_Wd
import Definitions.Def_GeoSemialgCSP_dWeight

namespace GeoSemialgCSP

/-- **Value of an ordinary solution on `(D_R)_P`.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3, printed p.7 (PDF p.8),
and Lemma 4.4, printed p.12 (PDF p.13): `val(ϕ, (D_R)_P) = E_{(Z̃₁,…,Z̃_k) ∼ D_R} P(ϕ(Z̃₁), …, ϕ(Z̃_k))`
for `ϕ : [M]^R → ℝ^d`. -/
noncomputable def valDord {k d h H : ℕ} (L : PMF ((Fin h → Fin k) → Wd k H)) (R : ℕ) (η : ℝ)
    (S : Set (Fin k → E d)) (ϕ : (Fin R → Wd k H) → E d) : ℝ :=
  ∑ Z' : Fin k → (Fin R → Wd k H), dWeight L R η Z' * S.indicator 1 (ϕ ∘ Z')

end GeoSemialgCSP


