-- Prove2me | Definitions.Def_GeoSemialgCSP_valD
-- name    : GeoSemialgCSP_valD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:51:17.841659+00:00
-- url     : https://prove2.me/theorems/a7870641-7bc9-4535-afc9-98b00ba4f44c
-- title:
--   Value of a fractional labelling on $(D_R)_f$
-- statement:
--   For a payoff $f:[q]^k\to\mathbb R$ and a map $F:[M]^R\to\mathcal P_q$,
--   $$\mathrm{val}(F,(D_R)_f)=\mathbb E_{(\tilde Z_1,\dots,\tilde Z_k)\sim D_R}\,f\bigl(F(\tilde Z_1),\dots,F(\tilde Z_k)\bigr),$$
--   with $f$ evaluated through its multilinear extension.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §4.4, p.12 (PDF p.13)

import Mathlib
import Definitions.Def_GeoSemialgCSP_Wd
import Definitions.Def_GeoSemialgCSP_dWeight
import Definitions.Def_GeoSemialgCSP_multilin

namespace GeoSemialgCSP

/-- **Value of a fractional labelling on `(D_R)_f`.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §4.4, printed p.12 (PDF
p.13), with `I = D_R`. -/
noncomputable def valD {k h H q : ℕ} (L : PMF ((Fin h → Fin k) → Wd k H)) (R : ℕ) (η : ℝ)
    (f : (Fin k → Fin q) → ℝ) (F : (Fin R → Wd k H) → Fin q → ℝ) : ℝ :=
  ∑ Z : Fin k → (Fin R → Wd k H), dWeight L R η Z * multilin f (fun j => F (Z j))

end GeoSemialgCSP


