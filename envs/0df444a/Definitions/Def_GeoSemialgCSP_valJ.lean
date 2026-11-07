-- Prove2me | Definitions.Def_GeoSemialgCSP_valJ
-- name    : GeoSemialgCSP_valJ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:49:29.957199+00:00
-- url     : https://prove2.me/theorems/a751f7be-2f83-4311-afab-073a7e7538f6
-- title:
--   Value of a fractional labelling on $(J_R)_f$
-- statement:
--   For a payoff $f:[q]^k\to\mathbb R$ and a map $F:[M]^R\to\mathcal P_q$,
--   $$\mathrm{val}(F,(J_R)_f)=\mathbb E_{(Z_1,\dots,Z_k)\sim J_R}\,f\bigl(F(Z_1),\dots,F(Z_k)\bigr),$$
--   with $f$ evaluated through its multilinear extension.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §4.4, p.12 (PDF p.13)

import Mathlib
import Definitions.Def_GeoSemialgCSP_Wd
import Definitions.Def_GeoSemialgCSP_jWeight
import Definitions.Def_GeoSemialgCSP_multilin

namespace GeoSemialgCSP

/-- **Value of a fractional labelling on `(J_R)_f`.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §4.4, printed p.12 (PDF
p.13): `val(F, I_f) = E_{(v₁,…,v_k) ∼ I} f(F(v₁), …, F(v_k))` (multilinear extension) for
`F : [M]^R → P_q`, here with `I = J_R`. -/
noncomputable def valJ {k h H q : ℕ} (L : PMF ((Fin h → Fin k) → Wd k H)) (R : ℕ)
    (f : (Fin k → Fin q) → ℝ) (F : (Fin R → Wd k H) → Fin q → ℝ) : ℝ :=
  ∑ Z : Fin k → (Fin R → Wd k H), jWeight L R Z * multilin f (fun j => F (Z j))

end GeoSemialgCSP


