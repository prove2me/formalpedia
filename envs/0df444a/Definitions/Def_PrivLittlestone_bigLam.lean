-- Prove2me | Definitions.Def_PrivLittlestone_bigLam
-- name    : PrivLittlestone_bigLam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:22:53.559338+00:00
-- url     : https://prove2.me/theorems/0b00bd5f-8e77-4224-b016-8d82415831c6
-- title:
--   The logarithmic factor $\Lambda_q = \log\frac{e(q+1)(T+1)}{\varepsilon\delta\beta}$
-- statement:
--   For $q, T \in \mathbb N$ and $\varepsilon, \delta, \beta > 0$,
--   $$
--   \Lambda_q = \log \frac{e(q+1)(T+1)}{\varepsilon \delta \beta},
--   $$
--   with the natural logarithm. It collects the logarithmic factors of the main mistake bounds.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), §1.1, p.1; (11), p.10; Appendix C.1, p.24

import Mathlib

namespace PrivLittlestone

/-- The logarithmic factor `Λ_q = log (e(q + 1)(T + 1)/(εδβ))` (He–He, *Private Online Learning of
Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562),
§1.1, p.1; also (11), p.10, and Appendix C.1, p.24). Natural logarithm. -/
noncomputable def bigLam (q T : ℕ) (ε δ β : ℝ) : ℝ :=
  Real.log (Real.exp 1 * ((q : ℝ) + 1) * ((T : ℝ) + 1) / (ε * δ * β))

end PrivLittlestone


