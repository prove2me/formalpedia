-- Prove2me | Definitions.Def_IAFTRL_cR
-- name    : IAFTRL_cR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:52.455102+00:00
-- url     : https://prove2.me/theorems/bd3a8448-e3f9-46d0-96f6-60fc58a3e7af
-- title:
--   The constant $c_R=\sqrt{d\log(eK)}$
-- statement:
--   The constant
--   $$
--   c_R=\sqrt{d\log(eK)}
--   $$
--   appears in the direct corruption bound $16\sqrt2\,c_R\sqrt C$ of Lemma D.14; it satisfies $d/\beta_t\le c_R/\sqrt t$.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Appendix B, Eq. (B.1), p.33

import Mathlib

namespace IAFTRL

/-- **The constant `c_R`.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Appendix B, Eq. (B.1), p.33: `c_R = √(d log(eK))`.

`cR d K = √(d · log(e·K))`. -/
noncomputable def cR (d K : ℕ) : ℝ :=
  Real.sqrt ((d : ℝ) * Real.log (Real.exp 1 * K))

end IAFTRL


