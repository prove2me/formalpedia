-- Prove2me | Definitions.Def_IAFTRL_Bc
-- name    : IAFTRL_Bc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:52.834574+00:00
-- url     : https://prove2.me/theorems/2cccfd7b-3b1e-40b6-8f68-aa4008b71835
-- title:
--   The constant $B$
-- statement:
--   The constant $B$ used in the constraints (2.3d)–(2.3e) is
--   $$
--   B=2^{25}\,\big\lceil 256+\log(2K)\big\rceil ,
--   $$
--   equivalently $B=2^{24}P$ with $P=2\lceil256+\log(2K)\rceil$.
--
--   **Formalization Note** The ceiling applies to $256+\log(2K)$ only; $B$ is a real number.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Section 2.1, p.17; Eqs. (C.4)–(C.5), p.56

import Mathlib

namespace IAFTRL

/-- **The constant `B`.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Section 2.1, p.17: "`B = 2^{25}⌈256 + log(2K)⌉`"; equivalently
`B = 2^{24} P` with `P = 2⌈256 + log(2K)⌉` ((C.4)–(C.5), p.56; (D.138), p.87).

`Bc K = 2^{25} · ⌈256 + log(2K)⌉`, a real number.

**Formalization Note.** The ceiling applies to `256 + log(2K)` only, not to the product. -/
noncomputable def Bc (K : ℕ) : ℝ :=
  2 ^ 25 * (⌈256 + Real.log (2 * (K : ℝ))⌉ : ℝ)

end IAFTRL


