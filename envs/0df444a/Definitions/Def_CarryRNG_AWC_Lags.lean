-- Prove2me | Definitions.Def_CarryRNG_AWC_Lags
-- name    : CarryRNG_AWC_Lags
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:05:02.20442+00:00
-- url     : https://prove2.me/theorems/6c4b1c3b-bc06-44a1-bcdd-5c91020d5990
-- title:
--   Lags $0 < s < r$ of the carry generators (Sections 2–3, pp. 465–466)
-- statement:
--   The paper's add-with-carry and subtract-with-borrow generators have two **lags** $r$ and $s$, positive integers with
--
--   $$0 < s < r .$$
--
--   The paper assumes "for the two lags $r$ and $s$ that $r > s$" throughout (Section 3, p. 466), and every generator it considers has $s \ge 1$. The pair is bundled as one object $L = (r, s)$ that carries both inequalities, so that every statement about either generator can use the positions $x_1$ and $x_{r+1-s}$ of a state without further side conditions.
--
--   **Formalization Note** The structure `Lags` has fields `r`, `s` and proofs `hs : 0 < s`, `hsr : s < r`.
-- source:
--   G. Marsaglia and A. Zaman, A new class of random number generators, Ann. Appl. Probab. 1 (1991), p. 465, Section 2 (lags r > s); p. 466, Section 3 ("Here and throughout, we assume for the two lags r and s that r > s")

import Mathlib

namespace CarryRNG.AWC

/-- The two lags `r` and `s` of an add-with-carry generator, with the paper's standing
convention `0 < s < r` (Section 2, p. 465; Section 3, p. 466). -/
structure Lags where
  r : ℕ
  s : ℕ
  hs : 0 < s
  hsr : s < r

end CarryRNG.AWC


