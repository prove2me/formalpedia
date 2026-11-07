-- Prove2me | Definitions.Def_HZTractability_SRFQ
-- name    : HZTractability_SRFQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:11:53.456831+00:00
-- url     : https://prove2.me/theorems/d40a7dbc-1dbe-4c59-8572-12445c52aee9
-- title:
--   Reference supplies and anchor counts (display (5))
-- statement:
--   The floor and upper reference groups at $v$ have supplies and anchor populations
--   $$
--   S^R_{Fv}=\Big\lceil\frac{F_v+1}{a\eta}\Big\rceil,\quad A^R_{Fv}=\lceil aL\,S^R_{Fv}\rceil,\quad
--   S^R_{Uv}=\Big\lceil\frac{c_v+1}{a\eta}\Big\rceil,\quad A^R_{Uv}=\lceil aU\,S^R_{Uv}\rceil .
--   $$
--   They pin the reference prices: at an exact equilibrium $aL\le r_{Fv}\le a(L+\eta)$ and $aU\le r_{Uv}\le a(U+\eta)$.
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), display (5), p.12 (PDF p.14)

import Mathlib
import Definitions.Def_HZTractability_Lp
import Definitions.Def_HZTractability_bvQ
import Definitions.Def_HZTractability_FvQ

namespace HZTractability

/-- **The reference supplies and anchor counts** (Panageas–Shein–Taherijam–Vazirani,
arXiv:2610.35848, held version, sha256 74b7bf9f…, display (5), p.12 (PDF 14)):
"S^R_{Fv} = ⌈(F_v + 1)/(aη)⌉, A^R_{Fv} = ⌈aL S^R_{Fv}⌉, S^R_{Uv} = ⌈(c_v + 1)/(aη)⌉,
A^R_{Uv} = ⌈aU S^R_{Uv}⌉". This is `S^R_{Fv}`, the supply of the floor reference group. -/
def SRFQ (a τ : ℚ) (K o : ℕ) : ℚ := (⌈(FvQ a K o + 1) / (a * eta a τ K)⌉ : ℚ)

/-- `A^R_{Fv} = ⌈a L S^R_{Fv}⌉`, the number of floor anchors (display (5), p.12). -/
def ARFQ (a τ : ℚ) (K o : ℕ) : ℚ := (⌈a * Lp a K * SRFQ a τ K o⌉ : ℚ)

/-- `S^R_{Uv} = ⌈(c_v + 1)/(aη)⌉`, the supply of the upper reference group (display (5), p.12). -/
def SRUQ (a τ : ℚ) (K o : ℕ) : ℚ := (⌈(cvQ a K o + 1) / (a * eta a τ K)⌉ : ℚ)

/-- `A^R_{Uv} = ⌈a U S^R_{Uv}⌉`, the number of upper anchors (display (5), p.12). -/
def ARUQ (a τ : ℚ) (K o : ℕ) : ℚ := (⌈a * Up a K * SRUQ a τ K o⌉ : ℚ)

end HZTractability


