-- Prove2me | Definitions.Def_MultiSelectPandora_encRatPair
-- name    : MultiSelectPandora_encRatPair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:08:51.918254+00:00
-- url     : https://prove2.me/theorems/bf3e788b-d881-4770-a4ad-729741cb967e
-- title:
--   Binary encoding of a pair of rationals
-- statement:
--   The binary encoding of the two numbers $W(M,0)$ and $\mathrm{OPT}_C$ of Lemma 3.8.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Lemma 3.8, p.9 (PDF p.10)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encRat

open OnlineCRS.Combine

namespace MultiSelectPandora

/-- **Binary encoding of a pair of rationals.** Auxiliary to Lemma 3.8, p.9 (PDF p.10) of the Beyhaghi–Han–Luqman manuscript. -/
def encRatPair (p : ℚ × ℚ) : List Sym := encRat p.1 ++ [3] ++ encRat p.2

end MultiSelectPandora


