-- Prove2me | Definitions.Def_NearOptOWF_SubexpIOExists
-- name    : NearOptOWF_SubexpIOExists
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:14:57.781471+00:00
-- url     : https://prove2.me/theorems/5d5aea5f-e095-4c09-9c52-42e9113673e3
-- title:
--   Existence of a sub-exponentially secure iO
-- statement:
--   The hypothesis that some obfuscator is a sub-exponentially secure indistinguishability obfuscator (Theorem 4.1, second bullet; Lemma 3.6).
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem 4.1, p.11 (PDF p.13); Lemma 3.6, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_NearOptOWF_MIOScheme_IsSubexpIO

namespace NearOptOWF

/-- The hypothesis "**there exists a sub-exponentially secure indistinguishability obfuscator**"
(Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem 4.1, p.11 (PDF p.13), second bullet; Lemma 3.6, p.9 (PDF p.11)). -/
def SubexpIOExists : Prop :=
  ∃ O : MIOScheme, O.IsSubexpIO

end NearOptOWF


