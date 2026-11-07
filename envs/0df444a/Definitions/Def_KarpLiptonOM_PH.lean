-- Prove2me | Definitions.Def_KarpLiptonOM_PH
-- name    : KarpLiptonOM_PH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:41:11.990509+00:00
-- url     : https://prove2.me/theorems/df146457-5441-4cd2-9ff5-668c9a28e51f
-- title:
--   The polynomial hierarchy $\mathrm{PH} = \bigcup_{k\ge1}\Sigma^{\mathrm P}_k$
-- statement:
--   The **polynomial hierarchy** is the union of all its levels:
--   $$
--   \mathrm{PH} = \bigcup_{k \ge 1} \Sigma^{\mathrm P}_k .
--   $$
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Theorem 1, p.5 (standard class)

import Mathlib
import Definitions.Def_KarpLiptonOM_SigmaP

namespace KarpLiptonOM

/-- The polynomial hierarchy `PH = ⋃_{k ≥ 1} Σ_k^P` (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), Theorem 1, p.5 and throughout; standard). -/
def PH : Set (Set (List Bool)) := {L | ∃ k, 1 ≤ k ∧ L ∈ SigmaP k}

end KarpLiptonOM


