-- Prove2me | Definitions.Def_KarpLiptonOM_coONP2
-- name    : KarpLiptonOM_coONP2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:40:57.589214+00:00
-- url     : https://prove2.me/theorems/8bc9dcf5-1fef-498a-8dc1-9641e51dc8ac
-- title:
--   A language of pairs in co-ONP
-- statement:
--   A language of pairs $T$ is in $\mathrm{co\text{-}ONP}$ if its complement $\{(u, a) : (u, a) \notin T\}$ is in $\mathrm{ONP}$. The testers of the class OM are languages of pairs $(1^n, a)$ in co-ONP.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.4, p.24; proof of Theorem A.4.5, p.31

import Mathlib
import Definitions.Def_KarpLiptonOM_ONP2

namespace KarpLiptonOM

/-- A language of pairs `T` is in **co-ONP** if its complement is in ONP (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.4, p.24, the
testers of OM; proof of Theorem A.4.5, p.31). The complement contains every pair not in `T`,
including pairs not of the form `(1ⁿ, a)` with `|a| = p(n)`. -/
def coONP2 (T : List Bool → List Bool → Prop) : Prop := ONP2 (fun u a => ¬ T u a)

end KarpLiptonOM


