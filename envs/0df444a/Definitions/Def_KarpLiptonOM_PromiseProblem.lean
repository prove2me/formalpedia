-- Prove2me | Definitions.Def_KarpLiptonOM_PromiseProblem
-- name    : KarpLiptonOM_PromiseProblem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:37:05.448724+00:00
-- url     : https://prove2.me/theorems/28af4c49-3821-406f-b2f0-6e3e7de0adb3
-- title:
--   Promise problem $\Pi = (\Pi_{\mathrm{YES}}, \Pi_{\mathrm{NO}})$
-- statement:
--   A **promise problem** is a pair $\Pi = (\Pi_{\mathrm{YES}}, \Pi_{\mathrm{NO}})$ of disjoint sets of binary strings, the yes-instances and the no-instances. Strings in neither set violate the promise; an algorithm for $\Pi$ only has to be correct on $\Pi_{\mathrm{YES}} \cup \Pi_{\mathrm{NO}}$.
--
--   Disjointness is part of the definition: it guarantees that some language is consistent with $\Pi$, so oracle classes $\mathrm P^\Pi$ and generator outputs are never defined over an empty family of oracles.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.2, p.21 (promise problems [ESY84])

import Mathlib

namespace KarpLiptonOM

/-- A **promise problem** `Π = (Π_YES, Π_NO)`: a pair of **disjoint** sets of binary strings
(Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.2, p.21). -/
structure PromiseProblem where
  /-- the yes-instances `Π_YES` -/
  yes : Set (List Bool)
  /-- the no-instances `Π_NO` -/
  no : Set (List Bool)
  /-- `Π_YES ∩ Π_NO = ∅` -/
  disjoint : Disjoint yes no

end KarpLiptonOM


