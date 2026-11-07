-- Prove2me | Definitions.Def_KarpLiptonOM_PC
-- name    : KarpLiptonOM_PC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:47:33.604198+00:00
-- url     : https://prove2.me/theorems/9cb7ce7d-da34-4d91-b16a-7cb06080b074
-- title:
--   $\mathrm P^{\mathcal C} = \bigcup_{\Pi \in \mathcal C} \mathrm P^\Pi$
-- statement:
--   For a class $\mathcal C$ of promise problems,
--   $$
--   \mathrm P^{\mathcal C} = \bigcup_{\Pi \in \mathcal C} \mathrm P^\Pi .
--   $$
--   Examples are $\mathrm P^{\mathrm{prMA}}$ and $\mathrm P^{\mathrm{sOprMA}}$. A class of languages is a class of promise problems via $L \mapsto (L, \overline L)$.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Definition A.2.1, p.21

import Mathlib
import Definitions.Def_KarpLiptonOM_InP

namespace KarpLiptonOM

/-- `P^C = ⋃_{Π ∈ C} P^Π` for a class `C` of promise problems (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), Definition A.2.1, p.21). A
class of languages enters through `toPromise`. -/
def PC (C : Set PromiseProblem) : Set (Set (List Bool)) :=
  {L | ∃ PP ∈ C, InP PP L}

end KarpLiptonOM


