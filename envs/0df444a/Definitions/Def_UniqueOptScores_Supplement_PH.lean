-- Prove2me | Definitions.Def_UniqueOptScores_Supplement_PH
-- name    : UniqueOptScores_Supplement_PH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:52:12.736213+00:00
-- url     : https://prove2.me/theorems/02c292a7-69e0-46b0-b7df-0a2e00394ccf
-- title:
--   The polynomial hierarchy $\mathrm{PH}=\bigcup_{k\ge0}\Sigma^{\mathrm P}_k$
-- statement:
--   The **polynomial hierarchy** is the union of all its levels, starting from $\Sigma^{\mathrm P}_0=\mathrm P$:
--   $$\mathrm{PH}=\bigcup_{k\ge 0}\Sigma^{\mathrm P}_k .$$
--
--   Theorem 1.1 compares $\mathrm{PH}$ with the class $\mathrm S_2^{\mathrm{NP}}$; equality is a collapse of the hierarchy to a fixed level.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), §3.2, p.14 (PDF p.15), "The polynomial hierarchy"

import Mathlib
import Definitions.Def_UniqueOptScores_Supplement_Sigma

namespace UniqueOptScores

namespace Supplement

/-- **The polynomial hierarchy PH.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §3.2, p.14 (PDF p.15): "With Σ^P_0 = Π^P_0 = P, the polynomial hierarchy is
PH := ⋃_{k≥0} Σ^P_k."

**Formalization Note.** The union is over every `k : ℕ`, including `k = 0` (P). -/
def PH : Set (Set (List Bool)) :=
  {L | ∃ k : ℕ, L ∈ Sigma k}

end Supplement

end UniqueOptScores


