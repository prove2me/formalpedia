-- Prove2me | Definitions.Def_TradeAgentNV_Unimodal
-- name    : TradeAgentNV_Unimodal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T10:29:37.199983+00:00
-- url     : https://prove2.me/theorems/92843032-5d3a-4077-b2de-35a06f1e7762
-- title:
--   Unimodal on $[0,\infty)$
-- statement:
--   A function $f$ is **unimodal on $[0,\infty)$** if there is a mode $m\ge0$ such that $f$ is strictly increasing on $[0,m]$ and strictly decreasing on $[m,\infty)$.
--
--   **Formalization Note** This is the strict notion the proof of Theorem 1 establishes ("strictly increasing in $[0,b^o)$ and strictly decreasing in $(b^o,\infty)$", p.29); for a function continuous on $[0,\infty)$ the closed and half-open intervals give the same notion.
-- source:
--   Çakıcı & Karaesmen, When Yield is Not the Only Supply Uncertainty: Newsvendor Model of a Trade Agent, SSRN 4409114 (v. Oct 14, 2023), https://ssrn.com/abstract=4409114, Theorem 1(ii), p.10, and proof of Theorem 1, p.29

import Mathlib

namespace TradeAgentNV

/-- A function `f` is **unimodal on `Ω = [0, ∞)`** (Theorem 1(ii), p.10, and the proof of
Theorem 1, p.29, of Çakıcı & Karaesmen, *When Yield is Not the Only Supply Uncertainty: Newsvendor Model of a
Trade Agent*, SSRN 4409114 (v. Oct 14, 2023)) if there is a mode `m ≥ 0` such that `f` is
strictly increasing on `[0, m]` and strictly decreasing on `[m, ∞)`.

**Formalization Note.** This is the strict reading used in the proof on p.29 ("strictly
increasing in [0, bᵒ) and strictly decreasing in (bᵒ, ∞)"); for a function continuous on
`[0, ∞)` the closed and half-open intervals give the same notion. -/
def Unimodal (f : ℝ → ℝ) : Prop :=
  ∃ m, 0 ≤ m ∧ StrictMonoOn f (Set.Icc 0 m) ∧ StrictAntiOn f (Set.Ici m)

end TradeAgentNV


