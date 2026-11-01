-- Prove2me | Definitions.Def_TradeAgentNV_salesSupplyRatio
-- name    : TradeAgentNV_salesSupplyRatio
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T10:29:34.074631+00:00
-- url     : https://prove2.me/theorems/a21dd96f-62ff-448d-993f-348f33c0fd77
-- title:
--   Expected sales-to-supply ratio $E[\min(U,D/q)]/E[U]$
-- statement:
--   For the yield fraction $U$, demand $D$ and lot size $q$, the **expected sales-to-supply ratio** is
--   $$
--   \frac{E[\min(U,D/q)]}{E[U]} .
--   $$
--   Theorem 1 compares it with the threshold $h/\rho$.
--
--   **Formalization Note** A real quotient; every theorem using it assumes $q>0$ and $E[U]>0$.
-- source:
--   Çakıcı & Karaesmen, When Yield is Not the Only Supply Uncertainty: Newsvendor Model of a Trade Agent, SSRN 4409114 (v. Oct 14, 2023), https://ssrn.com/abstract=4409114, Theorem 1, p.10, and the text after display (8), p.11

import Mathlib

open MeasureTheory

namespace TradeAgentNV

/-- The **expected sales-to-supply ratio** `E[min(U, D/q)] / E[U]` (Theorem 1, p.10, and the
discussion after display (8), p.11, of Çakıcı & Karaesmen, *When Yield is Not the Only Supply Uncertainty: Newsvendor Model of a
Trade Agent*, SSRN 4409114 (v. Oct 14, 2023)), where `U` is the yield
fraction on `(Ω, P)`, `D` the demand and `q` the seller's lot size.

**Formalization Note.** Real division; every theorem that uses it assumes `q > 0` and
`E[U] > 0`, so neither denominator vanishes. -/
noncomputable def salesSupplyRatio {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : Ω → ℝ)
    (D q : ℝ) : ℝ :=
  (∫ ω, min (U ω) (D / q) ∂P) / ∫ ω, U ω ∂P

end TradeAgentNV


