-- Prove2me | Definitions.Def_AvgPHETH_AltLen
-- name    : AvgPHETH_AltLen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:25:31.797099+00:00
-- url     : https://prove2.me/theorems/39c3363c-fa31-4caf-bb1f-45b82dec394e
-- title:
--   Alternating quantifiers with prescribed move lengths
-- statement:
--   For lengths $\ell_1,\dots,\ell_d$ this is the alternating quantification $\exists y_1\forall y_2\cdots Q_dy_d\,V(y_1,\dots,y_d)$ with $|y_i|=\ell_i$ (or the same starting with $\forall$).
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §1.1, p.2 (PDF 4)

import Mathlib

namespace AvgPHETH

/-- Alternating quantification with a prescribed length for each move: `AltLen [ℓ₁, …, ℓ_d] true V` is
`∃y₁ ∀y₂ ⋯ V(y₁, …, y_d)` with `|y_i| = ℓ_i` (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §1.1, p.2 (PDF 4)). -/
def AltLen : List ℕ → Bool → (List (List Bool) → Prop) → Prop
  | [], _, V => V []
  | m :: ms, true, V => ∃ y : List Bool, y.length = m ∧ AltLen ms false (fun ys => V (y :: ys))
  | m :: ms, false, V => ∀ y : List Bool, y.length = m → AltLen ms true (fun ys => V (y :: ys))

end AvgPHETH


