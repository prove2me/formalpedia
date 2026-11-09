-- Prove2me | Definitions.Def_MatroidOptGame_excessValue
-- name    : MatroidOptGame_excessValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:59:33.881719+00:00
-- url     : https://prove2.me/theorems/b0da9b52-de15-43dd-af2a-043b437472d8
-- title:
--   Excess value $\Delta(M,w)$
-- statement:
--   The **excess value** of the game is
--   $$
--   \Delta(M, w) = V(M, w) - w(B_{\min}(M, w)).
--   $$
--   It is $\infty$ exactly when $V(M, w) = \infty$.
--
--   **Formalization Note** Computed in the extended reals.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3 (display defining ∆)

import Mathlib
import Definitions.Def_MatroidOptGame_minBaseWeight
import Definitions.Def_MatroidOptGame_value
import Definitions.Def_NKtLB_toEReal

namespace MatroidOptGame

/-- The excess value `Δ(M, w) = V(M, w) − w(B_min(M, w))`.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3 (display "∆ = ∆(M, w) = V(M, w) − w(B_min(M, w))").

**Formalization Note.** In `EReal`, through the published embedding `NKtLB.toEReal`; `Δ = ⊤`
exactly when `V = ∞`. -/
noncomputable def excessValue {α : Type*} [Fintype α] [DecidableEq α] (M : Matroid α)
    (w : α → ℕ) : EReal :=
  NKtLB.toEReal (value M w) - ((minBaseWeight M w : ℝ) : EReal)

end MatroidOptGame


