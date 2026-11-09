-- Prove2me | Definitions.Def_Pr6453_Linear
-- name    : Pr6453_Linear
-- status  : Definition
-- author  : @gustasmickus
-- created : 2026-11-08T22:15:27.056524+00:00
-- url     : https://prove2.me/theorems/62e555e8-f416-45b8-8d20-386a949778f6
-- title:
--   PR #6453: additivity of the rows
-- statement:
--   Additivity of the rows in a replay: two row assignments that sum pointwise to a third, replayed from the same frame chart, give results whose rows sum pointwise. This is the index the linearity of a word's output is stated with — the rows a word computes are a linear function of the rows it starts from.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4: the guarded replay of research/p104-clean-piggyback/construct.py.

/-
PR #6453: additivity of the rows.
-/
import Definitions.Def_Pr6453_Replay

set_option autoImplicit false

namespace Pr6453

/-- The rows of two states sum pointwise to the rows of a third. -/
def RowsAdd {n : ℕ} (a b c : Fin n → ℕ →₀ ℚ) : Prop := ∀ i, c i = a i + b i

end Pr6453


