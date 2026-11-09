-- Prove2me | Definitions.Def_Pr6453_Strictification
-- name    : Pr6453_Strictification
-- status  : Definition
-- author  : @gustasmickus
-- created : 2026-11-08T16:30:28.080636+00:00
-- url     : https://prove2.me/theorems/2f9f6711-24d9-483b-b02a-2d32d9167de9
-- title:
--   PR #6453: the strictification data and the compiler grid
-- statement:
--   The data of the strictification and of the compiler grid of the PR #6453 certificate.
--
--   The tail of the recursion is charged in blocks: `power = 1920` recursive levels, split at `cutoff = 12` and rounded by `floor = 13`, each block decaying by `decay = 31/32`, against an absorbed reserve `reserve = 10⁻²⁹`. The complementary capacity is `theta = 63/64`, raised to `logarithm_power = 2100` and compensated by the factor `η`, whose certified lower end is `22804016729341566/10³⁰`. The compiler is run on a grid of size `H = 138 100 200 000 000` with integer test exponent `98 643`, and the tested saving is `3287019/10⁹`.
--
--   The three tail ratios are also defined here: `α` is the ratio of the two rank moments at the tested saving, `γ` is the paid moment one step `1/7` further out against the split, and `δ` is the rounding charged against the split.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4, RESULT.json fields complete_cost.strictification and complete_cost.compiler.

/-
PR #6453: the strictification and compiler data.
-/
import Definitions.Def_Pr6453_RankMoments

set_option autoImplicit false

namespace Pr6453

noncomputable section

/-! ## The strictification data -/

/-- The tested saving `3287019/10⁹`, `complete_cost.tested`. -/
def tested : ℚ := 3287019 / 1000000000

/-- The block length `1920`, `strictification.power`. -/
def power : ℕ := 1920

/-- The split `12`, `strictification.cutoff`. -/
def cutoff : ℕ := 12

/-- The rounding `13`, `strictification.floor`. -/
def floor' : ℕ := 13

/-- The absorbed reserve `10⁻²⁹`, `strictification.reserve`. -/
def reserve : ℚ := 1 / 10 ^ 29

/-- The per-block decay `31/32`, `strictification.tail_decay`. -/
def decay : ℚ := 31 / 32

/-- The complementary capacity `63/64`, `compiler.theta`. -/
def theta : ℚ := 63 / 64

/-- The logarithmic power `2100`, `compiler.logarithm_power`. -/
def logarithmPower : ℕ := 2100

/-- The compiler grid size `138 100 200 000 000`, `compiler.H`. -/
def H : ℕ := 138100200000000

/-- The integer test exponent `98 643`, `compiler.integer_test_exponent`. -/
def integerTestExponent : ℕ := 98643

/-- The lower end of the certified `η`, `compiler.eta.lower`. -/
def etaLower : ℚ := 22804016729341566 / 10 ^ 30

end
end Pr6453


