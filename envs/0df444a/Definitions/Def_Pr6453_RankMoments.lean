-- Prove2me | Definitions.Def_Pr6453_RankMoments
-- name    : Pr6453_RankMoments
-- status  : Definition
-- author  : @gustasmickus
-- created : 2026-11-08T15:47:36.526192+00:00
-- url     : https://prove2.me/theorems/13d61fca-9515-4ad7-a2cb-8305b64b1b4a
-- title:
--   PR #6453: rank histograms and rank moment of the third-anchor word
-- statement:
--   The two rank histograms of the integer-multiplication word of PR #6453 (`CrocSwap/integer-mult-bounds`, head `b1a3e525793eca35c56324aa7ffd0b714cf606d4`, `research/p104-third-anchor-clean-mixed-root/RESULT.json`): `targets`, the productive target fields by rank (total 13652, rank mass 185722), and `paid`, the paid calls by rank (total 67132, rank mass 184962). The rank moment of a histogram is $\sum_r n_r\, r^{\tau}$, the quantity the repository's pricing engine evaluates to decide the achievable exponent: the word realizes multiplication in time $O(n\,(\lg n)^{1-\kappa})$ for every $\kappa$ below the root of $\sum_r T_r r^{1-\kappa} = \sum_r P_r r^{1-\kappa}$. `kappa` is the claimed saving $1643507/500000000 = 0.003287014$, recorded exactly as `complete_cost.kappa`.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4, research/p104-third-anchor-clean-mixed-root/RESULT.json (fields complete_cost.targets, complete_cost.paid, complete_cost.kappa)

/-
# PR #6453: the rank histograms of the third-anchor word

Data extracted from the certificate published with PR #6453 of
`CrocSwap/integer-mult-bounds` (branch `third-anchor-clean-mixed-root`, head
`b1a3e525793eca35c56324aa7ffd0b714cf606d4`), file
`research/p104-third-anchor-clean-mixed-root/RESULT.json`,
fields `complete_cost.targets` (productive target fields, per rank) and
`complete_cost.paid` (paid calls, per rank).

The arithmetic of the claim is the moment inequality of the pricing engine
(`pricing.py`, `margin k = moment T (1-k) - moment P (1-k)`, with
`moment h τ = Σ_r n_r r^τ` from `research/higher-moment-strictification/verify.py`):
the word multiplies in time `O(n (lg n)^(1 - κ))` for every `κ` below the unique
root of `margin = 0`, and the claimed `κ = 0.003287014` lies below that root.
-/
import Mathlib

namespace Pr6453

/-- Productive target fields of the PR #6453 word, as `(rank, count)`.
`RESULT.json → complete_cost.targets`; total 13652, rank mass 185722. -/
def targets : List (ℕ × ℕ) :=
  [(1, 356), (2, 144), (3, 72), (4, 1926), (5, 270), (6, 54), (7, 162), (8, 702),
   (9, 6534), (17, 1872), (25, 416), (33, 416), (57, 416), (73, 208), (145, 104)]

/-- Paid calls of the PR #6453 word, as `(rank, count)`.
`RESULT.json → complete_cost.paid`; total 67132, rank mass 184962. -/
def paid : List (ℕ × ℕ) :=
  [(1, 42016), (2, 8154), (3, 8838), (4, 1962), (5, 2718), (6, 144), (7, 162), (8, 18),
   (16, 1872), (24, 416), (32, 416), (56, 416)]

/-- The rank moment `Σ n_r r^τ` of a histogram — `E.moment` of the certificate's
verifier `research/higher-moment-strictification/verify.py`, which evaluates
`r^τ` as `exp (τ log r)` in outward-rounded rational interval arithmetic. -/
noncomputable def moment (h : List (ℕ × ℕ)) (τ : ℝ) : ℝ :=
  (h.map fun p => (p.2 : ℝ) * ((p.1 : ℝ) ^ τ)).sum

/-- The claimed saving `κ = 0.003287014` of PR #6453, exactly
(`RESULT.json → complete_cost.kappa = "1643507/500000000"`). -/
def kappa : ℚ := 1643507 / 500000000

end Pr6453


