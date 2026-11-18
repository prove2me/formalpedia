-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_LinearConstructors
-- name    : RealPinwheel_FiveSixths_LinearConstructors
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:40:03.834932+00:00
-- url     : https://prove2.me/theorems/4dd2e142-8879-472c-a24c-e280238ba67f
-- title:
--   Finite vectors of linear combinations
-- statement:
--   This finite-list lookup builds a vector of integer linear combinations for the exact coverage checker.
--
--   $$i\longmapsto c_i.$$
--
--   Out-of-range lookup uses a fixed default. The checker validates all coordinate identities separately, so this constructor introduces no mathematical assumption.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Data representation for exact linear certificate verification.

import Definitions.Def_RealPinwheel_FiveSixths_LinearCertificate
namespace RealPinwheel.FiveSixths
/-- A finite vector of integer linear combinations, with an unused default. -/
def combinationVector {n : ℕ} (xs : List LinearCombination) (i : Fin n) : LinearCombination :=
  xs[i.val]?.getD ⟨1, []⟩
end RealPinwheel.FiveSixths


