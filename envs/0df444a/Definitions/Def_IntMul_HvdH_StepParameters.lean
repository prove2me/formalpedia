-- Prove2me | Definitions.Def_IntMul_HvdH_StepParameters
-- name    : IntMul_HvdH_StepParameters
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-09T14:32:48.019982+00:00
-- url     : https://prove2.me/theorems/fff904cc-d806-48a1-b9b8-1231b88578db
-- title:
--   Proposition 5.4 parameter constraints
-- statement:
--   Let $d,n,b,p,T,r$ be natural numbers. This predicate bundles exactly the parameter assumptions in Proposition 5.4:
--
--   $$n\ge 2^{d^{12}},\quad b=\lceil\log_2 n\rceil,\quad p=6b,$$
--   $$T=2^k,\quad 4n/b\le T<8n/b,$$
--   $$r=2^j,\quad T^{1/d}\le r<2T^{1/d},$$
--
--   for some natural numbers $k,j$. The condition $d\ge2$ is a separate hypothesis on the theorems using this predicate. Division and fractional powers use real numbers; $b$ is represented by `Nat.clog 2 n`.
-- source:
--   Supporting formalization of Harvey and van der Hoeven, Integer multiplication in time O(n log n), Annals of Mathematics 193(2) (2021), 563–617, DOI 10.4007/annals.2021.193.2.4; author preprint https://www.texmacs.org/joris/nlogn/nlogn.pdf, Proposition 5.4, printed pages 40–41. The clocked formulation is an explicit operational strengthening needed for the reduction, not a separately numbered theorem of the source.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log

/-- The parameter constraints in Harvey–van der Hoeven Proposition 5.4. -/
def IntMul.HvdH.StepParameters (d n b p T r : ℕ) : Prop :=
  2 ^ (d ^ 12) ≤ n ∧ b = Nat.clog 2 n ∧ p = 6 * b ∧
    (∃ k : ℕ, T = 2 ^ k) ∧ 4 * (n : ℝ) / b ≤ T ∧
    (T : ℝ) < 8 * (n : ℝ) / b ∧ (∃ j : ℕ, r = 2 ^ j) ∧
    (T : ℝ) ^ ((1 : ℝ) / d) ≤ r ∧
    (r : ℝ) < 2 * (T : ℝ) ^ ((1 : ℝ) / d)


