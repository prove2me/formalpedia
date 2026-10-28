-- Prove2me | Definitions.Def_TaoFivePrimes_SineBinData65k
-- name    : TaoFivePrimes_SineBinData65k
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:46:51.155711+00:00
-- url     : https://prove2.me/theorems/07d57256-475d-4808-9eee-b7e69db90b15
-- title:
--   Rational sine-square enclosure data for 65,000-height bins
-- statement:
--   For each integer $0\le n<180$, this table stores a nonnegative integer $b_n$. Its intended use is to bound $\sin^2 x$ by $b_n/10000$ on the interval
--
--   $$
--   \frac{65000+1290n}{4302}\le x\le\frac{65000+1290(n+1)}{4298}.
--   $$
--
--   The table is split into groups of twelve for efficient exact checking. For indices outside the table the function returns $10000$. The definition records data only; the interval enclosures are separate theorems.
-- source:
--   Exact outward-rounded interval data generated for the Tao five-primes Chebyshev-error reduction; based on the elementary sine-square interval enclosure and rational bounds on pi.

import Mathlib.Data.Nat.Basic

namespace TaoFivePrimes

/-- Outward-rounded upper bounds for sine squared in the 65,000-height bins. -/
def sineBinNumerator65k (i : ℕ) : ℕ :=
  match i / 12 with
  | 0 => ([3398, 1772, 1823, 3534, 6313, 10000, 10000, 10000, 10000, 7571, 4619, 2368] : List ℕ).getD (i % 12) 10000
  | 1 => ([1591, 2560, 4939, 7910, 10000, 10000, 10000, 10000, 6000, 3300, 1757, 1907] : List ℕ).getD (i % 12) 10000
  | 2 => ([3699, 6511, 10000, 10000, 10000, 10000, 7433, 4495, 2309, 1629, 2691, 5128] : List ℕ).getD (i % 12) 10000
  | 3 => ([8103, 10000, 10000, 10000, 10000, 5862, 3204, 1748, 1997, 3866, 6710, 10000] : List ℕ).getD (i % 12) 10000
  | 4 => ([10000, 10000, 10000, 7295, 4373, 2255, 1672, 2827, 5319, 8295, 10000, 10000] : List ℕ).getD (i % 12) 10000
  | 5 => ([10000, 8686, 5725, 3113, 1744, 2092, 4037, 6908, 10000, 10000, 10000, 10000] : List ℕ).getD (i % 12) 10000
  | 6 => ([7156, 4254, 2207, 1721, 2967, 5511, 8485, 10000, 10000, 10000, 8558, 5589] : List ℕ).getD (i % 12) 10000
  | 7 => ([3026, 1745, 2192, 4211, 7107, 10000, 10000, 10000, 10000, 7016, 4137, 2163] : List ℕ).getD (i % 12) 10000
  | 8 => ([1776, 3111, 5705, 8673, 10000, 10000, 10000, 8427, 5454, 2943, 1752, 2297] : List ℕ).getD (i % 12) 10000
  | 9 => ([4388, 7305, 10000, 10000, 10000, 10000, 6876, 4024, 2125, 1836, 3259, 5900] : List ℕ).getD (i % 12) 10000
  | 10 => ([10000, 10000, 10000, 10000, 8295, 5321, 2864, 1765, 2407, 4568, 7502, 10000] : List ℕ).getD (i % 12) 10000
  | 11 => ([10000, 10000, 10000, 6736, 3913, 2091, 1902, 3411, 6096, 10000, 10000, 10000] : List ℕ).getD (i % 12) 10000
  | 12 => ([10000, 8161, 5190, 2790, 1784, 2523, 4750, 7699, 10000, 10000, 10000, 10000] : List ℕ).getD (i % 12) 10000
  | 13 => ([6597, 3806, 2063, 1973, 3567, 6293, 10000, 10000, 10000, 10000, 8026, 5061] : List ℕ).getD (i % 12) 10000
  | 14 => ([2720, 1808, 2642, 4934, 7895, 10000, 10000, 10000, 10000, 6457, 3702, 2041] : List ℕ).getD (i % 12) 10000
  | _ => 10000

end TaoFivePrimes


