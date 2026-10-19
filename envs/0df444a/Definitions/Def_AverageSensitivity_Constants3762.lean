-- Prove2me | Definitions.Def_AverageSensitivity_Constants3762
-- name    : AverageSensitivity_Constants3762
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-16T12:49:46.199116+00:00
-- url     : https://prove2.me/theorems/633e949d-87e1-4269-ae40-5c3637827542
-- title:
--   Exact symmetric-binomial absolute moments and central coefficients
-- statement:
--   For a nonnegative integer n, rawMAD(n) is the unnormalised first absolute moment of the symmetric random walk: the sum of binomial(n,j) times |2j-n|. The normalised binomial mean absolute deviation is mad(n)=rawMAD(n)/(2*2^n). For k>=0, central(k)=binomial(2k,k)/4^k. These are finite-sum definitions; no estimates or conjectures are assumed.
-- source:
--   https://github.com/Anchen0823/average-sensitivity-lean/blob/main/AverageSensitivity/BinomialMAD.lean

import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

open scoped BigOperators
namespace AverageSensitivity

noncomputable def rawMAD (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ)*|2*(j:ℝ)-(n:ℝ)|

noncomputable def central (k : ℕ) : ℝ := (Nat.centralBinom k:ℝ)/(4:ℝ)^k

noncomputable def mad (n : ℕ) : ℝ := rawMAD n/(2*(2:ℝ)^n)

end AverageSensitivity


