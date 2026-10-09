-- Prove2me | Definitions.Def_RamanujanNotebooks_ch06_ch06PeriodicBernoulli
-- name    : RamanujanNotebooks_ch06_ch06PeriodicBernoulli
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T22:12:40.73677+00:00
-- url     : https://prove2.me/theorems/3e6717dd-1a51-46eb-ba67-ae52cea8dc38
-- title:
--   Ramanujan's Notebooks, Part I, Ch. 6: ch06PeriodicBernoulli
-- statement:
--   The periodic Bernoulli function `P_n(t) = B_n(t - [t]) / n!` of the Introduction, p. 13,
--   where `B_n` is the `n`-th Bernoulli polynomial (Mathlib `bernoulliFun`) and `[t]` the integer
--   part, so `t - [t] = Int.fract t`.
--   Domain: every `n : ℕ` and every real `t`; a bounded function of period `1`; no junk value.
--   Reference: `P_1(t) = (t - [t]) - 1/2`, `P_2(0) = 1/12`, `P_3(1/4) = 1/128`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 6.

import Mathlib

namespace RamanujanNotebooks

/-- The periodic Bernoulli function `P_n(t) = B_n(t - [t]) / n!` of the Introduction, p. 13,
where `B_n` is the `n`-th Bernoulli polynomial (Mathlib `bernoulliFun`) and `[t]` the integer
part, so `t - [t] = Int.fract t`.
Domain: every `n : ℕ` and every real `t`; a bounded function of period `1`; no junk value.
Reference: `P_1(t) = (t - [t]) - 1/2`, `P_2(0) = 1/12`, `P_3(1/4) = 1/128`. -/
noncomputable def ch06PeriodicBernoulli (n : ℕ) (t : ℝ) : ℝ :=
  bernoulliFun n (Int.fract t) / (n.factorial : ℝ)

end RamanujanNotebooks


