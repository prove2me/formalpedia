-- Prove2me | Definitions.Def_SmoothedNash_Supplement_alg3Depth
-- name    : SmoothedNash_Supplement_alg3Depth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:00:31.4088+00:00
-- url     : https://prove2.me/theorems/09bc4385-4490-4b21-8705-36c36afec0e5
-- title:
--   Depth $K = \lceil \log_2((1+L_1)/\varepsilon) \rceil$ of Algorithm 3
-- statement:
--   The number of levels of Algorithm 3 is
--   $$
--   K = \Bigl\lceil \log_2 \frac{1 + L_1}{\varepsilon} \Bigr\rceil .
--   $$
--   For $L_1 \ge 0$ and $0 < \varepsilon \le 1$ the logarithm is nonnegative.
--
--   **Formalization Note** The natural-number ceiling of the real base-2 logarithm.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Algorithm 3, line 1, p.21

import Mathlib
open MeasureTheory

namespace SmoothedNash.Supplement

/-- The depth `K = ⌈log₂((1 + L1)/ε)⌉` of Algorithm 3 (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), Algorithm 3, line 1, p.21).

**Formalization Note** `Nat.ceil` of `Real.logb 2 ((1 + L1)/ε)`. For `L1 ≥ 0` and `0 < ε ≤ 1` the
logarithm is nonnegative, so this is the paper's ceiling. -/
noncomputable def alg3Depth (L1 ε : ℝ) : ℕ :=
  ⌈Real.logb 2 ((1 + L1) / ε)⌉₊

end SmoothedNash.Supplement


