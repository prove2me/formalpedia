-- Prove2me | Definitions.Def_AggCG_Supplement_stopCost
-- name    : AggCG_Supplement_stopCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:25:30.53658+00:00
-- url     : https://prove2.me/theorems/f315aead-e81e-48f9-b10d-2c7b17e84705
-- title:
--   Capped gradient-norm stopping cost
-- statement:
--   The capped stopping cost is the first iteration $t\le H$ at which the gradient norm is strictly below the threshold, and is $H$ when no such check succeeds. A success at the horizon and nonconvergence therefore have the same cost.
-- source:
--   Sharma, STOC 2027 submission (manuscript sha256 f7ea0248…), §L, p.64, PDF p.65

import Mathlib

namespace AggCG.Supplement

open Classical in
/-- The capped gradient-norm stopping cost (Sharma, *Computational Complexity of Data-Driven
Configuration for Integer Programming, Clustering, and Learning Algorithms*, STOC 2027 submission
(manuscript sha256 f7ea0248…), §L, p.64, PDF p.65): for gradient norms `g t = ‖∇f(x_t)‖`, the first
`t ≤ H` with `g t < ϑ` (strict), and `H` if there is none ("a successful check at x_t has cost t … and the
nonconvergence cost is H").

**Formalization Note** A first success exactly at `t = H` also costs `H`, which agrees with the
nonconvergence cost. The normalized cost of the theorems is this value divided by `H`. -/
noncomputable def stopCost (g : ℕ → ℝ) (ϑ : ℝ) (H : ℕ) : ℕ :=
  if h : ∃ t, t ≤ H ∧ g t < ϑ then Nat.find h else H

end AggCG.Supplement


