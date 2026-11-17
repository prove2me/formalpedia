-- Prove2me | Definitions.Def_SparseHistComm_Supplement_algorithm1Returns
-- name    : SparseHistComm_Supplement_algorithm1Returns
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:41:42.369207+00:00
-- url     : https://prove2.me/theorems/1cb6fa4d-8421-4116-9761-c995c535974b
-- title:
--   Exact return relation for Algorithm 1
-- statement:
--   This predicate formalizes the three branches of Algorithm 1. It sets
--
--   $$
--   t=nk-\lfloor nD\rfloor,\quad h=\min\{k,t\},\quad
--   L=\left\lceil\log_2\frac{8}{\varepsilon\delta}\right\rceil,\quad
--   B=\frac{4t+8\lceil\log_2(2/\delta)\rceil}{\delta}.
--   $$
--
--   If $t\ge64L/\varepsilon^2$, it returns the printed binomial law, mixed with erasure with probability $(1-\delta)/(1-\varepsilon\delta/8)$. Otherwise it enumerates exactly the two printed probability grids, according as $n\le B+\varepsilon(1-\delta)t/2$ or not, and returns a minimum-cost feasible convex combination of at most two enumerated laws.
--
--   **Formalization Note** Probability laws are points of the standard simplex. Minimization over feasible two-law mixtures is equivalent to choosing the minimum-cost feasible point on the lower convex hull, while leaving the paper's unspecified tie-breaking open.
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Algorithm 1, p.11; proof of Theorem 6, pp.22–25

import Mathlib
import Definitions.Def_SparseHistComm_threshold
import Definitions.Def_SparseHistComm_levelSucc
import Definitions.Def_SparseHistComm_levelMean
import Definitions.Def_SparseHistComm_Supplement_Algorithm1Output

namespace SparseHistComm

namespace Supplement

/-- `algorithm1Returns n k D δ ε out` says that `out` is a possible result of the exact
three-branch procedure printed as Algorithm 1 (Ye–Fan, *Optimal Communication for Distributed
Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), p.11;
proof on pp.22–25).

The definition preserves `t = nk - ⌊nD⌋`, `h = min{k,t}`, `L = ⌈log₂(8/(εδ))⌉`,
`B = (4t + 8⌈log₂(2/δ)⌉)/δ`, the threshold `t ≥ 64L/ε²`, the binomial-and-erasure
mixture in the large-`t` branch, both printed finite probability grids in the small-`t` branch,
and the minimum-cost feasible convex combination of at most two enumerated laws.

**Formalization Note** A probability law is a point of Mathlib's standard simplex. In the small
branch the phrase "minimum cost feasible point on the lower convex hull" is written equivalently as
minimal cost among every feasible convex combination of two candidate laws. Ties are not resolved,
matching the pseudocode. `Nat.ceil` implements every printed ceiling. -/
def algorithm1Returns (n k : ℕ) (D δ ε : ℝ) (out : Algorithm1Output k) : Prop :=
  let tZ := threshold n k D
  let t : ℝ := tZ
  let h : ℕ := min k tZ.toNat
  let L : ℕ := ⌈Real.logb 2 (8 / (ε * δ))⌉₊
  let B : ℝ := (4 * t + 8 * (⌈Real.logb 2 (2 / δ)⌉₊ : ℝ)) / δ
  let mixSucc := fun (w : ℝ) (p q : stdSimplex ℝ (Fin (k + 1))) =>
    w * levelSucc n k D p + (1 - w) * levelSucc n k D q
  let mixCost := fun (w : ℝ) (p q : stdSimplex ℝ (Fin (k + 1))) =>
    (n : ℝ) * (w * levelMean k p + (1 - w) * levelMean k q)
  if 64 * (L : ℝ) / ε ^ 2 ≤ t then
    let p : ℝ := min 1 ((t + 2 * L + 2 * ⌈Real.sqrt (t * L)⌉₊) / ((n : ℝ) * k))
    out.weight = (1 - δ) / (1 - ε * δ / 8) ∧
      0 ≤ out.weight ∧ out.weight ≤ 1 ∧
      (∀ j, out.first j = (Nat.choose k j : ℝ) * p ^ (j : ℕ) *
        (1 - p) ^ (k - (j : ℕ))) ∧
      (∀ j, out.second j = if (j : ℕ) = 0 then 1 else 0) ∧
      out.hatLambda = mixCost out.weight out.first out.second
  else
    let m : ℕ := ⌈(n : ℝ) * h / (ε * (1 - δ) * t)⌉₊
    let ρ : ℝ := ε * (1 - δ) * t / (h * (h + 1))
    let smallN : Prop := (n : ℝ) ≤ B + ε * (1 - δ) * t / 2
    let candidate := fun p : stdSimplex ℝ (Fin (k + 1)) =>
      (∀ j : Fin (k + 1), h < (j : ℕ) → p j = 0) ∧
      if smallN then
        ∀ j : Fin (k + 1), (j : ℕ) ≤ h → ∃ a : ℕ, (m : ℝ) * p j = a
      else
        (∀ j : Fin (k + 1), 1 ≤ (j : ℕ) → (j : ℕ) ≤ h →
          ∃ a : ℕ, a ≤ 1 + ⌈B / ρ⌉₊ ∧ p j = (a : ℝ) * ρ / n) ∧
        p ⟨0, Nat.zero_lt_succ k⟩ =
          1 - ∑ j : Fin (k + 1), if (j : ℕ) = 0 then 0 else p j
    candidate out.first ∧ candidate out.second ∧
      0 ≤ out.weight ∧ out.weight ≤ 1 ∧
      1 - δ ≤ mixSucc out.weight out.first out.second ∧
      out.hatLambda = mixCost out.weight out.first out.second ∧
      ∀ (w : ℝ) (p q : stdSimplex ℝ (Fin (k + 1))),
        candidate p → candidate q → 0 ≤ w → w ≤ 1 →
        1 - δ ≤ mixSucc w p q → out.hatLambda ≤ mixCost w p q

end Supplement

end SparseHistComm


