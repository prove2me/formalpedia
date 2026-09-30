-- Prove2me | Definitions.Def_MarkovChainChoice_DimReduction_Algorithm
-- name    : MarkovChainChoice_DimReduction_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T09:43:39.802549+00:00
-- url     : https://prove2.me/theorems/e1841a52-2fee-437b-9703-3c320a6466e8
-- title:
--   The Dimension Reduction algorithm: iterates $(x^k,z^k)$, subsets $S^k$, scalars $\alpha^k$ and weights $\gamma^k$
-- statement:
--   The **Dimension Reduction** algorithm takes a pair $(\hat x,\hat z)$ (in the paper, the optimal solution of the (Reduced) linear program) and runs as follows.
--
--   1. *Step 0.* Set $(x^1,z^1)=(\hat x,\hat z)$ and $k=1$.
--   2. *Step 1.* Set $S^k=\{j\in N: x^k_j>0\}$. If $S^k=\emptyset$, set $\alpha^k=1$ and stop.
--   3. *Step 2.* Set $\alpha^k=\min\{x^k_j/P_{j,S^k}: j\in S^k\}$. If $\alpha^k=1$, stop.
--   4. *Step 3.* Set, for all $j\in N$,
--   $$
--   x^{k+1}_j=\frac{x^k_j-\alpha^kP_{j,S^k}}{1-\alpha^k},\qquad z^{k+1}_j=\frac{z^k_j-\alpha^kR_{j,S^k}}{1-\alpha^k}.
--   $$
--   5. *Step 4.* Increase $k$ by one and go to Step 1.
--
--   This file defines the support $S_x=\{j: x_j>0\}$, the step size $\alpha$ of Steps 1–2 (equal to $1$ on an empty support), the update of Step 3, the sequence of iterates $(x^k,z^k)_{k\ge1}$, the sets $S^k$, the scalars $\alpha^k$, the stopping predicate "the algorithm stops at iteration $k$" ($S^k=\emptyset$ or $\alpha^k=1$), and the weights
--   $$
--   \gamma^k=(1-\alpha^1)\cdots(1-\alpha^{k-1})\,\alpha^k .
--   $$
--
--   **Formalization Note** Iterations are numbered from $k=1$ as in the paper; the value at index $0$ is an unused copy of the input. The iterates are defined for every $k$, but only iterates up to the first stopping iteration are meaningful: past it Step 3 would divide by $1-1=0$, which Lean evaluates to $0$. The minimum in Step 2 is `Finset.inf'` over the nonempty support; Step 1's case $S^k=\emptyset$ gives $\alpha^k=1$ exactly as printed.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1333, Section 7, Dimension Reduction algorithm (Steps 0–4); p. 1334, Theorem 9 (definition of γ^k)

import Mathlib
import Definitions.Def_MarkovChainChoice_Shared_Model
import Definitions.Def_MarkovChainChoice_Shared_Balance
open MarkovChainChoice.Shared

namespace MarkovChainChoice.DimReduction

/-- The support `S_x = {j ∈ N : x_j > 0}` (Step 1). -/
noncomputable def drSupp {n : ℕ} (x : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => 0 < x j)

/-- The step size of Steps 1–2: `α = 1` if `S_x = ∅` (Step 1), otherwise
`α = min {x_j / P_{j,S_x} : j ∈ S_x}` (Step 2). -/
noncomputable def drAlpha {n : ℕ} (M : Model n) (x : Fin n → ℝ) : ℝ :=
  if h : (drSupp x).Nonempty then
    (drSupp x).inf' h (fun j => x j / purchase M (drSupp x) j)
  else 1

/-- Step 3: with `S = S_x` and `α` as in `drAlpha`, the next iterate
`x'_j = (x_j − α P_{j,S}) / (1 − α)`, `z'_j = (z_j − α R_{j,S}) / (1 − α)`. -/
noncomputable def drNext {n : ℕ} (M : Model n) (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  (fun j => (p.1 j - drAlpha M p.1 * purchase M (drSupp p.1) j) / (1 - drAlpha M p.1),
   fun j => (p.2 j - drAlpha M p.1 * visitNot M (drSupp p.1) j) / (1 - drAlpha M p.1))

/-- The iterates `(x^k, z^k)` of the Dimension Reduction algorithm started at `(x̂, ẑ)`,
indexed from `k = 1` as in the paper: `(x^1, z^1) = (x̂, ẑ)` (Step 0) and
`(x^{k+1}, z^{k+1})` is Step 3 applied to `(x^k, z^k)`. The value at index `0` is an unused
copy of `(x̂, ẑ)`. -/
noncomputable def drIter {n : ℕ} (M : Model n) (x z : Fin n → ℝ) :
    ℕ → (Fin n → ℝ) × (Fin n → ℝ)
  | 0 => (x, z)
  | 1 => (x, z)
  | k + 2 => drNext M (drIter M x z (k + 1))

/-- `S^k = {j ∈ N : x^k_j > 0}`. -/
noncomputable def drS {n : ℕ} (M : Model n) (x z : Fin n → ℝ) (k : ℕ) : Finset (Fin n) :=
  drSupp (drIter M x z k).1

/-- `α^k`, the step size of Steps 1–2 at iteration `k`. -/
noncomputable def drA {n : ℕ} (M : Model n) (x z : Fin n → ℝ) (k : ℕ) : ℝ :=
  drAlpha M (drIter M x z k).1

/-- The algorithm stops at iteration `k` (in Step 1 or in Step 2): `S^k = ∅` or `α^k = 1`. -/
def drStops {n : ℕ} (M : Model n) (x z : Fin n → ℝ) (k : ℕ) : Prop :=
  drS M x z k = ∅ ∨ drA M x z k = 1

/-- `γ^k = (1 − α^1) ⋯ (1 − α^{k−1}) α^k` (Theorem 9). -/
noncomputable def drGamma {n : ℕ} (M : Model n) (x z : Fin n → ℝ) (k : ℕ) : ℝ :=
  (∏ l ∈ Finset.Ico 1 k, (1 - drA M x z l)) * drA M x z k

end MarkovChainChoice.DimReduction


