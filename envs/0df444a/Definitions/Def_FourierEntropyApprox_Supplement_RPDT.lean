-- Prove2me | Definitions.Def_FourierEntropyApprox_Supplement_RPDT
-- name    : FourierEntropyApprox_Supplement_RPDT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:04:15.932081+00:00
-- url     : https://prove2.me/theorems/da4e8570-8377-4b19-a2cb-ff794f7ef567
-- title:
--   Parity decision trees, randomized parity decision trees and $R^{\oplus}(f)$
-- statement:
--   A **parity decision tree** on $n$ variables is a rooted binary tree whose internal nodes are labelled by subsets $S\subseteq[n]$ and whose leaves are labelled by outputs in $\{-1,1\}$. On input $x\in\{-1,1\}^n$ it evaluates the parity $\chi_S(x)=\prod_{i\in S}x_i$ at a node labelled $S$, moves to the child for that value, and outputs the label of the leaf it reaches. Its **depth** is the length of its longest root-to-leaf path.
--
--   A **randomized parity decision tree** is a probability distribution $\mu$ over deterministic parity decision trees $T_1,\dots,T_k$. Its **complexity** is the largest depth of a tree $T_i$ with $\mu(T_i)>0$. It **computes $f$ with bounded error** if for every input $x$,
--
--   $$\Pr_{T\sim\mu}[T(x)=f(x)]\ge\tfrac23 .$$
--
--   The **randomized parity-decision-tree complexity** $R^{\oplus}(f)$ is the least complexity of a randomized parity decision tree that computes $f$ with bounded error.
--
--   $R^{\oplus}$ is the query measure of Theorem 3.3; restricting every query to a single coordinate gives ordinary randomized decision trees.
--
--   **Formalization Note** `PDT n` is an inductive tree type; a leaf output $\pm1$ is coded by the base `spin` (`true` = $-1$); at a node the first subtree is followed when $\chi_S(x)=1$. A randomized tree is a finite family of trees with probability weights: there are finitely many trees of bounded depth, so finite support loses nothing. `Rparity f` is the infimum of the achievable complexities over the natural numbers; for Boolean $f$ the set is nonempty (the tree that queries every coordinate), so this is the paper's minimum.
-- source:
--   Paraashar, Saurabh, Fourier Entropy Bounds via Approximations, arXiv:2611.06451 (held version, sha256 adc9c5fc…), §2, pp.12–13 (parity-decision trees, randomized decision trees, R⊕(f))

import Mathlib
import Definitions.Def_FourierEntropyApprox_Cube

set_option autoImplicit false

namespace FourierEntropyApprox

/-!
# Parity decision trees and randomized parity decision trees

M. Paraashar, N. Saurabh, *Fourier Entropy Bounds via Approximations*, arXiv:2611.06451 (held version,
sha256 adc9c5fc…), §2, pp.12–13: "A parity-decision tree for f is similar to a deterministic decision tree,
except that each node in the tree is labelled by a subset S ⊆ [n]. On input x ∈ {−1, 1}ⁿ, the tree proceeds at
a node with label S by evaluating the parity of the bits xᵢ for i ∈ S and continues with the subtree
corresponding to the value of ⊕_{i∈S} xᵢ." "A randomized decision tree for f is a probability distribution µ
over deterministic decision trees for f. … The complexity of the randomized tree is the largest depth among all
deterministic trees with non-zero probability of being sampled according to µ. One can similarly define a
randomized parity-decision tree … We say that a randomized decision tree computes f with bounded-error if for
all x ∈ {−1, 1}ⁿ its output equals f(x) with probability at least 2/3. … R⊕(f) denotes the complexity of the
optimal randomized … parity decision tree that computes f with bounded-error".

**Formalization Note.**
* `PDT n` is a binary tree: a leaf carries an output `±1`, coded as `Bool` by the base `spin`
  (`true ↦ −1`); an internal node carries a subset `S` and two subtrees, followed when `χ_S(x) = 1` and
  `χ_S(x) = −1` respectively (`χ_S(x) = ∏_{i∈S} xᵢ` is the parity of the bits in `S`). Depth of a leaf is `0`.
* A randomized parity decision tree is a finite family of deterministic trees `T₁, …, T_k` with probability
  weights `µᵢ ≥ 0`, `∑ µᵢ = 1`. Finite support loses nothing: there are finitely many trees of bounded depth,
  and a distribution of finite complexity is supported on trees of bounded depth.
* Its complexity is the largest depth of a tree with `µᵢ > 0` (worst case, not expected depth).
* It computes `f` with bounded error if, for every `x`, the total weight of the trees whose output equals
  `f(x)` is at least `2/3`.
-/

namespace Supplement

/-- A (deterministic) parity decision tree on `n` variables (pp.12–13). -/
inductive PDT (n : ℕ) : Type
  /-- a leaf with output `spin b` (`true ↦ −1`, `false ↦ 1`) -/
  | leaf (b : Bool) : PDT n
  /-- a node querying `χ_S`; `tPos` is followed when `χ_S(x) = 1`, `tNeg` when `χ_S(x) = −1` -/
  | node (S : Finset (Fin n)) (tPos tNeg : PDT n) : PDT n

namespace PDT

/-- The output in `{−1, 1}` of a parity decision tree on input `x`. -/
noncomputable def eval {n : ℕ} : PDT n → Cube n → ℝ
  | leaf b, _ => spin b
  | node S tPos tNeg, x => if walsh S x = 1 then eval tPos x else eval tNeg x

/-- The depth: the length of the longest root-to-leaf path. -/
def depth {n : ℕ} : PDT n → ℕ
  | leaf _ => 0
  | node _ tPos tNeg => max (depth tPos) (depth tNeg) + 1

end PDT

/-- A randomized parity decision tree (p.13): a probability distribution `µ` over finitely many
deterministic parity decision trees. -/
structure RPDT (n : ℕ) where
  /-- number of trees in the support list -/
  k : ℕ
  /-- the deterministic trees -/
  tree : Fin k → PDT n
  /-- their probabilities -/
  μ : Fin k → ℝ
  /-- probabilities are nonnegative -/
  μ_nonneg : ∀ i, 0 ≤ μ i
  /-- probabilities sum to one -/
  μ_sum : ∑ i, μ i = 1

namespace RPDT

/-- The complexity: the largest depth among the trees sampled with nonzero probability (p.13). -/
noncomputable def complexity {n : ℕ} (T : RPDT n) : ℕ :=
  (Finset.univ.filter fun i => 0 < T.μ i).sup fun i => (T.tree i).depth

/-- The probability that the randomized tree outputs `f x` on input `x`. -/
noncomputable def successProb {n : ℕ} (T : RPDT n) (f : Cube n → ℝ) (x : Cube n) : ℝ :=
  ∑ i, if (T.tree i).eval x = f x then T.μ i else 0

/-- `T` computes `f` with bounded error: on every input it outputs `f(x)` with probability at least
`2/3`, i.e. errs with probability at most `1/3` (p.13). -/
def ComputesBoundedError {n : ℕ} (T : RPDT n) (f : Cube n → ℝ) : Prop :=
  ∀ x, 2 / 3 ≤ T.successProb f x

end RPDT

/-- The bounded-error randomized parity-decision-tree complexity `R⊕(f)` (p.13): the least complexity of a
randomized parity decision tree computing `f` with error at most `1/3` on every input. For Boolean `f` the set
is nonempty (the depth-`n` tree querying every single coordinate); `sInf ∅ = 0` is never used. -/
noncomputable def Rparity {n : ℕ} (f : Cube n → ℝ) : ℕ :=
  sInf {d : ℕ | ∃ T : RPDT n, T.ComputesBoundedError f ∧ T.complexity = d}

end Supplement

end FourierEntropyApprox


