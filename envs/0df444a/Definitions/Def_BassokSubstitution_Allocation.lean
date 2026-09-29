-- Prove2me | Definitions.Def_BassokSubstitution_Allocation
-- name    : BassokSubstitution_Allocation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T08:09:57.70682+00:00
-- url     : https://prove2.me/theorems/696f9ff9-2853-4272-a901-bc52c8ea0372
-- title:
--   Allocation LP (3), its value $G(y,d)$, Allocation Algorithm (A) and subproblem shortages $S^i_j$
-- statement:
--   Fix stock levels $y \in \mathbb R^N$ (after ordering) and realized demands $d \in \mathbb R^N$. An **allocation** consists of quantities $w_{ji}$ of product $j$ allocated to class $i$, shortages $u_i$ of class $i$, and leftovers $v_j$ of product $j$. It is **feasible** for the allocation linear program (3) when
--   $$u_i + \sum_{j=1}^{i} w_{ji} = d_i,\qquad v_j + \sum_{i=1}^{N} w_{ji} = y_j,\qquad w_{ji} \ge 0,\ u_i \ge 0,\ v_j \ge 0,$$
--   and $w_{ji} = 0$ whenever $i < j$ (a product cannot be used for a more flexible class). Its **objective** is
--   $$\sum_{i=1}^N \sum_{j=1}^{i} a_{ji} w_{ji} + \sum_{i=1}^N s_i v_i - \sum_{i=1}^N \pi_i u_i,$$
--   and $G(y,d)$ is the supremum of the objective over feasible allocations, i.e. the optimal value of (3).
--
--   **Allocation Algorithm (A)** (Figure 1 of the paper) processes the classes $i = 1, 2, \dots, N$ in order. For class $i$ it sets $u_i = d_i$ and then, for $j = i, i-1, \dots, 1$, allocates $w_{ji} = \min(u_i, v_j)$ units of the remaining stock $v_j$ of product $j$ and subtracts this amount from $u_i$ and $v_j$. Thus class $i$ is served first from its own product and then from the leftovers of the more flexible products, the closest first.
--
--   For $k \le j$, the **subproblem shortage** $S^k_j$ is the unmet demand of class $j$ when Algorithm (A) is run on the classes $k, \dots, j$ with the products $k, \dots, j$ only (the paper's "subproblem with only products $k, \dots, j$"). For a first product $k$ and a range of classes $a, \dots, n$, the vector condition $\vec S^k_{a,n} = 0$ means $S^k_m = 0$ for every $a \le m \le n$; it holds vacuously when the range is empty. Since shortages are nonnegative, the paper's $\vec S^k_{a,n} > 0$ is its negation.
--
--   These objects carry the paper's whole analysis: $G$ is the second-stage profit, and the shortages $S^k_j$ are the random quantities in terms of which the first partial derivatives of the expected profit are written.
--
--   **Formalization Note.** Indices are 0-based (`Fin N`). The algorithm is implemented on `ℕ`-indexed arrays (`innerLoop`, `runFrom`, with vectors extended by `0` outside `Fin N`); `runFrom k y d n` is the state after classes $k,\dots,k+n-1$ of the subproblem starting at product $k$. The paper's loop guard "$u_i > 0$" is dropped: once $u_i = 0$ every further step allocates $\min(0, v_j) = 0$ units and changes nothing. In (3c) the paper sums over all classes; the upward arcs are forbidden arcs ("arcs with negative infinity costs", proof of Proposition 1), encoded as $w_{ji} = 0$ for $i < j$. `shortage y d k j` takes the first product `k` as a natural number and returns the junk value `0` when $j < k$ (never used). `G` is an `sSup`; for $y, d \ge 0$ the feasible set is nonempty and the objective is bounded above on it, so the supremum is the LP optimum.
-- source:
--   Bassok, Anupindi, Akella, Single-Period Multiproduct Inventory Models with Substitution, Operations Research 47(4):632–642 (1999), p. 634, Eq. (3a)–(3e), Figure 1 (Allocation Algorithm (A)), §2.3 (definition of S^i_j and of the vector S^i_{j,n}), pp. 634–635 (vector sign convention)

import Mathlib
import Definitions.Def_BassokSubstitution_Model

namespace BassokSubstitution

variable {N : ℕ}

/-- A candidate solution of the allocation linear program (3): `w j i` is the quantity of
product `j` allocated to demand class `i`, `u i` the shortage of class `i`, `v j` the leftover
stock of product `j`. -/
structure Allocation (N : ℕ) where
  w : Fin N → Fin N → ℝ
  u : Fin N → ℝ
  v : Fin N → ℝ

/-- Feasibility for the allocation LP (3b)–(3e) at stock `y` and demand `d`. Upward allocations
(product `j` to a class `i < j`) are forbidden arcs and are fixed to `0`. -/
def Allocation.Feasible (y d : Fin N → ℝ) (a : Allocation N) : Prop :=
  (∀ j i : Fin N, i < j → a.w j i = 0) ∧
  (∀ j i : Fin N, 0 ≤ a.w j i) ∧
  (∀ i : Fin N, 0 ≤ a.u i) ∧
  (∀ j : Fin N, 0 ≤ a.v j) ∧
  (∀ i : Fin N, a.u i + ∑ j ∈ Finset.Iic i, a.w j i = d i) ∧
  (∀ j : Fin N, a.v j + ∑ i, a.w j i = y j)

/-- Objective (3a): `∑_i ∑_{j ≤ i} a_{ji} w_{ji} + ∑_i s_i v_i - ∑_i π_i u_i`. -/
def Model.allocObjective (M : Model N) (a : Allocation N) : ℝ :=
  (∑ i, ∑ j ∈ Finset.Iic i, M.netRevenue j i * a.w j i) + (∑ i, M.s i * a.v i)
    - ∑ i, M.penalty i * a.u i

/-- `G(y, d)`: the optimal value of the allocation LP (3), i.e. the supremum of the objective
over all feasible allocations. -/
noncomputable def Model.G (M : Model N) (y d : Fin N → ℝ) : ℝ :=
  sSup (M.allocObjective '' {a : Allocation N | a.Feasible y d})

/-- Working state of Allocation Algorithm (A), on `ℕ`-indexed arrays: remaining stock `v`,
unmet demand `u`, and allocations `w j i` (product `j` to class `i`). -/
structure AlgState where
  v : ℕ → ℝ
  u : ℕ → ℝ
  w : ℕ → ℕ → ℝ

/-- The inner `While` loop of Algorithm (A) for class `i`, run for `n` steps starting at
product `j`: set `w_{ji} = min(u_i, v_j)`, subtract it from `u_i` and `v_j`, and move on to
product `j - 1`. -/
def innerLoop (i : ℕ) : ℕ → ℕ → AlgState → AlgState
  | 0, _, st => st
  | n + 1, j, st =>
      innerLoop i n (j - 1)
        { v := Function.update st.v j (st.v j - min (st.u i) (st.v j))
          u := Function.update st.u i (st.u i - min (st.u i) (st.v j))
          w := Function.update st.w j (Function.update (st.w j) i (min (st.u i) (st.v j))) }

/-- Algorithm (A) restricted to the subproblem whose cheapest-to-most-flexible product range
starts at product `k`: the state after classes `k, k+1, …, k+n-1` have been processed, class
`i` drawing on products `i, i-1, …, k` in that order. Initially `v = y`, `u = 0`, `w = 0`;
at class `i` the algorithm sets `u_i = d_i` and runs the inner loop from product `i`. -/
def runFrom (k : ℕ) (y d : ℕ → ℝ) : ℕ → AlgState
  | 0 => { v := y, u := fun _ => 0, w := fun _ _ => 0 }
  | n + 1 =>
      let st := runFrom k y d n
      innerLoop (k + n) (n + 1) (k + n) { st with u := Function.update st.u (k + n) (d (k + n)) }

/-- Extend a vector on `Fin N` by `0` to all of `ℕ`. -/
def extend (f : Fin N → ℝ) : ℕ → ℝ :=
  fun n => if h : n < N then f ⟨n, h⟩ else 0

/-- The allocation produced by Algorithm (A) (Figure 1) on the full problem with stock `y`
and demand `d`: classes `1, …, N` are processed in order, class `i` served first from
product `i`, then from `i-1, …, 1`. -/
def greedyAllocation (y d : Fin N → ℝ) : Allocation N :=
  let st := runFrom 0 (extend y) (extend d) N
  { w := fun j i => st.w j.val i.val
    u := fun i => st.u i.val
    v := fun j => st.v j.val }

/-- The subproblem shortage `S^k_j` (paper's notation, with `k` the first product of the
subproblem): the unmet demand of class `j` when Algorithm (A) is run on classes `k, …, j`
using products `k, …, j` only. Both indices are 0-based; `k` is a natural number so that
`k + 1` needs no bound. Junk value `0` when `j < k` (never used). -/
def shortage (y d : Fin N → ℝ) (k : ℕ) (j : Fin N) : ℝ :=
  if k ≤ j.val then (runFrom k (extend y) (extend d) (j.val + 1 - k)).u j.val else 0

/-- The vector condition `S⃗^k_{a,n} = 0`: `S^k_m = 0` for every class `m` with
`a ≤ m ≤ n` (0-based). It holds vacuously when the range is empty. The paper's
`S⃗^k_{a,n} > 0` is its negation (shortages are nonnegative). -/
def ShortVecZero (y d : Fin N → ℝ) (k a n : ℕ) : Prop :=
  ∀ m : Fin N, a ≤ m.val → m.val ≤ n → shortage y d k m = 0

end BassokSubstitution


