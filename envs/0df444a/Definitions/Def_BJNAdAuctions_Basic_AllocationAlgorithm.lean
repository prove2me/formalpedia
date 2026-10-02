-- Prove2me | Definitions.Def_BJNAdAuctions_Basic_AllocationAlgorithm
-- name    : BJNAdAuctions_Basic_AllocationAlgorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T16:26:11.736639+00:00
-- url     : https://prove2.me/theorems/b607bee8-21ee-418b-bb36-043013d40a83
-- title:
--   The primal-dual Allocation Algorithm for online ad-auctions
-- statement:
--   The **Allocation Algorithm** (Section 3) maintains a covering variable $x(i)$ for each buyer, initially $0$, together with the amount $\mathrm{spent}(i)$ charged to buyer $i$, the packing variables $y(i,j)$ and the covering variables $z(j)$, all initially $0$. It has a parameter $c$. When product $j$ arrives, it considers a buyer $i$ maximizing $b(i,j)\,(1 - x(i))$. If $x(i) \ge 1$ it does nothing (the product is not sold). Otherwise:
--
--   1. it charges buyer $i$ the amount $\min\{\, b(i,j),\ B(i) - \mathrm{spent}(i) \,\}$ and sets $y(i,j) \leftarrow 1$;
--   2. it sets $z(j) \leftarrow b(i,j)\,(1 - x(i))$;
--   3. it sets
--   $$
--   x(i) \leftarrow x(i)\Big(1 + \frac{b(i,j)}{B(i)}\Big) + \frac{b(i,j)}{(c-1)\,B(i)}.
--   $$
--
--   The choice among several maximizers is made by a **tie-breaking rule** $\mathrm{sel}$, a function that, given the current vector $x$ and the product $j$, returns a buyer; it is an **argmax rule** when $b(i,j)(1-x(i)) \le b(\mathrm{sel}(x,j),j)\,(1 - x(\mathrm{sel}(x,j)))$ for every $x$, $j$ and $i$. The step on product $j$ reads only the bids on product $j$, the budgets and the current state, so the algorithm is online.
--
--   The run after the first $k$ products is defined by recursion on $k$; the final state is the state after all $m$ products, and the **revenue** of the algorithm is $\sum_{i\in I} \mathrm{spent}(i)$ in the final state.
--
--   This definition fixes the object of Theorem 1: every claim of the mission is about the state this recursion computes from the instance, never about an arbitrary allocation.
--
--   **Formalization Note** `step` applies one iteration; `runPrefix inst c sel k` is the state after products $0, \dots, k-1$ of `Fin m` (constant for $k \ge m$); `run` is `runPrefix … m`; `revenue` sums `spent`. `IsArgmaxRule inst sel` is the argmax property of `sel`, required at every covering vector. The charge in step 1 is tracked separately from $y$, which is set to $1$ even when the charge is less than the bid, as the paper stresses (p. 7).
-- source:
--   Buchbinder, Jain & Naor, Online Primal-Dual Algorithms for Maximizing Ad-Auctions Revenue, ESA 2007, DOI 10.1007/978-3-540-75520-3_24, p. 6, Section 3, Allocation Algorithm (boxed)

import Mathlib
import Definitions.Def_BJNAdAuctions_Basic_Instance

namespace BJNAdAuctions.Basic

variable {I : Type*} [Fintype I] {m : ℕ}

/-- The state of the Allocation Algorithm (§3, p. 6) between two arrivals: the covering
variables `x`, the amount `spent i` charged to each buyer so far, the packing variables `y`
and the covering variables `z`. -/
structure State (I : Type*) (m : ℕ) where
  x : I → ℝ
  spent : I → ℝ
  y : I → Fin m → ℝ
  z : Fin m → ℝ

/-- Initially `x(i) = 0` for every buyer; nothing has been charged or allocated. -/
def State.init : State I m where
  x := fun _ => 0
  spent := fun _ => 0
  y := fun _ _ => 0
  z := fun _ => 0

/-- A tie-breaking rule for the Allocation Algorithm: `sel x j` is a buyer maximizing
`b(i, j) (1 - x(i))` for the current covering vector `x`. -/
def IsArgmaxRule (inst : Instance I m) (sel : (I → ℝ) → Fin m → I) : Prop :=
  ∀ (x : I → ℝ) (j : Fin m) (i : I),
    inst.b i j * (1 - x i) ≤ inst.b (sel x j) j * (1 - x (sel x j))

open Classical in
/-- One iteration of the Allocation Algorithm (§3, p. 6) on the arrival of product `j`.
The product goes to `i := sel s.x j`. If `x(i) ≥ 1` nothing happens. Otherwise
1. buyer `i` is charged `min (b(i, j)) (B(i) - spent(i))` and `y(i, j) ← 1`;
2. `z(j) ← b(i, j) (1 - x(i))`;
3. `x(i) ← x(i) (1 + b(i, j)/B(i)) + b(i, j)/((c - 1) B(i))`.
Only column `j` of the bids is read. -/
noncomputable def step (inst : Instance I m) (c : ℝ) (sel : (I → ℝ) → Fin m → I)
    (s : State I m) (j : Fin m) : State I m :=
  let i := sel s.x j
  if 1 ≤ s.x i then s else
    { x := Function.update s.x i
        (s.x i * (1 + inst.b i j / inst.B i) + inst.b i j / ((c - 1) * inst.B i))
      spent := Function.update s.spent i
        (s.spent i + min (inst.b i j) (inst.B i - s.spent i))
      y := Function.update s.y i (Function.update (s.y i) j 1)
      z := Function.update s.z j (inst.b i j * (1 - s.x i)) }

/-- The state of the Allocation Algorithm with parameter `c` and tie-breaking rule `sel`
after the first `k` products `0, …, k - 1` have been processed (for `k ≥ m`, after all). -/
noncomputable def runPrefix (inst : Instance I m) (c : ℝ) (sel : (I → ℝ) → Fin m → I) :
    ℕ → State I m
  | 0 => State.init
  | k + 1 =>
    if h : k < m then step inst c sel (runPrefix inst c sel k) ⟨k, h⟩
    else runPrefix inst c sel k

/-- The final state of the Allocation Algorithm, after all `m` products. -/
noncomputable def run (inst : Instance I m) (c : ℝ) (sel : (I → ℝ) → Fin m → I) : State I m :=
  runPrefix inst c sel m

/-- The total revenue the Allocation Algorithm collects: the sum over buyers of the amounts
charged to them. -/
noncomputable def revenue (inst : Instance I m) (c : ℝ) (sel : (I → ℝ) → Fin m → I) : ℝ :=
  ∑ i, (run inst c sel).spent i

end BJNAdAuctions.Basic


