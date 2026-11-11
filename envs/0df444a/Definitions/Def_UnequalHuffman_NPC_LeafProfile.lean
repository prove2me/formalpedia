-- Prove2me | Definitions.Def_UnequalHuffman_NPC_LeafProfile
-- name    : UnequalHuffman_NPC_LeafProfile
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:44:11.462945+00:00
-- url     : https://prove2.me/theorems/2321f542-1457-4feb-9420-f0e65bbed693
-- title:
--   Minimum-Score Tree with Prescribed Leaf Profile: instances, feasible trees, the score (1), optima and the binary instance code
-- statement:
--   **Minimum-Score Tree with Prescribed Leaf Profile** (§2.2). An instance is given by its coefficient rows: for each depth $t = 1,\dots,H$ an integer list $u_{t,1},\dots,u_{t,n_t}$ (`LPInstance = List (List ℤ)`, row $t$ at list index $t-1$; a depth with $n_t = 0$ has an empty row). Its leaf profile is $n_t$ = the length of row $t$ and $N = \sum_t n_t$. It is **well-formed** (`IsValid`) if the profile is feasible, $n_H > 0$, $N \ge 2$, and every row is nonincreasing, $u_{t,1} \ge \dots \ge u_{t,n_t}$.
--
--   A **feasible tree** is a full ordered binary tree with exactly $n_t$ leaves at every depth $t$ and no other leaves. Its score is
--   $$\mathrm{score}(T) = \sum_{t=1}^{H}\sum_{k=1}^{n_t} u_{t,k}\, z_{t,k}(T), \tag{1}$$
--   where $z_{t,1}(T) \le \dots \le z_{t,n_t}(T)$ are the depth-$t$ leaf coordinates sorted with repetitions ($k$ is a rank, not a position). `IsOptimalTree I T`: $T$ is feasible of minimum score; `IsOptTree I v`: $v = \mathrm{OPT}_{\mathrm{tree}}(I)$, i.e. some feasible tree has score $v$ and none less.
--
--   The binary code of an instance (`LPInstance.code`) is $H$, then for every depth $n_t$ followed by $u_{t,1},\dots,u_{t,n_t}$, all in binary (integers with a sign symbol).
-- source:
--   Chandran and Gajjala, Binary Huffman Coding with Unequal Letter Costs Is NP-Complete, arXiv:2611.04444v1, pp. 8–9, §2.2 (the leaf-profile problem, eq. (1))

import Mathlib
import Definitions.Def_UnequalHuffman_NPC_Trees
import Definitions.Def_ProjSchedTW_Complexity_Encoding

set_option autoImplicit false

namespace UnequalHuffman.NPC

open ProjSchedTW.Complexity

/-- An instance of Minimum-Score Tree with Prescribed Leaf Profile (§2.2): its coefficient rows,
row `t - 1` (0-based) being the depth-`t` list `u_{t,1}, …, u_{t,n_t}`. The height is
`H = I.length`, the leaf count at depth `t` is the length of row `t`, and a depth with `n_t = 0`
has an empty row. -/
abbrev LPInstance : Type := List (List ℤ)

namespace LPInstance

/-- The leaf profile `(n₁, …, n_H)` of the instance. -/
def counts (I : LPInstance) : List ℕ := I.map List.length

/-- `N = ∑_t n_t`, the number of explicitly listed coefficients. -/
def numLeaves (I : LPInstance) : ℕ := I.counts.sum

/-- The coefficient row of depth `t` (empty for `t = 0` and `t > H`). -/
def row (I : LPInstance) (t : ℕ) : List ℤ :=
  if t = 0 then [] else I.getD (t - 1) []

/-- A well-formed instance: the profile is feasible, `n_H > 0`, `N ≥ 2`, and every row is
nonincreasing, `u_{t,1} ≥ u_{t,2} ≥ ⋯ ≥ u_{t,n_t}`. -/
def IsValid (I : LPInstance) : Prop :=
  ProfileFeasible I.counts ∧ 0 < profileCount I.counts I.length ∧ 2 ≤ I.numLeaves ∧
  ∀ r ∈ I, r.Pairwise (· ≥ ·)

/-- A feasible solution: a full ordered binary tree with exactly `n_t` leaves at every depth `t`
and no leaves at other depths. -/
def IsFeasibleTree (I : LPInstance) (T : OTree) : Prop :=
  IsProfileTree I.counts T

/-- The score (1): `score(T) = ∑_t ∑_k u_{t,k} z_{t,k}(T)`, where `z_{t,1}(T) ≤ ⋯ ≤ z_{t,n_t}(T)`
are the depth-`t` leaf coordinates sorted nondecreasingly (rank `k`, not position). -/
def score (I : LPInstance) (T : OTree) : ℤ :=
  ∑ t ∈ Finset.range (I.length + 1),
    (List.zipWith (fun (u : ℤ) (z : ℕ) => u * (z : ℤ)) (I.row t) (T.leafCoords t)).sum

/-- `T` is an optimal source tree: feasible and of minimum score. -/
def IsOptimalTree (I : LPInstance) (T : OTree) : Prop :=
  IsFeasibleTree I T ∧ ∀ T', IsFeasibleTree I T' → I.score T ≤ I.score T'

/-- `v = OPT_tree(I)`: some feasible tree has score `v` and every feasible tree scores at
least `v`. -/
def IsOptTree (I : LPInstance) (v : ℤ) : Prop :=
  (∃ T, IsFeasibleTree I T ∧ I.score T = v) ∧ ∀ T, IsFeasibleTree I T → v ≤ I.score T

/-- The binary code of an instance: `H`, then for each depth `t = 1, …, H` the length `n_t`
followed by the integers `u_{t,1}, …, u_{t,n_t}`, all in binary. -/
def code (I : LPInstance) : List BSym :=
  encNat I.length ++ I.flatMap fun r => encNat r.length ++ encInts r

end LPInstance

end UnequalHuffman.NPC


