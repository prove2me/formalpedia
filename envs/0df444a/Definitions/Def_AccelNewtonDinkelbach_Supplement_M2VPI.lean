-- Prove2me | Definitions.Def_AccelNewtonDinkelbach_Supplement_M2VPI
-- name    : AccelNewtonDinkelbach_Supplement_M2VPI
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:59:05.244197+00:00
-- url     : https://prove2.me/theorems/109fb7ed-42e1-4faa-aadb-a94258c88dec
-- title:
--   Finite M2VPI systems, walks, gains, costs, and shortest paths
-- statement:
--   A finite **M2VPI system** is a directed multigraph with real arc costs $c_e$ and positive gains $\gamma_e$. Arc $e=(v,w)$ represents $y_v-\gamma_e y_w\le c_e$. For a walk $P=(e_1,\ldots,e_k)$,
--
--   $$c(P)=\sum_{i=1}^k\left(\prod_{j<i}\gamma_{e_j}\right)c_{e_i},\qquad \gamma(P)=\prod_{i=1}^k\gamma_{e_i}.$$
--
--   The trivial walk has cost $0$ and gain $1$. The definition includes $y$-cost, paths, cycles, shortest paths, feasibility, and the extended-real coordinatewise supremum $y^{\max}$ of feasible labels.
-- source:
--   Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, §4 and §4.1, p.11

import Mathlib

namespace AccelNewtonDinkelbach.Supplement

open scoped BigOperators

set_option autoImplicit false

/-- A finite monotone two-variables-per-inequality system.  Arc `e` represents
`y_(tail e) - gain e * y_(head e) ≤ cost e`. -/
structure M2VPI (n m : ℕ) where
  tail : Fin m → Fin n
  head : Fin m → Fin n
  cost : Fin m → ℝ
  gain : Fin m → ℝ
  gain_pos : ∀ e, 0 < gain e

namespace M2VPI

variable {n m : ℕ} (M : M2VPI n m)

/-- A real label vector satisfies all inequalities. -/
def Feasible (y : Fin n → ℝ) : Prop :=
  ∀ e, y (M.tail e) - M.gain e * y (M.head e) ≤ M.cost e

/-- Feasibility of the system. -/
def IsFeasible : Prop := ∃ y, M.Feasible y

/-- The pointwise supremum of feasible real labels, in the extended reals. -/
noncomputable def ymax (v : Fin n) : EReal :=
  ⨆ y : {y : Fin n → ℝ // M.Feasible y}, ((y.1 v : ℝ) : EReal)

/-- Validity of an arc list as a walk from `u` to `v`. -/
def IsWalkEdges : Fin n → Fin n → List (Fin m) → Prop
  | u, v, [] => u = v
  | u, v, e :: es => M.tail e = u ∧ IsWalkEdges (M.head e) v es

/-- A walk in the directed multigraph underlying an M2VPI system. -/
structure Walk where
  start : Fin n
  finish : Fin n
  edges : List (Fin m)
  valid : M.IsWalkEdges start finish edges

namespace Walk

variable {M : M2VPI n m}

/-- The vertices of a walk, including both endpoints. -/
def verticesFrom (M : M2VPI n m) : Fin n → List (Fin m) → List (Fin n)
  | u, [] => [u]
  | u, e :: es => u :: verticesFrom M (M.head e) es

def vertices (P : M.Walk) : List (Fin n) := verticesFrom M P.start P.edges

/-- Walk cost, with the gain accumulated before each arc. -/
def cost (M : M2VPI n m) : List (Fin m) → ℝ
  | [] => 0
  | e :: es => M.cost e + M.gain e * cost M es

def gain (M : M2VPI n m) : List (Fin m) → ℝ
  | [] => 1
  | e :: es => M.gain e * gain M es

def walkCost (P : M.Walk) : ℝ := cost M P.edges
def walkGain (P : M.Walk) : ℝ := gain M P.edges

/-- The `y`-cost `c(P)+γ(P)y_v`. -/
noncomputable def yCost (P : M.Walk) (y : Fin n → EReal) : EReal :=
  (P.walkCost : EReal) + (P.walkGain : EReal) * y P.finish

/-- A path has no repeated vertex. -/
def IsPath (P : M.Walk) : Prop := P.vertices.Nodup

/-- A cycle at `u`: a nontrivial `u-u` walk with distinct vertices before returning to `u`. -/
def IsCycleAt (P : M.Walk) (u : Fin n) : Prop :=
  P.start = u ∧ P.finish = u ∧ P.edges ≠ [] ∧ P.vertices.dropLast.Nodup

/-- `Q` is the initial `u-v` subpath of `P`. -/
def IsPrefixTo (Q P : M.Walk) (v : Fin n) : Prop :=
  Q.start = P.start ∧ Q.finish = v ∧ Q.edges <+: P.edges

/-- A shortest path with respect to the input labels, among all walks with the same endpoints. -/
def IsShortest (P : M.Walk) (y : Fin n → EReal) : Prop :=
  P.IsPath ∧ ∀ Q : M.Walk, Q.start = P.start → Q.finish = P.finish → P.yCost y ≤ Q.yCost y

end Walk

end M2VPI

end AccelNewtonDinkelbach.Supplement


