-- Prove2me | Definitions.Def_LogSupermodularBIS_Main_TreeWalk
-- name    : LogSupermodularBIS_Main_TreeWalk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:31:02.603975+00:00
-- url     : https://prove2.me/theorems/0058a719-3bad-4b21-a03b-801986f018e9
-- title:
--   The Sinclair–Jerrum walk on a weighted rooted tree
-- statement:
--   A finite **rooted tree** (the referenced definition `HarelTarjan.Compressed.RootedTree`) is given by a root $o$ and a parent map $v\mapsto v^-$ under which every vertex reaches the root; the depth of $v$ is the least number of parent steps from $v$ to $o$. A child of $v$ is a node $y\ne o$ with $y^-=v$, a leaf is a node with no child, and $x$ lies below $v$ if some iterate of the parent map takes $x$ to $v$. Given leaf weights $\omega_x$, the mass $Z_v$ is the sum of the weights of the leaves below $v$.
--
--   Given estimates $q_v$, the weighted degree (A.2) is $s_v=\mathbf 1\{v\ne o\}q_v+\sum_{y\text{ child of }v}q_y$ and $S_o=\sum_vs_v$. The walk $P_{tr}$ holds with probability $1/2$ and otherwise moves along an edge at the current node with probability proportional to its weight:
--   $$P_{tr}(v,y)=\frac{q_y}{2s_v}\ (y\text{ a child of }v),\qquad P_{tr}(v,v^-)=\frac{q_v}{2s_v}\ (v\ne o),\qquad P_{tr}(v,v)=\frac12.$$
--   The law $\pi(v)=s_v/S_o$ is its candidate stationary law.
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), pp. 39–40 (PDF 40–41), Appendix A.1, (A.1), (A.2) and the chain P_tr

import Mathlib
import Definitions.Def_HarelTarjan_Compressed_RootedTree

set_option autoImplicit false

namespace LogSupermodularBIS.Main

/-!
# The Sinclair–Jerrum walk on a weighted rooted tree (Appendix A.1, pp. 39–40)

The tree is the published `HarelTarjan.Compressed.RootedTree`: a finite vertex set, a root and a
parent map with `parent root = root` such that every vertex reaches the root; its depth is the
least number of parent steps to the root.
-/

open HarelTarjan.Compressed

namespace TreeWalk

variable {V : Type*} [Fintype V] [DecidableEq V] (𝒯 : RootedTree V)

/-- `y` is a child of `v`. -/
def IsChild (y v : V) : Prop := y ≠ 𝒯.root ∧ 𝒯.parent y = v

/-- `x` is a leaf: it has no child. -/
def IsLeaf (x : V) : Prop := ∀ y, ¬ IsChild 𝒯 y x

/-- `x` lies below `v`: `v` is an ancestor of `x` (or `x = v`). -/
def IsBelow (x v : V) : Prop := IsAncestor 𝒯 v x

open Classical in
/-- The mass `Z_v`: the sum of the leaf weights `ω_x` over the leaves `x` below `v`. -/
noncomputable def mass (ω : V → ℝ) (v : V) : ℝ :=
  ∑ x, if IsLeaf 𝒯 x ∧ IsBelow 𝒯 x v then ω x else 0

open Classical in
/-- The weighted degree (A.2): `s_v = 1{v ≠ o} q_v + Σ_{y child of v} q_y`. -/
noncomputable def weightedDegree (q : V → ℝ) (v : V) : ℝ :=
  (if v ≠ 𝒯.root then q v else 0) + ∑ y, if IsChild 𝒯 y v then q y else 0

/-- `S_o = Σ_v s_v`. -/
noncomputable def totalDegree (q : V → ℝ) : ℝ := ∑ v, weightedDegree 𝒯 q v

open Classical in
/-- The walk `P_tr`: hold with probability `1/2`; otherwise move along an edge at the current
node with probability proportional to its weight, the edge to a child `y` having weight `q_y` and
the edge to the parent of `v ≠ o` having weight `q_v`. -/
noncomputable def walk (q : V → ℝ) : Matrix V V ℝ := fun v y =>
  if y = v then 1 / 2
  else if IsChild 𝒯 y v then q y / (2 * weightedDegree 𝒯 q v)
  else if v ≠ 𝒯.root ∧ y = 𝒯.parent v then q v / (2 * weightedDegree 𝒯 q v)
  else 0

/-- The law `π(v) = s_v / S_o`. -/
noncomputable def stationaryLaw (q : V → ℝ) (v : V) : ℝ :=
  weightedDegree 𝒯 q v / totalDegree 𝒯 q

end TreeWalk

end LogSupermodularBIS.Main


