-- Prove2me | Definitions.Def_CancelFreeHessian_Formula_Tree
-- name    : CancelFreeHessian_Formula_Tree
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:56:07.941035+00:00
-- url     : https://prove2.me/theorems/5adacb35-62b6-4775-b988-b873f320c581
-- title:
--   Tree unfolding of a formula: leaf variables y, g(y), F_u and adjoints a, b, path products d, K(w), D_i, branching sets B_i, lowest common ancestors, entry order and virtual trees V_i
-- statement:
--   Let $D$ be a scalar formula whose output is an operation gate. Its **tree unfolding** $T$ has one node per operation gate and one separate **leaf** per filled slot holding an input or constant gate; the leaf $\ell=(v,\kappa)$ is slot $\kappa$ of the operation gate $v$. The root is the output gate, and the **child** of $v$ in slot $\kappa$ is the node of the gate in that slot if it is an operation gate, otherwise the leaf $(v,\kappa)$. A node $u$ lies **below** $w$ if $u$ is in the subtree of $w$ ($u=w$ included). $L_i$ is the set of leaves labelled $x_i$.
--
--   Each input leaf $\ell$ carries an independent variable $y_\ell$; a constant leaf holds its constant. Evaluating the tree gives the value of each node as a function of $y$, and $g(y)$ is the root value; at $y_\ell=x_{\mathrm{var}(\ell)}$ the tree computes $f(x)$. For a node $u$, holding every leaf outside the subtree of $u$ fixed, the root value is a function $F_u$ of the value $t$ at $u$; the **adjoints** are
--   $$a(u)=F_u'(\text{current value of }u),\qquad b(u)=F_u''(\text{current value of }u).$$
--   For a node $v$ below $u$, $d(u,v)$ is the product of the local first partials $\varphi_{w,\kappa}$ over the edges (child in slot $\kappa$ to $w$) of the path from $v$ up to $u$, with $d(v,v)=1$. For an operation gate $w$,
--   $$K(w)=b(w)\varphi_{w,1}\varphi_{w,2}+a(w)\varphi_{w,12},\qquad D_i(u)=\sum_{\ell\in L_i\text{ below }u}d(u,\ell),$$
--   with all local partials at the current children values. $B_i$ is the set of operation gates with leaves of $L_i$ below both children. The **lowest common ancestor** of two nodes is their lowest common node above both. Leaves are ordered by depth-first entry time, the slot-1 child visited first: $\ell$ precedes $\ell'$ when, at some node, $\ell$ lies below the slot-1 child and $\ell'$ below the slot-2 child. The **virtual tree** $V_i$ is $L_i$ together with the lowest common ancestors of adjacent pairs of $L_i$, and a $V_i$-**child** of $v$ below its tree child $c$ is a node of $V_i$ below $c$ with no other node of $V_i$ between it and $c$.
--
--   **Formalization Note.** Nodes are `Node.gate k` and `Node.leaf (v, κ)`; leaf variables are `y : ℕ × Fin 2 → ℝ` (only input leaves are read). `tval c φ y ov k` evaluates the tree with optional overrides `ov` of node values; `Fnode c φ y u t` overrides node `u` by `t`, which is "every leaf outside the subtree of $u$ held fixed". `gfun` is $g$, `leafPoint x` is $y_\ell=x_{\mathrm{var}(\ell)}$. `dGate`/`dpath` give $d(w,u)$ (with value $0$ when $u$ is not below $w$), `Kfac` is $K$, `Dsum` is $D_i$, `branching i` is $B_i$, `IsLCA`, `LeafBefore`, `Adjacent`, `vnodes i` ($V_i$, a finite set of nodes) and `VChild` are as above. All quantities are read at the current `y`.
-- source:
--   Tianlang Chen, The Cancellation-Free Cost of Hessian Diagonals: Exact Counts, Formulas and Interfaces, STOC 2027 submission (manuscript sha256 de5c3ef4…), pp. 11–12, §4 proof of Theorem 3 (Tree and leaf variables, Adjoints, Pair identity, Summation at branching nodes, Virtual tree)

import Mathlib
import Definitions.Def_CancelFreeHessian_Formula_Graph

open Classical

namespace CancelFreeHessian.Formula

/-!
# The tree unfolding of a formula: leaf variables, adjoints, path products, virtual trees

Tianlang Chen, *The Cancellation-Free Cost of Hessian Diagonals*, proof of Theorem 3, §4
(pp. 11–12). For a formula `D` (no operation gate reused) the tree `T` has one node per operation
gate (`Node.gate k`) and one separate leaf per filled slot holding an input or constant gate:
the leaf `Node.leaf (v, κ)` is slot `κ` of the operation gate `v` (`κ = 0` is slot 1, `κ = 1` is
slot 2). The root is the output gate. Each input leaf `ℓ` carries an independent variable `y_ℓ`
(`y : ℕ × Fin 2 → ℝ`); a constant leaf holds the value of its constant gate.

Every quantity is a function of the leaf variables `y` and is read at the current `y`. The node
values can be overridden (`ov u = some t` replaces the value of node `u` by `t`); this gives the
function `F_u` of the adjoints, the root value as a function of the value at `u` when every leaf
outside the subtree of `u` is held fixed.
-/

/-- A node of the tree unfolding: an operation gate, or the leaf at slot `κ` of the operation
gate `v`. -/
inductive Node where
  | gate (k : ℕ)
  | leaf (ℓ : ℕ × Fin 2)
  deriving DecidableEq

namespace Dag

variable {n : ℕ} (D : Dag n)

/-- The child of the operation gate `v` in slot `κ`: the node of the gate filling that slot if it
is an operation gate, otherwise the leaf `(v, κ)`. -/
noncomputable def child (v : ℕ) (κ : Fin 2) : Node :=
  if D.IsOp (D.slot v κ) then .gate (D.slot v κ) else .leaf (v, κ)

/-- `u` is a child of `w` in the tree unfolding. -/
def ChildOf (u w : Node) : Prop :=
  ∃ v κ, w = .gate v ∧ v < D.size ∧ D.IsOp v ∧ D.child v κ = u

/-- `u` lies below `w` (in the subtree of `w`, `u = w` included); equivalently `w` is an
ancestor of `u`. -/
def Below (u w : Node) : Prop := Relation.ReflTransGen D.ChildOf u w

/-- The nodes of the tree unfolding, as a finite set: the operation gates and the leaves. -/
noncomputable def nodes : Finset Node :=
  ((Finset.range D.size).filter fun k => D.IsOp k).image Node.gate ∪
    (((Finset.range D.size) ×ˢ (Finset.univ : Finset (Fin 2))).filter
      fun ℓ => D.IsOp ℓ.1 ∧ ¬ D.IsOp (D.slot ℓ.1 ℓ.2)).image Node.leaf

/-- `L_i`: the leaves labelled `x_i`, i.e. the slots `(v, κ)` of operation gates filled by the
input gate of `x_i`. -/
noncomputable def leavesOf (i : Fin n) : Finset (ℕ × Fin 2) :=
  ((Finset.range D.size) ×ˢ (Finset.univ : Finset (Fin 2))).filter
    fun ℓ => D.IsOp ℓ.1 ∧ D.gate (D.slot ℓ.1 ℓ.2) = .input i

/-- The value held by the leaf `ℓ = (v, κ)` under the leaf variables `y`: `y_ℓ` for an input
leaf, the value of the constant gate for a constant leaf. -/
noncomputable def leafVal (c : ℕ → ℝ) (y : ℕ × Fin 2 → ℝ) (ℓ : ℕ × Fin 2) : ℝ :=
  match D.gate (D.slot ℓ.1 ℓ.2) with
  | .input _ => y ℓ
  | .const => c (D.slot ℓ.1 ℓ.2)
  | .op _ _ => 0

/-- The value of the operation gate `k` in the tree, under the leaf variables `y` and the
overrides `ov`: `ov (gate k)` if set, otherwise `φ_k` of the values of its two children (a child
leaf takes its override if set, otherwise its leaf value). -/
noncomputable def tval (c : ℕ → ℝ) (φ : ℕ → ℝ × ℝ → ℝ) (y : ℕ × Fin 2 → ℝ)
    (ov : Node → Option ℝ) (k : ℕ) : ℝ :=
  (ov (.gate k)).getD <|
    match D.gate k with
    | .op p q =>
      if _h : p < k ∧ q < k then
        φ k ((if D.IsOp p then tval c φ y ov p else (ov (.leaf (k, 0))).getD (D.leafVal c y (k, 0))),
             (if D.IsOp q then tval c φ y ov q else (ov (.leaf (k, 1))).getD (D.leafVal c y (k, 1))))
      else 0
    | _ => 0
termination_by k
decreasing_by all_goals omega

/-- No override. -/
def noOv : Node → Option ℝ := fun _ => none

/-- The value of a node under the leaf variables `y` and the overrides `ov`. -/
noncomputable def nodeVal (c : ℕ → ℝ) (φ : ℕ → ℝ × ℝ → ℝ) (y : ℕ × Fin 2 → ℝ)
    (ov : Node → Option ℝ) : Node → ℝ
  | .gate k => D.tval c φ y ov k
  | .leaf ℓ => (ov (.leaf ℓ)).getD (D.leafVal c y ℓ)

/-- `g(y)`: the value of the root (the output gate) as a function of the leaf variables. -/
noncomputable def gfun (c : ℕ → ℝ) (φ : ℕ → ℝ × ℝ → ℝ) : (ℕ × Fin 2 → ℝ) → ℝ :=
  fun y => D.tval c φ y noOv D.out

/-- The leaf variables of the point `x`: `y_ℓ = x_{var(ℓ)}` on input leaves (`0` elsewhere,
never read). -/
def leafPoint (x : Fin n → ℝ) : ℕ × Fin 2 → ℝ :=
  fun ℓ => match D.gate (D.slot ℓ.1 ℓ.2) with
    | .input i => x i
    | _ => 0

/-- `F_u`: the root value as a function of the value `t` at the node `u`, every leaf outside the
subtree of `u` held at its value under `y`. -/
noncomputable def Fnode (c : ℕ → ℝ) (φ : ℕ → ℝ × ℝ → ℝ) (y : ℕ × Fin 2 → ℝ) (u : Node) :
    ℝ → ℝ :=
  fun t => D.tval c φ y (fun w => if w = u then some t else none) D.out

/-- The adjoint `a(u) = F_u'` at the current value of `u`. -/
noncomputable def adjA (c : ℕ → ℝ) (φ : ℕ → ℝ × ℝ → ℝ) (y : ℕ × Fin 2 → ℝ) (u : Node) : ℝ :=
  deriv (D.Fnode c φ y u) (D.nodeVal c φ y noOv u)

/-- The second adjoint `b(u) = F_u''` at the current value of `u`. -/
noncomputable def adjB (c : ℕ → ℝ) (φ : ℕ → ℝ × ℝ → ℝ) (y : ℕ × Fin 2 → ℝ) (u : Node) : ℝ :=
  deriv (deriv (D.Fnode c φ y u)) (D.nodeVal c φ y noOv u)

/-- The point (value of the slot-1 child, value of the slot-2 child) at which the local function
of the operation gate `v` is evaluated in the tree. -/
noncomputable def childArgs (c : ℕ → ℝ) (φ : ℕ → ℝ × ℝ → ℝ) (y : ℕ × Fin 2 → ℝ) (v : ℕ) :
    ℝ × ℝ :=
  (D.nodeVal c φ y noOv (D.child v 0), D.nodeVal c φ y noOv (D.child v 1))

/-- `d(w, u)` for the operation gate `w` and a node `u` below it: the product of the local first
partials `φ_{v,κ}` over the edges (from the child in slot `κ` up to `v`) of the path from `u` up
to `w`; `d(w, w) = 1`, and `0` when `u` is not below `w`. -/
noncomputable def dGate (c : ℕ → ℝ) (φ : ℕ → ℝ × ℝ → ℝ) (y : ℕ × Fin 2 → ℝ) (u : Node)
    (w : ℕ) : ℝ :=
  if Node.gate w = u then 1 else
    match D.gate w with
    | .op p q =>
      if _h : p < w ∧ q < w then
        if D.Below u (D.child w 0) then
          lp1 (φ w) 0 (D.childArgs c φ y w) * (if D.IsOp p then dGate c φ y u p else 1)
        else if D.Below u (D.child w 1) then
          lp1 (φ w) 1 (D.childArgs c φ y w) * (if D.IsOp q then dGate c φ y u q else 1)
        else 0
      else 0
    | _ => 0
termination_by w
decreasing_by all_goals omega

/-- `d(w, u)`: the product of local first partials on the path from `u` up to its ancestor `w`
(`d(u, u) = 1`; `0` when `u` is not below `w`). -/
noncomputable def dpath (c : ℕ → ℝ) (φ : ℕ → ℝ × ℝ → ℝ) (y : ℕ × Fin 2 → ℝ) (w u : Node) : ℝ :=
  match w with
  | .gate k => D.dGate c φ y u k
  | .leaf ℓ => if u = .leaf ℓ then 1 else 0

/-- `K(w) = b(w) φ_{w,1} φ_{w,2} + a(w) φ_{w,12}` for the operation gate `w`. -/
noncomputable def Kfac (c : ℕ → ℝ) (φ : ℕ → ℝ × ℝ → ℝ) (y : ℕ × Fin 2 → ℝ) (w : ℕ) : ℝ :=
  D.adjB c φ y (.gate w) * lp1 (φ w) 0 (D.childArgs c φ y w) * lp1 (φ w) 1 (D.childArgs c φ y w) +
    D.adjA c φ y (.gate w) * lp12 (φ w) (D.childArgs c φ y w)

/-- `D_i(u) = Σ_{ℓ ∈ L_i below u} d(u, ℓ)`. -/
noncomputable def Dsum (c : ℕ → ℝ) (φ : ℕ → ℝ × ℝ → ℝ) (y : ℕ × Fin 2 → ℝ) (i : Fin n)
    (u : Node) : ℝ :=
  ∑ ℓ ∈ (D.leavesOf i).filter (fun ℓ => D.Below (.leaf ℓ) u), D.dpath c φ y u (.leaf ℓ)

/-- `B_i`: the operation gates `w` with leaves of `L_i` below both children. -/
noncomputable def branching (i : Fin n) : Finset ℕ :=
  (Finset.range D.size).filter fun w =>
    D.IsOp w ∧ (∃ ℓ ∈ D.leavesOf i, D.Below (.leaf ℓ) (D.child w 0)) ∧
      (∃ ℓ ∈ D.leavesOf i, D.Below (.leaf ℓ) (D.child w 1))

/-- `w` is the lowest common ancestor of `u` and `v`. -/
def IsLCA (w u v : Node) : Prop :=
  D.Below u w ∧ D.Below v w ∧ ∀ w', D.Below u w' → D.Below v w' → D.Below w w'

/-- Depth-first entry order of leaves, children visited in slot order: `ℓ` comes before `ℓ'` when
at some operation gate `w`, `ℓ` lies below the slot-1 child and `ℓ'` below the slot-2 child. -/
def LeafBefore (ℓ ℓ' : ℕ × Fin 2) : Prop :=
  ∃ w < D.size, D.IsOp w ∧ D.Below (.leaf ℓ) (D.child w 0) ∧ D.Below (.leaf ℓ') (D.child w 1)

/-- `ℓ, ℓ'` are adjacent in the entry order of `L_i`: `ℓ` comes before `ℓ'` and no leaf of `L_i`
lies strictly between them. -/
def Adjacent (i : Fin n) (ℓ ℓ' : ℕ × Fin 2) : Prop :=
  ℓ ∈ D.leavesOf i ∧ ℓ' ∈ D.leavesOf i ∧ D.LeafBefore ℓ ℓ' ∧
    ¬ ∃ m ∈ D.leavesOf i, D.LeafBefore ℓ m ∧ D.LeafBefore m ℓ'

/-- The virtual tree node set `V_i`: the leaves of `L_i` together with the lowest common
ancestors of adjacent pairs of `L_i`. -/
noncomputable def vnodes (i : Fin n) : Finset Node :=
  D.nodes.filter fun u =>
    (∃ ℓ ∈ D.leavesOf i, u = .leaf ℓ) ∨
      ∃ ℓ ℓ', D.Adjacent i ℓ ℓ' ∧ D.IsLCA u (.leaf ℓ) (.leaf ℓ')

/-- `u` is a `V_i`-child of the operation gate `v` below its slot-`κ` child: `u ∈ V_i` lies below
`child v κ`, and no other node of `V_i` lies between `u` and `child v κ`. -/
def VChild (i : Fin n) (v : ℕ) (κ : Fin 2) (u : Node) : Prop :=
  u ∈ D.vnodes i ∧ D.Below u (D.child v κ) ∧
    ∀ u' ∈ D.vnodes i, D.Below u u' → D.Below u' (D.child v κ) → u' = u

end Dag

end CancelFreeHessian.Formula


