-- Prove2me | Definitions.Def_OAI_Analysis_RecursivePotentials_Main
-- name    : OAI_Analysis_RecursivePotentials_Main
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T07:49:05.761992+00:00
-- url     : https://prove2.me/theorems/1e6122c8-f46e-4a32-9ea1-d6d29dd0efcf
-- title:
--   Basis vectors, path vectors and children embeddings in the variable-exponent space
-- statement:
--   This file defines explicit test vectors in the component spaces and in the variable-exponent space $X_v$, and records how the coordinates and potentials of a zero-root completion act on finitely supported vectors.
--
--   **Setting.** For a rooted tree $T$ on an index set $\iota$ (root $r$, parent map $\pi$ with $\pi(r)=r$, depth $d$ with $d(r)=0$ and $d(\pi(s))<d(s)$ for $s\neq r$) and an exponent $e\ge1$, let $V_{T,e}$ be the space of finitely supported $v:\iota\to\mathbb{R}$ with the norm $\|v\|=P^e_v(r)+Q^e_v(r)$. Here the $e$-potentials are computed on the finite set $H_v$ formed by the root, the support of $v$ and all their ancestors, recursively from the deepest nodes:
--   $$P^e_v(s)=\max\bigl(A,\ v(s)+B\bigr),\quad Q^e_v(s)=\max\bigl(B,\ A-v(s)\bigr),\quad A=\Bigl(\sum_cP^e_v(c)^e\Bigr)^{1/e},\ \ B=\Bigl(\sum_cQ^e_v(c)^e\Bigr)^{1/e},$$
--   the sums running over the children $c$ of $s$ (the nodes $c\neq r$ with $\pi(c)=s$) in $H_v$, and $P^e_v=Q^e_v=0$ outside $H_v$. The completion of $V_{T,e}$ is the aggregation space $Y_{T,e}$. For an integer $h\ge1$ the component tree $T_h$ has as nodes the finite sequences of natural numbers of length at most $h$, the empty sequence $\emptyset$ as root, and the parent map deleting the last entry; with the exponent $p_h=1+\frac1h$, the component space is $Y_h=Y_{T_h,p_h}$. The nodes of the variable space are the pairs $(h,s)$ with $s$ a node of $T_h$, and
--   $$X_v=\Bigl(\bigoplus_{h\ge1}Y_h\Bigr)_{\ell^2}$$
--   is the $\ell^2$-direct sum of the component spaces; the coordinate of $x\in X_v$ at $(h,s)$ is the $s$-coordinate (the continuous extension of $v\mapsto v(s)$) of its $h$-th component. For a node $s$ of a rooted tree, the path vector $\mathbf{1}_{[r,s]}$ is the indicator function of the set consisting of $s$ and all its ancestors, including the root.
--
--   1. **Component basis vectors.** For $h\ge1$ and a node $s$ of $T_h$, $b_{h,s}\in Y_h$ is the unit coordinate vector at $s$ (value $1$ at $s$ and $0$ elsewhere).
--   2. **Component path vectors.** $\gamma_{h,s}\in Y_h$ is the path vector $\mathbf{1}_{[\emptyset,s]}$ of $T_h$, the indicator of the set of all initial segments of the sequence $s$ (from $\emptyset$ to $s$ itself).
--   3. **Truncated nodes.** For $h\in\mathbb{N}$ the component of height $h+1\ge1$ is used, and for a finite sequence $s$ of natural numbers, $s|_h$ denotes the sequence of its first $h$ entries (all of $s$ if it is shorter), a node of $T_{h+1}$ of length at most $h$.
--   4. **Path vectors of $X_v$.** For $h\in\mathbb{N}$ and a finite sequence $s$, $\Gamma_h(s)\in X_v$ is the vector whose component of index $h+1$ is $\gamma_{h+1,\,s|_h}$ and whose other components vanish.
--   5. **Children embeddings.** For $h\in\mathbb{N}$ and a sequence $s$ of length less than $h$, the map $\mathbb{N}\to T_{h+1}$ sending $k$ to the sequence $s$ followed by the entry $k$ is injective; its values are the children of $s$ in $T_{h+1}$.
--   6. **Zero-root vectors in the completion.** For a rooted tree $T$ let $V_T=V_{T,2}$ (quadratic potentials $P_v,Q_v$), $X_T$ its completion, $V^0_T=\{v\in V_T:v(r)=0\}$ with the norm $P_v(r)$, $X^0_T$ the completion of $V^0_T$, and $J:X^0_T\to X_T$ the continuous extension of the inclusion. The coordinate at $s$ and the potentials at $s$ of $x\in X^0_T$ are the continuous extensions of $v\mapsto v(s)$, $v\mapsto P_v(s)$, $v\mapsto Q_v(s)$ from $V_T$ to $X_T$, evaluated at $Jx$. For $v\in V^0_T$ they equal $v(s)$, $P_v(s)$ and $Q_v(s)$.
--
--   In the module, $\gamma_{h,s}$ has norm $1$, $b_{h,s}$ has norm at least $2$ when $s$ is not the root, and, for a sequence $s$ of length less than $h$, the increments $\Gamma_h(s\,k)-\Gamma_h(s)$ (with $s\,k$ the sequence $s$ followed by $k$) are the basis vectors of $X_v$ at the children of $s$ and form a weakly null sequence in $k$. These path vectors are the test vectors in the proof that every equivalent norm on $X_v$ has vanishing modulus at the ratio of its two equivalence constants.
--
--   **Formalization Note** The definitions are `Variable.componentBasis`, `Variable.componentPath` (the image of `(componentTree h).path s`, the indicator of `ancestors s`), `Variable.pathHeight h = h + 1 : ℕ+`, `Variable.pathNode h s = s.take h`, `Variable.pathVector h s = lp.single 2 (pathHeight h) (componentPath _ (pathNode h s))` and the embedding `Variable.children h s hs : ℕ ↪ ComponentNode (pathHeight h)`. Item 6 consists of the simp lemmas `ZeroTreeSpace.coordinate_coe`, `ZeroTreeSpace.P_coe` and `ZeroTreeSpace.Q_coe`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/Main.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/Main.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RecursivePotentials mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_EquivalentNorms
import Definitions.Def_OAI_Analysis_RecursivePotentials_JoinedGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_VariableEstimates
import Definitions.Def_OAI_Analysis_RecursivePotentials_VariableCompletion
import Definitions.Def_OAI_Analysis_RecursivePotentials_VariableLp
import Definitions.Def_OAI_Analysis_RecursivePotentials_VariableStability

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

open Filter Topology

open Filter Topology

open scoped ENNReal

open UniformSpace

open Filter

open scoped Topology

open Filter Topology TopologicalSpace

open scoped ENNReal

namespace VariableTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

end VariableTree

namespace Variable

open UniformSpace VariableExponent Filter Topology

def componentBasis (h : ℕ+) (s : ComponentNode h) : Component h :=
  ((AggregationVector.basisVector (componentTree h) (exponent h) s : AggregationVector (componentTree h) (exponent h)) : Component h)

def componentPath (h : ℕ+) (s : ComponentNode h) : Component h :=
  ((show AggregationVector (componentTree h) (exponent h) from (componentTree h).path s) : Component h)

def pathHeight (h : ℕ) : ℕ+ := ⟨h+1,by omega⟩

def pathNode (h : ℕ) (s : List ℕ) : ComponentNode (pathHeight h) :=
  ⟨s.take h,by change (s.take h).length ≤ h+1; simp only [List.length_take]; omega⟩

def pathVector (h : ℕ) (s : List ℕ) : Xv :=
  lp.single 2 (pathHeight h) (componentPath _ (pathNode h s))

def children (h : ℕ) (s : List ℕ) (hs : s.length < h) : ℕ ↪ ComponentNode (pathHeight h) where
  toFun k := pathNode h (s++[k])
  inj' := by
    intro k l he
    have hsk : (s++[k]).length ≤ h := by simp; omega
    have hsl : (s++[l]).length ≤ h := by simp; omega
    have hh := congrArg Subtype.val he
    simpa [pathNode,List.take_of_length_le hsk,List.take_of_length_le hsl] using hh

end Variable

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeSpace

namespace ZeroTreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

@[simp] lemma coordinate_coe (s : ι) (v : ZeroTreeVector T) :
    coordinate T s (v : ZeroTreeSpace T) = ZeroTreeVector.toTree T v s := by
  change TreeSpace.coordinate T s (inclusion T (v : ZeroTreeSpace T)) = _
  rw [inclusion_coe,TreeSpace.coordinate_coe]
  rfl

@[simp] lemma P_coe (s : ι) (v : ZeroTreeVector T) :
    P T s (v : ZeroTreeSpace T) = T.P (ZeroTreeVector.toTree T v) s := by
  unfold P
  rw [inclusion_coe,TreeSpace.P_coe]
  rfl

@[simp] lemma Q_coe (s : ι) (v : ZeroTreeVector T) :
    Q T s (v : ZeroTreeSpace T) = T.Q (ZeroTreeVector.toTree T v) s := by
  unfold Q
  rw [inclusion_coe,TreeSpace.Q_coe]
  rfl

end ZeroTreeSpace

namespace Variable

open VariableExponent

end Variable

end RecursivePotentials

end

end OAI


