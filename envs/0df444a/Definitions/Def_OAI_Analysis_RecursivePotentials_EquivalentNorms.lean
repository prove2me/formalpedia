-- Prove2me | Definitions.Def_OAI_Analysis_RecursivePotentials_EquivalentNorms
-- name    : OAI_Analysis_RecursivePotentials_EquivalentNorms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T07:35:49.058186+00:00
-- url     : https://prove2.me/theorems/be108f1d-61e3-42bf-9f85-8f7b0d8726f5
-- title:
--   Basis, path and cut-path vectors in tree spaces, child enumerations in the sequence and joined trees, and a weighted square inequality
-- statement:
--   This file names the concrete vectors and families of nodes that are used to test equivalent norms on the tree spaces, and proves an elementary weighted inequality.
--
--   **Setting.** Let $T$ be a rooted tree on a node set $I$ with root $r$, parent map $\pi$ (with $\pi(r)=r$) and depth strictly decreasing from a node to its parent; the children of $a$ are the nodes $c\neq r$ with $\pi(c)=a$, and the ancestors of $s$ are $s,\pi(s),\dots,r$. For a finitely supported $v:I\to\mathbb{R}$ let $(P_v,Q_v)$ be the tree potentials, the least pair of nonnegative functions with $P_v-Q_v=v$ such that $\sum_{c\in S}P_v(c)^2\le P_v(a)^2$ and $\sum_{c\in S}Q_v(c)^2\le Q_v(a)^2$ for every node $a$ and every finite set $S$ of children of $a$. Then $X_T$ is the completion of the space $c_{00}(I)$ of finitely supported vectors under $\|v\|=P_v(r)+Q_v(r)$, and $X^0_T$ is the completion of $\{v\in c_{00}(I):v(r)=0\}$ under $\|v\|_0=P_v(r)$, with $\iota:X^0_T\to X_T$ the continuous extension of the identity. Write $e_c$ for the coordinate vector at $c$ and $\gamma_s$ for the indicator of the ancestors of $s$.
--
--   Two particular trees occur. The *sequence tree* $\Sigma$ has as nodes all finite sequences of natural numbers, root the empty sequence $\varnothing$, parent map deleting the last entry, and depth equal to the length. The *joined tree* $J$ has as nodes a root $\ast$ and all pairs $(h,u)$ with $h\ge 1$ an integer and $u$ a finite sequence of natural numbers of length $|u|\le h$; the parent of $(h,\varnothing)$ is $\ast$, the parent of $(h,u)$ for nonempty $u$ is $(h,u^-)$ where $u^-$ is $u$ without its last entry, and the depth of $(h,u)$ is $|u|+1$. Thus $J$ joins below a common root one copy of the infinitely branching tree of height $h$ for every $h\ge 1$. For a sequence $u$ and $k\in\mathbb{N}$, $u^{\frown}k$ denotes $u$ with $k$ appended.
--
--   The file introduces the following objects.
--
--   1. **Test vectors in $X_T$.** For nodes $c$ and $s$: the basis vector $b_c=e_c$, the path vector $\gamma_s$, and the cut-path vector $\kappa_s=\gamma_s-e_r$, each regarded as an element of $X_T$ through the dense embedding $c_{00}(I)\subseteq X_T$. Path vectors are unit vectors:
--   $$
--   \|\gamma_s\|_{X_T}=1\qquad\text{for every node } s .
--   $$
--   2. **Test vectors in $X^0_T$.** For a node $c\neq r$, the basis vector $b^0_c=e_c\in X^0_T$, and for any node $s$ the path vector $\kappa^0_s=\gamma_s-e_r\in X^0_T$ (both vanish at the root). The inclusion maps them to the corresponding vectors of $X_T$:
--   $$
--   \iota(b^0_c)=b_c,\qquad \iota(\kappa^0_s)=\kappa_s .
--   $$
--   3. **Children in the sequence tree.** For $u\in\Sigma$, the injective map $\sigma_u:\mathbb{N}\to\Sigma$, $\sigma_u(k)=u^{\frown}k$, enumerating the children of $u$.
--   4. **Nodes and children in the joined tree.** For $h\in\mathbb{N}$ and a finite sequence $u$, the node $\nu_h(u)=(h+1,\,u|_h)$ of $J$, where $u|_h$ consists of the first $h$ entries of $u$ (all of $u$ if $|u|\le h$). If $|u|<h$, the map $\chi_{h,u}:\mathbb{N}\to J$, $\chi_{h,u}(k)=\nu_h(u^{\frown}k)=(h+1,u^{\frown}k)$, is injective; it enumerates the children of the node $(h+1,u)$.
--   5. **A weighted square inequality.** For real numbers $a,t,k,B$ with $k\ge 0$, $B\ge 0$ and $t^2\le kB$,
--   $$
--   (a+t)^2\le (k+1)\,(a^2+B).
--   $$
--
--   These are the test objects for the results that none of the spaces $X_\Sigma$, $X^0_J$ and $X_J$ admits an equivalent asymptotically uniformly convex norm. If $c$ is a child of $s$, then $\gamma_c-\gamma_s=e_c$ and $\kappa_c-\kappa_s=e_c$, so the enumerations $\sigma_u$ and $\chi_{h,u}$ turn path and cut-path vectors into trees of vectors whose successive increments are basis vectors at siblings. The inequality, a weighted form of $(a+t)^2\le(1+k)a^2+(1+1/k)t^2$ that also covers $k=0$, is an elementary step in the energy estimates for trees.
--
--   **Formalization Note** `TreeSpace.basisVector`, `TreeSpace.pathVector` and `TreeSpace.cutPathVector` are the images of `Finsupp.single c 1`, `T.path s` and `T.cutPath s` in `TreeSpace T`, the completion of `TreeVector T`; `pathVector_norm` is the unit-norm statement. `ZeroTreeSpace.basisVector` takes a proof of `c ≠ T.root` as an argument, `ZeroTreeSpace.pathVector s` is `T.cutPath s` in `ZeroTreeSpace T`, and `inclusion_basisVector`, `inclusion_pathVector` are the two inclusion identities. `sequenceChildren` and `joinedChildren` are function embeddings out of the natural numbers; `joinedNode h s` uses the positive integer `h + 1` as the component height and `s.take h` as the label. The inequality is `weighted_square_bound`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/EquivalentNorms.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/EquivalentNorms.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RecursivePotentials mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

open Filter Topology

namespace EquivalentNorm

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : EquivalentNorm E)

end EquivalentNorm

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end FiniteRootedTree

namespace TreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

open UniformSpace

def basisVector (c : ι) : TreeSpace T := (show TreeVector T from Finsupp.single c 1)

def pathVector (s : ι) : TreeSpace T := (show TreeVector T from T.path s)

@[simp] lemma pathVector_norm (s : ι) : ‖pathVector T s‖ = 1 := by
  change ‖(↑(show TreeVector T from T.path s) : TreeSpace T)‖ = 1
  rw [Completion.norm_coe, TreeVector.norm_def]
  exact T.normSum_path s

end

end TreeSpace

def sequenceChildren (s : List ℕ) : ℕ ↪ List ℕ where
  toFun k := s ++ [k]
  inj' := by intro k l h; simpa using h

namespace TreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

open UniformSpace

def cutPathVector (s : ι) : TreeSpace T := (show TreeVector T from T.cutPath s)

end

end TreeSpace

namespace ZeroTreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

open UniformSpace

def basisVector (c : ι) (hc : c ≠ T.root) : ZeroTreeSpace T :=
  (show ZeroTreeVector T from ⟨Finsupp.single c 1, by
    change (Finsupp.single c (1 : ℝ)) T.root = 0
    simp [hc]⟩)

def pathVector (s : ι) : ZeroTreeSpace T :=
  (show ZeroTreeVector T from ⟨T.cutPath s, T.cutPath_root s⟩)

@[simp] lemma inclusion_basisVector (c : ι) (hc : c ≠ T.root) :
    inclusion T (basisVector T c hc) = TreeSpace.basisVector T c := by
  exact inclusion_coe T (show ZeroTreeVector T from ⟨Finsupp.single c 1, by
    change (Finsupp.single c (1 : ℝ)) T.root = 0
    simp [hc]⟩)

@[simp] lemma inclusion_pathVector (s : ι) :
    inclusion T (pathVector T s) = TreeSpace.cutPathVector T s := by
  exact inclusion_coe T (show ZeroTreeVector T from ⟨T.cutPath s, T.cutPath_root s⟩)

end

end ZeroTreeSpace

def joinedNode (h : ℕ) (s : List ℕ) : JoinedNode :=
  some ⟨⟨h + 1, by omega⟩, ⟨s.take h, by change (s.take h).length ≤ h + 1; simp only [List.length_take]; omega⟩⟩

def joinedChildren (h : ℕ) (s : List ℕ) (hs : s.length < h) : ℕ ↪ JoinedNode where
  toFun k := joinedNode h (s ++ [k])
  inj' := by
    intro k l he
    have hsk : (s ++ [k]).length ≤ h := by simp; omega
    have hsl : (s ++ [l]).length ≤ h := by simp; omega
    have hh := congrArg (fun x : JoinedNode => x.map (fun y => y.2.1)) he
    simpa [joinedNode, List.take_of_length_le hsk, List.take_of_length_le hsl] using hh

namespace EquivalentNorm

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : EquivalentNorm E)

end EquivalentNorm

lemma weighted_square_bound {a r k B : ℝ} (hk : 0 ≤ k) (hB : 0 ≤ B)
    (hr : r ^ 2 ≤ k * B) : (a + r) ^ 2 ≤ (k + 1) * (a ^ 2 + B) := by
  by_cases hk0 : k = 0
  · subst k
    have hr0 : r = 0 := by nlinarith [sq_nonneg r]
    simp only [hr0, add_zero, zero_add, one_mul]
    linarith
  · have hkpos : 0 < k := lt_of_le_of_ne hk (Ne.symm hk0)
    have hc : k * (2 * a * r - k * a ^ 2 - B) ≤ 0 := by
      nlinarith [sq_nonneg (k * a - r)]
    have hh : 2 * a * r - k * a ^ 2 - B ≤ 0 :=
      (mul_le_mul_iff_right₀ hkpos).mp (by simpa only [mul_comm, mul_zero] using hc)
    nlinarith

end RecursivePotentials

end OAI


