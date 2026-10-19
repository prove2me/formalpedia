-- Prove2me | Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry
-- name    : OAI_Analysis_RecursivePotentials_ZeroRootGeometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T07:34:12.959332+00:00
-- url     : https://prove2.me/theorems/4eadd0c1-8f2a-4a86-b292-2a5cc2231c27
-- title:
--   Root-path indicators of unit norm, cut paths, and head coordinates on the zero-root tree space
-- statement:
--   This file studies the simplest nonzero vectors of the root-sum tree spaces, the indicators of root paths, and transfers head coordinates to the zero-root tree space.
--
--   **Setting.** A rooted tree $T$ on a node set $I$ (possibly infinite) consists of a root $r\in I$, a parent map $\pi:I\to I$ with $\pi(r)=r$, and a depth function $d:I\to\mathbb{N}$ with $d(r)=0$ and $d(\pi(i))<d(i)$ for $i\neq r$. The children of $a$ are the nodes $c\neq r$ with $\pi(c)=a$, and the ancestors of $s$ form the finite set $A(s)=\{s,\pi(s),\pi^2(s),\dots,r\}$. A function $p:I\to\mathbb{R}$ satisfies the *square-sum condition* if
--   $$
--   \sum_{c\in S}p(c)^2\le p(a)^2\qquad\text{for every node } a \text{ and every finite set } S \text{ of children of } a .
--   $$
--   For a finitely supported $v:I\to\mathbb{R}$, the potentials $(P_v,Q_v)$ are the least pair of nonnegative functions satisfying the square-sum condition with $P_v-Q_v=v$ (computed recursively on the finite subtree formed by the root and the ancestors of the points of the support of $v$, and $0$ elsewhere). The space $c_{00}(I)$ of finitely supported vectors carries the root-sum norm $\|v\|=P_v(r)+Q_v(r)$, with completion $X_T$; $e_c$ denotes the coordinate vector at $c$. The *zero-root space* is $c^0_{00}(I)=\{v\in c_{00}(I): v(r)=0\}$ with the norm $\|v\|_0=P_v(r)$ (equal to $\|v\|/2$ there), $X^0_T$ is its completion, and $\iota:X^0_T\to X_T$ is the continuous extension of the identity map $c^0_{00}(I)\to c_{00}(I)$. For a finite initial set $H$ (containing $r$ and closed under $\pi$), the head projection $\Pi_H v=v\,\mathbf{1}_H$ preserves $c^0_{00}(I)$; its restriction $\Pi^0_H$ and $\Pi_H$ extend to the completions.
--
--   The file introduces the following objects.
--
--   1. **Root-path indicator.** For a node $s$, $\gamma_s\in c_{00}(I)$ is the indicator of the ancestors of $s$,
--   $$
--   \gamma_s(c)=\begin{cases}1, & c\in A(s),\\ 0, & c\notin A(s).\end{cases}
--   $$
--   It is nonnegative, $\gamma_s(r)=1$, and it satisfies the square-sum condition (as does the zero function). Its potentials are explicit,
--   $$
--   P_{\gamma_s}(c)=\gamma_s(c),\qquad Q_{\gamma_s}(c)=0\qquad\text{for every node } c,
--   $$
--   and consequently $\|\gamma_s\|=1$.
--   2. **Cut path.** $\gamma^0_s=\gamma_s-e_r$, the root-path indicator with the root removed. It vanishes at the root, so it lies in the zero-root subspace $c^0_{00}(I)$.
--   3. **Head coordinates on the zero-root space.** For a finite set $H\subseteq I$, $C^0_H=C_H\circ\iota:X^0_T\to\mathbb{R}^H$, where $C_H(x)=(x(s))_{s\in H}$ is the head-coordinate map of $X_T$ and $x\mapsto x(s)$ is the continuous extension to $X_T$ of the coordinate functional $v\mapsto v(s)$.
--
--   Along the way the file proves several auxiliary facts: depth does not increase along ancestors ($c\in A(s)$ implies $d(c)\le d(s)$); two ancestors of $s$ that are different from the root and have the same parent are equal, so a root path contains at most one child of any node; on $c^0_{00}(I)$ the inclusion is the identity and satisfies $\iota\,\Pi^0_H=\Pi_H\,\iota$, and the completed inclusion and projections agree with these maps on finitely supported vectors; and the node set of the joined tree (a root together with all pairs $(h,u)$ where $h\ge 1$ is an integer and $u$ is a finite sequence of natural numbers of length at most $h$) is infinite.
--
--   Root-path indicators are unit vectors whose potentials are known exactly. If $c$ is a child of $s$, then $A(c)=A(s)\cup\{c\}$, so $\gamma_c-\gamma_s=e_c$: walking down the tree along children changes the path vector by coordinate vectors at siblings. This is the source of the trees of vectors used to show that the tree spaces admit no equivalent asymptotically uniformly convex norm. The cut paths play the same role in the zero-root space, and $C^0_H$ is used to describe the tails $\ker \Pi^0_H$ of $X^0_T$ as kernels of finitely many coordinates.
--
--   **Formalization Note** `FiniteRootedTree.path s` is `extend (T.ancestors s) (fun _ => 1)` and `cutPath s` is `path s - Finsupp.single T.root 1`; the square-sum condition is `GlobalUpper`, the potentials statement is `path_fields`, and the norm statement is `normSum_path`. The zero-root space is `ZeroTreeSpace T`, the completion of the kernel of the root coordinate in `TreeVector T`, whose norm is `T.P v T.root`; $C^0_H$ is `ZeroTreeSpace.headCoordinates`. The unnamed instance `Infinite JoinedNode` is witnessed by the injective map sending $n$ to the root of the component of height $n+1$. The remaining entries (`inclusion_apply`, `inclusion_projection`, `inclusion_coe`, `projection_coe`, `path_apply`, `path_nonneg`, `path_root`, `path_upper`, `GlobalUpper.zero`, `cutPath_root`, `depth_le_of_mem_ancestors`, `parent_ancestors_injective`) are the facts listed above.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/ZeroRootGeometry.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/ZeroRootGeometry.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RecursivePotentials mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
namespace OAI

noncomputable section

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

instance : Infinite JoinedNode := by
  apply Infinite.of_injective (fun n : ℕ => (some ⟨⟨n + 1, by omega⟩, ⟨[], by simp⟩⟩ : JoinedNode))
  intro n m h
  have he := congrArg (fun x : JoinedNode => x.map (fun y => y.1.val)) h
  simpa using he

namespace ZeroTreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

@[simp] lemma inclusion_apply (v : ZeroTreeVector T) : inclusion T v = toTree T v := rfl

@[simp] lemma inclusion_projection (H : Finset ι) (hH : T.Initial H) (v : ZeroTreeVector T) :
    inclusion T (projection T H hH v) = TreeVector.projection T H hH (inclusion T v) := rfl

end ZeroTreeVector

namespace ZeroTreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

@[simp] lemma inclusion_coe (v : ZeroTreeVector T) :
    inclusion T (v : ZeroTreeSpace T) = (ZeroTreeVector.inclusion T v : TreeSpace T) :=
  ContinuousLinearMap.completion_apply_coe _ v

@[simp] lemma projection_coe (H : Finset ι) (hH : T.Initial H) (v : ZeroTreeVector T) :
    projection T H hH (v : ZeroTreeSpace T) =
      (ZeroTreeVector.projection T H hH v : ZeroTreeSpace T) :=
  ContinuousLinearMap.completion_apply_coe _ v

end ZeroTreeSpace

namespace ZeroTreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end ZeroTreeVector

namespace ZeroTreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

def headCoordinates (H : Finset ι) : ZeroTreeSpace T →L[ℝ] (H → ℝ) :=
  (TreeSpace.headCoordinates T H).comp (inclusion T)

end ZeroTreeSpace

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma depth_le_of_mem_ancestors (s : ι) {c : ι} (hc : c ∈ T.ancestors s) :
    T.depth c ≤ T.depth s := by
  rw [ancestors] at hc
  split_ifs at hc with hs
  · have he := Finset.mem_singleton.mp hc
    subst c
    exact le_rfl
  · rcases Finset.mem_insert.mp hc with rfl | hc
    · exact le_rfl
    · exact (depth_le_of_mem_ancestors (T.parent s) hc).trans (T.parent_depth s hs).le
termination_by T.depth s

decreasing_by exact T.parent_depth s hs

lemma parent_ancestors_injective (s : ι) {a b : ι} (ha : a ∈ T.ancestors s)
    (hb : b ∈ T.ancestors s) (ha0 : a ≠ T.root) (hb0 : b ≠ T.root)
    (he : T.parent a = T.parent b) : a = b := by
  rw [ancestors] at ha hb
  split_ifs at ha hb with hs
  · exact (Finset.mem_singleton.mp ha).trans (Finset.mem_singleton.mp hb).symm
  · rcases Finset.mem_insert.mp ha with rfl | ha
    · rcases Finset.mem_insert.mp hb with rfl | hb
      · rfl
      · have h₁ := T.depth_le_of_mem_ancestors (T.parent a) hb
        have h₂ := T.parent_depth b hb0
        rw [he] at h₁
        omega
    · rcases Finset.mem_insert.mp hb with rfl | hb
      · have h₁ := T.depth_le_of_mem_ancestors (T.parent b) ha
        have h₂ := T.parent_depth a ha0
        rw [← he] at h₁
        omega
      · exact parent_ancestors_injective (T.parent s) ha hb ha0 hb0 he
termination_by T.depth s

decreasing_by exact T.parent_depth s hs

noncomputable def path (s : ι) : ι →₀ ℝ := extend (T.ancestors s) (fun _ => 1)

lemma path_apply (s c : ι) : T.path s c = if c ∈ T.ancestors s then 1 else 0 := by
  by_cases hc : c ∈ T.ancestors s
  · rw [path, extend_mem _ _ hc, ite_eq_left hc]
  · rw [path, extend_not_mem _ _ hc, ite_eq_right hc]

lemma path_nonneg (s c : ι) : 0 ≤ T.path s c := by
  rw [path_apply]
  split_ifs <;> norm_num

lemma path_root (s : ι) : T.path s T.root = 1 := by
  rw [path_apply, ite_eq_left (T.root_mem_ancestors s)]

lemma path_upper (s : ι) : T.GlobalUpper (T.path s) := by
  intro a S hS
  by_cases ha : a ∈ T.ancestors s
  · have hcard : (S.filter (fun c => c ∈ T.ancestors s)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro c hc d hd
      obtain ⟨hcS, hcA⟩ := Finset.mem_filter.mp hc
      obtain ⟨hdS, hdA⟩ := Finset.mem_filter.mp hd
      exact T.parent_ancestors_injective s hcA hdA (hS c hcS).1 (hS d hdS).1
        ((hS c hcS).2.trans (hS d hdS).2.symm)
    calc
      ∑ c ∈ S, T.path s c ^ 2 = ∑ c ∈ S.filter (fun c => c ∈ T.ancestors s), (1 : ℝ) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro c hc
        rw [path_apply]
        split_ifs <;> norm_num
      _ = ((S.filter (fun c => c ∈ T.ancestors s)).card : ℝ) := by simp
      _ ≤ 1 := by exact_mod_cast hcard
      _ = T.path s a ^ 2 := by rw [path_apply, ite_eq_left ha]; norm_num
  · have hz : ∑ c ∈ S, T.path s c ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro c hc
      have hcA : c ∉ T.ancestors s := by
        intro h
        have hpar := T.ancestors_parent_closed s h
        rw [(hS c hc).2] at hpar
        exact ha hpar
      rw [path_apply, ite_eq_right hcA]
      norm_num
    rw [hz]
    exact sq_nonneg _

lemma GlobalUpper.zero {ι : Type uIndex} [DecidableEq ι] (T : FiniteRootedTree ι) :
    T.GlobalUpper (0 : ι → ℝ) := by
  intro s S hS
  simp

theorem path_fields (s c : ι) : T.P (T.path s) c = T.path s c ∧ T.Q (T.path s) c = 0 := by
  have h := T.potentials_minimal (T.path s) (T.path s) 0 (T.path_nonneg s)
    (fun _ => le_rfl) (fun _ => sub_zero _) (T.path_upper s) (GlobalUpper.zero T) c
  have hq : T.Q (T.path s) c = 0 := le_antisymm h.2 (T.Q_nonneg _ _)
  have hd := T.P_sub_Q (T.path s) c
  rw [hq, sub_zero] at hd
  exact ⟨hd, hq⟩

lemma normSum_path (s : ι) : T.normSum (T.path s) = 1 := by
  unfold normSum
  rw [(T.path_fields s T.root).1, (T.path_fields s T.root).2, T.path_root, add_zero]

noncomputable def cutPath (s : ι) : ι →₀ ℝ := T.path s - Finsupp.single T.root 1

lemma cutPath_root (s : ι) : T.cutPath s T.root = 0 := by
  simp [cutPath, T.path_root]

end FiniteRootedTree

end RecursivePotentials

end

end OAI


