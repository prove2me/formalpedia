-- Prove2me | Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
-- name    : OAI_Analysis_RecursivePotentials_TreeGeometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T07:32:51.216126+00:00
-- url     : https://prove2.me/theorems/bbb90603-65ed-4931-a1c6-c7aebf5a39e6
-- title:
--   Root-sum tree norms: midpoint defects, Lipschitz potentials, head coordinates and finite-codimensional tails
-- statement:
--   This file sets up the basic geometry of the root-sum tree spaces: auxiliary quantities for convexity estimates, the continuity of the tree potentials, and a description of the tail subspaces through finitely many coordinates.
--
--   **Setting.** A rooted tree $T$ on a node set $I$ (finite or infinite) consists of a root $r\in I$, a parent map $\pi:I\to I$ with $\pi(r)=r$, and a depth function $d:I\to\mathbb{N}$ with $d(r)=0$ and $d(\pi(i))<d(i)$ for $i\neq r$. The children of a node $s$ are the nodes $c\neq r$ with $\pi(c)=s$; the ancestors of $s$ are $s,\pi(s),\pi^2(s),\dots,r$; and a finite set $H\subseteq I$ is *initial* if $r\in H$ and $\pi(H)\subseteq H$. For $x,a,b\in\mathbb{R}$ the *least pair* is $\lambda(x,a,b)=(\max\{a,x+b\},\ \max\{b,a-x\})$, the smallest pair $(p,q)$ with $p\ge a$, $q\ge b$ and $p-q=x$. If $I$ is finite and $v:I\to\mathbb{R}$, the *fields* $(p_s(v),q_s(v))_{s\in I}$ are defined recursively from the leaves upward by
--
--   $$
--   (p_s(v),q_s(v))=\lambda\Bigl(v(s),\ \Bigl(\sum_{c\ \text{child of}\ s}p_c(v)^2\Bigr)^{1/2},\ \Bigl(\sum_{c\ \text{child of}\ s}q_c(v)^2\Bigr)^{1/2}\Bigr).
--   $$
--
--   For a finitely supported $v:I\to\mathbb{R}$ on an arbitrary tree, the *potentials* $P_v(s)$ and $Q_v(s)$ are the fields of $v$ computed on the finite subtree consisting of the root and all ancestors of points of the support of $v$, and are $0$ at nodes outside this subtree. The space $c_{00}(I)$ of finitely supported vectors carries the *root-sum norm* $\|v\|=P_v(r)+Q_v(r)$, and $X_T$ denotes its completion. For initial $H$ the head projection $\Pi_H v=v\,\mathbf{1}_H$ does not increase the norm and extends continuously to $X_T$; its kernel $X_T^{H}=\ker \Pi_H$ is the *tail* beyond $H$. The coordinate functionals $v\mapsto v(s)$ satisfy $|v(s)|\le\|v\|$ and extend to continuous linear functionals $x\mapsto x(s)$ on $X_T$.
--
--   The file introduces the following objects.
--
--   1. **Root sum and midpoint defect (finite trees).** For finite $I$, $v,x,z:I\to\mathbb{R}$ and $s\in I$,
--   $$
--   \rho_T(v)=p_r(v)+q_r(v),\qquad \delta_s(x,z)=\frac{p_s(x+z)+p_s(x-z)}{2}-p_s(x).
--   $$
--   The fields of the zero vector vanish and $(p_s(-v),q_s(-v))=(q_s(v),p_s(v))$ for every $s$; consequently $\rho_T(0)=0$ and $\rho_T(-v)=\rho_T(v)$.
--   2. **Mean excess.** For $x,z\in c_{00}(I)$, and likewise for $x,z\in X_T$,
--   $$
--   \mathcal{E}(x,z)=\frac{\|x+z\|+\|x-z\|}{2}-\|x\|;
--   $$
--   the two versions agree on finitely supported vectors.
--   3. **Extension from a head and head coordinates.** For a finite set $H\subseteq I$, the map $E_H:\mathbb{R}^H\to c_{00}(I)$ extends a function on $H$ by zero, $E_H(f)(s)=f(s)$ for $s\in H$ and $E_H(f)(s)=0$ otherwise; it is linear and continuous. The head-coordinate map $C_H:X_T\to\mathbb{R}^H$, $C_H(x)=(x(s))_{s\in H}$, is continuous and linear.
--   4. **Closed finite-codimensional subspaces.** For a real normed space $E$, these are the closed linear subspaces $F\subseteq E$ with $E/F$ finite-dimensional. The whole space $E$ is one (so the family is never empty), and for every initial $H$ the tail $X_T^H$ is one.
--
--   The file also proves the basic facts that make these objects usable:
--
--   - the least pair is tight: the first coordinate of $\lambda(x,a,b)$ equals $a$ or its second coordinate equals $b$; on a finite tree $\sum_{s\in I}\sum_{c\ \text{child of}\ s}e(c)=\sum_{c\neq r}e(c)$ for every $e:I\to\mathbb{R}$; and the root is an ancestor of every node;
--   - *independence of the head*: if $H$ is initial and the support of $v\in c_{00}(I)$ is contained in $H$, then for every $s\in H$ the potentials $P_v(s)$ and $Q_v(s)$ coincide with the fields of the restriction $v|_H$ computed on the restricted tree $T|_H$;
--   - for $v,w\in c_{00}(I)$ and every node $s$: $P_v(s)\le\|v\|$, $Q_v(s)\le\|v\|$, $|P_v(s)-P_w(s)|\le\|v-w\|$ and $|Q_v(s)-Q_w(s)|\le\|v-w\|$. Hence $v\mapsto P_v(s)$ and $v\mapsto Q_v(s)$ are $1$-Lipschitz, and their continuous extensions $P_s,Q_s:X_T\to\mathbb{R}$, like the extended coordinates and head projections, agree with the original maps on $c_{00}(I)$;
--   - for initial $H$ and $x\in X_T$: $(\Pi_H x)(s)=x(s)$ if $s\in H$ and $(\Pi_H x)(s)=0$ otherwise; $\Pi_H x=E_H(C_H x)$; the tail $X_T^H$ equals $\ker C_H$ and is closed; and $X_T/X_T^H$ is finite-dimensional.
--
--   These are the working tools for the convexity estimates in $X_T$. The mean excess $\mathcal{E}(x,z)$ is the quantity that the cubic estimates bound from below when $x$ is supported on a head and $z$ lies in the corresponding tail, and the node-wise defects $\delta_s$ and root sums $\rho_T$ are the quantities through which it is analysed on finite trees. Head independence and the Lipschitz bounds let computations on finite heads pass to the completion, and the tails, packaged as closed finite-codimensional subspaces, serve as the subspaces in the supremum that defines the averaged asymptotic modulus of $X_T$ when this modulus is bounded from below.
--
--   **Formalization Note** Despite its name, `FiniteRootedTree ι` does not require `ι` to be finite; `rootSum` and `defect` are defined only under `[Fintype ι]` because they use `fields`, while everything else needs only `DecidableEq ι`. $X_T$ is `TreeSpace T`, the `UniformSpace.Completion` of `TreeVector T` (finitely supported functions with norm `normSum`), and $P_s,Q_s$ are obtained by `Completion.extension`. The mean excess is defined twice, as `FiniteRootedTree.meanExcess` on vectors and `TreeSpace.meanExcess` on the completion, linked by `meanExcess_coe`. $E_H$ is `TreeVector.ofHeadLinear` / `TreeVector.ofHead` (continuity is automatic on the finite-dimensional domain), $C_H$ is `TreeSpace.headCoordinates`, and the closed finite-codimensional subspaces are the structure `CofiniteSubspace`, with `CofiniteSubspace.top`, the derived `Nonempty` instance, and `TreeSpace.cofiniteTail`. The listed facts are `leastPair_tight`, `sum_children`, `root_mem_ancestors`, `fields_zero`, `fields_neg`, `potentials_on_head`, `potentials_le_normSum`, `potentials_lipschitz`, `lipschitz_P`, `lipschitz_Q`, `coordinate_projection`, `projection_reconstructs`, `tail_eq_coordinate_kernel`, `tail_closed` and `tail_finite_codimension`; the remaining entries are simp lemmas.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/TreeGeometry.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/TreeGeometry.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RecursivePotentials mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

noncomputable section

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

lemma leastPair_tight (x a b : ℝ) :
    (leastPair x a b).1 = a ∨ (leastPair x a b).2 = b := by
  rcases le_total (x + b) a with h | h
  · exact Or.inl (max_eq_left h)
  · exact Or.inr (max_eq_left (by linarith))

namespace FiniteRootedTree

section

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι)

lemma sum_children (e : ι → ℝ) :
    ∑ s, ∑ c ∈ T.children s, e c = ∑ c ∈ Finset.univ.erase T.root, e c := by
  classical
  simp only [children, Finset.sum_filter]
  rw [Finset.sum_comm]
  calc
    (∑ c, ∑ s, if c ≠ T.root ∧ T.parent c = s then e c else 0) =
        ∑ c, if c = T.root then 0 else e c := by
      apply Finset.sum_congr rfl
      intro c hc
      by_cases h : c = T.root
      · simp [h]
      · simp [h]
    _ = ∑ c ∈ Finset.univ.erase T.root, e c := by
      have hset : Finset.univ.erase T.root =
          Finset.univ.filter (fun c => c ≠ T.root) := by
        ext c
        simp
      rw [hset, Finset.sum_filter]
      simp only [ite_not]

lemma fields_zero (s : ι) : T.fields (fun _ => 0) s = (0, 0) := by
  have h := T.fields_minimal (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => by ring)
    (fun _ => by simp) (fun _ => by simp) s
  exact Prod.ext (le_antisymm h.1 (T.fields_nonneg _ s).1)
    (le_antisymm h.2 (T.fields_nonneg _ s).2)

lemma fields_neg (v : ι → ℝ) (s : ι) :
    T.fields (-v) s = ((T.fields v s).2, (T.fields v s).1) := by
  have h₁ := T.fields_minimal (-v) (fun t => (T.fields v t).2) (fun t => (T.fields v t).1)
    (fun t => (T.fields_nonneg v t).2) (fun t => (T.fields_nonneg v t).1)
    (fun t => by simp only [Pi.neg_apply]; linarith [T.fields_difference v t])
    (T.fields_upper v).2 (T.fields_upper v).1 s
  have h₂ := T.fields_minimal v (fun t => (T.fields (-v) t).2) (fun t => (T.fields (-v) t).1)
    (fun t => (T.fields_nonneg (-v) t).2) (fun t => (T.fields_nonneg (-v) t).1)
    (fun t => by have := T.fields_difference (-v) t; simp only [Pi.neg_apply] at this; linarith)
    (T.fields_upper (-v)).2 (T.fields_upper (-v)).1 s
  exact Prod.ext (le_antisymm h₁.1 h₂.2) (le_antisymm h₁.2 h₂.1)

noncomputable def rootSum (v : ι → ℝ) : ℝ :=
  (T.fields v T.root).1 + (T.fields v T.root).2

@[simp] lemma rootSum_zero : T.rootSum (fun _ => 0) = 0 := by
  simp [rootSum, T.fields_zero]

@[simp] lemma rootSum_neg (v : ι → ℝ) : T.rootSum (-v) = T.rootSum v := by
  simp [rootSum, T.fields_neg, add_comm]

noncomputable def defect (x z : ι → ℝ) (s : ι) : ℝ :=
  ((T.fields (x + z) s).1 + (T.fields (x - z) s).1) / 2 - (T.fields x s).1

end

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma root_mem_ancestors (s : ι) : T.root ∈ T.ancestors s := by
  rw [ancestors]
  split_ifs with hs
  · simp [hs]
  · exact Finset.mem_insert_of_mem (root_mem_ancestors (T.parent s))
termination_by T.depth s
decreasing_by exact T.parent_depth s hs

theorem potentials_on_head (v : ι →₀ ℝ) (H : Finset ι) (hH : T.Initial H)
    (hv : v.support ⊆ H) (s : H) :
    T.P v s.1 = ((T.restrict H hH).fields (fun c => v c.1) s).1 ∧
    T.Q v s.1 = ((T.restrict H hH).fields (fun c => v c.1) s).2 := by
  let U := T.restrict H hH
  let p : ι →₀ ℝ := extend H (fun c => (U.fields (fun c => v c.1) c).1)
  let q : ι →₀ ℝ := extend H (fun c => (U.fields (fun c => v c.1) c).2)
  have hdiff : ∀ c, p c - q c = v c := by
    intro c
    by_cases hc : c ∈ H
    · simp only [p, q, extend_mem _ _ hc]
      exact U.fields_difference _ _
    · have hv0 : v c = 0 := Finsupp.notMem_support_iff.mp (fun h => hc (hv h))
      simp only [p, q, extend_not_mem _ _ hc, hv0, sub_zero]
  have h₁ := T.potentials_minimal v p q
    (extend_nonneg _ _ (fun c => (U.fields_nonneg _ c).1))
    (extend_nonneg _ _ (fun c => (U.fields_nonneg _ c).2)) hdiff
    (T.extend_upper _ _ _ (U.fields_upper _).1)
    (T.extend_upper _ _ _ (U.fields_upper _).2) s.1
  have h₂ := U.fields_minimal (fun c => v c.1) (fun c => T.P v c.1)
    (fun c => T.Q v c.1) (fun c => T.P_nonneg v c.1) (fun c => T.Q_nonneg v c.1)
    (fun c => T.P_sub_Q v c.1) ((T.P_upper v).restrict T H hH)
    ((T.Q_upper v).restrict T H hH) s
  simp only [p, q, extend_coe] at h₁
  exact ⟨le_antisymm h₁.1 h₂.1, le_antisymm h₁.2 h₂.2⟩

lemma potentials_le_normSum (v : ι →₀ ℝ) (s : ι) :
    T.P v s ≤ T.normSum v ∧ T.Q v s ≤ T.normSum v := by
  have hp := (T.P_upper v).le_root T (T.P_nonneg v) s
  have hq := (T.Q_upper v).le_root T (T.Q_nonneg v) s
  have hp0 := T.P_nonneg v T.root
  have hq0 := T.Q_nonneg v T.root
  unfold normSum
  constructor <;> linarith

lemma potentials_lipschitz (v w : ι →₀ ℝ) (s : ι) :
    |T.P v s - T.P w s| ≤ T.normSum (v - w) ∧
    |T.Q v s - T.Q w s| ≤ T.normSum (v - w) := by
  have h₁ := T.potentials_add_le (v - w) w s
  have h₂ := T.potentials_add_le (w - v) v s
  rw [sub_add_cancel] at h₁ h₂
  have hk₁ := T.potentials_le_normSum (v - w) s
  have hk₂ := T.potentials_le_normSum (w - v) s
  have hn : T.normSum (w - v) = T.normSum (v - w) := by
    rw [← neg_sub v w, T.normSum_neg]
  rw [hn] at hk₂
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2, hk₁.1, hk₁.2, hk₂.1, hk₂.2]

end FiniteRootedTree

namespace TreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma norm_def (v : TreeVector T) : ‖v‖ = T.normSum v := rfl

@[simp] lemma coordinate_apply (s : ι) (v : TreeVector T) : coordinate T s v = v s := rfl

lemma lipschitz_P (s : ι) : LipschitzWith 1 (fun v : TreeVector T => T.P v s) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul, norm_def]
  exact (T.potentials_lipschitz v w s).1

lemma lipschitz_Q (s : ι) : LipschitzWith 1 (fun v : TreeVector T => T.Q v s) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul, norm_def]
  exact (T.potentials_lipschitz v w s).2

@[simp] lemma projection_apply (H : Finset ι) (hH : T.Initial H) (v : TreeVector T) :
    projection T H hH v = T.projectHead H v := rfl

end TreeVector

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

@[simp] lemma coordinate_coe (s : ι) (v : TreeVector T) :
    coordinate T s (v : TreeSpace T) = v s := by
  exact ContinuousLinearMap.fromCompletion_apply_coe _ v

@[simp] lemma P_coe (s : ι) (v : TreeVector T) : P T s (v : TreeSpace T) = T.P v s :=
  Completion.extension_coe (TreeVector.lipschitz_P T s).uniformContinuous v

@[simp] lemma Q_coe (s : ι) (v : TreeVector T) : Q T s (v : TreeSpace T) = T.Q v s :=
  Completion.extension_coe (TreeVector.lipschitz_Q T s).uniformContinuous v

@[simp] lemma projection_coe (H : Finset ι) (hH : T.Initial H) (v : TreeVector T) :
    projection T H hH (v : TreeSpace T) = (TreeVector.projection T H hH v : TreeSpace T) :=
  ContinuousLinearMap.completion_apply_coe _ v

lemma coordinate_projection (H : Finset ι) (hH : T.Initial H) (s : ι) (x : TreeSpace T) :
    coordinate T s (projection T H hH x) = if s ∈ H then coordinate T s x else 0 := by
  induction x using Completion.induction_on with
  | hp =>
      by_cases hs : s ∈ H
      · simp only [ite_eq_left hs]
        exact isClosed_eq (by fun_prop) (by fun_prop)
      · simp only [ite_eq_right hs]
        exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih v =>
      rw [projection_coe, coordinate_coe, coordinate_coe]
      exact T.projectHead_apply H v s

lemma tail_closed (H : Finset ι) (hH : T.Initial H) : IsClosed (tail T H hH : Set (TreeSpace T)) :=
  (projection T H hH).isClosed_ker

end TreeSpace

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

noncomputable def meanExcess (x z : ι →₀ ℝ) : ℝ :=
  (T.normSum (x + z) + T.normSum (x - z)) / 2 - T.normSum x

end FiniteRootedTree

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

def meanExcess (x z : TreeSpace T) : ℝ := (‖x + z‖ + ‖x - z‖) / 2 - ‖x‖

@[simp] lemma meanExcess_coe (x z : TreeVector T) :
    meanExcess T (x : TreeSpace T) (z : TreeSpace T) = T.meanExcess x z := by
  simp only [meanExcess, ← Completion.coe_add, ← Completion.coe_sub,
    Completion.norm_coe, TreeVector.norm_def]
  rfl

end TreeSpace

namespace TreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

def ofHeadLinear (H : Finset ι) : (H → ℝ) →ₗ[ℝ] TreeVector T where
  toFun := FiniteRootedTree.extend H
  map_add' f g := by
    change FiniteRootedTree.extend H (f + g) = FiniteRootedTree.extend H f + FiniteRootedTree.extend H g
    ext s
    by_cases hs : s ∈ H
    · simp [FiniteRootedTree.extend, hs]
    · simp [FiniteRootedTree.extend, hs]
  map_smul' a f := by
    change FiniteRootedTree.extend H (a • f) = a • FiniteRootedTree.extend H f
    ext s
    by_cases hs : s ∈ H
    · simp [FiniteRootedTree.extend, hs]
    · simp [FiniteRootedTree.extend, hs]

def ofHead (H : Finset ι) : (H → ℝ) →L[ℝ] TreeVector T :=
  (ofHeadLinear T H).toContinuousLinearMap

lemma ofHead_apply (H : Finset ι) (f : H → ℝ) (s : ι) :
    ofHead T H f s = if hs : s ∈ H then f ⟨s, hs⟩ else 0 := by
  change FiniteRootedTree.extend H f s = _
  simp [FiniteRootedTree.extend]

end TreeVector

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

def headCoordinates (H : Finset ι) : TreeSpace T →L[ℝ] (H → ℝ) :=
  ContinuousLinearMap.pi (fun s : H => coordinate T s.1)

@[simp] lemma headCoordinates_apply (H : Finset ι) (x : TreeSpace T) (s : H) :
    headCoordinates T H x s = coordinate T s.1 x := rfl

theorem projection_reconstructs (H : Finset ι) (hH : T.Initial H) (x : TreeSpace T) :
    projection T H hH x = ((TreeVector.ofHead T H (headCoordinates T H x)) : TreeSpace T) := by
  induction x using Completion.induction_on with
  | hp =>
      apply isClosed_eq
      · exact (projection T H hH).continuous
      · exact ((Completion.toComplL : TreeVector T →L[ℝ] TreeSpace T).comp
          ((TreeVector.ofHead T H).comp (headCoordinates T H))).continuous
  | ih v =>
      rw [projection_coe]
      apply congrArg ((↑) : TreeVector T → TreeSpace T)
      apply Finsupp.ext
      intro s
      change T.projectHead H v s = TreeVector.ofHead T H (headCoordinates T H (v : TreeSpace T)) s
      rw [TreeVector.ofHead_apply]
      have hp := T.projectHead_apply H (show ι →₀ ℝ from v) s
      rw [hp]
      by_cases hs : s ∈ H
      · simp only [ite_eq_left hs, dite_eq_left hs, headCoordinates_apply, coordinate_coe]
      · simp only [ite_eq_right hs, dite_eq_right hs]

lemma tail_eq_coordinate_kernel (H : Finset ι) (hH : T.Initial H) :
    tail T H hH = (headCoordinates T H).ker := by
  ext x
  constructor
  · intro hx
    change headCoordinates T H x = 0
    ext s
    have hz : projection T H hH x = 0 := hx
    have he := coordinate_projection T H hH s.1 x
    rw [hz, map_zero, ite_eq_left s.2] at he
    exact he.symm
  · intro hx
    change projection T H hH x = 0
    rw [projection_reconstructs]
    have hz : headCoordinates T H x = 0 := hx
    rw [hz, map_zero, Completion.coe_zero]

theorem tail_finite_codimension (H : Finset ι) (hH : T.Initial H) :
    Module.Finite ℝ (TreeSpace T ⧸ tail T H hH) := by
  rw [tail_eq_coordinate_kernel]
  exact Submodule.CoFG.ker (headCoordinates T H).toLinearMap

end TreeSpace

namespace CofiniteSubspace

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]

def top : CofiniteSubspace E where
  space := ⊤
  closed := isClosed_univ
  finiteQuotient := inferInstance

instance : Nonempty (CofiniteSubspace E) := ⟨top⟩

end CofiniteSubspace

section Moduli

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Moduli

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

def cofiniteTail (H : Finset ι) (hH : T.Initial H) : CofiniteSubspace (TreeSpace T) where
  space := tail T H hH
  closed := tail_closed T H hH
  finiteQuotient := tail_finite_codimension T H hH

end TreeSpace

end RecursivePotentials

end

end OAI


