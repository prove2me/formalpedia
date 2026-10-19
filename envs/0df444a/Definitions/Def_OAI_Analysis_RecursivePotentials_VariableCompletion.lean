-- Prove2me | Definitions.Def_OAI_Analysis_RecursivePotentials_VariableCompletion
-- name    : OAI_Analysis_RecursivePotentials_VariableCompletion
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T07:41:52.559412+00:00
-- url     : https://prove2.me/theorems/9d94d20c-51c2-4301-9955-88a069571e4d
-- title:
--   Head projections, tails and head coordinates on completed $\ell^p$-aggregation tree spaces
-- statement:
--   This file equips the $\ell^p$-aggregation tree spaces with projections onto initial subtrees, their tails, and the maps between head data and vectors, after proving that the potentials are Lipschitz in the norm.
--
--   **Setting.** Let $T$ be a rooted tree on an index set $I$ (possibly infinite): a root $r$, a parent map $\pi:I\to I$ with $\pi(r)=r$, and a depth $d:I\to\mathbb N$ with $d(r)=0$ and $d(\pi(s))<d(s)$ for $s\neq r$. Let $p\ge1$ be real. For a finitely supported $v:I\to\mathbb R$ the $\ell^p$-potentials $(P_v,Q_v)$ form the least pair of nonnegative functions on $I$ with $P_v-Q_v=v$ such that, for every node $s$ and every finite set $S$ of children of $s$ (nodes $c\neq r$ with $\pi(c)=s$),
--
--   $$
--   \Big(\sum_{c\in S}P_v(c)^p\Big)^{1/p}\le P_v(s),\qquad \Big(\sum_{c\in S}Q_v(c)^p\Big)^{1/p}\le Q_v(s).
--   $$
--
--   On the ancestor closure of the support of $v$ they are given by the recursion $P_v(s)=\max(A_s,\,v(s)+B_s)$, $Q_v(s)=\max(B_s,\,-v(s)+A_s)$, with $A_s,B_s$ the $\ell^p$-norms of the values of $P_v,Q_v$ at the children of $s$, and they vanish elsewhere. The aggregation norm is $\|v\|_{T,p}=P_v(r)+Q_v(r)$, and the aggregation space $Y_{T,p}$ is the completion of the finitely supported vectors in this norm. It carries the continuous coordinate functionals $x\mapsto x(s)$ and the potentials $P_s,Q_s:Y_{T,p}\to\mathbb R$, defined as the extensions of $v\mapsto P_v(s)$ and $v\mapsto Q_v(s)$. A finite set $H\subseteq I$ is initial if $r\in H$ and $\pi(s)\in H$ for all $s\in H$.
--
--   The file first proves, for finitely supported $v,w$ and every node $s$, that $P_v(s)\le\|v\|_{T,p}$ and $Q_v(s)\le\|v\|_{T,p}$, and that the potentials are $1$-Lipschitz:
--   $$
--   |P_v(s)-P_w(s)|\le\|v-w\|_{T,p},\qquad |Q_v(s)-Q_w(s)|\le\|v-w\|_{T,p}.
--   $$
--   Consequently the extended potentials and coordinates on $Y_{T,p}$ agree with $P_v(s)$, $Q_v(s)$ and $v(s)$ on finitely supported vectors.
--
--   1. **Head truncation.** For a finite set $H$ and finitely supported $v$, $\mathbf 1_Hv$ is the vector equal to $v(s)$ for $s\in H$ and $0$ otherwise. If $H$ is initial, then $\|\mathbf 1_Hv\|_{T,p}\le\|v\|_{T,p}$.
--
--   2. **Head projection on vectors.** The linear map $v\mapsto\mathbf 1_Hv$ on finitely supported vectors; for initial $H$ it is a continuous linear operator of norm at most $1$.
--
--   3. **Head projection on the completion.** For initial $H$, $\Pi_H:Y_{T,p}\to Y_{T,p}$ is the continuous extension of $v\mapsto\mathbf 1_Hv$; on finitely supported vectors it is the truncation.
--
--   4. **Tail.** For initial $H$, the tail is the closed subspace $\ker\Pi_H\subseteq Y_{T,p}$.
--
--   5. **Vectors from head data.** For a finite set $H$, the map $\mathbb R^H\to\{\text{finitely supported vectors}\}$ that extends $f:H\to\mathbb R$ by zero outside $H$, as a linear map and as a continuous linear map (continuity is automatic because $\mathbb R^H$ is finite-dimensional).
--
--   6. **Head coordinates.** For a finite set $H$, the continuous linear map $Y_{T,p}\to\mathbb R^H$, $x\mapsto(x(s))_{s\in H}$.
--
--   These maps give the finite-dimensional decomposition behind the completion statements for the aggregation spaces: in the subsequent development $\Pi_H$ is shown to be a contractive idempotent projection onto the vectors supported in $H$, whose kernel is cut out by the head coordinates and has finite codimension, while the Lipschitz estimates let the potentials pass continuously to the completion. They are used for the variable-exponent spaces built from the component trees with exponents $1+1/h$, where stability estimates proved on finite trees are transferred to the completed spaces.
--
--   **Formalization Note** The exponent is a `ChildExponent` (a real number at least $1$). Finitely supported vectors with the aggregation norm form `AggregationVector T e`, whose norm is `VariableTree.normSum T e`, and $Y_{T,p}$ is `AggregationSpace T e`, the `UniformSpace.Completion`; its potentials `AggregationSpace.P`, `AggregationSpace.Q` are `Completion.extension`s, which agree with the finite potentials by `P_coe`, `Q_coe` because of the Lipschitz lemmas `lipschitz_P`, `lipschitz_Q` (from `potentials_le_normSum` and `potentials_lipschitz`). Initial sets are `T.Initial H`. Lean names: `VariableTree.projectHead` (which takes the tree as an unused argument) with `projectHead_bound`; `AggregationVector.projectionLinear`, `AggregationVector.projection`; `AggregationSpace.projection`, `AggregationSpace.tail`; `AggregationVector.ofHeadLinear`, `AggregationVector.ofHead`; `AggregationSpace.headCoordinates`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/VariableCompletion.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/VariableCompletion.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
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

namespace VariableTree

open FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

lemma potentials_le_normSum (v : ι →₀ ℝ) (s : ι) :
    P T e v s ≤ normSum T e v ∧ Q T e v s ≤ normSum T e v := by
  have hp := (P_upper T e v).le_root T e (P_nonneg T e v) s
  have hq := (Q_upper T e v).le_root T e (Q_nonneg T e v) s
  have hp0 := P_nonneg T e v T.root
  have hq0 := Q_nonneg T e v T.root
  unfold normSum
  constructor <;> linarith

lemma potentials_lipschitz (v w : ι →₀ ℝ) (s : ι) :
    |P T e v s - P T e w s| ≤ normSum T e (v - w) ∧
    |Q T e v s - Q T e w s| ≤ normSum T e (v - w) := by
  have h₁ := potentials_add_le T e (v - w) w s
  have h₂ := potentials_add_le T e (w - v) v s
  rw [sub_add_cancel] at h₁ h₂
  have hk₁ := potentials_le_normSum T e (v - w) s
  have hk₂ := potentials_le_normSum T e (w - v) s
  have hn : normSum T e (w - v) = normSum T e (v - w) := by
    rw [← neg_sub v w, normSum_neg T e]
  rw [hn] at hk₂
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2, hk₁.1, hk₁.2, hk₂.1, hk₂.2]

def projectHead (_T : FiniteRootedTree ι) (H : Finset ι) (v : ι →₀ ℝ) : ι →₀ ℝ := v.filter (· ∈ H)

lemma projectHead_apply (H : Finset ι) (v : ι →₀ ℝ) (s : ι) :
    projectHead T H v s = if s ∈ H then v s else 0 := Finsupp.filter_apply _ _ _

lemma projectHead_bound (H : Finset ι) (hH : T.Initial H) (v : ι →₀ ℝ) :
    normSum T e (projectHead T H v) ≤ normSum T e v := by
  let p := extend H (fun s => P T e v s.1)
  let q := extend H (fun s => Q T e v s.1)
  have hdiff : ∀ s, p s - q s = projectHead T H v s := by
    intro s
    rw [projectHead_apply T]
    by_cases hs : s ∈ H
    · simp only [p, q, extend_mem _ _ hs, ite_eq_left hs, P_sub_Q T e]
    · simp only [p, q, extend_not_mem _ _ hs, ite_eq_right hs, sub_zero]
  have h := potentials_minimal T e _ p q
    (extend_nonneg _ _ (fun s => P_nonneg T e v s.1))
    (extend_nonneg _ _ (fun s => Q_nonneg T e v s.1)) hdiff
    (extend_upper T e H hH _ ((P_upper T e v).restrict T e H hH))
    (extend_upper T e H hH _ ((Q_upper T e v).restrict T e H hH)) T.root
  simp only [p, q, extend_mem _ _ hH.1] at h
  unfold normSum
  exact add_le_add h.1 h.2

end VariableTree

namespace AggregationVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

lemma norm_def (v : AggregationVector T e) : ‖v‖ = VariableTree.normSum T e v := rfl

@[simp] lemma coordinate_apply (s : ι) (v : AggregationVector T e) : coordinate T e s v = v s := rfl

lemma lipschitz_P (s : ι) :
    LipschitzWith 1 (fun v : AggregationVector T e => VariableTree.P T e v s) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul, norm_def]
  exact (VariableTree.potentials_lipschitz T e v w s).1

lemma lipschitz_Q (s : ι) :
    LipschitzWith 1 (fun v : AggregationVector T e => VariableTree.Q T e v s) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul, norm_def]
  exact (VariableTree.potentials_lipschitz T e v w s).2

def projectionLinear (H : Finset ι) : AggregationVector T e →ₗ[ℝ] AggregationVector T e where
  toFun := VariableTree.projectHead T H
  map_add' v w := by
    change ι →₀ ℝ at v w
    apply Finsupp.ext
    intro s
    change VariableTree.projectHead T H (v + w) s = (VariableTree.projectHead T H v + VariableTree.projectHead T H w) s
    by_cases hs : s ∈ H <;> simp [VariableTree.projectHead, hs]
  map_smul' a v := by
    change ι →₀ ℝ at v
    apply Finsupp.ext
    intro s
    change VariableTree.projectHead T H (a • v) s = (a • VariableTree.projectHead T H v) s
    by_cases hs : s ∈ H <;> simp [VariableTree.projectHead, hs]

noncomputable def projection (H : Finset ι) (hH : T.Initial H) :
    AggregationVector T e →L[ℝ] AggregationVector T e :=
  (projectionLinear T e H).mkContinuous 1 (fun v => by
    change VariableTree.normSum T e (VariableTree.projectHead T H v) ≤ 1 * VariableTree.normSum T e v
    rw [one_mul]
    exact VariableTree.projectHead_bound T e H hH v)

@[simp] lemma projection_apply (H : Finset ι) (hH : T.Initial H) (v : AggregationVector T e) :
    projection T e H hH v = VariableTree.projectHead T H v := rfl

end AggregationVector

namespace AggregationSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

@[simp] lemma coordinate_coe (s : ι) (v : AggregationVector T e) :
    coordinate T e s (v : AggregationSpace T e) = v s := by
  exact ContinuousLinearMap.fromCompletion_apply_coe _ v

@[simp] lemma P_coe (s : ι) (v : AggregationVector T e) :
    P T e s (v : AggregationSpace T e) = VariableTree.P T e v s :=
  Completion.extension_coe (AggregationVector.lipschitz_P T e s).uniformContinuous v

@[simp] lemma Q_coe (s : ι) (v : AggregationVector T e) :
    Q T e s (v : AggregationSpace T e) = VariableTree.Q T e v s :=
  Completion.extension_coe (AggregationVector.lipschitz_Q T e s).uniformContinuous v

def projection (H : Finset ι) (hH : T.Initial H) :
    AggregationSpace T e →L[ℝ] AggregationSpace T e :=
  (AggregationVector.projection T e H hH).completion

@[simp] lemma projection_coe (H : Finset ι) (hH : T.Initial H) (v : AggregationVector T e) :
    projection T e H hH (v : AggregationSpace T e) = (AggregationVector.projection T e H hH v : AggregationSpace T e) :=
  ContinuousLinearMap.completion_apply_coe _ v

def tail (H : Finset ι) (hH : T.Initial H) : Submodule ℝ (AggregationSpace T e) :=
  (projection T e H hH).ker

end AggregationSpace

namespace AggregationVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

def ofHeadLinear (H : Finset ι) : (H → ℝ) →ₗ[ℝ] AggregationVector T e where
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

def ofHead (H : Finset ι) : (H → ℝ) →L[ℝ] AggregationVector T e :=
  (ofHeadLinear T e H).toContinuousLinearMap

end AggregationVector

namespace AggregationSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

def headCoordinates (H : Finset ι) : AggregationSpace T e →L[ℝ] (H → ℝ) :=
  ContinuousLinearMap.pi (fun s : H => coordinate T e s.1)

@[simp] lemma headCoordinates_apply (H : Finset ι) (x : AggregationSpace T e) (s : H) :
    headCoordinates T e H x s = coordinate T e s.1 x := rfl

end AggregationSpace

namespace VariableExponent

end VariableExponent

namespace VariableTree

open VariableExponent

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

end VariableTree

namespace AggregationSpace

open UniformSpace VariableExponent

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

end AggregationSpace

end RecursivePotentials

end

end OAI


