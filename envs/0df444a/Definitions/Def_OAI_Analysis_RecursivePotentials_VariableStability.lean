-- Prove2me | Definitions.Def_OAI_Analysis_RecursivePotentials_VariableStability
-- name    : OAI_Analysis_RecursivePotentials_VariableStability
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T07:46:18.843739+00:00
-- url     : https://prove2.me/theorems/2a7a12c6-9868-4978-95e2-c3d6deb64135
-- title:
--   Child-potential vectors, separable duals and finite-support bookkeeping for the variable-exponent space
-- statement:
--   This file introduces the vectors of child potentials in the aggregation spaces, records that the variable-exponent space $X_v$ and its components have separable duals, and sets up the finite-support bookkeeping used in the stability estimates for $X_v$.
--
--   **Setting.** For a rooted tree $T$ on an index set $\iota$ (root $r$, parent map $\pi$ with $\pi(r)=r$, depth $d$ with $d(r)=0$ and $d(\pi(s))<d(s)$ for $s\neq r$) and an exponent $e\ge1$, let $V_{T,e}$ be the space of finitely supported $v:\iota\to\mathbb{R}$ with the norm $\|v\|=P^e_v(r)+Q^e_v(r)$. Here the $e$-potentials are computed on the finite set $H_v$ formed by the root, the support of $v$ and all their ancestors, recursively from the deepest nodes:
--   $$P^e_v(s)=\max\bigl(A,\ v(s)+B\bigr),\quad Q^e_v(s)=\max\bigl(B,\ A-v(s)\bigr),\quad A=\Bigl(\sum_cP^e_v(c)^e\Bigr)^{1/e},\ \ B=\Bigl(\sum_cQ^e_v(c)^e\Bigr)^{1/e},$$
--   the sums running over the children $c$ of $s$ (the nodes $c\neq r$ with $\pi(c)=s$) in $H_v$, and $P^e_v=Q^e_v=0$ outside $H_v$. The completion of $V_{T,e}$ is the aggregation space $Y_{T,e}$. For an integer $h\ge1$ the component tree $T_h$ has as nodes the finite sequences of natural numbers of length at most $h$, the empty sequence $\emptyset$ as root, and the parent map deleting the last entry; with the exponent $p_h=1+\frac1h$, the component space is $Y_h=Y_{T_h,p_h}$. The nodes of the variable space are the pairs $(h,s)$ with $s$ a node of $T_h$, and
--   $$X_v=\Bigl(\bigoplus_{h\ge1}Y_h\Bigr)_{\ell^2}$$
--   is the $\ell^2$-direct sum of the component spaces; the coordinate of $x\in X_v$ at $(h,s)$ is the $s$-coordinate (the continuous extension of $v\mapsto v(s)$) of its $h$-th component.
--
--   1. **$\ell^2$-sums.** For a family $(E_i)$ of normed spaces, the outer space is the $\ell^2$-direct sum $\bigl(\bigoplus_iE_i\bigr)_{\ell^2}$.
--   2. **Children vectors.** For $s\in\iota$ and a finitely supported $f:\iota\to\mathbb{R}$, the vector $\mathrm{ch}_s(f)\in\ell^e(\iota)$ is $f$ restricted to the children of $s$: its entry at $c$ is $f(c)$ if $c\neq r$ and $\pi(c)=s$, and $0$ otherwise. If $f\ge0$ and $\bigl(\sum_{c\in S}|f(c)|^e\bigr)^{1/e}\le f(s')$ for every node $s'$ and every finite set $S$ of children of $s'$, then $\|\mathrm{ch}_s(f)\|_e\le f(s)$.
--   3. **Child potentials.** For $v\in V_{T,e}$ put $\mathrm{ch}^P_s(v)=\mathrm{ch}_s(P^e_v)$ and $\mathrm{ch}^Q_s(v)=\mathrm{ch}_s(Q^e_v)$. Then $\|\mathrm{ch}^P_s(v)\|_e\le P^e_v(s)$ and $\|\mathrm{ch}^Q_s(v)\|_e\le Q^e_v(s)$; for all finitely supported $v,w$ both $|P^e_v(s)-P^e_w(s)|$ and $|Q^e_v(s)-Q^e_w(s)|$ are at most $P^e_{v-w}(s)+Q^e_{v-w}(s)$; and
--   $$\|\mathrm{ch}^P_s(v)-\mathrm{ch}^P_s(w)\|_e\le\|v-w\|,\qquad\|\mathrm{ch}^Q_s(v)-\mathrm{ch}^Q_s(w)\|_e\le\|v-w\| .$$
--   Being $1$-Lipschitz, $\mathrm{ch}^P_s$ and $\mathrm{ch}^Q_s$ extend to continuous maps $Y_{T,e}\to\ell^e(\iota)$, denoted in the same way, which agree with the original maps on $V_{T,e}$.
--   4. **Separable duals.** The dual of every component space $Y_h$ is separable, and the dual of $X_v$ is separable: every functional on $X_v$ is represented by an $\ell^2$-family of functionals on the components.
--   5. **Finite supports and ancestral heads.** The vectors of $X_v$ with finite total support (all coordinates vanish outside some finite set of nodes) form a linear subspace of $X_v$. For a finite set $S$ of nodes and $h\ge1$, the fiber is $S_h=\{s:(h,s)\in S\}$; the ancestral head $A_h(S)$ is the set formed by the root of $T_h$, the points of $S_h$ and all their ancestors, an initial set of $T_h$; and the ancestral union is the finite set of nodes $(h,s)$ such that $h$ is the first entry of some node of $S$ and $s\in A_h(S)$.
--
--   In the module, the extended child-potential maps express the recursion of the potentials on the whole completion: writing $x_s$, $P_s$, $Q_s$ for the continuous extensions to $Y_{T,e}$ of $v\mapsto v(s)$, $P^e_v(s)$, $Q^e_v(s)$, $P_s=\max\bigl(\|\mathrm{ch}^P_s\|_e,\ x_s+\|\mathrm{ch}^Q_s\|_e\bigr)$ and $Q_s=\max\bigl(\|\mathrm{ch}^Q_s\|_e,\ \|\mathrm{ch}^P_s\|_e-x_s\bigr)$, and the ancestral heads supply admissible heads for vectors of finite support in the stability and weak-tail estimates for $X_v$.
--
--   **Formalization Note** `VariableExponent.Outer E` is `lp E 2`. The maps `childLp`, `childP`, `childQ` live in `AggregationVector` (with the bounds `childLp_norm_le`, `child_bounds`, `field_differences`, `children_dist_le` and the Lipschitz lemmas), and their extensions `AggregationSpace.childP`, `AggregationSpace.childQ` are `Completion.extension`s, with `childP_coe`, `childQ_coe`. The component data are `componentTree h`, `exponent h` (value `heightExponent h = 1 + 1/h`), `Component h`, `Xv = SquareSum.Space Component` and `Node = Σ h : ℕ+, ComponentNode h`; the separability instances are `Variable.component_dual_separable` and `Variable.dual_separable`, and `coordinate_apply` unfolds the coordinates of $X_v$. The bookkeeping objects are `finiteSubmodule`, `fiber`, `ancestralHeads` and `ancestralUnion`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/VariableStability.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/VariableStability.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

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

namespace VariableExponent

noncomputable section

section Outer

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (E : ι → Type uFiber)
  [∀ i, NormedAddCommGroup (E i)] [fiberNormedSpace : ∀ i, NormedSpace ℝ (E i)]

abbrev Outer := ↥(lp E 2)

end Outer

end

end VariableExponent

namespace AggregationVector

noncomputable section

open FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

def childLp (s : ι) (f : ι →₀ ℝ) : CoordinateLp ι e :=
  toLpLinear T e (f.filter fun c => c ≠ T.root ∧ T.parent c = s)

@[simp] lemma childLp_apply (s c : ι) (f : ι →₀ ℝ) :
    childLp T e s f c = if c ≠ T.root ∧ T.parent c = s then f c else 0 := by
  exact (toLpLinear_apply T e (f.filter fun c => c ≠ T.root ∧ T.parent c = s) c).trans
    (Finsupp.filter_apply _ _ _)

lemma childLp_norm_le (s : ι) (f : ι →₀ ℝ) (hf : ∀ c, 0 ≤ f c)
    (hU : VariableTree.GlobalUpper T e f) : ‖childLp T e s f‖ ≤ f s := by
  apply lp.norm_le_of_forall_sum_le
    (by simpa only [ENNReal.toReal_ofReal e.pos.le] using e.pos) (hf s)
  intro S
  simp only [ENNReal.toReal_ofReal e.pos.le,Real.norm_eq_abs,childLp_apply]
  have hh := (e.agg_le_iff (S.filter fun c => c ≠ T.root ∧ T.parent c = s) f (hf s)).mp
    (hU s _ (fun c hc => (Finset.mem_filter.mp hc).2))
  simpa [ChildExponent.agg,Finset.sum_filter,apply_ite,Real.zero_rpow e.ne_zero] using hh

def childP (s : ι) (v : AggregationVector T e) :
    CoordinateLp ι e := childLp T e s (VariableTree.P T e v)

def childQ (s : ι) (v : AggregationVector T e) :
    CoordinateLp ι e := childLp T e s (VariableTree.Q T e v)

lemma child_bounds (s : ι) (v : AggregationVector T e) :
    ‖childP T e s v‖ ≤ VariableTree.P T e v s ∧ ‖childQ T e s v‖ ≤ VariableTree.Q T e v s :=
  ⟨childLp_norm_le T e s _ (VariableTree.P_nonneg T e v) (VariableTree.P_upper T e v),
    childLp_norm_le T e s _ (VariableTree.Q_nonneg T e v) (VariableTree.Q_upper T e v)⟩

lemma field_differences (v w : ι →₀ ℝ) (s : ι) :
    |VariableTree.P T e v s-VariableTree.P T e w s| ≤ VariableTree.P T e (v-w) s+VariableTree.Q T e (v-w) s ∧
    |VariableTree.Q T e v s-VariableTree.Q T e w s| ≤ VariableTree.P T e (v-w) s+VariableTree.Q T e (v-w) s := by
  have h₁ := VariableTree.potentials_add_le T e (v-w) w s
  have h₂ := VariableTree.potentials_add_le T e (w-v) v s
  rw [sub_add_cancel] at h₁ h₂
  have hneg := VariableTree.potentials_neg T e (v-w) s
  rw [neg_sub] at hneg
  rw [hneg.1,hneg.2] at h₂
  have hP := VariableTree.P_nonneg T e (v-w) s
  have hQ := VariableTree.Q_nonneg T e (v-w) s
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith [h₁.1,h₁.2,h₂.1,h₂.2]

lemma children_dist_le (s : ι) (v w : AggregationVector T e) :
    ‖childP T e s v-childP T e s w‖ ≤ ‖v-w‖ ∧
    ‖childQ T e s v-childQ T e s w‖ ≤ ‖v-w‖ := by
  have hb : ‖childP T e s (v-w)+childQ T e s (v-w)‖ ≤ ‖v-w‖ := by
    have h := norm_add_le (childP T e s (v-w)) (childQ T e s (v-w))
    have hc := child_bounds T e s (v-w)
    have hp := (VariableTree.P_upper T e (v-w)).le_root T e (VariableTree.P_nonneg T e (v-w)) s
    have hq := (VariableTree.Q_upper T e (v-w)).le_root T e (VariableTree.Q_nonneg T e (v-w)) s
    change _ ≤ VariableTree.P T e (v-w) T.root + VariableTree.Q T e (v-w) T.root
    linarith [hc.1,hc.2]
  have hp0 : ENNReal.ofReal e.val ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr e.pos)
  constructor
  · refine (lp.norm_mono hp0 (y := childP T e s (v-w)+childQ T e s (v-w)) ?_).trans hb
    intro c
    simp only [lp.coeFn_sub,lp.coeFn_add,Pi.sub_apply,Pi.add_apply,Real.norm_eq_abs,childP,childQ,childLp_apply]
    split_ifs with hc
    · rw [abs_of_nonneg (add_nonneg (VariableTree.P_nonneg T e (v-w) c) (VariableTree.Q_nonneg T e (v-w) c))]
      exact (field_differences T e v w c).1
    · simp
  · refine (lp.norm_mono hp0 (y := childP T e s (v-w)+childQ T e s (v-w)) ?_).trans hb
    intro c
    simp only [lp.coeFn_sub,lp.coeFn_add,Pi.sub_apply,Pi.add_apply,Real.norm_eq_abs,childP,childQ,childLp_apply]
    split_ifs with hc
    · rw [abs_of_nonneg (add_nonneg (VariableTree.P_nonneg T e (v-w) c) (VariableTree.Q_nonneg T e (v-w) c))]
      exact (field_differences T e v w c).2
    · simp

lemma childP_lipschitz (s : ι) : LipschitzWith 1 (childP T e s) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simpa only [dist_eq_norm,NNReal.coe_one,one_mul] using (children_dist_le T e s v w).1

lemma childQ_lipschitz (s : ι) : LipschitzWith 1 (childQ T e s) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simpa only [dist_eq_norm,NNReal.coe_one,one_mul] using (children_dist_le T e s v w).2

end

end AggregationVector

namespace AggregationSpace

noncomputable section

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

def childP (s : ι) : AggregationSpace T e → AggregationVector.CoordinateLp ι e :=
  Completion.extension (AggregationVector.childP T e s)

def childQ (s : ι) : AggregationSpace T e → AggregationVector.CoordinateLp ι e :=
  Completion.extension (AggregationVector.childQ T e s)

@[simp] lemma childP_coe (s : ι) (v : AggregationVector T e) :
    childP T e s (v : AggregationSpace T e) = AggregationVector.childP T e s v :=
  Completion.extension_coe (AggregationVector.childP_lipschitz T e s).uniformContinuous v

@[simp] lemma childQ_coe (s : ι) (v : AggregationVector T e) :
    childQ T e s (v : AggregationSpace T e) = AggregationVector.childQ T e s v :=
  Completion.extension_coe (AggregationVector.childQ_lipschitz T e s).uniformContinuous v

end

end AggregationSpace

namespace Variable

noncomputable section

open UniformSpace VariableExponent Filter Topology TopologicalSpace

instance component_dual_separable (h : ℕ+) : SeparableSpace (Component h →L[ℝ] ℝ) :=
  AggregationSpace.finite_height_dual_separable (componentTree h) (exponent h) (heightExponent_gt_one h)
    (component_step h) h.val (component_height h)

instance dual_separable : SeparableSpace (Xv →L[ℝ] ℝ) := by
  let : SeparableSpace (SquareSum.Space (SquareSum.DualFamily Component)) :=
    LpSupport.separable (SquareSum.DualFamily Component) 2 (by norm_num)
  have hs : Function.Surjective (SquareSum.pairing Component) :=
    fun f => ⟨SquareSum.restrict Component f,SquareSum.pairing_restrict Component f⟩
  exact hs.denseRange.separableSpace (SquareSum.pairing Component).continuous

@[simp] lemma coordinate_apply (s : Node) (x : Xv) :
    coordinate s x = componentCoordinate s.1 s.2 (x s.1) := rfl

end

end Variable

namespace ScalarLp

noncomputable section

open Filter Topology

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι]

end

end ScalarLp

namespace Variable

noncomputable section

open UniformSpace VariableExponent Filter Topology TopologicalSpace

def finiteSubmodule : Submodule ℝ Xv where
  carrier := FiniteTotalSupport
  zero_mem' := ⟨∅, by simp⟩
  add_mem' := by
    rintro x y ⟨S,hS⟩ ⟨T,hT⟩
    refine ⟨S ∪ T,fun s hs => ?_⟩
    simp only [Finset.mem_union,not_or] at hs
    rw [map_add,hS s hs.1,hT s hs.2,add_zero]
  smul_mem' := by
    rintro a x ⟨S,hS⟩
    exact ⟨S,fun s hs => by rw [map_smul,hS s hs,smul_zero]⟩

def fiber (S : Finset Node) (h : ℕ+) : Finset (ComponentNode h) :=
  S.preimage (Sigma.mk h) (fun _ _ _ _ hxy => by simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using hxy)

def ancestralHeads (S : Finset Node) (h : ℕ+) : Finset (ComponentNode h) :=
  (componentTree h).ancestorClosure (fiber S h)

def ancestralUnion (S : Finset Node) : Finset Node := (S.image Sigma.fst).sigma (ancestralHeads S)

end

end Variable

end RecursivePotentials

end OAI


