-- Prove2me | Definitions.Def_OAI_Analysis_DiamondDistortion_UpperFunction
-- name    : OAI_Analysis_DiamondDistortion_UpperFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:26:02.04223+00:00
-- url     : https://prove2.me/theorems/b4d7a153-c721-4d74-a297-99fc95366e00
-- title:
--   Least upper values $(P_h,Q_h)$ on $\ell_p$ of the countably branching tree of height $h$
-- statement:
--   Fix an exponent $p$ with $1\le p<\infty$. For $h\in\mathbb{N}$ let $T_h$ be the rooted, countably branching tree of height $h$: $T_0=\{o\}$ is a single root, and $T_{h+1}=\{o\}\sqcup(\mathbb{N}\times T_h)$ consists of a root $o$ below which hang countably many disjoint copies $\{i\}\times T_h$ $(i\in\mathbb{N})$ of $T_h$. Let $\ell_p(T_h)$ be the Banach space of real functions $v$ on $T_h$ with $\|v\|_p=\big(\sum_{s\in T_h}|v(s)|^p\big)^{1/p}<\infty$. This file constructs, by recursion on the height, a pair of nonnegative functionals on $\ell_p(T_h)$.
--
--   1. **Child restrictions.** For $v\in\ell_p(T_{h+1})$ and $i\in\mathbb{N}$, the $i$-th child of $v$ is $v_i\in\ell_p(T_h)$, $v_i(s)=v(i,s)$. The sequence $(v_i)_{i\in\mathbb{N}}$ is an element of the space $\ell_p(\mathbb{N};\ell_p(T_h))$ of $p$-summable sequences in $\ell_p(T_h)$, with
--   $$
--   \Big(\sum_{i\in\mathbb{N}}\|v_i\|_p^p\Big)^{1/p}\le\|v\|_p ,
--   $$
--   and $v\mapsto v_i$ is linear.
--
--   2. **Upper data.** For a real normed space $E$ and a real constant $C$, *upper data of size $C$* on $E$ is a map $U=(U_1,U_2):E\to\mathbb{R}^2$ with $0\le U_1(x)\le C\|x\|$ and $0\le U_2(x)\le C\|x\|$ for all $x\in E$. When $C\ge0$, applying $U_1$ (respectively $U_2$) entrywise to a sequence $x=(x_i)_{i\in\mathbb{N}}\in\ell_p(\mathbb{N};E)$ gives the *positive array* $(U_1(x_i))_{i}$ (respectively the *negative array* $(U_2(x_i))_{i}$), an element of $\ell_p(\mathbb{N})$ of norm at most $C\|x\|$; for this construction any exponent $p\in[1,\infty]$ is allowed.
--
--   3. **Least upper values.** For $r,a,b\in\mathbb{R}$ put $J(r,a,b)=\big(\max(a,\,r+b),\ \max(a-r,\,b)\big)$. The pair $(P_h,Q_h):\ell_p(T_h)\to\mathbb{R}^2$ is defined by
--   $$
--   P_0(v)=\max(v(o),0),\qquad Q_0(v)=\max(-v(o),0),
--   $$
--   $$
--   \big(P_{h+1}(v),\,Q_{h+1}(v)\big)=J\big(v(o),\,a_v,\,b_v\big),\qquad a_v=\big\|(P_h(v_i))_{i\in\mathbb{N}}\big\|_{\ell_p},\quad b_v=\big\|(Q_h(v_i))_{i\in\mathbb{N}}\big\|_{\ell_p}.
--   $$
--   At every height $(P_h,Q_h)$ is upper data of size $3^h$, that is $0\le P_h(v)\le 3^h\|v\|_p$ and $0\le Q_h(v)\le 3^h\|v\|_p$; this is what makes the sequences defining $a_v$ and $b_v$ $p$-summable. In particular $P_h(0)=Q_h(0)=0$.
--
--   The pair $J(r,a,b)$ is the smallest pair $(P,Q)$ with $P\ge a$, $Q\ge b$ and $P-Q=r$. Accordingly, $(P_h(v),Q_h(v))$ are the root values of the least pair of nonnegative arrays on $T_h$ whose difference equals $v$ at every vertex and each of which dominates, at every vertex, the $\ell_p$ norm of its own values at the children of that vertex (this minimality is established separately). The sum $P_h+Q_h$ is the recursive tree norm on the full space $\ell_p(T_h)$ that is studied in the companion file on recursive bounds.
--
--   **Formalization Note** The tree $T_h$ is the type `Coord h` and $\ell_p(T_h)$ is `Full p h`, Mathlib's `lp` space of real functions on `Coord h`; the exponent is an extended nonnegative real carrying the instance hypothesis $1\le p$. The child maps `child`, `children` and the recursion `fullUpperData`, `fullUpper` also take the hypothesis `hp : 0 < p.toReal`, which (given $1\le p$) says exactly that $p<\infty$. Upper data is the structure `UpperFunction.Data E C`, with arrays `positiveArray` and `negativeArray`. The constant $3^h$ is propagated by the lemma `join_upper_bound`: if $C\ge1$, $M\ge0$, $|r|\le M$ and $a,b\le CM$, then both components of $J(r,a,b)$ are at most $3CM$. The function $J$ is `RecursiveModel.join` from a companion file; `fullUpper_nonneg`, `fullUpper_bound` and `fullUpper_zero` record the stated properties, and the remaining lemmas are linearity identities for `child`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/UpperFunction.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/UpperFunction.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DiamondDistortion mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Definitions.Def_OAI_Analysis_DiamondDistortion_Orthogonality
import Definitions.Def_OAI_Analysis_DiamondDistortion_ForestModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_DiamondGraph
import Definitions.Def_OAI_Analysis_DiamondDistortion_CoordinateSpace
import Definitions.Def_OAI_Analysis_DiamondDistortion_RecursiveModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_InfimalCost
import Definitions.Def_OAI_Analysis_DiamondDistortion_PathModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_StartModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_CoordinateDual
import Definitions.Def_OAI_Analysis_DiamondDistortion_Incomparable
import Definitions.Def_OAI_Analysis_DiamondDistortion_ModelMaps
import Definitions.Def_OAI_Analysis_DiamondDistortion_EquivalentNorm

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

namespace RecursiveModel
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]
abbrev Full (h : ℕ) := lp (fun _ : Coord h => ℝ) p
lemma p_ne_zero : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ≥0∞)<1) (Fact.out : 1 ≤ p))
variable (hp : 0 < p.toReal)

def child (h : ℕ) (v : Full p (h+1)) (i : ℕ) : Full p h :=
  ⟨fun s => v (.inr (i,s)),(memℓp_gen_iff hp).mpr ((v.property.summable hp).comp_injective (by
    intro a b hh
    exact (Prod.mk.inj (Sum.inr.inj hh)).2))⟩
lemma child_sum (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal) (h : ℕ) (v : Full p (h+1)) (i : ℕ) :
    ‖child p hp h v i‖^p.toReal=∑' s : Coord h,‖v (.inr (i,s))‖^p.toReal :=
  lp.norm_rpow_eq_tsum hp _
lemma child_summable (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal) (h : ℕ) (v : Full p (h+1)) :
    Summable (fun q : ℕ × Coord h => ‖v (.inr q)‖^p.toReal) :=
  (v.property.summable hp).comp_injective Sum.inr_injective

def children (h : ℕ) (v : Full p (h+1)) : lp (fun _ : ℕ => Full p h) p :=
  ⟨fun i => child p hp h v i,(memℓp_gen_iff hp).mpr (by
    have hh := (child_summable p hp h v).prod
    simpa only [← child_sum p hp h v] using hh)⟩
lemma children_apply (h : ℕ) (v : Full p (h+1)) (i : ℕ) : children p hp h v i=child p hp h v i := rfl
lemma children_norm (h : ℕ) (v : Full p (h+1)) : ‖children p hp h v‖ ≤ ‖v‖ := by
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hp).mp
  rw [lp.norm_rpow_eq_tsum hp,lp.norm_rpow_eq_tsum hp]
  simp_rw [children_apply,child_sum]
  rw [← (child_summable p hp h v).tsum_prod]
  exact Summable.tsum_le_tsum_of_inj (fun q : ℕ × Coord h => (Sum.inr q : Coord (h+1)))
    Sum.inr_injective (fun _ _ => by positivity) (fun _ => le_rfl)
    (child_summable p hp h v) (v.property.summable hp)

@[simp] lemma child_add (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal) (h : ℕ) (u v : Full p (h+1)) (i : ℕ) :
    child p hp h (u+v) i=child p hp h u i+child p hp h v i := by ext s; rfl
@[simp] lemma child_neg (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal) (h : ℕ) (v : Full p (h+1)) (i : ℕ) :
    child p hp h (-v) i=-child p hp h v i := by ext s; rfl
@[simp] lemma child_smul (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal) (h : ℕ) (a : ℝ) (v : Full p (h+1)) (i : ℕ) :
    child p hp h (a • v) i=a • child p hp h v i := by ext s; rfl
@[simp] lemma child_zero (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal) (h : ℕ) (i : ℕ) : child p hp h 0 i=0 := by ext s; rfl
end RecursiveModel

namespace UpperFunction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
structure Data (E : Type*) [NormedAddCommGroup E] (C : ℝ) where
  value : E → ℝ × ℝ
  nonneg : ∀ v,0 ≤ (value v).1 ∧ 0 ≤ (value v).2
  bound : ∀ v,(value v).1 ≤ C*‖v‖ ∧ (value v).2 ≤ C*‖v‖
namespace Data
variable {C : ℝ} (U : Data E C) (hC : 0 ≤ C) {p : ℝ≥0∞} [Fact (1 ≤ p)]
def positiveArray (v : lp (fun _ : ℕ => E) p) : lp (fun _ : ℕ => ℝ) p :=
  LpBoundedMap.map (fun x => (U.value x).1) C hC (fun x => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (U.nonneg x).1] using (U.bound x).1) v
def negativeArray (v : lp (fun _ : ℕ => E) p) : lp (fun _ : ℕ => ℝ) p :=
  LpBoundedMap.map (fun x => (U.value x).2) C hC (fun x => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (U.nonneg x).2] using (U.bound x).2) v
lemma positiveArray_norm (hp : p ≠ 0) (v : lp (fun _ : ℕ => E) p) :
    ‖positiveArray U hC v‖ ≤ C*‖v‖ := LpBoundedMap.map_norm hp _ _ _ _ v
lemma negativeArray_norm (hp : p ≠ 0) (v : lp (fun _ : ℕ => E) p) :
    ‖negativeArray U hC v‖ ≤ C*‖v‖ := LpBoundedMap.map_norm hp _ _ _ _ v
end Data
end UpperFunction

namespace RecursiveModel
lemma join_upper_bound {r a b C M : ℝ} (hC : 1 ≤ C) (hM : 0 ≤ M)
    (hr : |r| ≤ M) (ha : a ≤ C*M) (hb : b ≤ C*M) :
    (join r a b).1 ≤ (3*C)*M ∧ (join r a b).2 ≤ (3*C)*M := by
  have hCM : M ≤ C*M := by nlinarith
  have hrp := (abs_le.mp hr).2
  have hrn := (abs_le.mp hr).1
  constructor <;> apply max_le <;> nlinarith

variable (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal)
/-- Least upper values on the original full ℓp component, not on a finite-support
    substitute. All child sequences are genuine countable ℓp vectors. -/
def fullUpperData : (h : ℕ) → UpperFunction.Data (Full p h) (3^h)
  | 0 => {
      value v := (max (v ()) 0,max (-v ()) 0)
      nonneg v := ⟨le_max_right _ _,le_max_right _ _⟩
      bound v := by
        simp only [pow_zero,one_mul]
        have hb := lp.norm_apply_le_norm (p_ne_zero p) v ()
        rw [Real.norm_eq_abs] at hb
        exact ⟨max_le ((le_abs_self _).trans hb) (norm_nonneg _),
          max_le ((neg_le_abs _).trans hb) (norm_nonneg _)⟩ }
  | h+1 =>
    let U := fullUpperData h
    let a (v : Full p (h+1)) := ‖U.positiveArray (by positivity) (children p hp h v)‖
    let b (v : Full p (h+1)) := ‖U.negativeArray (by positivity) (children p hp h v)‖
    { value v := join (v (.inl ())) (a v) (b v)
      nonneg v := ⟨(norm_nonneg _).trans (le_max_left _ _),(norm_nonneg _).trans (le_max_right _ _)⟩
      bound v := by
        have ha := (U.positiveArray_norm (by positivity) (p_ne_zero p) (children p hp h v)).trans
          (mul_le_mul_of_nonneg_left (children_norm p hp h v) (by positivity : (0:ℝ) ≤ 3^h))
        have hb := (U.negativeArray_norm (by positivity) (p_ne_zero p) (children p hp h v)).trans
          (mul_le_mul_of_nonneg_left (children_norm p hp h v) (by positivity : (0:ℝ) ≤ 3^h))
        have hr : |v (.inl ())| ≤ ‖v‖ := by
          simpa only [Real.norm_eq_abs] using lp.norm_apply_le_norm (p_ne_zero p) v (.inl ())
        have hh := join_upper_bound (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 3)) (norm_nonneg v) hr ha hb
        simpa only [pow_succ,show (3:ℝ)*3^h=3^h*3 by ring] using hh }

def fullUpper (h : ℕ) (v : Full p h) : ℝ × ℝ := (fullUpperData p hp h).value v
lemma fullUpper_nonneg (h : ℕ) (v : Full p h) :
    0 ≤ (fullUpper p hp h v).1 ∧ 0 ≤ (fullUpper p hp h v).2 := (fullUpperData p hp h).nonneg v
lemma fullUpper_bound (h : ℕ) (v : Full p h) :
    (fullUpper p hp h v).1 ≤ 3^h*‖v‖ ∧ (fullUpper p hp h v).2 ≤ 3^h*‖v‖ :=
  (fullUpperData p hp h).bound v

@[simp] lemma fullUpper_zero (h : ℕ) : fullUpper p hp h 0=0 := by
  have hn := fullUpper_nonneg p hp h 0
  have hb := fullUpper_bound p hp h 0
  simp only [norm_zero,mul_zero] at hb
  exact Prod.ext (le_antisymm hb.1 hn.1) (le_antisymm hb.2 hn.2)

end RecursiveModel

end DiamondDistortion

end

end OAI


