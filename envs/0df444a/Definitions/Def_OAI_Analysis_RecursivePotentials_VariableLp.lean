-- Prove2me | Definitions.Def_OAI_Analysis_RecursivePotentials_VariableLp
-- name    : OAI_Analysis_RecursivePotentials_VariableLp
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T07:44:52.573534+00:00
-- url     : https://prove2.me/theorems/7b6b57bf-142b-427a-bde8-d381f1a23e97
-- title:
--   Scalar $\ell^p$ duality, norming vectors and separability of duals
-- statement:
--   This file sets up the real $\ell^p$ spaces with exponent $p>1$, the duality between $\ell^p$ and $\ell^{p'}$ through coefficient sequences, and the separability facts used to show that the duals of the variable-exponent tree spaces are separable.
--
--   1. **Exponents above one.** A power exponent is a real number $p>1$. Its conjugate exponent is $p'=\frac{p}{p-1}$, which is again a power exponent and satisfies $\frac1p+\frac1{p'}=1$.
--   2. **Scalar $\ell^p$ spaces.** For an index type $I$ and a power exponent $p$, $\ell^p(I)$ is the Banach space of real families $x=(x_i)_{i\in I}$ with $\|x\|_p=\bigl(\sum_{i\in I}|x_i|^p\bigr)^{1/p}<\infty$; $e_i$ denotes the $i$-th unit vector.
--   3. **Duality pairing.** For power exponents $p,q$ with $\frac1p+\frac1q=1$, the map
--   $$\Phi:\ell^q(I)\to\ell^p(I)^*,\qquad\Phi(y)(x)=\sum_{i\in I}y_i\,x_i,$$
--   is continuous and linear; in particular $\Phi(y)(a\,e_i)=a\,y_i$ and $\Phi(a\,e_i)(x)=a\,x_i$.
--   4. **Coefficients, norming values and restriction.** The coefficients of $f\in\ell^p(I)^*$ are $f_i=f(e_i)$, so that $f(a\,e_i)=a\,f_i$. For $a,\rho\in\mathbb{R}$ the norming value is $n_\rho(a)=\sigma(a)\,|a|^{\rho-1}$, where $\sigma(a)=1$ for $a\ge0$ and $\sigma(a)=-1$ for $a<0$; it satisfies $|n_\rho(a)|=|a|^{\rho-1}$, $n_q(a)\,a=|a|^q$ and, for Hölder-conjugate $p,q$, $|n_q(a)|^p=|a|^q$. Testing $f$ on $\sum_{i\in S}n_q(f_i)\,e_i$ shows that for every finite set $S\subseteq I$
--   $$\sum_{i\in S}|f_i|^q\le\|f\|^q .$$
--   Consequently $(f_i)_{i\in I}\in\ell^q(I)$. This family is the restriction $R(f)\in\ell^q(I)$, and $\Phi(R(f))=f$: every functional on $\ell^p(I)$ is represented by an element of $\ell^q(I)$.
--   5. **Separability.** If $I$ is countable, every $E_i$ is a separable normed space and $1\le p<\infty$, then the $\ell^p$-direct sum of the $E_i$ is separable. If $E^*$ is separable and $E$ is isomorphic to $F$ by a continuous linear isomorphism, then $F^*$ is separable. For countable $I$ the space $\ell^p(I)$ is separable, and so is its dual, being the continuous image of the separable space $\ell^q(I)$ under $\Phi$.
--   6. **Aggregation spaces of bounded height.** For a rooted tree $T$ on an index set $\iota$ (root $r$, parent map $\pi$ with $\pi(r)=r$, depth $d$ with $d(r)=0$ and $d(\pi(s))<d(s)$ for $s\neq r$) and an exponent $e\ge1$, let $V_{T,e}$ be the space of finitely supported $v:\iota\to\mathbb{R}$ with the norm $\|v\|=P^e_v(r)+Q^e_v(r)$. Here the $e$-potentials are computed on the finite set $H_v$ formed by the root, the support of $v$ and all their ancestors, recursively from the deepest nodes:
--   $$P^e_v(s)=\max\bigl(A,\ v(s)+B\bigr),\quad Q^e_v(s)=\max\bigl(B,\ A-v(s)\bigr),\quad A=\Bigl(\sum_cP^e_v(c)^e\Bigr)^{1/e},\ \ B=\Bigl(\sum_cQ^e_v(c)^e\Bigr)^{1/e},$$
--   the sums running over the children $c$ of $s$ (the nodes $c\neq r$ with $\pi(c)=s$) in $H_v$, and $P^e_v=Q^e_v=0$ outside $H_v$. The completion of $V_{T,e}$ is the aggregation space $Y_{T,e}$. The map from $V_{T,e}$ to $\ell^e(\iota)$ keeps every coordinate. If $\iota$ is countable, $e>1$, $d(c)=d(\pi(c))+1$ for every $c\neq r$, and $d(s)\le h$ for all $s$ and some $h\in\mathbb{N}$, then the dual of $Y_{T,e}$ is separable.
--
--   These facts describe $\ell^p(I)^*$ concretely through coefficient sequences, which is what is needed to prove that the component spaces of the variable-exponent space, and their $\ell^2$-sum, have separable duals.
--
--   **Formalization Note** `PowerExponent` is a structure holding a real `val` with `1 < val`, and `conjugate` uses `Real.conjExponent`; `ScalarLp.Space ι p` is `lp (fun _ : ι => ℝ) (ENNReal.ofReal p.val)`. The pairing is built from `lp.dualPairing` (with `pairing_apply` giving the series $\sum_i y_ix_i$ as a `tsum`), and `coefficient`, `norming`, `restrict` are the coefficients, norming values and restriction, with `pairing_restrict` stating $\Phi\circ R=\mathrm{id}$. The separability results are `LpSupport.separable`, `dual_separable_of_equiv`, `ScalarLp.separable`, `ScalarLp.dual_separable` and `AggregationSpace.finite_height_dual_separable`, the last one via the isomorphism `AggregationSpace.lpEquiv` of the model file; `toLpLinear_apply` records that the map into $\ell^e$ is the identity on coordinates.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/VariableLp.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/VariableLp.lean by skeleton subtraction
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

noncomputable section

namespace LpSupport

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (E : ι → Type uFiber)
  [∀ i, NormedAddCommGroup (E i)] [fiberNormedSpace : ∀ i, NormedSpace ℝ (E i)]
  (p : ℝ≥0∞) [Fact (1 ≤ p)]

lemma separable [Countable ι] [∀ i, SeparableSpace (E i)] (hp : p ≠ ⊤) :
    SeparableSpace (↥(lp E p)) := by
  let S : Set (↥(lp E p)) := ⋃ i, Set.range (lp.single p i : E i → lp E p)
  have hS : TopologicalSpace.IsSeparable S := TopologicalSpace.IsSeparable.iUnion
    (fun i => TopologicalSpace.isSeparable_range (lp.singleContinuousLinearMap ℝ E p i).continuous)
  let V : Submodule ℝ (↥(lp E p)) := Submodule.span ℝ S
  have hsingle (i : ι) (x : E i) : lp.single p i x ∈ V :=
    Submodule.subset_span (Set.mem_iUnion.mpr ⟨i, ⟨x,rfl⟩⟩)
  have htop : V.topologicalClosure = ⊤ := by
    apply top_unique
    intro x hx
    exact V.isClosed_topologicalClosure.mem_of_tendsto (lp.hasSum_single hp x)
      (Filter.Eventually.of_forall fun J => V.topologicalClosure.sum_mem
        fun i hi => V.le_topologicalClosure (hsingle i (x i)))
  have hh := (hS.span (R := ℝ)).closure
  change TopologicalSpace.IsSeparable (V.topologicalClosure : Set (↥(lp E p))) at hh
  rw [htop] at hh
  exact TopologicalSpace.isSeparable_univ_iff.mp (by simpa using hh)

end LpSupport

lemma dual_separable_of_equiv {E : Type uSpace} {F : Type uOther} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [SeparableSpace (E →L[ℝ] ℝ)]
    (e : E ≃L[ℝ] F) : SeparableSpace (F →L[ℝ] ℝ) := by
  let D : (E →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ F E ℝ).flip e.symm.toContinuousLinearMap
  have hD : Function.Surjective D := by
    intro f
    refine ⟨f.comp e.toContinuousLinearMap, ?_⟩
    ext y
    change f (e (e.symm y)) = f y
    rw [e.apply_symm_apply]
  exact hD.denseRange.separableSpace D.continuous

structure PowerExponent where
  val : ℝ
  one_lt : 1 < val

namespace PowerExponent

lemma pos (p : PowerExponent) : 0 < p.val := zero_lt_one.trans p.one_lt

lemma ne_zero (p : PowerExponent) : p.val ≠ 0 := p.pos.ne'

instance (p : PowerExponent) : Fact (1 ≤ ENNReal.ofReal p.val) :=
  ⟨by simpa using ENNReal.ofReal_le_ofReal p.one_lt.le⟩

def conjugate (p : PowerExponent) : PowerExponent :=
  ⟨Real.conjExponent p.val, (Real.HolderConjugate.conjExponent p.one_lt).symm.lt⟩

lemma holder (p : PowerExponent) : p.val.HolderConjugate p.conjugate.val :=
  Real.HolderConjugate.conjExponent p.one_lt

end PowerExponent

namespace ScalarLp

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι]

abbrev Space (ι : Type uIndex) (p : PowerExponent) := ↥(lp (fun _ : ι => ℝ) (ENNReal.ofReal p.val))

variable (p q : PowerExponent) (hpq : p.val.HolderConjugate q.val)

def pairing : Space ι q →L[ℝ] (Space ι p →L[ℝ] ℝ) := by
  let := hpq.symm.ennrealOfReal
  exact lp.dualPairing (ENNReal.ofReal q.val) (ENNReal.ofReal p.val)
    (fun _ => ContinuousLinearMap.mul ℝ ℝ) (K := 1)
    (fun _ => ContinuousLinearMap.opNorm_mul_le ℝ ℝ)

lemma pairing_apply {ι : Type uIndex} [DecidableEq ι] (p q : PowerExponent)
    (hpq : p.val.HolderConjugate q.val) (y : Space ι q) (x : Space ι p) :
    pairing p q hpq y x = ∑' i, y i * x i := rfl

@[simp] lemma pairing_single_right (y : Space ι q) (i : ι) (a : ℝ) :
    pairing p q hpq y (lp.single (ENNReal.ofReal p.val) i a) = y i * a := by
  rw [pairing_apply, tsum_eq_single i, lp.single_apply_self]
  intro j hj
  rw [lp.single_apply_ne _ _ _ hj, mul_zero]

@[simp] lemma pairing_single_left (i : ι) (a : ℝ) (x : Space ι p) :
    pairing p q hpq (lp.single (ENNReal.ofReal q.val) i a) x = a * x i := by
  rw [pairing_apply, tsum_eq_single i, lp.single_apply_self]
  intro j hj
  rw [lp.single_apply_ne _ _ _ hj, zero_mul]

def coefficient (f : Space ι p →L[ℝ] ℝ) (i : ι) : ℝ :=
  f (lp.single (ENNReal.ofReal p.val) i 1)

lemma apply_single (f : Space ι p →L[ℝ] ℝ) (i : ι) (a : ℝ) :
    f (lp.single (ENNReal.ofReal p.val) i a) = a * coefficient p f i := by
  have hh := lp.single_smul (E := fun _ : ι => ℝ) (ENNReal.ofReal p.val) i a (1:ℝ)
  simp only [smul_eq_mul, mul_one] at hh
  rw [hh, map_smul, smul_eq_mul]
  rfl

def norming (a r : ℝ) : ℝ := (if 0 ≤ a then 1 else -1) * |a| ^ (r-1)

lemma abs_norming (a r : ℝ) : |norming a r| = |a| ^ (r-1) := by
  unfold norming
  split <;> simp [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg a) _)]

lemma norming_mul (a : ℝ) : norming a q.val * a = |a| ^ q.val := by
  by_cases ha : a = 0
  · simp [ha, norming, Real.zero_rpow q.ne_zero]
  have hab : 0 < |a| := abs_pos.mpr ha
  have he : |a| ^ q.val = |a| ^ (q.val-1) * |a| := by
    calc |a| ^ q.val = |a| ^ ((q.val-1)+1) := by congr 1; ring
         _ = _ := by rw [Real.rpow_add hab, Real.rpow_one]
  rw [he]
  unfold norming
  split
  · rename_i ha
    simp only [one_mul, abs_of_nonneg ha]
  · rename_i ha
    rw [abs_of_neg (lt_of_not_ge ha)]
    ring

include hpq

lemma norming_rpow (a : ℝ) : |norming a q.val| ^ p.val = |a| ^ q.val := by
  rw [abs_norming, ← Real.rpow_mul (abs_nonneg a), hpq.symm.sub_one_mul_conj]

lemma restriction_bound (f : Space ι p →L[ℝ] ℝ) (S : Finset ι) :
    ∑ i ∈ S, |coefficient p f i| ^ q.val ≤ ‖f‖ ^ q.val := by
  let A := ∑ i ∈ S, |coefficient p f i| ^ q.val
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _
  let v : Space ι p := ∑ i ∈ S, lp.single (ENNReal.ofReal p.val) i (norming (coefficient p f i) q.val)
  have hv : ‖v‖ ^ p.val = A := by
    have hh := lp.norm_sum_single (E := fun _ : ι => ℝ) (p := ENNReal.ofReal p.val)
      (by simpa only [ENNReal.toReal_ofReal p.pos.le] using p.pos)
      (fun i => norming (coefficient p f i) q.val) S
    simp only [ENNReal.toReal_ofReal p.pos.le, Real.norm_eq_abs, norming_rpow p q hpq] at hh
    exact hh
  have hfv : f v = A := by
    dsimp [v,A]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [apply_single, norming_mul]
  have hv' : ‖v‖ = A ^ (1/p.val) := by
    rw [← hv, ← Real.rpow_mul (norm_nonneg _)]
    simp [p.ne_zero]
  have hf : A ≤ ‖f‖ * A ^ (1/p.val) := by
    calc A = f v := hfv.symm
         _ ≤ ‖f‖ * ‖v‖ := (le_abs_self _).trans (f.le_opNorm v)
         _ = _ := by rw [hv']
  change A ≤ ‖f‖ ^ q.val
  by_cases hz : A = 0
  · rw [hz]; positivity
  have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hz)
  have hsplit : A = A ^ (1/q.val) * A ^ (1/p.val) := by
    rw [← Real.rpow_add hAp]
    have he : 1/q.val + 1/p.val = 1 := by simpa only [one_div] using hpq.symm.inv_add_inv_eq_one
    rw [he, Real.rpow_one]
  have hb : A ^ (1/q.val) ≤ ‖f‖ :=
    (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hAp (1/p.val))).mp (hsplit.symm.trans_le hf)
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hA _) hb q.pos.le
  simpa only [← Real.rpow_mul hA, one_div_mul_cancel q.ne_zero, Real.rpow_one] using hh

lemma restriction_mem (f : Space ι p →L[ℝ] ℝ) :
    Memℓp (coefficient p f) (ENNReal.ofReal q.val) := by
  apply memℓp_gen' (C := ‖f‖ ^ q.val)
  intro S
  simpa only [ENNReal.toReal_ofReal q.pos.le, Real.norm_eq_abs] using restriction_bound p q hpq f S

def restrict (f : Space ι p →L[ℝ] ℝ) : Space ι q :=
  ⟨coefficient p f, restriction_mem p q hpq f⟩

@[simp] lemma restrict_apply (f : Space ι p →L[ℝ] ℝ) (i : ι) :
    restrict p q hpq f i = coefficient p f i := rfl

lemma pairing_restrict (f : Space ι p →L[ℝ] ℝ) : pairing p q hpq (restrict p q hpq f) = f := by
  apply lp.ext_continuousLinearMap ENNReal.ofReal_ne_top
  intro i
  apply ContinuousLinearMap.ext
  intro a
  change pairing p q hpq (restrict p q hpq f) (lp.single _ i a) = f (lp.single _ i a)
  rw [pairing_single_right, restrict_apply, apply_single, mul_comm]

omit hpq in
lemma separable {ι : Type uIndex} [DecidableEq ι] (p q : PowerExponent)
    (_hpq : p.val.HolderConjugate q.val) [Countable ι] : SeparableSpace (Space ι p) :=
  LpSupport.separable (fun _ : ι => ℝ) (ENNReal.ofReal p.val) ENNReal.ofReal_ne_top

lemma dual_separable [Countable ι] : SeparableSpace (Space ι p →L[ℝ] ℝ) := by
  let : SeparableSpace (Space ι q) := separable q p hpq.symm
  have hh : Function.Surjective (pairing p q hpq (ι := ι)) :=
    fun f => ⟨restrict p q hpq f, pairing_restrict p q hpq f⟩
  exact hh.denseRange.separableSpace (pairing p q hpq).continuous

end ScalarLp

end

namespace AggregationVector

noncomputable section

open scoped ENNReal

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

lemma toLpLinear_apply (v : AggregationVector T e) (s : ι) : toLpLinear T e v s = v s := by
  change (∑ i ∈ (show ι →₀ ℝ from v).support, lp.single _ i (v i)) s = v s
  simp only [lp.coeFn_sum,Finset.sum_apply,lp.coeFn_single,Finset.sum_pi_single]
  split_ifs with hs
  · rfl
  · exact (Finsupp.notMem_support_iff.mp hs).symm

end

end AggregationVector

namespace AggregationSpace

noncomputable section

open AggregationVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

theorem finite_height_dual_separable [Countable ι] (hp : 1 < e.val)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (h : ℕ) (hh : ∀ s, T.depth s ≤ h) : SeparableSpace (AggregationSpace T e →L[ℝ] ℝ) := by
  let p : PowerExponent := ⟨e.val,hp⟩
  let : SeparableSpace (ScalarLp.Space ι p →L[ℝ] ℝ) := ScalarLp.dual_separable p p.conjugate p.holder
  exact dual_separable_of_equiv (lpEquiv T e hp hstep h hh).symm

end

end AggregationSpace

end RecursivePotentials

end OAI


