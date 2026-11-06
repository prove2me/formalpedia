-- Prove2me | Definitions.Def_BianchiIX_Dynamics_MaximalFlow
-- name    : BianchiIX_Dynamics_MaximalFlow
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T15:26:32.36971+00:00
-- url     : https://prove2.me/theorems/308e98c7-26cd-45f8-b122-add393806a8c
-- title:
--   Exact normalized solutions and their maximal interval
-- statement:
--   For real variables $p,s,a,b,c$, set
--   $$K=a^2+b^2+c^2-2(ab+bc+ca),\qquad S=p^2+s^2,\qquad C=S+K.$$
--   The shear components and wall rates are
--   $$P=Kp-2a^2+b^2+c^2+ab-2bc+ac,$$
--   $$Q=Ks+\sqrt{3}(-b^2+c^2+ab-ac),$$
--   $$r_1=-S+2p,\qquad r_2=-S-p+\sqrt{3}s,\qquad r_3=-S-p-\sqrt{3}s.$$
--   These functions define the normalized vacuum Bianchi IX vector field
--   $(P,Q,r_1a,r_2b,r_3c)$.
--
--   Let $X=\mathbb R^5$ with coordinates $x=(p,s,a,b,c)$ and the sup norm. Write
--   $$F(x)=(P,Q,r_1a,r_2b,r_3c),\qquad \mathcal C(x)=C(p,s,a,b,c),$$
--   and let $W=\{(p,s,a,b,c)\in X:a>0,\ b>0,\ c>0\}$.
--
--   For initial data $(x_0,t_0)$, an exact solution consists of an open convex
--   time domain $I$ containing $t_0$ and a curve $\alpha:\mathbb R\to X$ with
--   $\alpha(t_0)=x_0$ and $\alpha'(t)=F(\alpha(t))$ on $I$.
--   Let $I_{\max}(x_0,t_0)$ be the union of all these domains. Uniqueness makes
--   their curves agree on overlaps, defining a curve $\alpha_{\max}$ on this
--   union. The curve is assigned the value $x_0$ outside the union.
--   The construction includes proofs that the maximal domain is open and convex
--   and that this curve, with this domain, is itself an exact solution.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/MaximalFlow.lean

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique

section
open BianchiIX
noncomputable section

private theorem BianchiIX.hasDerivAt_constraint
    {p s a b c : ℝ → ℝ} {t : ℝ}
    (hp : HasDerivAt p (shearPlus (p t) (a t) (b t) (c t)) t)
    (hs : HasDerivAt s (shearMinus (s t) (a t) (b t) (c t)) t)
    (ha : HasDerivAt a (rateOne (p t) (s t) * a t) t)
    (hb : HasDerivAt b (rateTwo (p t) (s t) * b t) t)
    (hc : HasDerivAt c (rateThree (p t) (s t) * c t) t) :
    HasDerivAt (fun u => constraint (p u) (s u) (a u) (b u) (c u)) 0 t := by
  convert ((hp.pow 2).add (hs.pow 2)).add
    (((ha.pow 2).add (hb.pow 2)).add (hc.pow 2) |>.sub
      ((((ha.mul hb).add (hb.mul hc)).add (hc.mul ha)).const_mul 2)) using 1 <;>
    first | rfl | (norm_num [constraint, shearSq, curvature, shearPlus, shearMinus,
      rateOne, rateTwo, rateThree]; ring)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.contDiff_normalizedField (n : WithTop ℕ∞) : ContDiff ℝ n normalizedField := by
  rw [contDiff_pi]
  intro i
  fin_cases i <;>
    dsimp [normalizedField, shearPlus, shearMinus, rateOne, rateTwo, rateThree, shearSq, curvature] <;>
    fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasDerivAt_normalized_components {α : ℝ → NormalizedState} {t : ℝ}
    (hα : HasDerivAt α (normalizedField (α t)) t) :
    HasDerivAt (fun u => α u 0) (shearPlus (α t 0) (α t 2) (α t 3) (α t 4)) t ∧
    HasDerivAt (fun u => α u 1) (shearMinus (α t 1) (α t 2) (α t 3) (α t 4)) t ∧
    HasDerivAt (fun u => α u 2) (rateOne (α t 0) (α t 1) * α t 2) t ∧
    HasDerivAt (fun u => α u 3) (rateTwo (α t 0) (α t 1) * α t 3) t ∧
    HasDerivAt (fun u => α u 4) (rateThree (α t 0) (α t 1) * α t 4) t :=
  ⟨hasDerivAt_pi.mp hα 0, hasDerivAt_pi.mp hα 1, hasDerivAt_pi.mp hα 2,
    hasDerivAt_pi.mp hα 3, hasDerivAt_pi.mp hα 4⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasDerivAt_stateConstraint {α : ℝ → NormalizedState} {t : ℝ}
    (hα : HasDerivAt α (normalizedField (α t)) t) :
    HasDerivAt (fun u => stateConstraint (α u)) 0 t := by
  obtain ⟨hp, hs, ha, hb, hc⟩ := hasDerivAt_normalized_components hα
  exact hasDerivAt_constraint hp hs ha hb hc

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.normalized_constraint_constant {I : Set ℝ} (hI : Convex ℝ I)
    {α : ℝ → NormalizedState} (hα : ∀ t ∈ I, HasDerivAt α (normalizedField (α t)) t)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I) :
    stateConstraint (α t) = stateConstraint (α t₀) := by
  have H := hI.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (hasDerivAt_stateConstraint (hα u hu)).hasDerivWithinAt)
    (C := 0) (fun _ _ => by simp) ht₀ ht
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using H

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology NNReal

private theorem BianchiIX.normalizedField_lipschitz_closedBall (x : NormalizedState) (r : ℝ) :
    ∃ L : ℝ≥0, LipschitzOnWith L normalizedField (closedBall x r) :=
  (contDiff_normalizedField 1).contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall x r) (isCompact_closedBall x r)

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology NNReal

private theorem BianchiIX.normalized_solution_unique_Icc {α β : ℝ → NormalizedState} {a b t₀ : ℝ}
    (hα : ∀ t ∈ Icc a b, HasDerivAt α (normalizedField (α t)) t)
    (hβ : ∀ t ∈ Icc a b, HasDerivAt β (normalizedField (β t)) t)
    (ht₀ : t₀ ∈ Icc a b) (heq : α t₀ = β t₀) : EqOn α β (Icc a b) := by
  have hcα := HasDerivAt.continuousOn hα
  have hcβ := HasDerivAt.continuousOn hβ
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hcα
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcβ
  obtain ⟨L, hL⟩ := normalizedField_lipschitz_closedBall 0 (max A B)
  have hαball (t : ℝ) (ht : t ∈ Icc a b) : α t ∈ closedBall 0 (max A B) := by
    simpa only [mem_closedBall, dist_zero_right] using (hA t ht).trans (le_max_left A B)
  have hβball (t : ℝ) (ht : t ∈ Icc a b) : β t ∈ closedBall 0 (max A B) := by
    simpa only [mem_closedBall, dist_zero_right] using (hB t ht).trans (le_max_right A B)
  have hleft : Icc a t₀ ⊆ Icc a b := Icc_subset_Icc_right ht₀.2
  have hright : Icc t₀ b ⊆ Icc a b := Icc_subset_Icc_left ht₀.1
  rw [← Icc_union_Icc_eq_Icc ht₀.1 ht₀.2]
  apply EqOn.union
  · exact ODE_solution_unique_of_mem_Icc_left
      (v := fun _ => normalizedField) (s := fun _ => closedBall 0 (max A B))
      (fun _ _ => hL) (hcα.mono hleft)
      (fun t ht => (hα t (hleft (Ioc_subset_Icc_self ht))).hasDerivWithinAt)
      (fun t ht => hαball t (hleft (Ioc_subset_Icc_self ht))) (hcβ.mono hleft)
      (fun t ht => (hβ t (hleft (Ioc_subset_Icc_self ht))).hasDerivWithinAt)
      (fun t ht => hβball t (hleft (Ioc_subset_Icc_self ht))) heq
  · exact ODE_solution_unique_of_mem_Icc_right
      (v := fun _ => normalizedField) (s := fun _ => closedBall 0 (max A B))
      (fun _ _ => hL) (hcα.mono hright)
      (fun t ht => (hα t (hright (Ico_subset_Icc_self ht))).hasDerivWithinAt)
      (fun t ht => hαball t (hright (Ico_subset_Icc_self ht))) (hcβ.mono hright)
      (fun t ht => (hβ t (hright (Ico_subset_Icc_self ht))).hasDerivWithinAt)
      (fun t ht => hβball t (hright (Ico_subset_Icc_self ht))) heq

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology NNReal

private theorem BianchiIX.normalized_solution_unique {I : Set ℝ} (hI : Convex ℝ I)
    {α β : ℝ → NormalizedState} {t₀ : ℝ}
    (hα : ∀ t ∈ I, HasDerivAt α (normalizedField (α t)) t)
    (hβ : ∀ t ∈ I, HasDerivAt β (normalizedField (β t)) t)
    (ht₀ : t₀ ∈ I) (heq : α t₀ = β t₀) : EqOn α β I := by
  intro t ht
  have hsub : uIcc t₀ t ⊆ I := hI.ordConnected.uIcc_subset ht₀ ht
  exact normalized_solution_unique_Icc (fun u hu => hα u (hsub hu))
    (fun u hu => hβ u (hsub hu)) left_mem_uIcc heq right_mem_uIcc

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology NNReal

private theorem BianchiIX.exists_normalized_localFlow (x₀ : NormalizedState) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ Φ : NormalizedState × ℝ → NormalizedState,
      ContinuousOn Φ (closedBall x₀ r ×ˢ Icc (t₀ - ε) (t₀ + ε)) ∧
      ∀ x ∈ closedBall x₀ r, Φ (x, t₀) = x ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt (fun u => Φ (x, u)) (normalizedField (Φ (x, t))) t ∧
          stateConstraint (Φ (x, t)) = stateConstraint x := by
  obtain ⟨ε, hε, a, r, L, K, hr, hPL⟩ :=
    IsPicardLindelof.of_contDiffAt_one ((contDiff_normalizedField 1).contDiffAt (x := x₀))
  obtain ⟨Φ, hΦ, hcΦ⟩ := (hPL t₀).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  refine ⟨r, hr, ε, hε, Φ, hcΦ, ?_⟩
  intro x hx
  have hODE (t : ℝ) (ht : t ∈ Ioo (t₀ - ε) (t₀ + ε)) :
      HasDerivAt (fun u => Φ (x, u)) (normalizedField (Φ (x, t))) t :=
    ((hΦ x hx).2 t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  refine ⟨(hΦ x hx).1, fun t ht => ⟨hODE t ht, ?_⟩⟩
  have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := by constructor <;> linarith
  exact (normalized_constraint_constant (convex_Ioo _ _) hODE ht₀ ht).trans
    (congrArg stateConstraint (hΦ x hx).1)

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology NNReal

private theorem BianchiIX.exists_normalized_solution (x₀ : NormalizedState) (t₀ : ℝ) :
    ∃ α : ℝ → NormalizedState, α t₀ = x₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt α (normalizedField (α t)) t ∧ stateConstraint (α t) = stateConstraint x₀ := by
  obtain ⟨r, hr, ε, hε, Φ, _, hΦ⟩ := exists_normalized_localFlow x₀ t₀
  exact ⟨fun t => Φ (x₀, t), (hΦ x₀ (mem_closedBall_self hr.le)).1,
    ε, hε, (hΦ x₀ (mem_closedBall_self hr.le)).2⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology NNReal

private theorem BianchiIX.convex_union_real {I J : Set ℝ} (hI : Convex ℝ I) (hJ : Convex ℝ J)
    {s : ℝ} (hsI : s ∈ I) (hsJ : s ∈ J) : Convex ℝ (I ∪ J) := by
  rw [convex_iff_ordConnected]
  refine ⟨fun x hx y hy z hz => ?_⟩
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact Or.inl (hI.ordConnected.out hx hy hz)
  · by_cases hzs : z ≤ s
    · exact Or.inl (hI.ordConnected.out hx hsI ⟨hz.1, hzs⟩)
    · exact Or.inr (hJ.ordConnected.out hsJ hy ⟨le_of_not_ge hzs, hz.2⟩)
  · by_cases hzs : z ≤ s
    · exact Or.inr (hJ.ordConnected.out hx hsJ ⟨hz.1, hzs⟩)
    · exact Or.inl (hI.ordConnected.out hsI hy ⟨le_of_not_ge hzs, hz.2⟩)
  · exact Or.inr (hJ.ordConnected.out hx hy hz)

end
end


noncomputable section

namespace BianchiIX

open Set Filter Metric
open scoped Topology

/-- An exact solution on an open interval containing its initial time. -/
structure NormalizedSolution (x₀ : NormalizedState) (t₀ : ℝ) where
  domain : Set ℝ
  isOpen_domain : IsOpen domain
  convex_domain : Convex ℝ domain
  initial_mem : t₀ ∈ domain
  curve : ℝ → NormalizedState
  initial_eq : curve t₀ = x₀
  hasDerivAt : ∀ t ∈ domain, HasDerivAt curve (normalizedField (curve t)) t

theorem nonempty_normalizedSolution (x₀ : NormalizedState) (t₀ : ℝ) :
    Nonempty (NormalizedSolution x₀ t₀) := by
  obtain ⟨α, hinit, ε, hε, hα⟩ := exists_normalized_solution x₀ t₀
  exact ⟨⟨Ioo (t₀ - ε) (t₀ + ε), isOpen_Ioo, convex_Ioo _ _,
    by constructor <;> linarith, α, hinit, fun t ht => (hα t ht).1⟩⟩

theorem NormalizedSolution.compatible {x₀ : NormalizedState} {t₀ : ℝ}
    (S T : NormalizedSolution x₀ t₀) : EqOn S.curve T.curve (S.domain ∩ T.domain) :=
  normalized_solution_unique (S.convex_domain.inter T.convex_domain)
    (fun t ht => S.hasDerivAt t ht.1) (fun t ht => T.hasDerivAt t ht.2)
    ⟨S.initial_mem, T.initial_mem⟩ (S.initial_eq.trans T.initial_eq.symm)

def normalizedMaxDomain (x₀ : NormalizedState) (t₀ : ℝ) : Set ℝ :=
  ⋃ S : NormalizedSolution x₀ t₀, S.domain

def normalizedMaxCurve (x₀ : NormalizedState) (t₀ t : ℝ) : NormalizedState := by
  classical
  exact if h : t ∈ normalizedMaxDomain x₀ t₀ then
    (mem_iUnion.mp h).choose.curve t else x₀

theorem NormalizedSolution.domain_subset_maximal {x₀ : NormalizedState} {t₀ : ℝ}
    (S : NormalizedSolution x₀ t₀) : S.domain ⊆ normalizedMaxDomain x₀ t₀ :=
  subset_iUnion (fun T : NormalizedSolution x₀ t₀ => T.domain) S

theorem normalizedMaxCurve_eqOn {x₀ : NormalizedState} {t₀ : ℝ}
    (S : NormalizedSolution x₀ t₀) : EqOn (normalizedMaxCurve x₀ t₀) S.curve S.domain := by
  classical
  intro t ht
  have hmem := S.domain_subset_maximal ht
  simp only [normalizedMaxCurve, dif_pos hmem]
  exact ((mem_iUnion.mp hmem).choose.compatible S) ⟨(mem_iUnion.mp hmem).choose_spec, ht⟩

theorem isOpen_normalizedMaxDomain (x₀ : NormalizedState) (t₀ : ℝ) :
    IsOpen (normalizedMaxDomain x₀ t₀) :=
  isOpen_iUnion fun S => S.isOpen_domain

theorem convex_normalizedMaxDomain (x₀ : NormalizedState) (t₀ : ℝ) :
    Convex ℝ (normalizedMaxDomain x₀ t₀) := by
  rw [convex_iff_ordConnected]
  refine ⟨fun x hx y hy z hz => ?_⟩
  obtain ⟨S, hx⟩ := mem_iUnion.mp hx
  obtain ⟨T, hy⟩ := mem_iUnion.mp hy
  have hzST := (convex_union_real S.convex_domain T.convex_domain
    S.initial_mem T.initial_mem).ordConnected.out (Or.inl hx) (Or.inr hy) hz
  exact (union_subset S.domain_subset_maximal T.domain_subset_maximal) hzST

theorem initial_mem_normalizedMaxDomain (x₀ : NormalizedState) (t₀ : ℝ) :
    t₀ ∈ normalizedMaxDomain x₀ t₀ := by
  obtain ⟨S⟩ := nonempty_normalizedSolution x₀ t₀
  exact S.domain_subset_maximal S.initial_mem

theorem normalizedMaxCurve_initial (x₀ : NormalizedState) (t₀ : ℝ) :
    normalizedMaxCurve x₀ t₀ t₀ = x₀ := by
  obtain ⟨S⟩ := nonempty_normalizedSolution x₀ t₀
  exact (normalizedMaxCurve_eqOn S S.initial_mem).trans S.initial_eq

theorem hasDerivAt_normalizedMaxCurve {x₀ : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x₀ t₀) :
    HasDerivAt (normalizedMaxCurve x₀ t₀) (normalizedField (normalizedMaxCurve x₀ t₀ t)) t := by
  obtain ⟨S, ht⟩ := mem_iUnion.mp ht
  rw [normalizedMaxCurve_eqOn S ht]
  exact (S.hasDerivAt t ht).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (S.isOpen_domain.mem_nhds ht)
      fun u hu => normalizedMaxCurve_eqOn S hu)

/-- The union of all compatible local solutions is itself a solution. -/
def maximalNormalizedSolution (x₀ : NormalizedState) (t₀ : ℝ) : NormalizedSolution x₀ t₀ where
  domain := normalizedMaxDomain x₀ t₀
  isOpen_domain := isOpen_normalizedMaxDomain x₀ t₀
  convex_domain := convex_normalizedMaxDomain x₀ t₀
  initial_mem := initial_mem_normalizedMaxDomain x₀ t₀
  curve := normalizedMaxCurve x₀ t₀
  initial_eq := normalizedMaxCurve_initial x₀ t₀
  hasDerivAt := fun _ ht => hasDerivAt_normalizedMaxCurve ht



end BianchiIX


