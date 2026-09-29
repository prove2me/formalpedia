-- Prove2me | solution 1 for AutomorphicForm.exists_isFactorizableTestFn_isBiInvariantUnder_forall_archCasimirAt_convOp_eq_convOp_of_isReal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/cfc527d3-8d80-543c-a641-3e3b6219820b

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_AutomorphicForm_archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isFactorizableTestFn_isBiInvariantUnder_forall_archCasimirAt_convOp_eq_convOp_of_isReal

set_option autoImplicit false

noncomputable section

open scoped Classical
open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel
open IsDedekindDomain AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace ShiftReal

variable {K : Type} [Field K] [NumberField K]

def L {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) (α : AdelicGL2 (𝓞 K) K → ℂ) :
    AdelicGL2 (𝓞 K) K → ℂ :=
  fun y => deriv (fun t : ℝ => α (archFlowAt hw d (-t) * y)) 0

def Rep (α : AdelicGL2 (𝓞 K) K → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ) : Prop :=
  IsArchTestFactor K fa ∧ IsFinTestFactor K ff ∧ ∀ g, α g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)

theorem Rep.isFactorizableTestFn {α : AdelicGL2 (𝓞 K) K → ℂ} {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ} (h : Rep α fa ff) : IsFactorizableTestFn K α :=
  ⟨fa, ff, h.1, h.2.1, h.2.2⟩

theorem exists_rep_of_isFactorizableTestFn {α : AdelicGL2 (𝓞 K) K → ℂ} (h : IsFactorizableTestFn K α) :
    ∃ fa ff, Rep α fa ff := by
  obtain ⟨fa, ff, hfa, hff, hrepr⟩ := h
  exact ⟨fa, ff, hfa, hff, hrepr⟩

theorem exists_rep_L {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) {α : AdelicGL2 (𝓞 K) K → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ}
    (h : Rep α fa ff) : ∃ fa', Rep (L hw d α) fa' ff := by
  obtain ⟨fa', hfa', heq⟩ :=
    (AutomorphicForm.archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn K hw d).2.1 fa ff h.1
  refine ⟨fa', hfa', h.2.1, fun g => ?_⟩
  have hL : L hw d α = fun y => deriv (fun t : ℝ => fa (glArch (𝓞 K) K (archFlowAt hw d (-t) * y)) *
      ff (glFin (𝓞 K) K (archFlowAt hw d (-t) * y))) 0 := by
    funext y
    simp only [L, h.2.2]
  rw [hL, heq]

theorem isArchTestFactor_add {fa fb : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    (ha : IsArchTestFactor K fa) (hb : IsArchTestFactor K fb) : IsArchTestFactor K (fa + fb) := by
  obtain ⟨⟨Φ, hΦ, hΦe⟩, hca⟩ := ha
  obtain ⟨⟨Ψ, hΨ, hΨe⟩, hcb⟩ := hb
  exact ⟨⟨Φ + Ψ, hΦ.add hΨ, fun g => by simp [hΦe g, hΨe g]⟩, hca.add hcb⟩

theorem isArchTestFactor_smul (c : ℂ) {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    (ha : IsArchTestFactor K fa) : IsArchTestFactor K (c • fa) := by
  obtain ⟨⟨Φ, hΦ, hΦe⟩, hca⟩ := ha
  refine ⟨⟨c • Φ, hΦ.const_smul c, fun g => by simp [hΦe g]⟩, ?_⟩
  exact hca.smul_left

theorem Rep.add {α β : AdelicGL2 (𝓞 K) K → ℂ} {fa fb : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ} (ha : Rep α fa ff) (hb : Rep β fb ff) :
    Rep (α + β) (fa + fb) ff :=
  ⟨isArchTestFactor_add ha.1 hb.1, ha.2.1, fun g => by
    simp only [Pi.add_apply, ha.2.2 g, hb.2.2 g]; ring⟩

theorem Rep.smul (c : ℂ) {α : AdelicGL2 (𝓞 K) K → ℂ} {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ} (ha : Rep α fa ff) : Rep (c • α) (c • fa) ff :=
  ⟨isArchTestFactor_smul c ha.1, ha.2.1, fun g => by
    simp only [Pi.smul_apply, smul_eq_mul, ha.2.2 g]; ring⟩

theorem Rep.neg {α : AdelicGL2 (𝓞 K) K → ℂ} {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ} (ha : Rep α fa ff) : Rep (-α) ((-1 : ℂ) • fa) ff := by
  have := ha.smul (-1)
  rwa [neg_one_smul] at this

theorem isBiInvariantUnder_L {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir)
    {U : Subgroup (AdelicGL2 (𝓞 K) K)} (hU : U ≤ finiteAdelicGL2Subgroup K)
    {α : AdelicGL2 (𝓞 K) K → ℂ} (hα : IsBiInvariantUnder K U α) : IsBiInvariantUnder K U (L hw d α) := by
  intro u hu g
  have hk : glArch (𝓞 K) K u = 1 := (mem_finiteAdelicGL2Subgroup_iff K u).1 (hU hu)
  constructor
  · simp only [L]
    congr 1
    funext t
    rw [← mul_assoc, archFlowAt_mul_comm_of_glArch_eq_one hw d (-t) hk, mul_assoc]
    exact (hα u hu _).1
  · simp only [L]
    congr 1
    funext t
    rw [← mul_assoc]
    exact (hα u hu _).2

theorem biInv_add {U : Subgroup (AdelicGL2 (𝓞 K) K)} {α β : AdelicGL2 (𝓞 K) K → ℂ}
    (hα : IsBiInvariantUnder K U α) (hβ : IsBiInvariantUnder K U β) : IsBiInvariantUnder K U (α + β) :=
  fun u hu g => ⟨by simp only [Pi.add_apply, (hα u hu g).1, (hβ u hu g).1],
    by simp only [Pi.add_apply, (hα u hu g).2, (hβ u hu g).2]⟩

theorem biInv_smul {U : Subgroup (AdelicGL2 (𝓞 K) K)} (c : ℂ) {α : AdelicGL2 (𝓞 K) K → ℂ}
    (hα : IsBiInvariantUnder K U α) : IsBiInvariantUnder K U (c • α) :=
  fun u hu g => ⟨by simp only [Pi.smul_apply, (hα u hu g).1], by simp only [Pi.smul_apply, (hα u hu g).2]⟩

theorem biInv_neg {U : Subgroup (AdelicGL2 (𝓞 K) K)} {α : AdelicGL2 (𝓞 K) K → ℂ}
    (hα : IsBiInvariantUnder K U α) : IsBiInvariantUnder K U (-α) :=
  fun u hu g => ⟨by simp only [Pi.neg_apply, (hα u hu g).1], by simp only [Pi.neg_apply, (hα u hu g).2]⟩

theorem integrable_mul_of_continuous_of_test (x : AdelicGL2 (𝓞 K) K → ℂ) (hx : Continuous x)
    {α : AdelicGL2 (𝓞 K) K → ℂ} (hα : IsFactorizableTestFn K α) (g : AdelicGL2 (𝓞 K) K) :
    Integrable (fun y => x (g * y) * α y) (adelicGLHaar (Fin 2) (𝓞 K) K) := by
  obtain ⟨hc, hcs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K α hα
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  refine Continuous.integrable_of_hasCompactSupport ((hx.comp (continuous_const_mul g)).mul hc) ?_
  exact hcs.mul_left

theorem rightConv_add_test (x : AdelicGL2 (𝓞 K) K → ℂ) (hx : Continuous x)
    {α β : AdelicGL2 (𝓞 K) K → ℂ} (hα : IsFactorizableTestFn K α) (hβ : IsFactorizableTestFn K β) :
    rightConv K x (α + β) = rightConv K x α + rightConv K x β := by
  funext g
  simp only [rightConv, Pi.add_apply]
  rw [← integral_add (integrable_mul_of_continuous_of_test x hx hα g) (integrable_mul_of_continuous_of_test x hx hβ g)]
  congr 1; funext y; ring

theorem rightConv_smul_test (x : AdelicGL2 (𝓞 K) K → ℂ) (c : ℂ) (α : AdelicGL2 (𝓞 K) K → ℂ) :
    rightConv K x (c • α) = c • rightConv K x α := by
  funext g
  simp only [rightConv, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext y; ring

theorem rightConv_neg_test (x : AdelicGL2 (𝓞 K) K → ℂ) (α : AdelicGL2 (𝓞 K) K → ℂ) :
    rightConv K x (-α) = -rightConv K x α := by
  have := rightConv_smul_test x (-1) α
  rwa [neg_one_smul, neg_one_smul] at this

end ShiftReal

open ShiftReal in
theorem solution
    (K : Type) [Field K] [NumberField K] (w : InfinitePlace K) (hw : w.IsReal)
    (U : Subgroup (AdelicGL2 (𝓞 K) K)) (hU : U ≤ finiteAdelicGL2Subgroup K)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hff : IsFactorizableTestFn K f) (hfU : IsBiInvariantUnder K U f) :
    ∃ β : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K β ∧ IsBiInvariantUnder K U β ∧
      ∀ x : AdelicGL2 (𝓞 K) K → ℂ, Continuous x →
        IsArchSmoothAt hw (convOp K f x) ∧ archCasimirAt hw (convOp K f x) = convOp K β x := by
  classical
  obtain ⟨fa, ff, hrep⟩ := ShiftReal.exists_rep_of_isFactorizableTestFn hff
  have D := (AutomorphicForm.archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn K hw)

  obtain ⟨faH, hrepH⟩ := ShiftReal.exists_rep_L hw .H hrep
  obtain ⟨faHH, hrepHH⟩ := ShiftReal.exists_rep_L hw .H hrepH
  obtain ⟨faF, hrepF⟩ := ShiftReal.exists_rep_L hw .Fm hrep
  obtain ⟨faEF, hrepEF⟩ := ShiftReal.exists_rep_L hw .E hrepF
  set αH := ShiftReal.L hw .H f with hαH
  set αHH := ShiftReal.L hw .H αH with hαHH
  set αF := ShiftReal.L hw .Fm f with hαF
  set αEF := ShiftReal.L hw .E αF with hαEF

  have hUH := ShiftReal.isBiInvariantUnder_L hw .H hU hfU
  have hUHH := ShiftReal.isBiInvariantUnder_L hw .H hU hUH
  have hUF := ShiftReal.isBiInvariantUnder_L hw .Fm hU hfU
  have hUEF := ShiftReal.isBiInvariantUnder_L hw .E hU hUF

  set β : AdelicGL2 (𝓞 K) K → ℂ := -((1 / 4 : ℂ) • αHH + (-1 : ℂ) • ((1 / 2 : ℂ) • αH) + αEF) with hβ
  have hrepA := hrepHH.smul (1 / 4 : ℂ)
  have hrepB := (hrepH.smul (1 / 2 : ℂ)).smul (-1 : ℂ)
  have hrepAB := hrepA.add hrepB
  have hrepABC := hrepAB.add hrepEF
  have hrepβ := hrepABC.neg
  have hβU : IsBiInvariantUnder K U β :=
    ShiftReal.biInv_neg (ShiftReal.biInv_add (ShiftReal.biInv_add (ShiftReal.biInv_smul _ hUHH)
      (ShiftReal.biInv_smul _ (ShiftReal.biInv_smul _ hUH))) hUEF)
  refine ⟨β, hrepβ.isFactorizableTestFn, hβU, fun x hx => ?_⟩

  have s1 := (D .H).1 x f hx hff
  have s2 := (D .H).1 x αH hx hrepH.isFactorizableTestFn
  have s3 := (D .Fm).1 x f hx hff
  have s4 := (D .E).1 x αF hx hrepF.isFactorizableTestFn
  refine ⟨by rw [convOp_apply]; exact s1.1, ?_⟩
  rw [convOp_apply, convOp_apply]
  have eH : archDerivAt hw .H (rightConv K x f) = rightConv K x αH := s1.2
  have eHH : archDerivAt hw .H (archDerivAt hw .H (rightConv K x f)) = rightConv K x αHH := by rw [eH]; exact s2.2
  have eF : archDerivAt hw .Fm (rightConv K x f) = rightConv K x αF := s3.2
  have eEF : archDerivAt hw .E (archDerivAt hw .Fm (rightConv K x f)) = rightConv K x αEF := by rw [eF]; exact s4.2

  have lhs : archCasimirAt hw (rightConv K x f) =
      -((1 / 4 : ℂ) • rightConv K x αHH - (1 / 2 : ℂ) • rightConv K x αH + rightConv K x αEF) := by
    show -((1 / 4 : ℂ) • archDerivAt hw .H (archDerivAt hw .H (rightConv K x f)) -
        (1 / 2 : ℂ) • archDerivAt hw .H (rightConv K x f) +
        archDerivAt hw .E (archDerivAt hw .Fm (rightConv K x f))) = _
    rw [eHH, eEF, eH]

  have rhs : rightConv K x β =
      -((1 / 4 : ℂ) • rightConv K x αHH + (-1 : ℂ) • ((1 / 2 : ℂ) • rightConv K x αH) + rightConv K x αEF) := by
    simp only [hβ]
    rw [ShiftReal.rightConv_neg_test, ShiftReal.rightConv_add_test x hx hrepAB.isFactorizableTestFn
      hrepEF.isFactorizableTestFn, ShiftReal.rightConv_add_test x hx hrepA.isFactorizableTestFn
      hrepB.isFactorizableTestFn, ShiftReal.rightConv_smul_test, ShiftReal.rightConv_smul_test,
      ShiftReal.rightConv_smul_test]
  rw [lhs, rhs, neg_one_smul, sub_eq_add_neg]

#print axioms solution

end
end S_AutomorphicForm_exists_isFactorizableTestFn_isBiInvariantUnder_forall_archCasimirAt_convOp_eq_convOp_of_isReal
end P2MW
export P2MW.S_AutomorphicForm_exists_isFactorizableTestFn_isBiInvariantUnder_forall_archCasimirAt_convOp_eq_convOp_of_isReal (solution)
