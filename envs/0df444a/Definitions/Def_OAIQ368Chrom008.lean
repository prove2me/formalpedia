-- Prove2me | Definitions.Def_OAIQ368Chrom008
-- name    : OAIQ368Chrom008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:16:03.390217+00:00
-- url     : https://prove2.me/theorems/b79918d6-8fa0-4064-9738-af7085dc57e3
-- title:
--   Definitions bundle OAIQ368Chrom008 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 106 declarations of OpenAI's Lean: 37 definitions and 69 theorems. The definitions and types are `OAI.ElementaryPositivity.QuantumTorus.incomingSolution`, `OAI.ElementaryPositivity.QuantumTorus.incomingSolutionCoefficients`, `OAI.ElementaryPositivity.QuantumTorus.incomingTruncation`, `OAI.ElementaryPositivity.QuantumTorus.literalIncomingLog`, `OAI.ElementaryPositivity.QuantumTorus.literalTotalTransport`, `OAI.ElementaryPositivity.QuantumTorus.mutatedLineCompletion`, `OAI.ElementaryPositivity.QuantumTorus.mutatedLineFactor`, `OAI.ElementaryPositivity.QuantumTorus.mutatedLineProduct`, `OAI.ElementaryPositivity.QuantumTorus.mutatedPathCompletedPositive`, `OAI.ElementaryPositivity.QuantumTorus.mutatedPathCompletion`, `OAI.ElementaryPositivity.QuantumTorus.mutatedPathProduct`, `OAI.ElementaryPositivity.QuantumTorus.mutatedTransport`, `OAI.ElementaryPositivity.QuantumTorus.negativeCovectorUnit`, `OAI.ElementaryPositivity.QuantumTorus.noncutOldLineFactor`, `OAI.ElementaryPositivity.QuantumTorus.pureFaceLogAddCommGroup`, `OAI.ElementaryPositivity.QuantumTorus.pureFaceLogAddCommMonoid`, `OAI.ElementaryPositivity.QuantumTorus.pureFaceLogAddGroup`, `OAI.ElementaryPositivity.QuantumTorus.pureFaceProjectionAddCommGroup`, `OAI.ElementaryPositivity.QuantumTorus.pureFaceProjectionAddGroup`, `OAI.ElementaryPositivity.QuantumTorus.rootChartRatio`, `OAI.ElementaryPositivity.QuantumTorus.simpleCompleted`, `OAI.ElementaryPositivity.QuantumTorus.simpleOriented`, `OAI.ElementaryPositivity.QuantumTorus.simpleOrientedCompleted`, `OAI.ElementaryPositivity.QuantumTorus.simpleTotalTransport`, `OAI.ElementaryPositivity.RationalFiber.actualInfinityPathProductUnit`, `OAI.ElementaryPositivity.RationalFiber.actualLineLetter`, `OAI.ElementaryPositivity.RationalFiber.actualLineWord`, `OAI.ElementaryPositivity.RationalFiber.actualPathAction`, `OAI.ElementaryPositivity.RationalFiber.actualPathWord`, `OAI.ElementaryPositivity.RationalFiber.comparisonAction`, `OAI.ElementaryPositivity.RationalFiber.comparisonOld`, `OAI.ElementaryPositivity.RationalFiber.comparisonWordAction`, `OAI.ElementaryPositivity.RationalFiber.comparisonWordOld`, `OAI.ElementaryPositivity.RationalFiber.covectorNegativeUnit`, `OAI.ElementaryPositivity.RationalFiber.lineNegativeUnit`, `OAI.ElementaryPositivity.RationalFiber.mutatedPathProductPositive`, `OAI.ElementaryPositivity.RationalFiber.oldPureUnit`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Chromatic_GradedAlgebra_HalfspacePolynomialCoefficients`, `Chromatic_GradedAlgebra_MutationDegreeBound`, `Chromatic_GradedAlgebra_PureFaceLog`, `Chromatic_GradedAlgebra_SimpleBinomial`, `Chromatic_QuantumTorus_GlobalFiberBound`, `Chromatic_QuantumTorus_MutationFiberArithmetic`, `Chromatic_QuantumTorus_PureFaceProjection`, `Chromatic_QuantumTorus_SimplePlaneGeometry`, `Chromatic_QuantumTorus_UpstreamFiber`, `Chromatic_QuantumTorus_UpstreamSimpleFiber`, `Chromatic_Walls_ComparisonLine`, `Chromatic_Walls_CompletedPathAction`, `Chromatic_Walls_CompletedPureComparison`, `Chromatic_Walls_FiniteRefinementImportAll`, `Chromatic_Walls_GlobalWallPositive`, `Chromatic_Walls_IncomingRayElement`, `Chromatic_Walls_IncomingSystem`, `Chromatic_Walls_InfinityPath`, `Chromatic_Walls_LineOldTransport`, `Chromatic_Walls_MutatedLineCompletion`, `Chromatic_Walls_MutatedNoCutTransport`, `Chromatic_Walls_MutatedPathCompletion`, `Chromatic_Walls_MutatedPathIndependent`, `Chromatic_Walls_OffCutJoint`, `Chromatic_Walls_PathOldTransport`, `Chromatic_Walls_PureCutFactorization`, `Chromatic_Walls_SimpleAdjointFiber`, `Chromatic_Walls_SimpleIncomingData`, `Chromatic_Walls_SimpleIncomingElement`, `Chromatic_Walls_WallRegrade`.
--
--   **Imports.** It imports the bundle `OAIQ368Chrom007` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ368Chrom012` and `OAIQ368Chrom024`; the statements `OAI.ElementaryPositivity.QuantumTorus.halfspace_canonical_polynomial_coefficients`, `OAI.ElementaryPositivity.QuantumTorus.mutatedIncoming_probe`, `OAI.ElementaryPositivity.QuantumTorus.mutatedTransport_canonical`, `OAI.ElementaryPositivity.QuantumTorus.mutatedTransport_negative_ratio`, `OAI.ElementaryPositivity.RationalFiber.actualInfinityPath_loop_commute`, `OAI.ElementaryPositivity.RationalFiber.actualInfinityPath_product_square`, `OAI.ElementaryPositivity.RationalFiber.actualPath_rational_loop_coefficient` and `OAI.ElementaryPositivity.RationalFiber.finite_refinement_import`; the proofs of `OAI.ElementaryPositivity.QuantumTorus.halfspace_canonical_polynomial_coefficients`, `OAI.ElementaryPositivity.QuantumTorus.mutatedIncoming_probe`, `OAI.ElementaryPositivity.QuantumTorus.mutatedTransport_canonical`, `OAI.ElementaryPositivity.QuantumTorus.mutatedTransport_negative_ratio`, `OAI.ElementaryPositivity.QuantumTorus.positive_sections`, `OAI.ElementaryPositivity.RationalFiber.actualInfinityPath_loop_commute` and `OAI.ElementaryPositivity.RationalFiber.actualPath_rational_loop_coefficient`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom007

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_IncomingSystem
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries ElementaryPositivity.PowerSeriesSplit
noncomputable section

variable {R M I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
attribute [local instance] Classical.propDecidable

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instAddGroupTorus_1
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instSubTorus_1
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instModuleRatTorus
lemma incomingCoefficient_graded (n : ℕ) (f : PowerSeries (Torus v Ω)) :
    incomingCoefficient v Ω C n f ∈ rootGrade v Ω C n := by
  intro m hm
  rw [incomingCoefficient_apply,ite_eq_right hm]

def incomingSolutionCoefficients (l : ℕ → Torus v Ω) : ℕ → Torus v Ω
  | 0 => 1
  | n+1 => l (n+1)-incomingCoefficient v Ω C (n+1)
    (PowerSeries.mk (fun k => if _ : k≤n then incomingSolutionCoefficients l k else 0))
termination_by n => n

def incomingSolution (l : ℕ → Torus v Ω) : PowerSeries (Torus v Ω) :=
  PowerSeries.mk (incomingSolutionCoefficients v Ω C l)

lemma incomingSolution_constant (l : ℕ → Torus v Ω) :
    constantCoeff (incomingSolution v Ω C l)=1 := by
  rw [←coeff_zero_eq_constantCoeff_apply]
  simp only [incomingSolution,coeff_mk,incomingSolutionCoefficients]

lemma incomingSolution_graded (l : ℕ → Torus v Ω)
    (hl : ∀n,l n∈rootGrade v Ω C n) (n : ℕ) :
    coeff n (incomingSolution v Ω C l)∈rootGrade v Ω C n := by
  cases n with
  | zero => simpa only [coeff_zero_eq_constantCoeff_apply,incomingSolution_constant] using rootGrade_one v Ω C
  | succ n =>
    simp only [incomingSolution,coeff_mk,incomingSolutionCoefficients]
    intro m hm
    rw [torus_sub_apply,hl _ m hm,incomingCoefficient_graded v Ω C _ _ m hm,sub_self]

def incomingTruncation (l : ℕ → Torus v Ω) (n : ℕ) : PowerSeries (Torus v Ω) :=
  PowerSeries.mk (fun k => if k≤n then incomingSolutionCoefficients v Ω C l k else 0)

lemma incomingTruncation_lower (l : ℕ → Torus v Ω) (n k : ℕ) (hk : k≤n) :
    coeff k (incomingSolution v Ω C l)=coeff k (incomingTruncation v Ω C l n) := by
  simp only [incomingSolution,incomingTruncation,coeff_mk,ite_eq_left hk]

lemma incomingTruncation_top (l : ℕ → Torus v Ω) (n : ℕ) :
    coeff (n+1) (incomingTruncation v Ω C l n)=0 := by
  simp only [incomingTruncation,coeff_mk,show ¬n+1≤n by omega,ite_false, if_false]

lemma incomingSolution_step (l : ℕ → Torus v Ω) (n : ℕ) :
    coeff (n+1) (incomingSolution v Ω C l)=
      l (n+1)-incomingCoefficient v Ω C (n+1) (incomingTruncation v Ω C l n) := by
  simp only [incomingSolution,coeff_mk,incomingSolutionCoefficients,incomingTruncation,dite_eq_ite]

lemma incomingSolution_prescription_difference (hΩ : ∀m,Ω m m=0) (l : ℕ → Torus v Ω)
    (hl : ∀n,l n∈rootGrade v Ω C n) (n : ℕ) :
    incomingCoefficient v Ω C (n+1) (incomingSolution v Ω C l)-
      incomingCoefficient v Ω C (n+1) (incomingTruncation v Ω C l n)=
      coeff (n+1) (incomingSolution v Ω C l)-0 := by
  have hpgrade : coeff (n+1) (incomingTruncation v Ω C l n)∈rootGrade v Ω C (n+1) := by
    intro m hm
    rw [incomingTruncation_top]
    rfl
  have H := incomingCoefficient_leading v Ω C hΩ
    (incomingSolution v Ω C l) (incomingTruncation v Ω C l n) n
    (incomingTruncation_lower v Ω C l n) (incomingSolution_graded v Ω C l hl _) hpgrade
  rw [incomingTruncation_top] at H
  exact H

lemma incomingSolution_prescription (hΩ : ∀m,Ω m m=0) (l : ℕ → Torus v Ω)
    (hl : ∀n,l n∈rootGrade v Ω C n) (n : ℕ) :
    incomingCoefficient v Ω C (n+1) (incomingSolution v Ω C l)=l (n+1) := by
  have H := incomingSolution_prescription_difference v Ω C hΩ l hl n
  rw [incomingSolution_step] at H
  ext m
  have he := congrArg (fun x : Torus v Ω => x m) H
  simp only [torus_sub_apply,Finsupp.zero_apply,sub_zero] at he
  exact sub_left_inj.mp he

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_IncomingRayElement
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M→+M→+ℤ) (C : (I→ℤ)→+M)

lemma root_graded_log (F : CompletedPositive v Ω C) (n : ℕ) :
    coeff n (FormalLog.log F.val)∈rootGrade v Ω C n := by
  apply FormalLog.log_graded (rootGrade v Ω C) (rootGrade_one v Ω C)
    (rootGrade_mul v Ω C) _ F.val F.property.2 n
  intro j a x hx m hm
  change a • x m=0
  rw [hx m hm,smul_zero]

theorem incoming_ray_element_through (hΩ : ∀m,Ω m m=0) (r : M) (k : M→+ℝ)
    (hk : k r=0) (F D : CompletedPositive v Ω C) (N : ℕ)
    (hgeneric : ∀n,0<n→n≤N→∀m,HasRootDegree C n m→Ω m r=0→k m=0→OnPositiveRay r m)
    (hD : ∀n m,coeff (n+1) D.val m≠0→OnPositiveRay r m)
    (hprescribed : ∀n≤N,∀m,OnPositiveRay r m→
      coeff n (FormalLog.log (chartZero v Ω C (incomingCovector Ω m) F).val) m=
        coeff n (FormalLog.log D.val) m) :
    ∀n≤N,coeff n (chartZero v Ω C k
      (chartZero v Ω C (incomingCovector Ω r) F)).val=coeff n D.val := by
  let B:=chartZero v Ω C k (chartZero v Ω C (incomingCovector Ω r) F)
  apply FormalLog.log_injective_through B.val D.val N B.property.1 D.property.1
  intro n hn
  apply Finsupp.ext
  intro m
  by_cases hm : OnPositiveRay r m
  · exact (incoming_ray_log v Ω C hΩ r k hk F m hm n).trans (hprescribed n hn m hm)
  · have hD0:=strict_log_support v Ω (V:=OnPositiveRay r)
      (fun a b ha hb=>ha.add hb) D.val D.property.1
      (fun j m hm=>not_not.mp (fun hx=>hm (hD j m hx))) n m hm
    rw [hD0]
    by_cases hn0 : n=0
    · subst n
      simp only [coeff_zero_eq_constantCoeff,FormalLog.log_constant,Finsupp.zero_apply]
    · by_contra hx
      have hr : HasRootDegree C n m:=by
        by_contra hh; exact hx (root_graded_log v Ω C B n m hh)
      have hker : Ω m r=0 ∧ k m=0:=by
        by_contra hh; exact hx (incoming_ray_log_support v Ω C r k F n m hh)
      exact hm (hgeneric n (by omega) hn m hr hker.1 hker.2)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_GlobalWallPositive
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
attribute [local instance] Classical.propDecidable
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)

def literalIncomingLog (l : List (WallUnitDatum M)) (n : ℕ) : Torus LaurentRay.vUnit Ω := by
  classical
  exact Finsupp.onFinset (rootDegree_finite C n).toFinset
    (fun m => if HasRootDegree C n m then coeff n (FormalLog.log (literalIncomingRay Ω l m)) m else 0)
    (by intro m hm; rw [Set.Finite.mem_toFinset]; by_contra hn; exact hm (ite_eq_right hn))
lemma literalIncomingLog_apply (l : List (WallUnitDatum M)) (n : ℕ) (m : M) :
    literalIncomingLog Ω C l n m=
      if HasRootDegree C n m then coeff n (FormalLog.log (literalIncomingRay Ω l m)) m else 0 := by
  classical
  rfl
lemma literalIncomingLog_graded (l : List (WallUnitDatum M)) (n : ℕ) :
    literalIncomingLog Ω C l n∈rootGrade LaurentRay.vUnit Ω C n := by
  classical
  intro m hm
  rw [literalIncomingLog_apply,ite_eq_right hm]

def literalTotalTransport (l : List (WallUnitDatum M)) : CompletedPositive LaurentRay.vUnit Ω C :=
  ⟨incomingSolution LaurentRay.vUnit Ω C (literalIncomingLog Ω C l),
    incomingSolution_constant LaurentRay.vUnit Ω C _,
    incomingSolution_graded LaurentRay.vUnit Ω C _ (literalIncomingLog_graded Ω C l)⟩

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_OffCutJoint
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries RootTruncation
noncomputable section
variable {R M E I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M]
  [AddCommGroup E] [Module ℝ E] [Fintype I] [DecidableEq I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀d m,HasRootDegree C d m → L (e m)=(d:ℝ))

lemma simpleRoot_degree : HasRootDegree C 1 (simpleRoot C pc) := by
  refine ⟨Pi.single pc 1,by simp,?_⟩
  congr 1
  ext i
  by_cases hi : i=pc
  · subst i; simp
  · simp [hi]

include hcoord he hB hcomp hdeg in
lemma offcut_planar_support (N : ℕ) (hN : 0<N) (n : ℤ) (P : AddSubmonoid M)
    (pos : Bool) (r : M) (dr : ℕ) (hdr : 0<dr) (hrd : HasRootDegree C dr r)
    (s : E) (hrs : B (e r) s≠0) (k : Module.Dual ℝ E)
    (hkr : k (e r)=0) (hks : k s=0)
    (hzero : ∀d,d≤N → ∀m,HasRootDegree C d m → k (e m)=0 → e m∈Submodule.span ℝ {e r,s})
    (hside : cutSide pos (k.toAddMonoidHom.comp e) (simpleRoot C pc))
    (F : CompletedPositive v Ω C)
    (HI : ∀q d,0<d → HasRootDegree C d q → ∀h : Module.Dual ℝ E,
      RayGeneric C N q (h.toAddMonoidHom.comp e) →
      cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc) →
      ∀j≤N,∀m,coeff j (chartZero v Ω C (h.toAddMonoidHom.comp e) F).val m≠0 →
        nonpDegree coord pc m<n → m∈P)
    (HR : ∀j≤N,∀m,
      coeff j (chartZero v Ω C (incomingCovector Ω r)
        (chartZero v Ω C (k.toAddMonoidHom.comp e) F)).val m≠0 →
      nonpDegree coord pc m=n → m∈P) :
    ∀j≤N,∀m,
      coeff j (chartZero v Ω C (-incomingCovector Ω r)
        (chartZero v Ω C (k.toAddMonoidHom.comp e) F)).val m≠0 →
      nonpDegree coord pc m=n → m∈P := by
  classical
  let kM:=k.toAddMonoidHom.comp e
  let J:=chartZero v Ω C kM F
  let Jc:=completedCut v Ω C N J
  let w:=nonpDegree coord pc
  let h:=incomingCovector Ω r
  let Q:=nonpSupportFrame w h P n
  have hp : kM (simpleRoot C pc)≠0:=by
    cases pos <;> simp only [cutSide,Bool.false_eq_true,ite_false, if_false,ite_true, if_true] at hside
    · exact ne_of_lt hside
    · exact ne_of_gt hside
  have hker : ∀j,coeff j Jc.val∈supportedSubring v Ω kM.ker.toAddSubmonoid:=
    completedCut_supported v Ω C N J _ (fun j _=>chartZero_supported_kernel v Ω C kM F j)
  have hplane : ∀j,coeff j Jc.val∈supportedSubring v Ω (planeRoots e (e r) s):=by
    apply completedCut_supported v Ω C N J _
    intro j hj m hm
    by_contra hval
    have hmroot:=chart_root_of_ne v Ω C J j m hval
    have hmz : kM m=0:=by
      by_contra HH; exact hval (chartZero_supported_kernel v Ω C kM F j m HH)
    exact hm (hzero j hj m hmroot hmz)
  have hcut (a : M →+ ℝ) : ∀j≤N,coeff j (chartZero v Ω C a Jc).val=coeff j (chartZero v Ω C a J).val:=by
    apply chartZero_congr_through v Ω C a Jc J N
    exact fun j hj=>coeff_cut_of_le J.val hj
  have hrootpos (q : M) (j : ℕ) (hj : 0<j) (m : M)
      (hm : coeff j (chartZero v Ω C (incomingCovector Ω q) Jc).val m≠0) : 0<w m:=by
    apply nonp_positive_off_cut C coord hcoord pc hj
      (chart_root_of_ne v Ω C _ j m hm) kM hp
    by_contra HH
    exact hm ((chartThree_supported v Ω C (incomingCovector Ω q) kM.ker.toAddSubmonoid Jc hker).2.1 j m HH)
  have htargeteq : ∀q d,0<d → HasRootDegree C d q → q∈planeRoots e (e r) s →
      Ω q r=0 → chartZero v Ω C (incomingCovector Ω q) Jc=chartZero v Ω C h Jc:=by
    intro q d hd hdq hqP hqr
    have hqr' : OnPositiveRay r q:=positive_ray_of_pairing_zero e he B hB L (e r) s C hdeg hrs
      q r d dr hd hdr hdq hrd hqP (Submodule.subset_span (by simp)) (by rw [hcomp,hqr,Int.cast_zero])
    exact (incoming_same_ray v Ω C hqr' Jc).symm
  have hhIncoming : ∀q d,0<d → d≤N → HasRootDegree C d q → q∈planeRoots e (e r) s →
      ∀j≤N,coeff j (chartZero v Ω C (incomingCovector Ω q) Jc).val∈supportedSubring v Ω Q:=by
    intro q d hd hdN hdq hqP j hj m hmQ
    by_contra hval
    have hm0 : m≠0:=by intro hh; exact hmQ (hh ▸ Q.zero_mem)
    have hj0 : 0<j:=by
      by_contra hh
      have hjz : j=0:=by omega
      subst j
      rw [coeff_zero_eq_constantCoeff,(chartZero v Ω C (incomingCovector Ω q) Jc).property.1] at hval
      exact hval (Finsupp.single_eq_of_ne hm0)
    apply hmQ
    refine Or.inr ⟨hrootpos q j hj0 m hval,?_⟩
    intro hw
    rcases hw with hw | ⟨hw,hh⟩
    · obtain ⟨η,hη,Hη⟩:=planar_refinement_generic v Ω C e he B hB hcomp L hdeg N
        (e r) s hrs k hkr hks hzero q d hd hdq hqP F
      obtain ⟨ε,hε,Hε⟩:=root_lex_epsilon C N kM (incomingCovector Ω q)
      let δ:=min η ε/2
      have hδ : 0<δ:=by dsimp [δ] <;> positivity
      have hδη : δ<η:=by dsimp [δ]; have := min_le_left η ε; linarith [lt_min hη hε]
      have hδε : δ<ε:=by dsimp [δ]; have := min_le_right η ε; linarith [lt_min hη hε]
      obtain ⟨hgen,HRef⟩:=Hη δ hδ hδη
      have hsign:=Hε δ hδ hδε 1 hN (simpleRoot C pc) (simpleRoot_degree C pc)
      have hside' : cutSide pos ((k+δ • B.flip (e q)).toAddMonoidHom.comp e) (simpleRoot C pc):=by
        rw [real_perturbed_covector Ω e B hcomp]
        cases pos <;> simp only [cutSide,Bool.false_eq_true,ite_false, if_false,ite_true, if_true] at hside ⊢
        · exact hsign.2.1 hside
        · exact hsign.1 hside
      apply HI q d hd hdq _ hgen hside' j hj m ?_ hw
      rw [HRef j hj,←hcut _ j hj]
      exact hval
    · have hmroot:=chart_root_of_ne v Ω C _ j m hval
      have hmP : m∈planeRoots e (e r) s:=by
        by_contra HH
        exact hval ((chartThree_supported v Ω C (incomingCovector Ω q) (planeRoots e (e r) s) Jc hplane).2.1 j m HH)
      have hmqr : B (e m) (e q)=0:=by
        rw [hcomp]
        have HK:=chartZero_supported_kernel v Ω C (incomingCovector Ω q) Jc j
        by_contra HH
        exact hval (HK m HH)
      have hqm : OnPositiveRay q m:=positive_ray_of_pairing_zero e he B hB L (e r) s C hdeg hrs
        m q j d hj0 hd hmroot hdq hmP hqP hmqr
      have hqr : Ω q r=0:=by
        have HH:=(hqm.eval h).2.1.mp hh
        change (Ω q r:ℝ)=0 at HH
        exact_mod_cast HH
      have hhEq:=htargeteq q d hd hdq hqP hqr
      rw [hhEq,hcut h j hj] at hval
      exact HR j hj m hval hw
  have hQ:=planar_joint_support v Ω C e he B hB hcomp L hdeg (e r) s
    (by rw [hdeg dr r hrd]; exact_mod_cast hdr) hrs Jc hplane N Q hhIncoming (-h)
  intro j hj m hval hw
  apply nonpSupportFrame_target (w:=w) (h:=h) (n:=n) (m:=m) (P:=P) ?_ hw ?_
  · by_contra HH
    have Hzero:=hQ j hj m HH
    rw [hcut (-h) j hj] at Hzero
    exact hval Hzero
  · have HK:=chartZero_supported_kernel v Ω C (-h) J j
    have Hneg : (-h) m=0:=by by_contra HH; exact hval (HK m HH)
    simpa only [AddMonoidHom.neg_apply,neg_eq_zero] using Hneg
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_SimpleIncomingData
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d)

lemma simpleDatum_allowed (i : I) : (simpleDatum C i).Allowed C (fun _=>True) :=
  ⟨Nat.zero_lt_one,simpleRoot_degree C i,True.intro⟩
lemma simpleIncomingList_allowed : ∀u∈simpleIncomingList C,u.Allowed C (fun _=>True) := by
  intro u hu
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hu
  exact simpleDatum_allowed C i

def simpleTotalTransport : CompletedPositive LaurentRay.vUnit Ω C := literalTotalTransport Ω C (simpleIncomingList C)
include hcoord in
lemma simpleIncomingRay_fiber (pc : I) (r : M) (hr : 0<nonpDegree coord pc r)
    (α : I → ℤ) (σ : ℤ) :
    literalIncomingRay Ω (simpleIncomingList C) r∈literalRootProducts Ω C (fun m=>m∈fiberCone coord pc α σ) := by
  classical
  refine ⟨(simpleIncomingList C).filter (fun u=>OnPositiveRay r u.root),?_,rfl⟩
  intro u hu
  have hu':=List.mem_filter.mp hu
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hu'.1
  have hri : OnPositiveRay r (simpleRoot C i):=by exact of_decide_eq_true hu'.2
  have hip : i≠pc:=by intro hh; subst i; exact positive_nonp_not_simple_ray C coord hcoord pc r hr hri
  exact ⟨Nat.zero_lt_one,simpleRoot_degree C i,simple_off_fiber C coord hcoord pc i hip α σ⟩
include hcoord in
lemma simpleIncomingCompleted_fiber (pc : I) (r : M) (hr : 0<nonpDegree coord pc r)
    (α : I → ℤ) (σ : ℤ) :
    ∀j,coeff j (literalIncomingCompleted Ω C (simpleIncomingList C) (simpleIncomingList_allowed C) r).val∈
      supportedSubring LaurentRay.vUnit Ω (fiberCone coord pc α σ) := by
  intro j
  cases j with
  | zero=>
    rw [coeff_zero_eq_constantCoeff,(literalIncomingCompleted Ω C _ _ r).property.1]
    exact (supportedSubring LaurentRay.vUnit Ω _).one_mem
  | succ j=>
    exact literalRootProducts_strictSupport Ω C (fun m=>m∈fiberCone coord pc α σ)
      (fun a b ha hb=>(fiberCone coord pc α σ).add_mem ha hb)
      (simpleIncomingRay_fiber Ω C coord hcoord pc r hr α σ) j

omit [DecidableEq I] in
lemma literalTotalTransport_ray_prescription (hΩ : ∀m,Ω m m=0)
    (l : List (WallUnitDatum M)) (hl : ∀u∈l,u.Allowed C (fun _=>True)) (r : M) :
    ∀n m,OnPositiveRay r m →
      coeff n (FormalLog.log (chartZero LaurentRay.vUnit Ω C (incomingCovector Ω m)
        (literalTotalTransport Ω C l)).val) m=
      coeff n (FormalLog.log (literalIncomingCompleted Ω C l hl r).val) m := by
  classical
  intro n m hm
  cases n with
  | zero=>simp only [coeff_zero_eq_constantCoeff,FormalLog.log_constant,Finsupp.zero_apply]
  | succ n=>
    by_cases hroot : HasRootDegree C (n+1) m
    · have H:=congrArg (fun x : Torus LaurentRay.vUnit Ω=>x m)
        (incomingSolution_prescription LaurentRay.vUnit Ω C hΩ _ (literalIncomingLog_graded Ω C l) n)
      rw [incomingCoefficient_apply,ite_eq_left hroot,literalIncomingLog_apply,ite_eq_left hroot] at H
      change coeff (n+1) (FormalLog.log (chartZero LaurentRay.vUnit Ω C (incomingCovector Ω m)
        (literalTotalTransport Ω C l)).val) m=coeff (n+1) (FormalLog.log (literalIncomingRay Ω l r)) m
      rw [literalIncomingRay_eq Ω l hm]
      exact H
    · rw [root_graded_log LaurentRay.vUnit Ω C _ (n+1) m hroot,
        root_graded_log LaurentRay.vUnit Ω C (literalIncomingCompleted Ω C l hl r) (n+1) m hroot]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_MutationFiberArithmetic
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
include hcoord in
lemma root_simple_expansion {n : ℕ} {m : M} (hm : HasRootDegree C n m) :
    m=∑i,(coord m i) • simpleRoot C i := by
  obtain ⟨d,hd,hc,he⟩:=root_coordinates C coord hcoord hm
  have hsplit : (fun i=>(d i:ℤ))=∑i,((d i:ℤ) • (Pi.single i 1 : I → ℤ)) := by
    ext j
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i hi hij; simp [Ne.symm hij]
    · simp
  calc
    m=∑i,(d i:ℤ) • simpleRoot C i:=by
      rw [←he,hsplit,map_sum]
      simp only [map_zsmul,simpleRoot]
    _=∑i,coord m i • simpleRoot C i:=by simp only [hc]
include hcoord in
lemma root_pairing_coordinates (hΩ : ∀m,Ω m m=0) {n : ℕ} {m : M}
    (hm : HasRootDegree C n m) :
    Ω (simpleRoot C pc) m=∑i∈Finset.univ.erase pc,mutationPairing Ω C pc i*coord m i := by
  have HH:=congrArg (Ω (simpleRoot C pc)) (root_simple_expansion C coord hcoord hm)
  rw [map_sum] at HH
  simp only [map_zsmul,smul_eq_mul] at HH
  rw [←Finset.sum_erase_add _ _ (Finset.mem_univ pc)] at HH
  simp only [hΩ,mul_zero,add_zero] at HH
  rw [HH]
  apply Finset.sum_congr (by ext i; simp)
  intro i hi
  exact mul_comm _ _
include hcoord in
lemma fiberUpper_simple (α : I → ℤ) (σ : ℤ) : fiberUpper coord pc α σ (simpleRoot C pc)=0 := by
  change (∑i∈Finset.univ.erase pc,max 0 (-σ*α i)*coord (simpleRoot C pc) i)=0
  apply Finset.sum_eq_zero
  intro i hi
  rw [simpleRoot_coordinates C coord hcoord]
  simp [(Finset.mem_erase.mp hi).1]
include hcoord in
lemma fiber_shift_bound (hΩ : ∀m,Ω m m=0) {n : ℕ} {m : M} (hm : HasRootDegree C n m)
    (σ : ℤ) (j : ℕ) (hj : (j:ℤ)≤σ*Ω (simpleRoot C pc) m)
    (hP : m∈fiberCone coord pc (mutationPairing Ω C pc) σ) :
    m+j • simpleRoot C pc∈fiberCone coord pc (mutationPairing Ω C pc) (-σ) := by
  have hc : coord (m+j • simpleRoot C pc) pc=coord m pc+(j:ℤ):=by
    simp only [map_add,map_nsmul,Pi.add_apply,Pi.smul_apply]
    rw [simpleRoot_coordinates C coord hcoord]
    simp
  have hu : fiberUpper coord pc (mutationPairing Ω C pc) (-σ) (m+j • simpleRoot C pc)=
      fiberUpper coord pc (mutationPairing Ω C pc) σ m+σ*Ω (simpleRoot C pc) m:=by
    rw [map_add,map_nsmul,fiberUpper_simple C coord hcoord,nsmul_zero,add_zero,fiberUpper_flip,
      ←root_pairing_coordinates Ω C coord hcoord pc hΩ hm]
  change 0 ≤ coord (m+j • simpleRoot C pc) pc ∧
    coord (m+j • simpleRoot C pc) pc≤fiberUpper coord pc (mutationPairing Ω C pc) (-σ) (m+j • simpleRoot C pc)
  rw [hc,hu]
  exact ⟨add_nonneg hP.1 (Int.natCast_nonneg j),add_le_add hP.2 hj⟩
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CompletedPureComparison
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (δ k : M →+ ℤ) (p : M) (hp : k p=1)

variable (hδ : δ p=0)
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorus_5
local instance instAddCommMonoidTorus_2_r7588b2_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_2_r7588b2_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_5_r7588b2_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_5_r7588b2_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
def oldPureUnit : (biSupportedSubring v Ω δ k)ˣ where
  val:=⟨raySeries v Ω p (shiftedElementary v 0),pure_biSupported v Ω δ k p hδ hp _⟩
  inv:=⟨raySeries v Ω p (shiftedElementary v 0)⁻¹,pure_biSupported v Ω δ k p hδ hp _⟩
  val_inv:=Subtype.ext (rayUnit v Ω p (hΩ p) _ (shiftedElementary_constant v 0)).val_inv
  inv_val:=Subtype.ext (rayUnit v Ω p (hΩ p) _ (shiftedElementary_constant v 0)).inv_val
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (δ k : M →+ ℤ) (p : M) (hp : k p=1) (hδ : δ p=0) (B : ℕ)

local instance instRingTorus_6_r7588b2_1 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance instAddCommMonoidTorus_3_r7588b2_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_3_r7588b2_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_6_r7588b2_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_6_r7588b2_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
def comparisonOld : ComparisonCrossing v Ω δ k B → (biSupportedSubring v Ω δ k)ˣ
  | .bounded u _ _=>u
  | .pure true=>oldPureUnit v Ω hΩ δ k p hp hδ
  | .pure false=>(oldPureUnit v Ω hΩ δ k p hp hδ)⁻¹

def comparisonAction (c : ComparisonCrossing v Ω δ k B) :
    PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)) →+*
      PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)) :=
  match c with
  | .bounded u hf hg=>innerHom (boundedRationalUnit v Ω hΩ δ k p hp B u hf hg)
  | .pure true=>(completedPureAction v _ _).toRingHom
  | .pure false=>(completedPureAction v _ _).symm.toRingHom

def comparisonWordOld (l : List (ComparisonCrossing v Ω δ k B)) :
    (biSupportedSubring v Ω δ k)ˣ := (l.map (comparisonOld v Ω hΩ δ k p hp hδ B)).prod

def comparisonWordAction (l : List (ComparisonCrossing v Ω δ k B))
    (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))) :=
  l.foldr (fun c a=>comparisonAction v Ω hΩ δ k p hp B c a) f
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_PureFaceProjection
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
local instance pureFaceProjectionAddCommGroup : AddCommGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommGroup
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.pureFaceProjectionAddCommMonoid
local instance pureFaceProjectionAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance pureFaceProjectionSub_r7588b2_1 : Sub (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toSub
lemma pureFaceSeries_one : pureFaceSeries Ω coord pc 1=1 := by
  apply PowerSeries.ext
  intro n
  rw [coeff_pureFaceSeries,coeff_one]
  split_ifs with hn
  · exact zeroProject_one _ _ _
  · exact map_zero _
lemma pureFaceSeries_sub (F G : PowerSeries (Torus LaurentRay.vUnit Ω)) :
    pureFaceSeries Ω coord pc (F-G)=pureFaceSeries Ω coord pc F-pureFaceSeries Ω coord pc G := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_pureFaceSeries,map_sub]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_PureFaceLog
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
local instance pureFaceLogAddCommGroup : AddCommGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommGroup
local instance pureFaceLogAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance pureFaceLogAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance pureFaceLogSub_r7588b2_1 : Sub (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toSub
omit [DecidableEq I] in
lemma graded_series_pow (F : PowerSeries (Torus LaurentRay.vUnit Ω))
    (hF : ∀n,coeff n F∈rootGrade LaurentRay.vUnit Ω C n) (k : ℕ) :
    ∀n,coeff n (F^k)∈rootGrade LaurentRay.vUnit Ω C n := by
  induction k with
  | zero=>simpa only [pow_zero] using FormalLog.graded_one _ (rootGrade_one LaurentRay.vUnit Ω C)
  | succ k ih=>simpa only [pow_succ] using FormalLog.graded_multiply _ (rootGrade_mul LaurentRay.vUnit Ω C) _ _ ih hF
include hcoord in
lemma pureFaceSeries_pow (F : PowerSeries (Torus LaurentRay.vUnit Ω))
    (hF : ∀n,coeff n F∈rootGrade LaurentRay.vUnit Ω C n) (k : ℕ) :
    pureFaceSeries Ω coord pc (F^k)=(pureFaceSeries Ω coord pc F)^k := by
  induction k with
  | zero=>simpa only [pow_zero] using pureFaceSeries_one Ω coord pc
  | succ k ih=>rw [pow_succ,pureFaceSeries_mul Ω C coord hcoord pc _ _
      (graded_series_pow Ω C F hF k) hF,ih,pow_succ]
lemma zeroProject_rat_smul (h : M →+ ℝ) (a : ℚ) (x : Torus LaurentRay.vUnit Ω) :
    zeroProject LaurentRay.vUnit Ω h (a • x)=a • zeroProject LaurentRay.vUnit Ω h x := by
  classical
  exact map_rat_smul (zeroProject LaurentRay.vUnit Ω h) a x
include hcoord in
lemma pureFaceSeries_log (F : CompletedPositive LaurentRay.vUnit Ω C) :
    pureFaceSeries Ω coord pc (FormalLog.log F.val)=FormalLog.log (pureFace Ω C coord pc F).val := by
  have hu : ∀n,coeff n (F.val-1)∈rootGrade LaurentRay.vUnit Ω C n:=by
    intro n
    rw [map_sub]
    exact (rootGrade LaurentRay.vUnit Ω C n).sub_mem (F.property.2 n)
      (FormalLog.graded_one _ (rootGrade_one LaurentRay.vUnit Ω C) n)
  apply PowerSeries.ext
  intro n
  rw [coeff_pureFaceSeries]
  simp only [FormalLog.log,coeff_mk,map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [zeroProject_rat_smul,←coeff_pureFaceSeries,pureFaceSeries_pow Ω C coord hcoord pc _ hu,
    pureFaceSeries_sub,pureFaceSeries_one]
  rfl
include hcoord in
lemma pureFace_log_chart_apply (h : M →+ ℝ) (hp : h (simpleRoot C pc)=0)
    (F : CompletedPositive LaurentRay.vUnit Ω C) (n : ℕ) (m : M)
    (hm : nonpDegree coord pc m=0) :
    coeff n (FormalLog.log (chartZero LaurentRay.vUnit Ω C h F).val) m=
      coeff n (FormalLog.log F.val) m := by
  have H:=congrArg (fun D : CompletedPositive LaurentRay.vUnit Ω C=>coeff n (FormalLog.log D.val) m)
    (pureFace_chartZero Ω C coord hcoord pc h hp F)
  rw [←pureFaceSeries_log Ω C coord hcoord pc,←pureFaceSeries_log Ω C coord hcoord pc] at H
  simpa only [pureFaceSeries_apply,hm,ite_true, if_true] using H
include hcoord in
lemma pureFace_simpleTransport (hΩ : ∀m,Ω m m=0) :
    pureFace Ω C coord pc (simpleTotalTransport Ω C)=
      literalIncomingCompleted Ω C (simpleIncomingList C) (simpleIncomingList_allowed C) (simpleRoot C pc) := by
  let F:=simpleTotalTransport Ω C
  let D:=literalIncomingCompleted Ω C (simpleIncomingList C) (simpleIncomingList_allowed C) (simpleRoot C pc)
  apply Subtype.ext
  apply PowerSeries.ext
  intro N
  apply FormalLog.log_injective_through (pureFace Ω C coord pc F).val D.val N
    (pureFace Ω C coord pc F).property.1 D.property.1
  intro n hn
  apply Finsupp.ext
  intro m
  rw [←pureFaceSeries_log Ω C coord hcoord pc,pureFaceSeries_apply]
  have hdlog : ∀j m,coeff j (FormalLog.log D.val) m≠0→OnPositiveRay (simpleRoot C pc) m:=by
    intro j m hm
    by_contra hh
    exact hm (strict_log_support LaurentRay.vUnit Ω (fun a b ha hb=>ha.add hb) D.val D.property.1
      (literalRootProducts_strictSupport Ω C (OnPositiveRay (simpleRoot C pc))
        (fun a b ha hb=>ha.add hb)
        (literalIncomingRay_mem Ω C (simpleIncomingList C) (simpleIncomingList_allowed C) (simpleRoot C pc))) j m hh)
  by_cases hz : nonpDegree coord pc m=0
  · rw [ite_eq_left hz]
    by_cases hr : HasRootDegree C n m
    · cases n with
      | zero=>simp only [coeff_zero_eq_constantCoeff_apply,FormalLog.log_constant,Finsupp.zero_apply]
      | succ n=>
        have hmray : OnPositiveRay (simpleRoot C pc) m:=by
          refine ⟨1,n+1,by omega,by omega,?_⟩
          rw [one_nsmul,nonp_zero_root C coord hcoord pc hr hz]
        have hp : incomingCovector Ω m (simpleRoot C pc)=0:=by
          change (Ω (simpleRoot C pc) m : ℝ)=0
          rw [nonp_zero_root C coord hcoord pc hr hz,map_nsmul,hΩ,nsmul_zero,Int.cast_zero]
        rw [←pureFace_log_chart_apply Ω C coord hcoord pc (incomingCovector Ω m) hp F _ m hz]
        exact literalTotalTransport_ray_prescription Ω C hΩ _ (simpleIncomingList_allowed C) _ _ _ hmray
    · rw [root_graded_log LaurentRay.vUnit Ω C F n m hr,root_graded_log LaurentRay.vUnit Ω C D n m hr]
  · rw [ite_eq_right hz]
    by_contra hh
    have hmr:=hdlog n m (Ne.symm hh)
    obtain ⟨a,b,ha,hb,he⟩:=hmr
    have HH:=congrArg (nonpDegree coord pc) he
    rw [map_nsmul,map_nsmul,nonpDegree_simple_self C coord hcoord,nsmul_zero,nsmul_eq_mul] at HH
    exact hz ((mul_eq_zero.mp HH).resolve_left (by exact_mod_cast (Nat.ne_of_gt ha)))
  exact Nat.le_refl N
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_SimpleBinomial
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits PowerSeriesAdjoint
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
lemma normalizedSimple_constant (p : M) : constantCoeff (normalizedSimple Ω p)=1 := by
  rw [←coeff_zero_eq_constantCoeff]
  rw [normalizedSimple,coeff_raySeries,zero_nsmul,coeff_zero_eq_constantCoeff,constant_elementary]
  rfl
lemma normalizedSimple_inverse (hΩ : ∀m,Ω m m=0) (p : M) :
    invOfUnit (normalizedSimple Ω p) 1=
      raySeries LaurentRay.vUnit Ω p
        (elementary (HahnSeries.single (2:ℤ) (1:ℚ)) (HahnSeries.single (1:ℤ) (1:ℚ)))⁻¹ := by
  let U:=rayUnit LaurentRay.vUnit Ω p (hΩ p)
    (elementary (HahnSeries.single (2:ℤ) (1:ℚ)) (HahnSeries.single (1:ℤ) (1:ℚ))) (constant_elementary _ _)
  change invOfUnit U.val 1=U.inv
  calc
    _=invOfUnit U.val 1*(U.val*U.inv):=by rw [U.val_inv,mul_one]
    _=(invOfUnit U.val 1*U.val)*U.inv:=by rw [mul_assoc]
    _=U.inv:=by rw [invOfUnit_mul U.val 1 (normalizedSimple_constant Ω p),one_mul]
lemma normalizedSimple_adjoint_support (hΩ : ∀m,Ω m m=0) (p m x : M) (t N : ℕ)
    (ht : Ω p m=(t:ℤ))
    (hx : coeff N (adjoint (normalizedSimple Ω p) (PowerSeries.C (Torus.X LaurentRay.vUnit Ω m))) x≠0) :
    N≤t ∧ x=m+N • p := by
  rw [adjoint,normalizedSimple_inverse Ω hΩ p] at hx
  exact elementary_adjoint_support LaurentRay.vUnit Ω hΩ p m x _ _ laurent_q_nonzero
    UnitSelections.laurent_q_not_root t N (by rw [ht]; exact laurent_shift_positive t) hx
lemma normalizedSimple_inverse_adjoint_support (hΩ : ∀m,Ω m m=0) (p m x : M) (t N : ℕ)
    (ht : Ω p m= -(t:ℤ))
    (hx : coeff N (adjoint (invOfUnit (normalizedSimple Ω p) 1)
      (PowerSeries.C (Torus.X LaurentRay.vUnit Ω m))) x≠0) : N≤t ∧ x=m+N • p := by
  rw [adjoint_inverse _ _ (normalizedSimple_constant Ω p),normalizedSimple_inverse Ω hΩ p] at hx
  exact elementary_inverse_adjoint_support LaurentRay.vUnit Ω hΩ p m x _ _ laurent_q_nonzero
    UnitSelections.laurent_q_not_root t N (by rw [ht]; exact laurent_shift_negative t) hx
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_SimpleIncomingElement
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries RootTruncation WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)

include hcoord in
lemma pureFace_simpleTransport_value (hΩ : ∀m,Ω m m=0) :
    (pureFace Ω C coord pc (simpleTotalTransport Ω C)).val=normalizedSimple Ω (simpleRoot C pc) := by
  rw [pureFace_simpleTransport Ω C coord hcoord pc hΩ]
  exact literalIncoming_simple Ω C coord hcoord pc

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_SimpleAdjointFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)

local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_2_r7588b2_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddCommGroupTorusLaurentSeriesRatVUnit_1_r7588b2_1 : AddCommGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommGroup
local instance instAddGroupTorusLaurentSeriesRatVUnit_2_r7588b2_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance instSubTorusLaurentSeriesRatVUnit_1_r7588b2_1 : Sub (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toSub
def simpleOriented (pos : Bool) (p : M) : PowerSeries (Torus LaurentRay.vUnit Ω) :=
  if pos then normalizedSimple Ω p else invOfUnit (normalizedSimple Ω p) 1

lemma simpleOriented_support (hΩ : ∀m,Ω m m=0) (pos : Bool) (p m x : M)
    (N : ℕ) (htrend : 0≤ sideSign pos*Ω p m)
    (hx : coeff N (adjoint (simpleOriented Ω pos p)
      (PowerSeries.C (Torus.X LaurentRay.vUnit Ω m))) x≠0) :
    (N:ℤ)≤ sideSign pos*Ω p m ∧ x=m+N • p := by
  let t:=(sideSign pos*Ω p m).toNat
  have ht : (t:ℤ)=sideSign pos*Ω p m:=Int.toNat_of_nonneg htrend
  have HG : N≤t ∧ x=m+N • p:=by
    cases pos
    · apply normalizedSimple_inverse_adjoint_support Ω hΩ p m x t N ?_ hx
      simpa only [sideSign,Bool.false_eq_true,ite_false, if_false,neg_one_mul,Int.neg_neg] using congrArg Neg.neg ht.symm
    · apply normalizedSimple_adjoint_support Ω hΩ p m x t N ?_ hx
      simpa only [sideSign,ite_true, if_true,one_mul] using ht.symm
  exact ⟨by rw [←ht]; exact_mod_cast HG.1,HG.2⟩

include hcoord in
lemma simpleOriented_adjoint_fiber (hΩ : ∀m,Ω m m=0) (pos : Bool)
    (A : PowerSeries (Torus LaurentRay.vUnit Ω)) (N : ℕ) (n : ℤ)
    (hA : ∀j≤N,coeff j A∈rootGrade LaurentRay.vUnit Ω C j)
    (htrend : ∀j≤N,∀m,coeff j A m≠0 → 0≤ sideSign pos*Ω (simpleRoot C pc) m)
    (hbound : ∀j≤N,∀m,coeff j A m≠0 → nonpDegree coord pc m≤n →
      m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)) :
    ∀x,coeff N (adjoint (simpleOriented Ω pos (simpleRoot C pc)) A) x≠0 →
      nonpDegree coord pc x≤n →
      x∈fiberCone coord pc (mutationPairing Ω C pc) (-sideSign pos) := by
  classical
  intro x hx hxn
  rw [coeff_adjoint_expansion,torus_ring_eval_sum] at hx
  obtain ⟨j,hj,hterm⟩:=Finset.exists_ne_zero_of_sum_ne_zero hx
  have hjN : j≤N:=by have H:=Finset.mem_range.mp hj; omega
  rw [adjoint_torus_expansion] at hterm
  obtain ⟨m,hm,hterm⟩:=Finset.exists_ne_zero_of_sum_ne_zero hterm
  have hmA : coeff j A m≠0:=(mul_ne_zero_iff.mp hterm).1
  have hmAd:=(mul_ne_zero_iff.mp hterm).2
  have HS:=simpleOriented_support Ω hΩ pos (simpleRoot C pc) m x (N-j)
    (htrend j hjN m hmA) hmAd
  have hroot : HasRootDegree C j m:=by
    by_contra hh
    exact hmA (hA j hjN m hh)
  have hw : nonpDegree coord pc x=nonpDegree coord pc m:=by
    rw [HS.2,map_add,map_nsmul,nonpDegree_simple_self C coord hcoord,nsmul_zero,add_zero]
  rw [hw] at hxn
  rw [HS.2]
  exact fiber_shift_bound Ω C coord hcoord pc hΩ hroot (sideSign pos) (N-j) HS.1
    (hbound j hjN m hmA hxn)
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)

include hcoord in
lemma mutatedCoordinate_at (hΩ : ∀m,Ω m m=0) (pos : Bool) {n : ℕ} {m : M}
    (hm : HasRootDegree C n m) :
    mutatedCoordinates Ω C coord pc (mutationLinearPiece Ω C pc pos m) pc=
      fiberUpper coord pc (mutationPairing Ω C pc) (sideSign pos) m-coord m pc := by
  change mutatedCoefficientMap pc (mutationPairing Ω C pc)
    (coord (mutationLinearPiece Ω C pc pos m)) pc=_
  rw [mutatedCoefficientMap_at]
  have HH : (∑j∈Finset.univ.erase pc,max 0 (-mutationPairing Ω C pc j)*
      coord (mutationLinearPiece Ω C pc pos m) j)=
      ∑j∈Finset.univ.erase pc,max 0 (-mutationPairing Ω C pc j)*coord m j:=by
    apply Finset.sum_congr rfl
    intro j hj
    rw [mutationLinearPiece_coordinates Ω C coord hcoord]
    cases pos <;> simp [(Finset.mem_erase.mp hj).1]
  rw [HH,mutationLinearPiece_coordinates Ω C coord hcoord]
  cases pos
  · simp only [Bool.false_eq_true,ite_false, if_false,Pi.sub_apply,Pi.smul_apply,Pi.single_eq_same,
      smul_eq_mul,mul_one,sideSign]
    have Hflip:=fiberUpper_flip coord pc (mutationPairing Ω C pc) 1 m
    rw [←root_pairing_coordinates Ω C coord hcoord pc hΩ hm] at Hflip
    change fiberUpper coord pc (mutationPairing Ω C pc) (-1) m=
      fiberUpper coord pc (mutationPairing Ω C pc) 1 m+1*Ω (simpleRoot C pc) m at Hflip
    rw [Hflip]
    change -(coord m pc-Ω (simpleRoot C pc) m)+
        (∑j∈Finset.univ.erase pc,max 0 (-mutationPairing Ω C pc j)*coord m j)=_
    simp only [fiberUpper,AddMonoidHom.coe_mk,ZeroHom.coe_mk,neg_mul,one_mul]
    ring
  · simp only [ite_true, if_true,sideSign]
    change -coord m pc+(∑j∈Finset.univ.erase pc,max 0 (-mutationPairing Ω C pc j)*coord m j)=_
    simp only [fiberUpper,AddMonoidHom.coe_mk,ZeroHom.coe_mk,neg_mul,one_mul]
    ring

include hcoord in
lemma mutation_root_image (hΩ : ∀m,Ω m m=0) (pos : Bool) {n : ℕ} {m : M}
    (hm : HasRootDegree C n m)
    (hb : m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)) :
    ∃d : ℕ,HasRootDegree (mutatedRoots Ω C pc) d (mutationLinearPiece Ω C pc pos m) ∧
      (d:ℤ)=nonpDegree coord pc m+
        fiberUpper coord pc (mutationPairing Ω C pc) (sideSign pos) m-coord m pc := by
  let q:=mutatedCoordinates Ω C coord pc (mutationLinearPiece Ω C pc pos m)
  have hq : ∀i,0≤q i:=by
    intro i
    by_cases hi : i=pc
    · subst i
      change 0 ≤ mutatedCoordinates Ω C coord pc (mutationLinearPiece Ω C pc pos m) pc
      rw [mutatedCoordinate_at Ω C coord hcoord pc hΩ pos hm]
      exact sub_nonneg.mpr hb.2
    · change 0 ≤ mutatedCoordinates Ω C coord pc (mutationLinearPiece Ω C pc pos m) i
      rw [mutatedCoordinate_off Ω C coord hcoord pc pos m i hi]
      obtain ⟨a,ha,hac,he⟩:=root_coordinates C coord hcoord hm
      rw [hac]
      exact Int.natCast_nonneg _
  refine ⟨∑i,(q i).toNat,⟨fun i=>(q i).toNat,rfl,?_⟩,?_⟩
  · have he : (fun i=>((q i).toNat:ℤ))=q:=funext (fun i=>Int.toNat_of_nonneg (hq i))
    rw [he]
    exact mutated_span Ω C coord hcoord pc hm pos
  · rw [Nat.cast_sum]
    simp only [Int.toNat_of_nonneg (hq _)]
    rw [←Finset.sum_erase_add _ _ (Finset.mem_univ pc)]
    have ha : q pc=fiberUpper coord pc (mutationPairing Ω C pc) (sideSign pos) m-coord m pc:=
      mutatedCoordinate_at Ω C coord hcoord pc hΩ pos hm
    have ho : (∑i∈Finset.univ.erase pc,q i)=nonpDegree coord pc m:=
      mutated_nonpDegree Ω C coord hcoord pc pos m
    rw [ha,ho]
    ring
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PureCutFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint RootTruncation WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)

include hcoord in
def simpleCompleted : CompletedPositive LaurentRay.vUnit Ω C :=
  ⟨normalizedSimple Ω (simpleRoot C pc),normalizedSimple_constant Ω _,by
    rw [←literalIncoming_simple Ω C coord hcoord pc]
    exact (literalIncomingCompleted Ω C (simpleIncomingList C) (simpleIncomingList_allowed C)
      (simpleRoot C pc)).property.2⟩

include hcoord in
lemma simpleCompleted_ray (j : ℕ) (m : M)
    (hm : coeff (j+1) (simpleCompleted Ω C coord hcoord pc).val m≠0) :
    OnPositiveRay (simpleRoot C pc) m := by
  change coeff (j+1) (normalizedSimple Ω (simpleRoot C pc)) m≠0 at hm
  rw [normalizedSimple,coeff_raySeries] at hm
  have he : m=(j+1) • simpleRoot C pc:=by
    by_contra hh; exact hm (Finsupp.single_eq_of_ne hh)
  exact ⟨1,j+1,by omega,by omega,by simpa only [one_nsmul] using he⟩

include hcoord in
def simpleOrientedCompleted (pos : Bool) : CompletedPositive LaurentRay.vUnit Ω C :=
  if pos then simpleCompleted Ω C coord hcoord pc else
    completedInverse LaurentRay.vUnit Ω C (simpleCompleted Ω C coord hcoord pc)

include hcoord in
lemma simpleOrientedCompleted_value (pos : Bool) :
    (simpleOrientedCompleted Ω C coord hcoord pc pos).val=
      simpleOriented Ω pos (simpleRoot C pc) := by cases pos <;> rfl

include hcoord in
lemma simple_cut_chart_bound (hΩ : ∀m,Ω m m=0) (pos : Bool)
    (A F : CompletedPositive LaurentRay.vUnit Ω C) (N : ℕ) (n : ℤ)
    (hprod : ∀j≤N,coeff j F.val=coeff j
      (if pos then (normalizedSimple Ω (simpleRoot C pc))*A.val
       else A.val*(normalizedSimple Ω (simpleRoot C pc))))
    (htrend : ∀j≤N,∀m,coeff j A.val m≠0 → 0≤ sideSign pos*Ω (simpleRoot C pc) m)
    (hbound : ∀j≤N,∀m,coeff j A.val m≠0 → nonpDegree coord pc m≤n →
      m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos))
    (h : M →+ ℝ) (hside : cutSide (!pos) h (simpleRoot C pc)) :
    ∀j≤N,∀m,coeff j (chartZero LaurentRay.vUnit Ω C h F).val m≠0 →
      nonpDegree coord pc m≤n → m∈fiberCone coord pc (mutationPairing Ω C pc) (-sideSign pos) := by
  let D:=simpleCompleted Ω C coord hcoord pc
  let O:=simpleOrientedCompleted Ω C coord hcoord pc pos
  let G:=completedConjugate LaurentRay.vUnit Ω C O A
  have hGval : G.val=adjoint (simpleOriented Ω pos (simpleRoot C pc)) A.val:=by
    change O.val*A.val*invOfUnit O.val 1=_
    rw [show O.val=simpleOriented Ω pos (simpleRoot C pc) from simpleOrientedCompleted_value Ω C coord hcoord pc pos]
    rfl
  let P:=fiberCone coord pc (mutationPairing Ω C pc) (-sideSign pos)
  let Q:=boundedNonpFrame (nonpDegree coord pc) P n
  have hQ : ∀j≤N,coeff j G.val∈supportedSubring LaurentRay.vUnit Ω Q:=by
    intro j hj m hmQ
    by_contra hm
    apply hmQ
    refine ⟨nonpDegree_root_nonneg C coord hcoord pc (chart_root_of_ne LaurentRay.vUnit Ω C G j m hm),?_⟩
    intro hn
    apply simpleOriented_adjoint_fiber Ω C coord hcoord pc hΩ pos A.val j n
      (fun a _=>A.property.2 a) (fun a ha=>htrend a (ha.trans hj))
      (fun a ha=>hbound a (ha.trans hj)) m ?_ hn
    rwa [←hGval]
  let Gc:=completedCut LaurentRay.vUnit Ω C N G
  have hchartQ:= (chartThree_supported LaurentRay.vUnit Ω C h Q Gc
    (completedCut_supported LaurentRay.vUnit Ω C N G Q hQ)).2.1
  have hremove : ∀j≤N,coeff j (chartZero LaurentRay.vUnit Ω C h F).val=
      coeff j (chartZero LaurentRay.vUnit Ω C h G).val:=by
    cases pos
    · have Hprod : ∀j≤N,coeff j F.val=coeff j (completedMul LaurentRay.vUnit Ω C D G).val:=by
        intro j hj
        rw [hprod j hj]
        simp only [Bool.false_eq_true,ite_false, if_false]
        change coeff j (A.val*D.val)=coeff j (D.val*G.val)
        rw [hGval]
        change coeff j (A.val*D.val)=coeff j (D.val*adjoint (invOfUnit D.val 1) A.val)
        rw [adjoint_inverse _ _ D.property.1,←mul_assoc,←mul_assoc,mul_invOfUnit _ 1 D.property.1,one_mul]
      intro j hj
      rw [chartZero_congr_through LaurentRay.vUnit Ω C h F _ N Hprod j hj]
      apply chartZero_left_positive LaurentRay.vUnit Ω C h D G N ?_ j hj
      intro k hk m hm
      have HR:=simpleCompleted_ray Ω C coord hcoord pc k m hm
      exact (HR.eval h).1.mpr hside
    · have Hprod : ∀j≤N,coeff j F.val=coeff j (completedMul LaurentRay.vUnit Ω C G D).val:=by
        intro j hj
        rw [hprod j hj]
        simp only [ite_true, if_true]
        change coeff j (D.val*A.val)=coeff j (G.val*D.val)
        rw [hGval]
        change coeff j (D.val*A.val)=coeff j (adjoint D.val A.val*D.val)
        rw [adjoint,mul_assoc,mul_assoc,invOfUnit_mul _ 1 D.property.1,mul_one]
      intro j hj
      rw [chartZero_congr_through LaurentRay.vUnit Ω C h F _ N Hprod j hj]
      apply chartZero_right_negative LaurentRay.vUnit Ω C h G D N ?_ j hj
      intro k hk m hm
      have HR:=simpleCompleted_ray Ω C coord hcoord pc k m hm
      exact (HR.eval h).2.2.mpr hside
  have hcut:=chartZero_congr_through LaurentRay.vUnit Ω C h Gc G N
    (fun j hj=>coeff_cut_of_le G.val hj)
  intro j hj m hm hn
  have hmGc : coeff j (chartZero LaurentRay.vUnit Ω C h Gc).val m≠0:=by
    rw [hcut j hj,←hremove j hj]; exact hm
  have hmQ : m∈Q:=by by_contra hh; exact hmGc (hchartQ j m hh)
  exact hmQ.2 hn
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_SimplePlaneGeometry
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries RootTruncation WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀d m,HasRootDegree C d m → L (e m)=(d:ℝ))
include hcoord he hB hcomp hdeg in
lemma cut_planar_fiber (N : ℕ) (n : ℤ) (pos : Bool)
    (r : M) (hr : 0<nonpDegree coord pc r)
    (ht : 0 < sideSign pos*Ω (simpleRoot C pc) r)
    (k : Module.Dual ℝ E) (hkp : k (e (simpleRoot C pc))=0) (hkr : k (e r)=0)
    (hzero : ∀j,j≤N → ∀m,HasRootDegree C j m → k (e m)=0 →
      m∈planeRoots e (e (simpleRoot C pc)) (e r))
    (HU : ∀q d,0<d → HasRootDegree C d q →
      0 < sideSign pos*Ω (simpleRoot C pc) q → ∀h : Module.Dual ℝ E,
      RayGeneric C N q (h.toAddMonoidHom.comp e) →
      cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc) →
      ∀j≤N,∀m,coeff j (chartZero LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e)
        (simpleTotalTransport Ω C)).val m≠0 → nonpDegree coord pc m≤n →
        m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)) :
    ∀j≤N,∀m,coeff j (chartZero LaurentRay.vUnit Ω C (-incomingCovector Ω r)
      (chartZero LaurentRay.vUnit Ω C (k.toAddMonoidHom.comp e) (simpleTotalTransport Ω C))).val m≠0 →
      nonpDegree coord pc m≤n →
      m∈fiberCone coord pc (mutationPairing Ω C pc) (-sideSign pos) := by
  classical
  let p:=simpleRoot C pc
  let F:=simpleTotalTransport Ω C
  let kM:=k.toAddMonoidHom.comp e
  let J:=chartZero LaurentRay.vUnit Ω C kM F
  let Jc:=completedCut LaurentRay.vUnit Ω C N J
  let P:=fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)
  let Q:=boundedNonpFrame (nonpDegree coord pc) P n
  have hΩ : ∀m,Ω m m=0:=by
    intro m; have H:=hB (e m); rw [hcomp] at H; exact_mod_cast H
  have hpr : B (e p) (e r)≠0:=by
    rw [hcomp]
    intro hz
    have hz' : Ω p r=0:=by exact_mod_cast hz
    change 0 < sideSign pos*Ω p r at ht
    rw [hz',mul_zero] at ht; omega
  have hplane : ∀j,coeff j Jc.val∈supportedSubring LaurentRay.vUnit Ω (planeRoots e (e p) (e r)):=by
    apply completedCut_supported
    intro j hj m hm
    by_contra hv
    have hz : kM m=0:=by
      by_contra hh; exact hv (chartZero_supported_kernel LaurentRay.vUnit Ω C kM F j m hh)
    exact hm (hzero j hj m (chart_root_of_ne LaurentRay.vUnit Ω C J j m hv) hz)
  obtain ⟨l,hl,hpair,hRay,hfact⟩:=planar_joint_factorization LaurentRay.vUnit Ω C e he B hB hcomp
    L hdeg (e p) (e r) (by rw [hdeg 1 p (simpleRoot_degree C pc)]; norm_num) hpr Jc hplane N
  let K (q : M):=completedCut LaurentRay.vUnit Ω C N (chartZero LaurentRay.vUnit Ω C (incomingCovector Ω q) Jc)
  let lA:=l.filter (fun q=>decide (nonpDegree coord pc q≠0))
  let A:=completedListProduct LaurentRay.vUnit Ω C lA K
  have hcut (a : M →+ ℝ) : ∀j≤N,coeff j (chartZero LaurentRay.vUnit Ω C a Jc).val=
      coeff j (chartZero LaurentRay.vUnit Ω C a J).val:=
    chartZero_congr_through LaurentRay.vUnit Ω C a Jc J N (fun j hj=>coeff_cut_of_le J.val hj)
  have hKray : ∀q∈l,∀j m,coeff (j+1) (K q).val m≠0 → OnPositiveRay q m:=by
    intro q hq j m hm
    change coeff (j+1) (cut N (chartZero LaurentRay.vUnit Ω C (incomingCovector Ω q) Jc).val) m≠0 at hm
    rw [coeff_cut] at hm
    split_ifs at hm with hj
    · exact hRay q hq j hj m hm
    · exact False.elim (hm rfl)
  have hltrend : ∀q∈l,0≤ sideSign pos*Ω p q:=by
    intro q hq
    obtain ⟨d,hd,hdN,hdq,hqP⟩:=hl q hq
    exact (plane_simple_pairing_sign Ω C coord hcoord pc e he B hB hcomp pos r q hr ht hqP).1
      (nonpDegree_root_nonneg C coord hcoord pc hdq)
  have hAframe : ∀j,coeff j A.val∈supportedSubring LaurentRay.vUnit Ω Q:=by
    apply completed_list_supported
    intro q hq
    have hq':=List.mem_filter.mp hq
    obtain ⟨d,hd,hdN,hdq,hqP⟩:=hl q hq'.1
    have hnq : 0<nonpDegree coord pc q:=lt_of_le_of_ne
      (nonpDegree_root_nonneg C coord hcoord pc hdq) (Ne.symm (of_decide_eq_true hq'.2))
    have htq:=(plane_simple_pairing_sign Ω C coord hcoord pc e he B hB hcomp pos r q hr ht hqP).2.1 hnq
    apply completedCut_supported
    intro j hj m hmQ
    by_contra hv
    apply hmQ
    refine ⟨nonpDegree_root_nonneg C coord hcoord pc
      (chart_root_of_ne LaurentRay.vUnit Ω C _ j m hv),?_⟩
    intro hn
    obtain ⟨ε,hε,Hε⟩:=planar_refinement_generic LaurentRay.vUnit Ω C e he B hB hcomp L hdeg
      N (e p) (e r) hpr k hkp hkr hzero q d hd hdq hqP F
    obtain ⟨hg,heq⟩:=Hε (ε/2) (by positivity) (by linarith)
    apply HU q d hd hdq htq _ hg ?_ j hj m ?_ hn
    · rw [real_perturbed_covector Ω e B hcomp]
      have hev : (kM+(ε/2) • incomingCovector Ω q) p=(ε/2)*(Ω p q:ℝ):=by
        change k (e p)+(ε/2)*(Ω p q:ℝ)=_; rw [hkp,zero_add]
      cases pos <;> simp only [cutSide,Bool.false_eq_true,ite_false, if_false,ite_true, if_true] <;> rw [hev]
      · have hh : (Ω p q:ℝ)<0:=by
          have : Ω p q<0:=by simpa [sideSign] using htq
          exact_mod_cast this
        exact mul_neg_of_pos_of_neg (by positivity) hh
      · have hh : 0<(Ω p q:ℝ):=by
          have : 0<Ω p q:=by simpa [sideSign] using htq
          exact_mod_cast this
        exact mul_pos (by positivity) hh
    · rw [heq j hj,←hcut _ j hj]; exact hv
  have hAplane : ∀j,coeff j A.val∈supportedSubring LaurentRay.vUnit Ω (planeRoots e (e p) (e r)):=by
    apply completed_list_supported
    intro q hq
    apply completedCut_supported
    intro j hj
    exact (chartThree_supported LaurentRay.vUnit Ω C (incomingCovector Ω q) _ Jc hplane).2.1 j
  have hAtrend : ∀j≤N,∀m,coeff j A.val m≠0 → 0≤ sideSign pos*Ω p m:=by
    intro j hj m hm
    have hmP : m∈planeRoots e (e p) (e r):=by by_contra hh; exact hm (hAplane j m hh)
    exact (plane_simple_pairing_sign Ω C coord hcoord pc e he B hB hcomp pos r m hr ht hmP).1
      (nonpDegree_root_nonneg C coord hcoord pc (chart_root_of_ne LaurentRay.vUnit Ω C A j m hm))
  have hface : ∀j≤N,coeff j (pureFace Ω C coord pc Jc).val=
      coeff j (simpleCompleted Ω C coord hcoord pc).val:=by
    intro j hj
    change coeff j (pureFaceSeries Ω coord pc Jc.val)=_
    rw [coeff_pureFaceSeries]
    change zeroProject LaurentRay.vUnit Ω (pureFaceCovector coord pc) (coeff j (cut N J.val))=_
    rw [coeff_cut_of_le J.val hj,←coeff_pureFaceSeries]
    change coeff j (pureFace Ω C coord pc J).val=_
    rw [pureFace_chartZero Ω C coord hcoord pc kM hkp F,pureFace_simpleTransport_value Ω C coord hcoord pc hΩ]
    rfl
  have hprod : ∀j≤N,coeff j Jc.val=coeff j
      (if pos then (normalizedSimple Ω p)*A.val else A.val*(normalizedSimple Ω p)):=by
    apply ordered_pure_factor_through Ω C coord hcoord pc hΩ pos l K hpair
      (fun q hq=>by obtain ⟨d,hd,_,hr,_⟩:=hl q hq; exact ⟨d,hd,hr⟩) hltrend hKray
      Jc (simpleCompleted Ω C coord hcoord pc) N ?_ hface
    intro j hj
    refine (hfact j hj).trans ?_
    exact completedListProduct_congr_through LaurentRay.vUnit Ω C l _ K N
      (fun q _ a ha=>(coeff_cut_of_le _ ha).symm) j hj
  have hside : cutSide (!pos) (-incomingCovector Ω r) p:=by
    cases pos <;> simp only [cutSide,Bool.not_false,Bool.not_true,ite_true, if_true,Bool.false_eq_true,ite_false, if_false,
      AddMonoidHom.neg_apply,incomingCovector] <;>
      norm_num only [Int.cast_neg,neg_pos,neg_lt_zero]
    · have H : Ω p r<0:=by simpa [sideSign] using ht
      change (Ω p r:ℝ)<0
      exact_mod_cast H
    · have H : 0<Ω p r:=by simpa [sideSign] using ht
      change 0<(Ω p r:ℝ)
      exact_mod_cast H
  have HB:=simple_cut_chart_bound Ω C coord hcoord pc hΩ pos A Jc N n hprod hAtrend
    (by
      intro j hj m hm hn
      have H : m∈Q:=by by_contra hh; exact hm (hAframe j m hh)
      exact H.2 hn)
    (-incomingCovector Ω r) hside
  intro j hj m hm hn
  exact HB j hj m (by rwa [hcut _ j hj]) hn
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_UpstreamFiber
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries RootTruncation FiniteRayGeometry FiniteEventTraversal
noncomputable section
variable {R M E I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M]
  [AddCommGroup E] [Module ℝ E] [Fintype I] [DecidableEq I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀d m,HasRootDegree C d m → L (e m)=(d:ℝ))
include hcoord he hB hcomp hdeg in
lemma upstream_fiber_induction (N : ℕ) (hN : 0<N) (n : ℤ) (P : AddSubmonoid M)
    (pos : Bool) (r : M) (dr : ℕ) (hdr : 0<dr) (hrd : HasRootDegree C dr r)
    (F D : CompletedPositive v Ω C)
    (hD : ∀j m,coeff (j+1) D.val m≠0 → OnPositiveRay r m)
    (hpres : ∀j≤N,∀m,OnPositiveRay r m →
      coeff j (FormalLog.log (chartZero v Ω C (incomingCovector Ω m) F).val) m=
        coeff j (FormalLog.log D.val) m)
    (hDP : ∀j≤N,∀m,coeff j D.val m≠0 → nonpDegree coord pc m=n → m∈P)
    (HI : ∀q d,0<d → HasRootDegree C d q → ∀h : Module.Dual ℝ E,
      RayGeneric C N q (h.toAddMonoidHom.comp e) →
      cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc) →
      ∀j≤N,∀m,coeff j (chartZero v Ω C (h.toAddMonoidHom.comp e) F).val m≠0 →
        nonpDegree coord pc m<n → m∈P)
    (h : Module.Dual ℝ E) (hg : RayGeneric C N r (h.toAddMonoidHom.comp e))
    (hside : cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc))
    (htrend : if pos then 0≤Ω (simpleRoot C pc) r else Ω (simpleRoot C pc) r≤0) :
    ∀j≤N,∀m,coeff j (chartZero v Ω C (h.toAddMonoidHom.comp e) F).val m≠0 →
      nonpDegree coord pc m=n → m∈P := by
  classical
  let S:=realRootsThrough e C N
  let vR:=B.flip (e r)
  obtain ⟨k,Hk,Hsign⟩:=exists_generic_offset S (e r) vR h hg.1
  let events:=lineEvents S vR k
  let Q (a : ℝ):=∀j≤N,∀m,
    coeff j (chartZero v Ω C ((k+a • vR).toAddMonoidHom.comp e) F).val m≠0 →
      nonpDegree coord pc m=n → m∈P
  have hsidek : cutSide pos (k.toAddMonoidHom.comp e) (simpleRoot C pc):=by
    have HH:=Hsign (e (simpleRoot C pc)) (realRoot_mem e C N 1 hN _ (simpleRoot_degree C pc))
    cases pos <;> simp only [cutSide,Bool.false_eq_true,ite_false, if_false,ite_true, if_true] at hside ⊢
    · exact HH.2 hside
    · exact HH.1 hside
  have hsidea (a : ℝ) (ha : 0≤a) :
      cutSide pos ((k+a • vR).toAddMonoidHom.comp e) (simpleRoot C pc):=by
    have heval : ((k+a • vR).toAddMonoidHom.comp e) (simpleRoot C pc)=
        k (e (simpleRoot C pc))+a*(Ω (simpleRoot C pc) r:ℝ):=by
      change k (e (simpleRoot C pc))+a*B (e (simpleRoot C pc)) (e r)=_
      rw [hcomp]
    cases pos <;> simp only [cutSide,Bool.false_eq_true,ite_false, if_false,ite_true, if_true] at hsidek htrend ⊢ <;> rw [heval]
    · have ht : (Ω (simpleRoot C pc) r:ℝ)≤0:=by exact_mod_cast htrend
      have hk : k (e (simpleRoot C pc))<0:=hsidek
      nlinarith
    · have ht : 0≤(Ω (simpleRoot C pc) r:ℝ):=by exact_mod_cast htrend
      have hk : 0<k (e (simpleRoot C pc)):=hsidek
      nlinarith
  have h0 : (0:ℝ)∉events:=by
    intro hevent
    obtain ⟨s,hs,hv,hs0⟩:=(mem_lineEvents_iff S vR k 0).mp hevent
    have hn : s∉Submodule.span ℝ {e r}:=by
      intro hmem
      obtain ⟨c,hc⟩:=Submodule.mem_span_singleton.mp hmem
      apply hv
      rw [←hc,map_smul]
      change c*B (e r) (e r)=0
      rw [hB,mul_zero]
    apply Hk.avoid s hs hn
    simpa only [zero_smul,add_zero] using hs0
  have hstart : ∃b,0≤b ∧ (∀a∈events,a<b) ∧ Q b:=by
    obtain ⟨b,hb,hbound⟩:=finite_upper_bound events
    have hΩ : ∀m,Ω m m=0:=by
      intro m; have HH:=hB (e m); rw [hcomp] at HH; exact_mod_cast HH
    have Hgen:=offset_ray_generic C e he L hdeg N dr r hdr hrd vR k Hk
    have Hinc:=incoming_ray_element_through v Ω C hΩ r (k.toAddMonoidHom.comp e)
      Hk.on_ray F D N (fun j hj hjN m hm hΩm hkm=>Hgen.2 j hj hjN m hm hkm) hD hpres
    have Href:=chart_zero_refinement v Ω C (incomingCovector Ω r) (k.toAddMonoidHom.comp e)
      ((k+b • vR).toAddMonoidHom.comp e) F N (by
        intro j hj m hm
        have HH:=far_line_lex S vR k b hbound (e m) (realRoot_mem e C N j hj m hm)
        simp only [vR,LinearMap.flip_apply,hcomp] at HH
        exact HH)
    refine ⟨b,hb.le,hbound,?_⟩
    intro j hj m hm hn
    apply hDP j hj m ?_ hn
    rw [Href j hj,Hinc j hj] at hm
    exact hm
  have hcell : ∀a b,0≤a → 0≤b → a∉events → b∉events →
      (∀z∈events,a<z ↔ b<z) → Q a → Q b:=by
    intro a b ha hb haS hbS Hside hpa
    have Hchart:=chart_sign_congr_through v Ω C
      ((k+a • vR).toAddMonoidHom.comp e) ((k+b • vR).toAddMonoidHom.comp e) F N (by
        intro j hj hjN m hm
        exact line_cell_signs S vR k a b haS hbS Hside (e m) (realRoot_mem e C N j hjN m hm))
    intro j hj m hm hn
    apply hpa j hj m ?_ hn
    rwa [Hchart j hj]
  have hstep : ∀a∈events,0<a → ∃ε>0,∀δ : ℝ,0<δ → δ<ε → Q (a+δ) → Q (a-δ):=by
    intro a ha ha0
    obtain ⟨s,hs,hsv,hsa⟩:=(mem_lineEvents_iff S vR k a).mp ha
    have hrs : B (e r) s≠0:=by
      rw [PlanarRayOrder.alternating_swap B hB]
      exact neg_ne_zero.mpr hsv
    let ka:=k+a • vR
    let kaM:=ka.toAddMonoidHom.comp e
    have hkr : ka (e r)=0:=by
      change k (e r)+a*B (e r) (e r)=0
      rw [Hk.on_ray,hB,mul_zero,add_zero]
    have hzero:=joint_roots_plane C e B N r k Hk a s hs hsv hsa
    obtain ⟨εp,hεp,Hεp⟩:=root_lex_epsilon C N kaM (incomingCovector Ω r)
    obtain ⟨εm,hεm,Hεm⟩:=root_lex_epsilon C N kaM (-incomingCovector Ω r)
    refine ⟨min εp εm,lt_min hεp hεm,?_⟩
    intro δ hδ hδε hright
    have hrefp:=chart_zero_refinement v Ω C kaM (incomingCovector Ω r)
      (kaM+δ • incomingCovector Ω r) F N (Hεp δ hδ (lt_of_lt_of_le hδε (min_le_left _ _)))
    have hrefm:=chart_zero_refinement v Ω C kaM (-incomingCovector Ω r)
      (kaM+δ • (-incomingCovector Ω r)) F N (Hεm δ hδ (lt_of_lt_of_le hδε (min_le_right _ _)))
    have hlp : ((k+(a+δ) • vR).toAddMonoidHom.comp e)=kaM+δ • incomingCovector Ω r:=by
      ext m; change k (e m)+(a+δ)*B (e m) (e r)=k (e m)+a*B (e m) (e r)+δ*(Ω m r:ℝ)
      rw [hcomp]; ring
    have hlm : ((k+(a-δ) • vR).toAddMonoidHom.comp e)=kaM+δ • (-incomingCovector Ω r):=by
      ext m; change k (e m)+(a-δ)*B (e m) (e r)=k (e m)+a*B (e m) (e r)+δ* -(Ω m r:ℝ)
      rw [hcomp]; ring
    have HH:=offcut_planar_support v Ω C coord hcoord pc e he B hB hcomp L hdeg N hN n P pos r dr hdr hrd
      s hrs ka hkr hsa hzero (hsidea a ha0.le) F HI (by
        intro j hj m hm hn
        apply hright j hj m ?_ hn
        rw [hlp,hrefp j hj]
        exact hm)
    intro j hj m hm hn
    rw [hlm,hrefm j hj] at hm
    exact HH j hj m hm hn
  have HK : ∀j≤N,∀m,coeff j (chartZero v Ω C (k.toAddMonoidHom.comp e) F).val m≠0 →
      nonpDegree coord pc m=n → m∈P:=by
    have HH:=descend events Q hstart hcell hstep 0 (le_refl 0) h0
    simpa only [Q,zero_smul,add_zero] using HH
  have Hchart:=chart_sign_congr_through v Ω C (h.toAddMonoidHom.comp e) (k.toAddMonoidHom.comp e) F N (by
    intro j hj hjN m hm
    have HS:=Hsign (e m) (realRoot_mem e C N j hjN m hm)
    refine ⟨HS.1,?_,HS.2⟩
    intro hh
    exact ((hg.2 j hj hjN m hm hh).eval (k.toAddMonoidHom.comp e)).2.1.mpr Hk.on_ray)
  intro j hj m hm hn
  apply HK j hj m ?_ hn
  rwa [←Hchart j hj]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_UpstreamSimpleFiber
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.segmentBetween_finish _root_.OAI.ElementaryPositivity.QuantumTorus.segmentBetween_start _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀d m,HasRootDegree C d m → L (e m)=(d:ℝ))
include hcoord he hB hcomp hdeg in
lemma upstream_simple_fiber (N : ℕ) (hN : 0<N) (n : ℤ) (pos : Bool)
    (r : M) (dr : ℕ) (hdr : 0<dr) (hrd : HasRootDegree C dr r)
    (hr : 0<nonpDegree coord pc r)
    (HI : ∀q d,0<d → HasRootDegree C d q → ∀h : Module.Dual ℝ E,
      RayGeneric C N q (h.toAddMonoidHom.comp e) →
      cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc) →
      ∀j≤N,∀m,coeff j (chartZero LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e)
        (simpleTotalTransport Ω C)).val m≠0 → nonpDegree coord pc m<n →
        m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos))
    (h : Module.Dual ℝ E) (hg : RayGeneric C N r (h.toAddMonoidHom.comp e))
    (hside : cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc))
    (htrend : 0≤ sideSign pos*Ω (simpleRoot C pc) r) :
    ∀j≤N,∀m,coeff j (chartZero LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e)
      (simpleTotalTransport Ω C)).val m≠0 → nonpDegree coord pc m=n →
      m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos) := by
  have hΩ : ∀m,Ω m m=0:=by
    intro m; have H:=hB (e m); rw [hcomp] at H; exact_mod_cast H
  apply upstream_fiber_induction LaurentRay.vUnit Ω C coord hcoord pc e he B hB hcomp L hdeg
    N hN n _ pos r dr hdr hrd (simpleTotalTransport Ω C)
    (literalIncomingCompleted Ω C (simpleIncomingList C) (simpleIncomingList_allowed C) r)
    (by
      intro j m hm
      by_contra hh
      exact hm (literalRootProducts_strictSupport Ω C (OnPositiveRay r)
        (fun a b ha hb=>ha.add hb) (literalIncomingRay_mem Ω C
          (simpleIncomingList C) (simpleIncomingList_allowed C) r) j m hh))
    (fun j _ m hm=>literalTotalTransport_ray_prescription Ω C hΩ
      (simpleIncomingList C) (simpleIncomingList_allowed C) r j m hm) ?_ HI h hg hside ?_
  · intro j hj m hm hn
    by_contra hh
    exact hm (simpleIncomingCompleted_fiber Ω C coord hcoord pc r hr
      (mutationPairing Ω C pc) (sideSign pos) j m hh)
  · cases pos <;> simpa [sideSign] using htrend
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries RootTruncation FiniteRayGeometry FiniteEventTraversal WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀d m,HasRootDegree C d m → L (e m)=(d:ℝ))
include hcoord he hB hcomp hdeg in
lemma global_simple_fiber_step (N : ℕ) (hN : 0<N) (n : ℤ)
    (HI : ∀q d,0<d → HasRootDegree C d q → ∀h : Module.Dual ℝ E,
      RayGeneric C N q (h.toAddMonoidHom.comp e) → ∀pos : Bool,
      cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc) →
      ∀j≤N,∀m,coeff j (chartZero LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e)
        (simpleTotalTransport Ω C)).val m≠0 → nonpDegree coord pc m<n →
        m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos))
    (r : M) (dr : ℕ) (hdr : 0<dr) (hrd : HasRootDegree C dr r)
    (h : Module.Dual ℝ E) (hg : RayGeneric C N r (h.toAddMonoidHom.comp e))
    (pos : Bool) (hside : cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc)) :
    ∀j≤N,∀m,coeff j (chartZero LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e)
      (simpleTotalTransport Ω C)).val m≠0 → nonpDegree coord pc m=n →
      m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos) := by
  classical
  let p:=simpleRoot C pc
  let F:=simpleTotalTransport Ω C
  have hp : (h.toAddMonoidHom.comp e) p≠0:=by
    cases pos <;> simp only [cutSide,Bool.false_eq_true,ite_false, if_false,ite_true, if_true] at hside
    · exact ne_of_lt hside
    · exact ne_of_gt hside
  have hr : 0<nonpDegree coord pc r:=nonp_positive_off_cut C coord hcoord pc hdr hrd
    (h.toAddMonoidHom.comp e) hp hg.1
  have hΩ : ∀m,Ω m m=0:=by
    intro m; have H:=hB (e m); rw [hcomp] at H; exact_mod_cast H
  have HU (side : Bool) : ∀q d,0<d → HasRootDegree C d q →
      0 < sideSign side*Ω p q → ∀b : Module.Dual ℝ E,
      RayGeneric C N q (b.toAddMonoidHom.comp e) → cutSide side (b.toAddMonoidHom.comp e) p →
      ∀j≤N,∀m,coeff j (chartZero LaurentRay.vUnit Ω C (b.toAddMonoidHom.comp e) F).val m≠0 →
        nonpDegree coord pc m≤n → m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign side):=by
    intro q d hd hdq ht b hb hs j hj m hm hn
    by_cases hn' : nonpDegree coord pc m<n
    · exact HI q d hd hdq b hb side hs j hj m hm hn'
    have hqn : 0<nonpDegree coord pc q:=by
      apply nonp_positive_off_cut C coord hcoord pc hd hdq (b.toAddMonoidHom.comp e) ?_ hb.1
      cases side <;> simp only [cutSide,Bool.false_eq_true,ite_false, if_false,ite_true, if_true] at hs
      · exact ne_of_lt hs
      · exact ne_of_gt hs
    exact upstream_simple_fiber Ω C coord hcoord pc e he B hB hcomp L hdeg N hN n side q d hd hdq hqn
      (fun q d hd hr b hb hs=>HI q d hd hr b hb side hs) b hb hs ht.le j hj m hm (by omega)
  let S:=realRootsThrough e C N
  let vR:=B.flip (e r)
  obtain ⟨k,Hk,Hsign⟩:=exists_generic_offset S (e r) vR h hg.1
  let events:=lineEvents S vR k
  let P (side : Bool):=fiberCone coord pc (mutationPairing Ω C pc) (sideSign side)
  let Q (a : ℝ):=∀side : Bool,cutSide side ((k+a • vR).toAddMonoidHom.comp e) p →
    ∀j≤N,∀m,coeff j (chartZero LaurentRay.vUnit Ω C ((k+a • vR).toAddMonoidHom.comp e) F).val m≠0 →
      nonpDegree coord pc m=n → m∈P side
  have h0 : (0:ℝ)∉events:=by
    intro hevent
    obtain ⟨s,hs,hv,hs0⟩:=(mem_lineEvents_iff S vR k 0).mp hevent
    have hn : s∉Submodule.span ℝ {e r}:=by
      intro hmem
      obtain ⟨c,hc⟩:=Submodule.mem_span_singleton.mp hmem
      apply hv
      rw [←hc,map_smul]
      change c*B (e r) (e r)=0
      rw [hB,mul_zero]
    apply Hk.avoid s hs hn
    simpa only [zero_smul,add_zero] using hs0
  have hstart : ∃b,0≤b ∧ (∀a∈events,a<b) ∧ Q b:=by
    obtain ⟨b,hb,hbound⟩:=finite_upper_bound events
    let D:=literalIncomingCompleted Ω C (simpleIncomingList C) (simpleIncomingList_allowed C) r
    have Hgen:=offset_ray_generic C e he L hdeg N dr r hdr hrd vR k Hk
    have Hinc:=incoming_ray_element_through LaurentRay.vUnit Ω C hΩ r (k.toAddMonoidHom.comp e)
      Hk.on_ray F D N (fun j hj hjN m hm hΩm hkm=>Hgen.2 j hj hjN m hm hkm)
      (by intro j m hm; by_contra hh; exact hm (literalRootProducts_strictSupport Ω C (OnPositiveRay r)
        (fun a b ha hb=>ha.add hb) (literalIncomingRay_mem Ω C (simpleIncomingList C) (simpleIncomingList_allowed C) r) j m hh))
      (fun j _ m hm=>literalTotalTransport_ray_prescription Ω C hΩ (simpleIncomingList C)
        (simpleIncomingList_allowed C) r j m hm)
    have Href:=chart_zero_refinement LaurentRay.vUnit Ω C (incomingCovector Ω r) (k.toAddMonoidHom.comp e)
      ((k+b • vR).toAddMonoidHom.comp e) F N (by
        intro j hj m hm
        have HH:=far_line_lex S vR k b hbound (e m) (realRoot_mem e C N j hj m hm)
        simp only [vR,LinearMap.flip_apply,hcomp] at HH
        exact HH)
    refine ⟨b,hb.le,hbound,?_⟩
    intro side hs j hj m hm hn
    by_contra hh
    apply hm
    rw [Href j hj,Hinc j hj]
    exact simpleIncomingCompleted_fiber Ω C coord hcoord pc r hr (mutationPairing Ω C pc) (sideSign side) j m hh
  have hcell : ∀a b,0≤a → 0≤b → a∉events → b∉events →
      (∀z∈events,a<z ↔ b<z) → Q a → Q b:=by
    intro a b ha hb haS hbS Hside Hpa side hs j hj m hm hn
    have Hsigns:=line_cell_signs S vR k a b haS hbS Hside
    have Hchart:=chart_sign_congr_through LaurentRay.vUnit Ω C
      ((k+a • vR).toAddMonoidHom.comp e) ((k+b • vR).toAddMonoidHom.comp e) F N
      (fun j hj hjN m hm=>Hsigns (e m) (realRoot_mem e C N j hjN m hm))
    have hs' : cutSide side ((k+a • vR).toAddMonoidHom.comp e) p:=by
      have HH:=line_cell_signs S vR k b a hbS haS (fun z hz=>(Hside z hz).symm)
        (e p) (realRoot_mem e C N 1 hN p (simpleRoot_degree C pc))
      cases side <;> simp only [cutSide,Bool.false_eq_true,ite_false, if_false,ite_true, if_true] at hs ⊢
      · exact HH.2.2 hs
      · exact HH.1 hs
    apply Hpa side hs' j hj m ?_ hn
    rwa [Hchart j hj]
  have hstep : ∀a∈events,0<a → ∃ε>0,∀δ : ℝ,0<δ → δ<ε → Q (a+δ) → Q (a-δ):=by
    intro a ha ha0
    obtain ⟨s,hs,hsv,hsa⟩:=(mem_lineEvents_iff S vR k a).mp ha
    have hrs : B (e r) s≠0:=by
      rw [PlanarRayOrder.alternating_swap B hB]
      exact neg_ne_zero.mpr hsv
    let ka:=k+a • vR
    let kaM:=ka.toAddMonoidHom.comp e
    have hkr : ka (e r)=0:=by
      change k (e r)+a*B (e r) (e r)=0
      rw [Hk.on_ray,hB,mul_zero,add_zero]
    have hzero:=joint_roots_plane C e B N r k Hk a s hs hsv hsa
    obtain ⟨εp,hεp,Hεp⟩:=root_lex_epsilon C N kaM (incomingCovector Ω r)
    obtain ⟨εm,hεm,Hεm⟩:=root_lex_epsilon C N kaM (-incomingCovector Ω r)
    refine ⟨min εp εm,lt_min hεp hεm,?_⟩
    intro δ hδ hδε hright side hsideδ j hj m hm hn
    have hδp : δ<εp:=lt_of_lt_of_le hδε (min_le_left _ _)
    have hδm : δ<εm:=lt_of_lt_of_le hδε (min_le_right _ _)
    have hrefp:=chart_zero_refinement LaurentRay.vUnit Ω C kaM (incomingCovector Ω r)
      (kaM+δ • incomingCovector Ω r) F N (Hεp δ hδ hδp)
    have hrefm:=chart_zero_refinement LaurentRay.vUnit Ω C kaM (-incomingCovector Ω r)
      (kaM+δ • (-incomingCovector Ω r)) F N (Hεm δ hδ hδm)
    have hlp : ((k+(a+δ) • vR).toAddMonoidHom.comp e)=kaM+δ • incomingCovector Ω r:=by
      ext m; change k (e m)+(a+δ)*B (e m) (e r)=k (e m)+a*B (e m) (e r)+δ*(Ω m r:ℝ)
      rw [hcomp]; ring
    have hlm : ((k+(a-δ) • vR).toAddMonoidHom.comp e)=kaM+δ • (-incomingCovector Ω r):=by
      ext m; change k (e m)+(a-δ)*B (e m) (e r)=k (e m)+a*B (e m) (e r)+δ* -(Ω m r:ℝ)
      rw [hcomp]; ring
    rw [hlm,hrefm j hj] at hm
    by_cases hkp : kaM p=0
    · have hpr : Ω p r≠0:=by
        intro hz
        have hkp' : k (e p)=0:=by
          change k (e p)+a*B (e p) (e r)=0 at hkp
          simpa only [hcomp,hz,Int.cast_zero,mul_zero,add_zero] using hkp
        have Hgen:=offset_ray_generic C e he L hdeg N dr r hdr hrd vR k Hk
        exact positive_nonp_not_simple_ray C coord hcoord pc r hr
          (Hgen.2 1 Nat.zero_lt_one hN p (simpleRoot_degree C pc) hkp')
      have hprR : B (e p) (e r)≠0:=by rw [hcomp]; exact_mod_cast hpr
      have hzero' : ∀d,d≤N → ∀m,HasRootDegree C d m → ka (e m)=0 →
          m∈planeRoots e (e p) (e r):=by
        intro d hd m hm hz
        have HG:=joint_roots_plane C e B N r k Hk a (e p)
          (realRoot_mem e C N 1 hN p (simpleRoot_degree C pc)) hprR hkp d hd m hm hz
        change e m∈Submodule.span ℝ {e p,e r}
        simpa only [Set.pair_comm (e r) (e p)] using HG
      have ht : 0 < sideSign (!side)*Ω p r:=by
        rw [hlm] at hsideδ
        have hev : (kaM+δ • (-incomingCovector Ω r)) p= -δ*(Ω p r:ℝ):=by
          change kaM p+δ*(-(Ω p r:ℝ))=_
          rw [hkp]; ring
        cases side <;> simp only [cutSide,Bool.false_eq_true,ite_false, if_false,ite_true, if_true] at hsideδ <;>
          rw [hev] at hsideδ
        · have HP : 0<(Ω p r:ℝ):=by nlinarith
          simpa [sideSign] using (show 0<Ω p r from by exact_mod_cast HP)
        · have HP : (Ω p r:ℝ)<0:=by nlinarith
          simpa [sideSign] using (show Ω p r<0 from by exact_mod_cast HP)
      have HH:=cut_planar_fiber Ω C coord hcoord pc e he B hB hcomp L hdeg N n (!side)
        r hr ht ka hkp hkr hzero' (HU (!side)) j hj m hm (le_of_eq hn)
      change m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign side)
      simpa only [sideSign_neg,neg_neg] using HH
    · have hsignp:=Hεp δ hδ hδp 1 hN p (simpleRoot_degree C pc)
      have hsignm:=Hεm δ hδ hδm 1 hN p (simpleRoot_degree C pc)
      have hs0 : cutSide side kaM p:=by
        rw [hlm] at hsideδ
        cases side <;> simp only [cutSide,Bool.false_eq_true,ite_false, if_false,ite_true, if_true] at hsideδ ⊢
        · by_contra hh
          have hp : 0<kaM p:=lt_of_le_of_ne (by linarith) (Ne.symm hkp)
          have HH:=hsignm.1 hp
          linarith
        · by_contra hh
          have hp : kaM p<0:=lt_of_le_of_ne (by linarith) hkp
          have HH:=hsignm.2.1 hp
          linarith
      have hsplus : cutSide side ((k+(a+δ) • vR).toAddMonoidHom.comp e) p:=by
        rw [hlp]
        cases side <;> simp only [cutSide,Bool.false_eq_true,ite_false, if_false,ite_true, if_true] at hs0 ⊢
        · exact hsignp.2.1 hs0
        · exact hsignp.1 hs0
      exact offcut_planar_support LaurentRay.vUnit Ω C coord hcoord pc e he B hB hcomp L hdeg N hN n
        (P side) side r dr hdr hrd s hrs ka hkr hsa hzero hs0 F
        (fun q d hd hr b hb hs=>HI q d hd hr b hb side hs)
        (by
          intro j hj m hm hn
          apply hright side hsplus j hj m ?_ hn
          rw [hlp,hrefp j hj]; exact hm) j hj m hm hn
  have HK : Q 0:=descend events Q hstart hcell hstep 0 (le_refl 0) h0
  have hsidek : cutSide pos (k.toAddMonoidHom.comp e) p:=by
    have HH:=Hsign (e p) (realRoot_mem e C N 1 hN p (simpleRoot_degree C pc))
    cases pos <;> simp only [cutSide,Bool.false_eq_true,ite_false, if_false,ite_true, if_true] at hside ⊢
    · exact HH.2 hside
    · exact HH.1 hside
  have Hchart:=chart_sign_congr_through LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e)
    (k.toAddMonoidHom.comp e) F N (by
      intro j hj hjN m hm
      have HS:=Hsign (e m) (realRoot_mem e C N j hjN m hm)
      refine ⟨HS.1,?_,HS.2⟩
      intro hh
      exact ((hg.2 j hj hjN m hm hh).eval (k.toAddMonoidHom.comp e)).2.1.mpr Hk.on_ray)
  intro j hj m hm hn
  have HK':=HK pos (by simpa only [zero_smul,add_zero] using hsidek) j hj m
  apply HK' ?_ hn
  simpa only [zero_smul,add_zero] using (show coeff j (chartZero LaurentRay.vUnit Ω C
    (k.toAddMonoidHom.comp e) F).val m≠0 from by rwa [←Hchart j hj])
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_GlobalFiberBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀d m,HasRootDegree C d m → L (e m)=(d:ℝ))
include hcoord he hB hcomp hdeg in
theorem simple_fiber_bound_through (N : ℕ) (hN : 0<N)
    (r : M) (dr : ℕ) (hdr : 0<dr) (hrd : HasRootDegree C dr r)
    (h : Module.Dual ℝ E) (hg : RayGeneric C N r (h.toAddMonoidHom.comp e))
    (pos : Bool) (hside : cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc)) :
    ∀j≤N,∀m,coeff j (chartZero LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e)
      (simpleTotalTransport Ω C)).val m≠0 →
      m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos) := by
  have H : ∀n : ℕ,∀q d,0<d → HasRootDegree C d q → ∀b : Module.Dual ℝ E,
      RayGeneric C N q (b.toAddMonoidHom.comp e) → ∀s : Bool,
      cutSide s (b.toAddMonoidHom.comp e) (simpleRoot C pc) →
      ∀j≤N,∀m,coeff j (chartZero LaurentRay.vUnit Ω C (b.toAddMonoidHom.comp e)
        (simpleTotalTransport Ω C)).val m≠0 → nonpDegree coord pc m=(n:ℤ) →
        m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign s) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro q d hd hdq b hb s hs
      apply global_simple_fiber_step Ω C coord hcoord pc e he B hB hcomp L hdeg N hN (n:ℤ) ?_
        q d hd hdq b hb s hs
      intro q' d' hd' hdq' b' hb' s' hs' j hj m hm hn
      have hw : 0≤nonpDegree coord pc m:=nonpDegree_root_nonneg C coord hcoord pc
        (chart_root_of_ne LaurentRay.vUnit Ω C _ j m hm)
      exact ih (nonpDegree coord pc m).toNat (by omega) q' d' hd' hdq' b' hb' s' hs'
        j hj m hm (by omega)
  intro j hj m hm
  have hw : 0≤nonpDegree coord pc m:=nonpDegree_root_nonneg C coord hcoord pc
    (chart_root_of_ne LaurentRay.vUnit Ω C _ j m hm)
  exact H (nonpDegree coord pc m).toNat r dr hdr hrd h hg pos hside j hj m hm (by omega)

include hcoord he hB hcomp hdeg in
theorem simple_fiber_bound (r : M) (dr : ℕ) (hdr : 0<dr) (hrd : HasRootDegree C dr r)
    (h : Module.Dual ℝ E) (hg : ∀N,RayGeneric C N r (h.toAddMonoidHom.comp e))
    (pos : Bool) (hside : cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc)) :
    ∀j m,coeff j (chartZero LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e)
      (simpleTotalTransport Ω C)).val m≠0 →
      m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos) := by
  intro j m hm
  exact simple_fiber_bound_through Ω C coord hcoord pc e he B hB hcomp L hdeg (max 1 j)
    (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)) r dr hdr hrd h (hg _) pos hside
    j (le_max_right _ _) m hm

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_MutationDegreeBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)

include hcoord in
lemma mutation_root_image_bound (hΩ : ∀m,Ω m m=0) (pos : Bool) {n : ℕ} {m : M}
    (hm : HasRootDegree C n m)
    (hb : m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)) :
    ∃d : ℕ,HasRootDegree (mutatedRoots Ω C pc) d (mutationLinearPiece Ω C pc pos m) ∧
      (nonpDegree coord pc m:ℤ)≤(d:ℤ) ∧ n≤(mutationSize Ω C pc+1)*d := by
  obtain ⟨d,hd,hde⟩:=mutation_root_image Ω C coord hcoord pc hΩ pos hm hb
  have hwd : nonpDegree coord pc m≤(d:ℤ):=by have HB:=hb.2; omega
  have Hn:=fiber_full_degree_bound Ω C coord hcoord pc pos hm hb
  have HH : (n:ℤ)≤((mutationSize Ω C pc+1:ℕ):ℤ)*(d:ℤ):=
    Hn.trans (mul_le_mul_of_nonneg_left hwd (Int.natCast_nonneg _))
  refine ⟨d,hd,hwd,?_⟩
  exact_mod_cast HH

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_WallRegrade
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d)

variable {R : Type*} [CommRing R] [Algebra ℚ R] (v : Rˣ) (Ω : M →+ M →+ ℤ)

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable (pc : I) (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀d m,HasRootDegree C d m → L (e m)=(d:ℝ))
include hcoord he hS hcomp hdeg in
lemma simple_regrade_bound (r : M) (dr : ℕ) (hdr : 0<dr) (hrd : HasRootDegree C dr r)
    (h : Module.Dual ℝ E) (hg : ∀N,RayGeneric C N r (h.toAddMonoidHom.comp e))
    (pos : Bool) (hside : cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc)) :
    RegradeBound LaurentRay.vUnit Ω (nonpDegree coord pc) (mutationSize Ω C pc+1)
      (chartZero LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e) (simpleTotalTransport Ω C)).val := by
  intro j m hm
  have hroot:=chart_root_of_ne LaurentRay.vUnit Ω C (chartZero LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e) (simpleTotalTransport Ω C)) j m hm
  have hb:=simple_fiber_bound Ω C coord hcoord pc e he S hS hcomp L hdeg
    r dr hdr hrd h hg pos hside j m hm
  have H:=fiber_full_degree_bound Ω C coord hcoord pc pos hroot hb
  have hn:=nonpDegree_root_nonneg C coord hcoord pc hroot
  refine ⟨hn,?_⟩
  have hd : ((nonpDegree coord pc m).toNat:ℤ)=nonpDegree coord pc m:=Int.toNat_of_nonneg hn
  rw [←hd] at H
  exact_mod_cast H

include hcoord he hS hcomp hdeg in
lemma simple_inverse_regrade_bound (r : M) (dr : ℕ) (hdr : 0<dr) (hrd : HasRootDegree C dr r)
    (h : Module.Dual ℝ E) (hg : ∀N,RayGeneric C N r (h.toAddMonoidHom.comp e))
    (pos : Bool) (hside : cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc)) :
    RegradeBound LaurentRay.vUnit Ω (nonpDegree coord pc) (mutationSize Ω C pc+1)
      (PowerSeries.invOfUnit
        (chartZero LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e) (simpleTotalTransport Ω C)).val 1) :=
  (simple_regrade_bound C coord hcoord Ω pc e he S hS hcomp L hdeg r dr hdr hrd h hg pos hside).invOfUnit
    LaurentRay.vUnit Ω (nonpDegree coord pc) (mutationSize Ω C pc+1)
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I) (pos : Bool)

variable [Fintype I]

variable {R : Type*} [CommRing R] (v : Rˣ)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.wallRegradeRing
local instance wallRegradeAddCommMonoid_r7588b2_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance wallRegradeAddGroup_r7588b2_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
include hcoord hΩ in
lemma mutationCompletion_bound (f : CompletedPositive v Ω C)
    (hf : ∀n m,coeff n f.val m≠0 → m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)) :
    RegradeBound v Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1) f.val := by
  intro n m hm
  obtain ⟨d,hd,hnp,hn⟩:=mutation_root_image_bound Ω C coord hcoord pc hΩ pos
    (by by_contra hh; exact hm (f.property.2 n m hh)) (hf n m hm)
  rw [mutationNewOrder_of_root Ω C coord hcoord pc pos hd]
  exact ⟨Int.natCast_nonneg _,by simpa using hn⟩

include hcoord in
lemma mutationCompletion_graded (f : CompletedPositive v Ω C)
    (hf : ∀n m,coeff n f.val m≠0 → m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)) :
    ∀d,coeff d (mutationCompletion Ω hΩ C coord pc pos v f.val)∈
      rootGrade v Ω (mutatedRoots Ω C pc) d := by
  classical
  intro d m hm
  obtain ⟨a,rfl⟩:=mutationLinearPiece_surjective Ω hΩ C pc pos m
  rw [mutationCompletion_coeff_read]
  split_ifs with ha
  · by_contra hz
    obtain ⟨n,hn,hz⟩:=Finset.exists_ne_zero_of_sum_ne_zero hz
    obtain ⟨d',hd',he⟩:=mutation_root_image Ω C coord hcoord pc hΩ pos
      (by by_contra hh; exact hz (f.property.2 n a hh)) (hf n a hz)
    have he':=mutationNewOrder_of_root Ω C coord hcoord pc pos hd'
    rw [he',Int.toNat_natCast] at ha
    exact hm (ha ▸ hd')
  · rfl

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_ComparisonLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)

def actualLineLetter (a : ℝ) :
    ComparisonCrossing LaurentRay.vUnit Ω (nonpDegree coord pc) (pureDegree coord pc)
      (mutationSize Ω C pc+1) := by
  classical
  exact if ha : ∃N,a∈lineEvents (realRootsThrough e C N) v k then
    if hp : (k+a • v) (e (simpleRoot C pc))=0 then
      .pure (decide (v (e (simpleRoot C pc))<0))
    else
      let data:=lineRayData C e he L hdeg v k H a ha
      let U:=completedBiUnit LaurentRay.vUnit Ω C coord hcoord pc
        (chartZero LaurentRay.vUnit Ω C ((k+a • v).toAddMonoidHom.comp e) (simpleTotalTransport Ω C))
      let side:=decide (0<(k+a • v) (e (simpleRoot C pc)))
      let hs:=cutSide_decide ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc) hp
      let hf:=simple_regrade_bound C coord hcoord Ω pc e he S hS hcomp L hdeg
        data.root data.degree data.degree_pos data.root_degree (k+a • v) data.generic side hs
      let hi:=simple_inverse_regrade_bound C coord hcoord Ω pc e he S hS hcomp L hdeg
        data.root data.degree data.degree_pos data.root_degree (k+a • v) data.generic side hs
      orientedBounded LaurentRay.vUnit Ω (nonpDegree coord pc) (pureDegree coord pc)
        (mutationSize Ω C pc+1) U hf hi (decide (v (e data.root)<0))
  else .bounded 1 (RegradeBound.one _ _ _ _) (RegradeBound.one _ _ _ _)

include hdeg H in
lemma line_cut_event (a : ℝ) (ha : (k+a • v) (e (simpleRoot C pc))=0) :
    a∈lineEvents (realRootsThrough e C 1) v k := by
  by_contra hn
  exact line_chamber_of_not_event C e L hdeg 1 v k (H 1) a hn 1 one_pos le_rfl
    (simpleRoot C pc) (simpleRoot_degree C pc) ha

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteRefinementImportAll
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)

def actualLineWord (lo hi : ℝ) (N : ℕ) :
    List (ComparisonCrossing LaurentRay.vUnit Ω (nonpDegree coord pc) (pureDegree coord pc)
      (mutationSize Ω C pc+1)) :=
  (intervalEventList C e v k lo hi N).map
    (actualLineLetter Ω C coord hcoord pc e he S hS hcomp L hdeg v k H)

end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry WallUnits
noncomputable section
variable {A : Type*} [Ring A]

variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_3_r7588b2_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_3_r7588b2_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
def mutatedLineFactor (a : ℝ) : PowerSeries (Torus LaurentRay.vUnit Ω) := by
  classical
  exact if ha : ∃N,a∈lineEvents (realRootsThrough e C N) v k then
    if (k+a • v) (e (simpleRoot C pc))=0 then
      orientPowerSeries (!(decide (v (e (simpleRoot C pc))<0)))
        (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc))
    else
      let data:=lineRayData C e he L hdeg v k H a ha
      let pos:=decide (0<(k+a • v) (e (simpleRoot C pc)))
      mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit
        (orientPowerSeries (decide (v (e data.root)<0))
          (chartZero LaurentRay.vUnit Ω C ((k+a • v).toAddMonoidHom.comp e)
            (simpleTotalTransport Ω C)).val)
  else 1

lemma mutatedLineFactor_high (D N : ℕ) (hN : 1≤N)
    (hDN : (mutationSize Ω C pc+1)*D≤N) (a : ℝ)
    (ha : a∉lineEvents (realRootsThrough e C N) v k) :
    ∀n≤D,coeff n (mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H a)=coeff n 1 := by
  classical
  unfold mutatedLineFactor
  split
  · next hevent=>
    split
    · next hp=>
      exact False.elim (ha (lineEvents_mono (realRootsThrough_mono C e hN) v k
        (RationalFiber.line_cut_event C pc e L hdeg v k H a hp)))
    · have hf:=line_chart_trivial C e L hdeg LaurentRay.vUnit Ω (simpleTotalTransport Ω C) N v k (H N) a ha
      intro n hn
      rw [←mutationCompletion_one Ω hΩ C coord pc _ LaurentRay.vUnit]
      exact mutationCompletion_congr_through Ω hΩ C coord pc _ LaurentRay.vUnit _ _ n N
        ((Nat.mul_le_mul_left _ hn).trans hDN) (orientPowerSeries_trivial _ _ N hf)
  · exact fun _ _=>rfl

def mutatedLineProduct (lo hi : ℝ) (N : ℕ) : PowerSeries (Torus LaurentRay.vUnit Ω) :=
  ((intervalEventList C e v k lo hi N).map (mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H)).prod
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutatedLineCompletion
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.segmentBetween_finish _root_.OAI.ElementaryPositivity.QuantumTorus.segmentBetween_start
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_1
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_4_r7588b2_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_4_r7588b2_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
lemma mutatedLineProduct_stabilizes (lo hi : ℝ) (D A N : ℕ) (hA : 1≤A)
    (hDA : (mutationSize Ω C pc+1)*D≤A) (hAN : A≤N) :
    ∀n≤D,coeff n (mutatedLineProduct Ω hΩ C coord pc e he L hdeg v k H lo hi A)=
      coeff n (mutatedLineProduct Ω hΩ C coord pc e he L hdeg v k H lo hi N) := by
  classical
  unfold mutatedLineProduct
  rw [←intervalEventList_filter C e v k lo hi hAN]
  apply PowerSeriesAdjoint.filter_product_coeff_congr
  intro a ha hp
  exact mutatedLineFactor_high Ω hΩ C coord pc e he L hdeg v k H D A hA hDA a
    (event_not_retained C e v k lo hi a ha (of_decide_eq_false hp))

def mutatedLineCompletion (lo hi : ℝ) : PowerSeries (Torus LaurentRay.vUnit Ω) :=
  PowerSeries.mk (fun d=>coeff d (mutatedLineProduct Ω hΩ C coord pc e he L hdeg v k H lo hi
    (max 1 ((mutationSize Ω C pc+1)*d))))

lemma mutatedLineCompletion_coeff (lo hi : ℝ) (d N : ℕ) (hN : 1≤N)
    (hdN : (mutationSize Ω C pc+1)*d≤N) :
    coeff d (mutatedLineCompletion Ω hΩ C coord pc e he L hdeg v k H lo hi)=
      coeff d (mutatedLineProduct Ω hΩ C coord pc e he L hdeg v k H lo hi N) := by
  simp only [mutatedLineCompletion,PowerSeries.coeff_mk]
  exact mutatedLineProduct_stabilizes Ω hΩ C coord pc e he L hdeg v k H lo hi d
    (max 1 ((mutationSize Ω C pc+1)*d)) N (le_max_left _ _) (le_max_right _ _)
    (max_le hN hdN) d le_rfl
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {A : Type*} [Ring A]
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_2
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_5_r7588b2_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_5_r7588b2_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include hcoord in
lemma mutationCompletion_orient_graded (pos b : Bool) (f : CompletedPositive LaurentRay.vUnit Ω C)
    (hf : ∀n m,coeff n f.val m≠0 → m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)) :
    SeriesGraded LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
      (mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit (orientPowerSeries b f.val)) := by
  have hg : SeriesGraded LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
      (mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit f.val):=
    mutationCompletion_graded Ω hΩ C coord hcoord pc pos LaurentRay.vUnit f hf
  cases b
  · simp only [orientPowerSeries,Bool.false_eq_true,ite_false, if_false]
    rw [mutationCompletion_inverse Ω hΩ C coord pc pos f.val
      (mutationCompletion_bound Ω hΩ C coord hcoord pc pos LaurentRay.vUnit f hf) f.property.1]
    exact hg.inverse LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
  · exact hg

variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)
lemma mutatedLineFactor_constant (a : ℝ) :
    constantCoeff (mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H a)=1 := by
  classical
  unfold mutatedLineFactor
  split
  · split
    · exact orientPowerSeries_constant _ _ (normalizedSimple_constant Ω _)
    · exact mutationCompletion_constant Ω hΩ C coord pc _ LaurentRay.vUnit _
        (orientPowerSeries_constant _ _ (chartZero _ _ _ _ _).property.1)
  · exact constantCoeff_one

include hcoord hS hcomp in
lemma mutatedLineFactor_graded (a : ℝ) :
    SeriesGraded LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
      (mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H a) := by
  classical
  unfold mutatedLineFactor
  split
  · next ha=>
    split
    · apply orientPowerSeries_graded
      rw [←simpleDatum_value Ω (mutatedRoots Ω C pc) pc]
      exact WallUnitDatum.graded Ω _ (fun _=>True) _ (simpleDatum_allowed _ pc)
    · next hp=>
      let data:=lineRayData C e he L hdeg v k H a ha
      apply mutationCompletion_orient_graded Ω hΩ C coord hcoord pc
      exact simple_fiber_bound Ω C coord hcoord pc e he S hS hcomp L hdeg
        data.root data.degree data.degree_pos data.root_degree (k+a • v) data.generic _
        (cutSide_decide ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc) hp)
  · exact SeriesGraded.one LaurentRay.vUnit Ω _

lemma mutatedLineProduct_constant (lo hi : ℝ) (N : ℕ) :
    constantCoeff (mutatedLineProduct Ω hΩ C coord pc e he L hdeg v k H lo hi N)=1 := by
  unfold mutatedLineProduct
  induction intervalEventList C e v k lo hi N with
  | nil=>simp
  | cons a l ih=>
    simp only [List.map_cons,List.prod_cons,map_mul,mutatedLineFactor_constant,one_mul,ih]

include hcoord hS hcomp in
lemma mutatedLineProduct_graded (lo hi : ℝ) (N : ℕ) :
    SeriesGraded LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
      (mutatedLineProduct Ω hΩ C coord pc e he L hdeg v k H lo hi N) := by
  unfold mutatedLineProduct
  induction intervalEventList C e v k lo hi N with
  | nil=>exact SeriesGraded.one LaurentRay.vUnit Ω _
  | cons a l ih=>
    exact (mutatedLineFactor_graded Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a).mul
      LaurentRay.vUnit Ω _ ih

lemma mutatedLineCompletion_constant (lo hi : ℝ) :
    constantCoeff (mutatedLineCompletion Ω hΩ C coord pc e he L hdeg v k H lo hi)=1 := by
  rw [←coeff_zero_eq_constantCoeff_apply,mutatedLineCompletion_coeff Ω hΩ C coord pc e he L hdeg v k H lo hi 0 1 le_rfl (by omega),
    coeff_zero_eq_constantCoeff_apply,mutatedLineProduct_constant]

include hcoord hS hcomp in
lemma mutatedLineCompletion_graded (lo hi : ℝ) :
    SeriesGraded LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
      (mutatedLineCompletion Ω hΩ C coord pc e he L hdeg v k H lo hi) := by
  intro d
  rw [mutatedLineCompletion_coeff Ω hΩ C coord pc e he L hdeg v k H lo hi d
    (max 1 ((mutationSize Ω C pc+1)*d)) (le_max_left _ _) (le_max_right _ _)]
  exact mutatedLineProduct_graded Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi _ d

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_LineOldTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)

def lineNegativeUnit (a : ℝ) := completedBiUnit LaurentRay.vUnit Ω C coord hcoord pc
  (chartNegative LaurentRay.vUnit Ω C ((k+a • v).toAddMonoidHom.comp e) (simpleTotalTransport Ω C))

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PathOldTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

def actualPathWord {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b) (N : ℕ) :
    List (ComparisonCrossing LaurentRay.vUnit Ω (nonpDegree coord pc) (pureDegree coord pc)
      (mutationSize Ω C pc+1)) :=
  match p with
  | .nil _=>[]
  | .append s p=>actualLineWord Ω C coord hcoord pc e he S hS hcomp L hdeg
      s.direction s.offset s.generic s.lo s.hi N++
      actualPathWord p N

def covectorNegativeUnit (a : Module.Dual ℝ E) := completedBiUnit LaurentRay.vUnit Ω C coord hcoord pc
  (chartNegative LaurentRay.vUnit Ω C (a.toAddMonoidHom.comp e) (simpleTotalTransport Ω C))

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CompletedPathAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section

variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

def actualPathAction {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b)
    (f : PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω))) :=
  PowerSeries.mk (fun D=>coeff D
    (comparisonWordAction LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
      (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
      (actualPathWord Ω C coord hcoord pc e he S hS hcomp L hdeg p
        (max 1 ((mutationSize Ω C pc+1)*D))) f))

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutatedPathCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_4
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_7_r7588b2_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_7_r7588b2_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
def mutatedPathProduct {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b) (N : ℕ) :
    PowerSeries (Torus LaurentRay.vUnit Ω) :=
  match p with
  | .nil _=>1
  | .append s p=>mutatedLineProduct Ω hΩ C coord pc e he L hdeg s.direction s.offset s.generic s.lo s.hi N*
      mutatedPathProduct p N

def mutatedPathCompletion {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b) :
    PowerSeries (Torus LaurentRay.vUnit Ω) :=
  match p with
  | .nil _=>1
  | .append s p=>mutatedLineCompletion Ω hΩ C coord pc e he L hdeg s.direction s.offset s.generic s.lo s.hi*
      mutatedPathCompletion p

lemma mutatedPathCompletion_constant {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b) :
    constantCoeff (mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p)=1 := by
  induction p with
  | nil=>exact constantCoeff_one
  | append s p ih=>
    simp only [mutatedPathCompletion,map_mul,mutatedLineCompletion_constant,ih,one_mul]

variable (hcoord : ∀d,coord (C d)=d)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
include hcoord hS hcomp in
lemma mutatedPathCompletion_graded {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b) :
    SeriesGraded LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
      (mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p) := by
  induction p with
  | nil=>exact SeriesGraded.one LaurentRay.vUnit Ω _
  | append s p ih=>
    exact (mutatedLineCompletion_graded Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
      s.direction s.offset s.generic s.lo s.hi).mul LaurentRay.vUnit Ω _ ih

def mutatedPathCompletedPositive {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b) :
    CompletedPositive LaurentRay.vUnit Ω (mutatedRoots Ω C pc) :=
  ⟨mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p,
    mutatedPathCompletion_constant Ω hΩ C coord pc e he L hdeg p,
    mutatedPathCompletion_graded Ω hΩ C coord pc e he L hdeg hcoord S hS hcomp p⟩
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry RationalFiber
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)

variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_5
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_8_r7588b2_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_8_r7588b2_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
def noncutOldLineFactor (a : ℝ) : PowerSeries (Torus LaurentRay.vUnit Ω) := by
  classical
  exact if ha : ∃N,a∈lineEvents (realRootsThrough e C N) v k then
    let data:=lineRayData C e he L hdeg v k H a ha
    orientPowerSeries (decide (v (e data.root)<0))
      (chartZero LaurentRay.vUnit Ω C ((k+a • v).toAddMonoidHom.comp e) (simpleTotalTransport Ω C)).val
  else 1

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_InfinityPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorusLaurentSeriesRatVUnit_6
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_6_r7588b2_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_6_r7588b2_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
lemma mutatedPathProduct_constant {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b) (N : ℕ) :
    constantCoeff (mutatedPathProduct Ω hΩ C coord pc e he L hdeg p N)=1 := by
  induction p with
  | nil=>exact constantCoeff_one
  | append s p ih=>
    simp only [mutatedPathProduct,map_mul,mutatedLineProduct_constant,ih,one_mul]

include hcoord hS hcomp in
lemma mutatedPathProduct_graded {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b) (N : ℕ) :
    SeriesGraded LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
      (mutatedPathProduct Ω hΩ C coord pc e he L hdeg p N) := by
  induction p with
  | nil=>exact SeriesGraded.one LaurentRay.vUnit Ω _
  | append s p ih=>
    exact (mutatedLineProduct_graded Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
      s.direction s.offset s.generic s.lo s.hi N).mul LaurentRay.vUnit Ω _ ih

def mutatedPathProductPositive {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b) (N : ℕ) :
    CompletedPositive LaurentRay.vUnit Ω (mutatedRoots Ω C pc) :=
  ⟨mutatedPathProduct Ω hΩ C coord pc e he L hdeg p N,
    mutatedPathProduct_constant Ω hΩ C coord pc e he L hdeg p N,
    mutatedPathProduct_graded Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p N⟩

def actualInfinityPathProductUnit {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b) (N : ℕ) :
    (PowerSeries (HahnSeries ℤ (Torus LaurentRay.vUnit Ω)))ˣ :=
  infinityCompletedUnit Ω C coord hcoord pc LaurentRay.vUnit
    (mutatedPathProductPositive Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p N)

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutatedPathIndependent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry RationalFiber
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (hnd : ∀r≠0,∃m,Ω r m≠0)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.mutatedPathIndependentRing
local instance mutatedPathIndependentAddCommMonoid_r7588b2_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance mutatedPathIndependentAddGroup_r7588b2_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
def mutatedTransport {a b : Module.Dual ℝ E}
    (HA : RegularCovector C e a) (HB : RegularCovector C e b) :
    CompletedPositive LaurentRay.vUnit Ω (mutatedRoots Ω C pc) :=
  mutatedPathCompletedPositive Ω hΩ C coord pc e he L hdeg hcoord S hS hcomp
    (Classical.choice (generic_path_exists C e a b HA HB))

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutatedNoCutTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry RationalFiber
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.mutatedNoCutTransportPathRing
local instance mutatedNoCutTransportPathAddCommMonoid_r7588b2_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance mutatedNoCutTransportPathAddGroup_r7588b2_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
def negativeCovectorUnit (a : Module.Dual ℝ E) := completedBiUnit LaurentRay.vUnit Ω C coord hcoord pc
  (chartNegative LaurentRay.vUnit Ω C (a.toAddMonoidHom.comp e) (simpleTotalTransport Ω C))

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_HalfspacePolynomialCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits FiniteRayGeometry
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)
variable (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (hnd:∀r≠0,∃m,Ω r m≠0)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.halfspacePolynomialCoefficientsRing
local instance halfspacePolynomialCoefficientsAddCommMonoid_r7588b2_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance halfspacePolynomialCoefficientsAddGroup_r7588b2_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
def rootChartRatio (a b:M →+ ℝ) : CompletedPositive LaurentRay.vUnit Ω C :=
  ⟨(chartNegative LaurentRay.vUnit Ω C b (simpleTotalTransport Ω C)).val*
      invOfUnit (chartNegative LaurentRay.vUnit Ω C a (simpleTotalTransport Ω C)).val 1,
    by simp only [map_mul,(chartNegative LaurentRay.vUnit Ω C b (simpleTotalTransport Ω C)).property.1,
      constantCoeff_invOfUnit,inv_one,Units.val_one,mul_one],
    SeriesGraded.mul LaurentRay.vUnit Ω C
      (chartNegative LaurentRay.vUnit Ω C b (simpleTotalTransport Ω C)).property.2
      (SeriesGraded.inverse LaurentRay.vUnit Ω C
        (chartNegative LaurentRay.vUnit Ω C a (simpleTotalTransport Ω C)).property.2)⟩

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end


