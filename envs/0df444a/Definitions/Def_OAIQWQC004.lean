-- Prove2me | Definitions.Def_OAIQWQC004
-- name    : OAIQWQC004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T16:08:00.64698+00:00
-- url     : https://prove2.me/theorems/26527409-3c17-4736-91d6-dce50b234e96
-- title:
--   OpenAI quadric-surface split: charts, equalizer data and patch recovery (definitions bundle 5 of 5)
-- statement:
--   The fifth definitions bundle of the split of OpenAI's proof of the counterexample to Griffiths' positivity conjecture on the quadric surface (`OAI.QuadricCounterexample.main_theorem`). It holds OpenAI's definitions from the modules listed below of `lean/OAI/Geometry/QuadricBundles` (OpenAI, *Ample rank-two bundles on the quadric surface without Griffiths-positive metrics*, OpenAI Math Release, September 24, 2026, result family 050, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. Among them:
--   - the chart scalars, lifts and branch denominators of the power pullbacks (`chartScalars`, `chartLift`, `liftPolynomial`, `branchDenominator`, `divisorPolynomial`), and the equalizer data of the source graphs (`equalizerData`);
--   - the traced quadratic form of a smooth Hermitian metric and the matrix root trace (`SmoothHermitianMetric.tracedForm`, `matrixRootTrace`, `coefficientsQuadraticCLM`);
--   - the homogeneous coordinates and the patch recovery polynomials of the projective equations (`homogeneousCoordinate`, `normalize`, `patchCoordinates`, `patchRecovery`, `recoveryPolynomial`, `patchEquations`).
--
--   It also contains the 68 lemmas those definitions use in their bodies. One of them is the plurisubharmonicity of the root trace across the branch locus (`rootTrace_psh`). That lemma uses removability of a coordinate hyperplane for continuous nonnegative plurisubharmonic functions, which this bundle does not prove again: it imports the published statement `OAI.QuadricCounterexample.first_hyperplane_removable` of this split, which must be Proved first. One proof here differs from OpenAI's text: after `convert hh using 1`, this Mathlib leaves an instance side goal that the trailing `rfl` does not close, so the step is `exact hh` (the goal is definitionally `hh`).
--
--   The definitions of the published statement come from the published bundle `Def_QuadricBundles`. The bundle also imports the definitions bundles `OAIQWQC002` and `OAIQWQC003`.
--
--   Modules: `Charts.lean`, `Curvature.lean`, `DualForms.lean`, `Embedding.lean`, `Graphs.lean`, `MatrixDynamics.lean`, `ProjectiveEquations.lean`, `RootTrace.lean`, `TraceMetrics.lean`, `WeakLimits.lean`.
-- source:
--   OpenAI, Ample rank-two bundles on the quadric surface without Griffiths-positive metrics, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 050; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/ample-rank-two-bundles-on-the-quadric-surface-without-griffiths-positive-metrics-September-24-2026/paper.pdf, Sections 2–5; Apache License 2.0); definitions carved from lean/OAI/Geometry/QuadricBundles at commit adc7f12

import Mathlib
import Definitions.Def_QuadricBundles
import Definitions.Def_OAIQWQC002
import Definitions.Def_OAIQWQC003
import Theorems.Thm_OAI_QuadricCounterexample_first_hyperplane_removable

section
-- module Solutions.OAIQW_QuadricCounterexample.Charts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuadricCounterexample
open Set Filter Topology Metric OnePoint
noncomputable section
open scoped Matrix.Norms.Elementwise ComplexOrder

lemma reciprocalP1_coe_continuousAt_zero :
    ContinuousAt (fun z : ℂ ↦ reciprocalP1 z) 0 := by
  rw [continuousAt_iff_punctured_nhds, reciprocalP1_zero]
  have he : (fun z : ℂ ↦ reciprocalP1 z) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z : ℂ ↦ ((z⁻¹ : ℂ) : ProjectiveLine)) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact reciprocalP1_coe hz
  apply Tendsto.congr' he.symm
  have ht : Tendsto Inv.inv (𝓝[≠] (0 : ℂ)) (coclosedCompact ℂ) := by
    simpa only [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] using
      (tendsto_inv₀_nhdsNE_zero (α := ℂ))
  exact (show Tendsto ((↑) : ℂ → ProjectiveLine) (coclosedCompact ℂ) (𝓝 ∞) from
    (by rw [← OnePoint.comap_coe_nhds_infty]; exact tendsto_comap)).comp ht

lemma continuous_reciprocalP1 : Continuous reciprocalP1 := by
  rw [OnePoint.continuous_iff]
  constructor
  · have he : (fun z : ℂ ↦ reciprocalP1 z) =ᶠ[coclosedCompact ℂ]
        (fun z : ℂ ↦ ((z⁻¹ : ℂ) : ProjectiveLine)) := by
      have hn : ∀ᶠ z : ℂ in coclosedCompact ℂ, z ≠ 0 := by
        rw [coclosedCompact_eq_cocompact]
        exact isCompact_singleton.compl_mem_cocompact
      filter_upwards [hn] with z hz
      exact reciprocalP1_coe hz
    apply Tendsto.congr' he.symm
    apply OnePoint.continuous_coe.continuousAt.tendsto.comp
    simpa only [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] using
      (tendsto_inv₀_cobounded (α := ℂ))
  · apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hz : z = 0
    · subst z; exact reciprocalP1_coe_continuousAt_zero
    · have he : (fun w : ℂ ↦ reciprocalP1 w) =ᶠ[𝓝 z]
          (fun w : ℂ ↦ ((w⁻¹ : ℂ) : ProjectiveLine)) := by
        filter_upwards [eventually_ne_nhds hz] with w hw
        exact reciprocalP1_coe hw
      exact (OnePoint.continuous_coe.continuousAt.comp
        (continuousAt_id.inv₀ hz)).congr_of_eventuallyEq he

def reciprocalP1Homeomorph : ProjectiveLine ≃ₜ ProjectiveLine where
  toFun := reciprocalP1
  invFun := reciprocalP1
  left_inv := reciprocalP1_involutive
  right_inv := reciprocalP1_involutive
  continuous_toFun := continuous_reciprocalP1
  continuous_invFun := continuous_reciprocalP1

end
end QuadricCounterexample

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.Graphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

namespace QuadricCounterexample
open Polynomial
noncomputable section

namespace GraphScalars
variable (T : GraphScalars)

lemma P_product_dvd : T.P₁*T.P₂ ∣ T.L^24-1 := by
  refine ⟨C (T.c^2)*(T.Nquotient.comp T.L),?_⟩
  have h := congrArg (fun p : ℂ[X] ↦ p.comp T.L) T.Nquotient_spec
  simp only [sub_comp,pow_comp,X_comp,one_comp,mul_comp,T.N₁_comp_L,T.N₂_comp_L] at h
  rw [h,map_pow]
  ring

lemma P₁_dvd_mixed : T.P₁ ∣ T.J^24-X^24 := by
  have hd : T.P₁ ∣ T.L^24-1 := dvd_mul_right _ _ |>.trans T.P_product_dvd
  have hJ : T.P₁ ∣ T.J-(-X*T.L) := by
    refine ⟨-1,?_⟩
    linear_combination T.J_mod_P₁
  have hp := hJ.trans (sub_dvd_pow_sub_pow T.J (-X*T.L) 24)
  have hm := dvd_mul_of_dvd_right hd (X^24)
  convert dvd_add hp hm using 1; ring

lemma P₂_dvd_mixed : T.P₂ ∣ T.J^24-X^24 := by
  have hd : T.P₂ ∣ T.L^24-1 := dvd_mul_left _ _ |>.trans T.P_product_dvd
  have hJ : T.P₂ ∣ C (T.a^2)*T.J-(-X*T.L) := by
    refine ⟨-1,?_⟩
    linear_combination T.J_mod_P₂
  have hp := hJ.trans (sub_dvd_pow_sub_pow (C (T.a^2)*T.J) (-X*T.L) 24)
  have hm := dvd_mul_of_dvd_right hd (X^24)
  have ha : (C (T.a^2) : ℂ[X])^24=1 := by
    rw [← map_pow,← pow_mul,mul_comm 2 24,pow_mul,T.a_twentyfour,one_pow,map_one]
  rw [mul_pow,ha,one_mul] at hp
  convert dvd_add hp hm using 1; ring

lemma exists_graph_quotients : ∃ R R' : ℂ[X],
    T.L^24-1=T.P₁*T.P₂*R ∧ T.J^24-X^24=T.P₁*T.P₂*R' := by
  obtain ⟨R,hR⟩ := T.P_product_dvd
  obtain ⟨R',hR'⟩ := T.P_coprime.mul_dvd T.P₁_dvd_mixed T.P₂_dvd_mixed
  exact ⟨R,R',hR,hR'⟩

def sameQuotient : ℂ[X] := T.exists_graph_quotients.choose
def mixedQuotient : ℂ[X] := T.exists_graph_quotients.choose_spec.choose
lemma sameQuotient_spec : T.L^24-1=T.P₁*T.P₂*T.sameQuotient :=
  T.exists_graph_quotients.choose_spec.choose_spec.1
lemma mixedQuotient_spec : T.J^24-X^24=T.P₁*T.P₂*T.mixedQuotient :=
  T.exists_graph_quotients.choose_spec.choose_spec.2

def liftBeta (mixed : Bool) (x y : ℂ) : ℂ :=
  (if mixed then y^24 else 1)+graphOne mixed x y*T.graphTwo mixed x y*
    ((T.betaPolynomial mixed).eval y)^2*
    ((if mixed then T.mixedQuotient else T.sameQuotient).eval y)

lemma liftBeta_one {mixed : Bool} {x y : ℂ} (h : graphOne mixed x y=0) :
    T.liftBeta mixed x y = if mixed then y^24 else 1 := by
  simp [liftBeta,h]
lemma liftBeta_two {mixed : Bool} {x y : ℂ} (h : T.graphTwo mixed x y=0) :
    T.liftBeta mixed x y = if mixed then y^24 else 1 := by
  simp [liftBeta,h]

lemma eval_P₁_same {x y : ℂ} (h : T.graphThree false x y=0) :
    T.P₁.eval y = -graphOne false x y*T.L.eval y := by
  simp only [graphThree,Bool.false_eq_true,↓reduceIte] at h
  simp only [P₁,L,eval_sub,eval_add,eval_mul,eval_C,eval_X,eval_pow,graphOne,
    Bool.false_eq_true,↓reduceIte]
  linear_combination h

lemma eval_P₂_same {x y : ℂ} (h : T.graphThree false x y=0) :
    T.P₂.eval y = -T.graphTwo false x y*T.L.eval y := by
  simp only [graphThree,Bool.false_eq_true,↓reduceIte] at h
  simp only [P₂,L,eval_sub,eval_add,eval_mul,eval_C,eval_X,eval_pow,graphTwo,
    Bool.false_eq_true,↓reduceIte]
  linear_combination T.a^2*h

lemma eval_P₁_mixed {x y : ℂ} (h : T.graphThree true x y=0) :
    T.P₁.eval y = graphOne true x y*T.J.eval y := by
  simp only [graphThree,↓reduceIte] at h
  simp only [P₁,J,eval_sub,eval_add,eval_mul,eval_C,eval_X,eval_pow,graphOne,↓reduceIte]
  linear_combination y*h

lemma eval_P₂_mixed {x y : ℂ} (h : T.graphThree true x y=0) :
    T.P₂.eval y = T.graphTwo true x y*T.J.eval y := by
  simp only [graphThree,↓reduceIte] at h
  simp only [P₂,J,eval_sub,eval_add,eval_mul,eval_C,eval_X,eval_pow,graphTwo,↓reduceIte]
  linear_combination y*h

lemma liftBeta_three {mixed : Bool} {x y : ℂ} (h : T.graphThree mixed x y=0) :
    T.liftBeta mixed x y=((T.betaPolynomial mixed).eval y)^24 := by
  cases mixed
  · have he := congrArg (Polynomial.eval y) T.sameQuotient_spec
    simp only [eval_sub,eval_pow,eval_one,eval_mul,T.eval_P₁_same h,T.eval_P₂_same h] at he
    simp only [liftBeta,betaPolynomial,Bool.false_eq_true,↓reduceIte]
    linear_combination -he
  · have he := congrArg (Polynomial.eval y) T.mixedQuotient_spec
    simp only [eval_sub,eval_pow,eval_X,eval_mul,T.eval_P₁_mixed h,T.eval_P₂_mixed h] at he
    simp only [liftBeta,betaPolynomial,↓reduceIte]
    linear_combination -he

end GraphScalars
end
end QuadricCounterexample

namespace QuadricCounterexample
open MvPolynomial
noncomputable section

namespace GraphScalars
variable (T : GraphScalars)

lemma graphProduct_squarefree (mixed : Bool) : Squarefree (G1 mixed*T.G2 mixed*T.G3 mixed) := by
  apply squarefree_mul_iff.mpr
  refine ⟨?_,squarefree_mul_iff.mpr ⟨T.G1_G2_relPrime mixed,
    (G1_irreducible mixed).squarefree,(T.G2_irreducible mixed).squarefree⟩,
    (T.G3_irreducible mixed).squarefree⟩
  exact (T.G1_G3_relPrime mixed).mul_left (T.G2_G3_relPrime mixed)

end GraphScalars
end
end QuadricCounterexample

namespace QuadricCounterexample
open Matrix MvPolynomial
noncomputable section

lemma affineRepresentative_change (i j : Fin 2) {z : ℂ} (h : i=j ∨ z ≠ 0) :
    affineRepresentative i z = scalarFactor i j z •
      affineRepresentative j (scalarCoordinateChange i j z) := by
  rcases h with rfl | hz
  · simp [scalarFactor,scalarCoordinateChange]
  · fin_cases i <;> fin_cases j <;> ext k <;> fin_cases k <;>
      simp [affineRepresentative,scalarFactor,scalarCoordinateChange,hz]

lemma matrixGraphValue_change (M : TwoMatrix) (i j : StandardChart) (z : BaseCoordinates)
    (hz : z ∈ coordinateOverlap i j) :
    matrixGraphValue M i z=firstFactor i j z*secondFactor i j z*
      matrixGraphValue M j (coordinateChange i j z) := by
  have hi := ((coordinateOverlap_iff i j z).mp hz).1
  have hj := ((coordinateOverlap_iff i j z).mp hz).2
  have hx := affineRepresentative_change i.1 j.1 hi
  have hy := affineRepresentative_change i.2 j.2 hj
  unfold matrixGraphValue
  rw [hx,hy]
  simp only [Pi.smul_apply,smul_eq_mul,firstFactor,secondFactor,coordinateChange]
  ring

def matrixBranchDenominator (M : TwoMatrix) (i : StandardChart) (z : BaseCoordinates) : ℂ :=
  M i.2 0*affineRepresentative i.1 z.1 0+M i.2 1*affineRepresentative i.1 z.1 1

lemma matrixGraphValue_zero_iff (M : TwoMatrix) (i : StandardChart) (z : BaseCoordinates) :
    matrixGraphValue M i z=0 ↔ M *ᵥ affineRepresentative i.1 z.1=
      matrixBranchDenominator M i z • affineRepresentative i.2 z.2 := by
  constructor
  · intro h
    ext k
    fin_cases k <;> rcases i with ⟨i,j⟩ <;> fin_cases j <;>
      simp only [matrixGraphValue,affineRepresentative,↓reduceIte,Fin.isValue,Fin.zero_eta,
        Fin.mk_one,one_ne_zero,mulVec,Fin.sum_univ_two,dotProduct,
        Pi.smul_apply,smul_eq_mul,Matrix.cons_val_zero,Matrix.cons_val_one,
        one_mul,matrixBranchDenominator,mul_one] at h ⊢ <;> first | linear_combination h | linear_combination -h
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [mulVec,Fin.sum_univ_two,dotProduct,Pi.smul_apply,smul_eq_mul] at h0 h1
    dsimp only [matrixGraphValue]
    rw [h0,h1]
    ring

lemma matrixBranchDenominator_change (M : TwoMatrix) (i j : StandardChart)
    (z : BaseCoordinates) (hz : z ∈ coordinateOverlap i j) (h : matrixGraphValue M i z=0) :
    matrixBranchDenominator M i z*secondFactor i j z=
      firstFactor i j z*matrixBranchDenominator M j (coordinateChange i j z) := by
  have hv := (matrixGraphValue_zero_iff M i z).mp h
  have hx := affineRepresentative_change i.1 j.1 (((coordinateOverlap_iff i j z).mp hz).1)
  have hy := affineRepresentative_change i.2 j.2 (((coordinateOverlap_iff i j z).mp hz).2)
  rw [hx,hy,mulVec_smul] at hv
  have hj := congrFun hv j.2
  simp only [Pi.smul_apply,smul_eq_mul,affineRepresentative_index,mul_one,
    mulVec,dotProduct,Fin.sum_univ_two] at hj
  exact hj.symm

namespace GraphScalars
variable (T : GraphScalars)

def chartScalars (i : StandardChart) : GraphScalars := if i.2=0 then T.swapped else T

def mixedChart (i : StandardChart) : Bool := decide (i.1 ≠ i.2)

def chartProduct (i : StandardChart) : BasePolynomial :=
  G1 (mixedChart i)*(T.chartScalars i).G2 (mixedChart i)*(T.chartScalars i).G3 (mixedChart i)

def divisorPolynomial (i : StandardChart) : BasePolynomial :=
  matrixGraphPolynomial (T.matrices 0) i*matrixGraphPolynomial (T.matrices 1) i*
    matrixGraphPolynomial (T.matrices 2) i

def chartUnit (i : StandardChart) : ℂ := if i.2=0 then -T.a else T.a⁻¹

lemma chartUnit_ne_zero (i : StandardChart) : T.chartUnit i ≠ 0 := by
  unfold chartUnit
  split_ifs <;> simpa using T.a_ne_zero

lemma divisorPolynomial_eq (i : StandardChart) :
    T.divisorPolynomial i=C (T.chartUnit i)*T.chartProduct i := by
  apply MvPolynomial.funext
  intro z
  have hz : z=![z 0,z 1] := by ext k; fin_cases k <;> rfl
  rw [hz]
  rcases i with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [divisorPolynomial,matrixGraphPolynomial,affineRepresentative,matrices,
      chartUnit,chartProduct,chartScalars,mixedChart,swapped,G1,G2,G3] <;>
    field_simp [T.a_ne_zero] <;> ring

lemma divisorPolynomial_reduced (i : StandardChart) : Squarefree (T.divisorPolynomial i) := by
  have hu : IsUnit (C (T.chartUnit i) : BasePolynomial) :=
    (isUnit_iff_ne_zero.mpr (T.chartUnit_ne_zero i)).map C
  rw [T.divisorPolynomial_eq]
  apply Squarefree.squarefree_of_dvd ?_ ((T.chartScalars i).graphProduct_squarefree (mixedChart i))
  change C (T.chartUnit i)*T.chartProduct i ∣ T.chartProduct i
  exact hu.mul_left_dvd.mpr (dvd_refl _)

lemma divisorPolynomial_nonzero (i : StandardChart) : T.divisorPolynomial i ≠ 0 :=
  (T.divisorPolynomial_reduced i).ne_zero

lemma divisorPolynomial_change (i j : StandardChart) (z : BaseCoordinates)
    (hz : z ∈ coordinateOverlap i j) :
    baseEval (T.divisorPolynomial i) z = (firstFactor i j z*secondFactor i j z)^3*
      baseEval (T.divisorPolynomial j) (coordinateChange i j z) := by
  simp only [divisorPolynomial,baseEval_mul,baseEval_matrixGraphPolynomial]
  rw [matrixGraphValue_change _ i j z hz,matrixGraphValue_change (T.matrices 1) i j z hz,
    matrixGraphValue_change (T.matrices 2) i j z hz]
  ring

end GraphScalars
end
end QuadricCounterexample

namespace QuadricCounterexample
open Matrix MvPolynomial
noncomputable section
namespace GraphScalars
variable (T : GraphScalars)

def branchDenominator (k : Fin 3) (mixed : Bool) (x : ℂ) : ℂ :=
  ![if mixed then x else 1,
    if mixed then T.a⁻¹*x else T.a⁻¹,
    if mixed then (1-T.s)*x+T.c else T.c*x+1-T.s] k

lemma liftBeta_branch_one (mixed : Bool) (x y : ℂ)
    (h : graphOne mixed x y=0) :
    T.liftBeta mixed x y*(T.branchDenominator 0 mixed x)^24=1 := by
  rw [T.liftBeta_one h]
  cases mixed
  · simp [branchDenominator]
  · have he : x*y=1 := sub_eq_zero.mp h
    change y^24*x^24=1
    rw [← mul_pow,mul_comm y x,he,one_pow]

lemma liftBeta_branch_two (mixed : Bool) (x y : ℂ)
    (h : T.graphTwo mixed x y=0) :
    T.liftBeta mixed x y*(T.branchDenominator 1 mixed x)^24=1 := by
  rw [T.liftBeta_two h]
  cases mixed
  · simp [branchDenominator,inv_pow,T.a_twentyfour]
  · have he : x*y=T.a^2 := sub_eq_zero.mp h
    change y^24*(T.a⁻¹*x)^24=1
    calc
      y^24*(T.a⁻¹*x)^24 = (T.a⁻¹)^24*(x*y)^24 := by ring
      _ = 1 := by
        rw [he,inv_pow,← pow_mul,mul_comm 2 24,pow_mul,T.a_twentyfour]
        norm_num

lemma liftBeta_branch_three (mixed : Bool) (x y : ℂ)
    (h : T.graphThree mixed x y=0) :
    T.liftBeta mixed x y*(T.branchDenominator 2 mixed x)^24=1 := by
  rw [T.liftBeta_three h,← mul_pow]
  cases mixed
  · have he : T.L.eval y*(T.c*x+1-T.s)=1 := by
      simp only [graphThree,Bool.false_eq_true,↓reduceIte] at h
      simp only [L,Polynomial.eval_sub,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X]
      linear_combination -T.c*h+T.determinant
    change (T.L.eval y*(T.c*x+1-T.s))^24=1
    rw [he,one_pow]
  · have he : T.J.eval y*((1-T.s)*x+T.c)= -1 := by
      simp only [graphThree,↓reduceIte] at h
      simp only [J,Polynomial.eval_sub,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X]
      linear_combination -(1-T.s)*h-T.determinant
    change (T.J.eval y*((1-T.s)*x+T.c))^24=1
    rw [he]
    norm_num

lemma liftBeta_branch (k : Fin 3) (mixed : Bool) (x y : ℂ)
    (h : T.branchGraph k mixed x y=0) :
    T.liftBeta mixed x y*(T.branchDenominator k mixed x)^24=1 := by
  fin_cases k
  · exact T.liftBeta_branch_one mixed x y h
  · exact T.liftBeta_branch_two mixed x y h
  · exact T.liftBeta_branch_three mixed x y h

def liftPolynomial (mixed : Bool) : BasePolynomial :=
  (if mixed then X 1^24 else 1)+G1 mixed*T.G2 mixed*
    (Polynomial.aeval (X 1) (T.betaPolynomial mixed))^2*
    (Polynomial.aeval (X 1) (if mixed then T.mixedQuotient else T.sameQuotient))

lemma eval_aeval_snd (p : Polynomial ℂ) (z : BaseCoordinates) :
    baseEval (Polynomial.aeval (X 1 : BasePolynomial) p) z=p.eval z.2 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,baseEval,Polynomial.eval_add] at hp hq ⊢; rw [hp,hq]
  | monomial n a => simp [Polynomial.aeval_monomial,baseEval]

lemma eval_liftPolynomial (mixed : Bool) (z : BaseCoordinates) :
    baseEval (T.liftPolynomial mixed) z=T.liftBeta mixed z.1 z.2 := by
  cases mixed <;>
    simp only [liftPolynomial,liftBeta,Bool.false_eq_true,↓reduceIte,baseEval_add,baseEval_mul,
      baseEval_pow,eval_aeval_snd] <;> simp [baseEval]

def chartLift (i : StandardChart) : BasePolynomial :=
  (T.chartScalars i).liftPolynomial (mixedChart i)

lemma eval_chartLift (i : StandardChart) (z : BaseCoordinates) :
    baseEval (T.chartLift i) z=(T.chartScalars i).liftBeta (mixedChart i) z.1 z.2 :=
  (T.chartScalars i).eval_liftPolynomial _ _

lemma matrixGraphValue_eq_branch (k : Fin 3) (i : StandardChart) (z : BaseCoordinates) :
    matrixGraphValue (T.matrices k) i z =
      (if i.2=0 then -1 else 1)*
      (if k=1 then (T.chartScalars i).a⁻¹ else 1)*
      (T.chartScalars i).branchGraph k (mixedChart i) z.1 z.2 := by
  rcases i with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [matrixGraphValue,affineRepresentative,matrices,chartScalars,swapped,
      mixedChart,branchGraph,graphOne,graphTwo,graphThree] <;>
    field_simp [T.a_ne_zero] <;> first | (solve | ring) | (left; ring)

lemma matrixBranchDenominator_eq (k : Fin 3) (i : StandardChart) (z : BaseCoordinates) :
    matrixBranchDenominator (T.matrices k) i z=
      (T.chartScalars i).branchDenominator k (mixedChart i) z.1 := by
  rcases i with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [matrixBranchDenominator,affineRepresentative,matrices,chartScalars,
      swapped,mixedChart,branchDenominator] <;> ring

lemma chartLift_branch (k : Fin 3) (i : StandardChart) (z : BaseCoordinates)
    (h : matrixGraphValue (T.matrices k) i z=0) :
    baseEval (T.chartLift i) z*(matrixBranchDenominator (T.matrices k) i z)^24=1 := by
  rw [T.matrixGraphValue_eq_branch] at h
  have hn : (if i.2=0 then (-1 : ℂ) else 1)≠0 := by split_ifs <;> norm_num
  have hn' : (if k=1 then (T.chartScalars i).a⁻¹ else 1)≠0 := by
    split_ifs
    · exact inv_ne_zero (T.chartScalars i).a_ne_zero
    · exact one_ne_zero
  have hh := (mul_eq_zero.mp h).resolve_left (mul_ne_zero hn hn')
  rw [T.eval_chartLift,T.matrixBranchDenominator_eq]
  exact (T.chartScalars i).liftBeta_branch _ _ _ _ hh

lemma divisor_zero_branch (i : StandardChart) (z : BaseCoordinates)
    (h : baseEval (T.divisorPolynomial i) z=0) :
    ∃ k : Fin 3, matrixGraphValue (T.matrices k) i z=0 := by
  simp only [divisorPolynomial,baseEval_mul,baseEval_matrixGraphPolynomial,mul_eq_zero] at h
  rcases h with (h|h)|h
  · exact ⟨0,h⟩
  · exact ⟨1,h⟩
  · exact ⟨2,h⟩

lemma chartLift_unit (i : StandardChart) (z : BaseCoordinates)
    (h : baseEval (T.divisorPolynomial i) z=0) : baseEval (T.chartLift i) z ≠ 0 := by
  obtain ⟨k,hk⟩ := T.divisor_zero_branch i z h
  exact left_ne_zero_of_mul_eq_one (T.chartLift_branch k i z hk)

lemma chartLift_change (i j : StandardChart) (z : BaseCoordinates)
    (hz : z ∈ coordinateOverlap i j) (h : baseEval (T.divisorPolynomial i) z=0) :
    secondFactor i j z^24*baseEval (T.chartLift j) (coordinateChange i j z)=
      baseEval (T.chartLift i) z*firstFactor i j z^24 := by
  obtain ⟨k,hk⟩ := T.divisor_zero_branch i z h
  have hg := matrixGraphValue_change (T.matrices k) i j z hz
  have hs := firstFactor_ne_zero hz
  have ht := secondFactor_ne_zero hz
  have hkj : matrixGraphValue (T.matrices k) j (coordinateChange i j z)=0 := by
    rw [hk] at hg
    exact (mul_eq_zero.mp hg.symm).resolve_left (mul_ne_zero hs ht)
  have hi := T.chartLift_branch k i z hk
  have hj := T.chartLift_branch k j (coordinateChange i j z) hkj
  have hd := matrixBranchDenominator_change (T.matrices k) i j z hz hk
  have hd' : matrixBranchDenominator (T.matrices k) i z ≠ 0 := by
    exact fun he ↦ by simp [he] at hi
  have hdp := congrArg (fun a : ℂ ↦ a^24) hd
  simp only [mul_pow] at hdp
  apply mul_right_cancel₀ (pow_ne_zero 24 hd')
  calc
    _ = baseEval (T.chartLift j) (coordinateChange i j z)*
        (matrixBranchDenominator (T.matrices k) i z^24*secondFactor i j z^24) := by ring
    _ = firstFactor i j z^24 := by rw [hdp]; linear_combination firstFactor i j z^24*hj
    _ = _ := by linear_combination -firstFactor i j z^24*hi

def equalizerData : EqualizerData where
  divisor := T.divisorPolynomial
  lift := T.chartLift
  reduced := T.divisorPolynomial_reduced
  nonzero := T.divisorPolynomial_nonzero
  divisor_change := T.divisorPolynomial_change
  lift_change := T.chartLift_change
  lift_unit := T.chartLift_unit

end GraphScalars

end
end QuadricCounterexample

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.Curvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29

namespace QuadricCounterexample
open Set Filter Topology
open scoped Matrix.Norms.Elementwise
noncomputable section

lemma hessian_pullback_clm {X : Type u12} {Y : Type u13} {Z : Type u14}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : Y → Z} (L : X →L[ℝ] Y) {x : X} (hf : ContDiffAt ℝ 2 f (L x)) (v w : X) :
    fderiv ℝ (fderiv ℝ (fun y ↦ f (L y))) x v w =
      fderiv ℝ (fderiv ℝ f) (L x) (L v) (L w) := by
  change fderiv ℝ (fderiv ℝ (f ∘ L)) x v w = _
  rw [hessian_comp_apply L.contDiff.contDiffAt hf]
  have he : fderiv ℝ L = fun _ ↦ L := funext fun y ↦ L.fderiv
  simp [he]

section Quadratic
variable {X : Type u18} {ι : Type u19} [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype ι]

lemma base_entry_hessian {H : X → Matrix ι ι ℂ} {z : X}
    (hH : ContDiffAt ℝ 2 H z) (v : ι → ℂ) (i j : ι) (u : X) (w : ι → ℂ) :
    fderiv ℝ (fderiv ℝ (fun p : X × (ι → ℂ) ↦ H p.1 i j)) (z,v) (u,w) (u,w) =
      fderiv ℝ (fderiv ℝ H) z u u i j := by
  have he := hessian_pullback_clm (f := fun y ↦ H y i j)
    (x := (z,v)) (ContinuousLinearMap.fst ℝ X (ι → ℂ))
    ((entryCLM i j).contDiff.contDiffAt.comp z hH) (u,w) (u,w)
  have hh := hessian_clm hH (entryCLM i j) u u
  exact he.trans hh

lemma complexQuadratic_hessian {H : X → Matrix ι ι ℂ} {z : X}
    (hH : ContDiffAt ℝ 2 H z) (v : ι → ℂ) (u : X) (w : ι → ℂ) :
    fderiv ℝ (fderiv ℝ (complexQuadratic H)) (z,v) (u,w) (u,w) =
      star v ⬝ᵥ ((fderiv ℝ (fderiv ℝ H) z u u).mulVec v) +
      2 * (star w ⬝ᵥ ((fderiv ℝ H z u).mulVec v)) +
      2 * (star v ⬝ᵥ ((fderiv ℝ H z u).mulVec w)) +
      2 * (star w ⬝ᵥ ((H z).mulVec w)) := by
  have ht i j : ContDiffAt ℝ 2
      (fun p : X × (ι → ℂ) ↦ star (p.2 i)*H p.1 i j*p.2 j) (z,v) :=
    ((starFiberEntryCLM i).contDiff.contDiffAt.mul
      (base_entry_C2 hH v i j)).mul (fiberEntryCLM j).contDiff.contDiffAt
  have hh (i j : ι) := hessian_linear_mul_linear (base_entry_C2 hH v i j)
    (starFiberEntryCLM i) (fiberEntryCLM j) (u,w)
  simp only [base_entry_hessian hH,base_entry_fderiv hH] at hh
  rw [complexQuadratic_eq_sum,hessian_sum (fun i _ ↦ ContDiffAt.sum (fun j _ ↦ ht i j))]
  simp_rw [hessian_sum (fun j _ ↦ ht _ j)]
  change (∑ i, ∑ j, _) = _
  calc
    _ = ∑ i, ∑ j,
      (star (v i)*(fderiv ℝ (fderiv ℝ H) z u u i j)*v j +
      2*star (w i)*(fderiv ℝ H z u i j)*v j +
      2*star (v i)*(fderiv ℝ H z u i j)*w j + 2*star (w i)*H z i j*w j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact hh i j
    _ = _ := by
      simp only [dotProduct,Matrix.mulVec,Pi.star_apply,Finset.sum_add_distrib,
        Finset.mul_sum,mul_assoc]

end Quadratic

end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ComplexOrder
noncomputable section
variable {X : Type u28} {ι : Type u29} [NormedAddCommGroup X] [NormedSpace ℂ X] [Fintype ι]

lemma hermitianQuadratic_levi {H : X → Matrix ι ι ℂ} {z : X}
    (hH : ContDiffAt ℝ 2 H z) (hh : ∀ᶠ y in 𝓝 z, (H y).IsHermitian)
    (v : ι → ℂ) (u : X) (w : ι → ℂ) :
    leviTrace (hermitianQuadratic H) (z,v) (u,w) =
      4 * (star v ⬝ᵥ (mixedHessian H z u).mulVec v +
        star w ⬝ᵥ (wirtingerDerivative H z u).mulVec v +
        star v ⬝ᵥ (wirtingerDerivative H z u).conjTranspose.mulVec w +
        star w ⬝ᵥ (H z).mulVec w).re := by
  have hd := hH.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have ha := quadratic_levi_expansion (H z) (fderiv ℝ H z u)
    (fderiv ℝ H z (Complex.I • u)) (fderiv ℝ (fderiv ℝ H) z u u)
    (fderiv ℝ (fderiv ℝ H) z (Complex.I • u) (Complex.I • u))
    (hermitian_fderiv hd hh u) (hermitian_fderiv hd hh (Complex.I • u)) v w
  unfold leviTrace hermitianQuadratic
  rw [hessian_re (complexQuadratic_C2 hH v),hessian_re (complexQuadratic_C2 hH v)]
  change (fderiv ℝ (fderiv ℝ (complexQuadratic H)) (z,v) (u,w) (u,w)).re +
    (fderiv ℝ (fderiv ℝ (complexQuadratic H)) (z,v)
      (Complex.I • u,Complex.I • w) (Complex.I • u,Complex.I • w)).re = _
  rw [← Complex.add_re,complexQuadratic_hessian hH,complexQuadratic_hessian hH,ha]
  norm_num [Complex.mul_re,wirtingerDerivative,mixedHessian]

lemma hermitianQuadratic_levi_nonneg [DecidableEq ι]
    {H : X → Matrix ι ι ℂ} {z : X} (hH : ContDiffAt ℝ 2 H z)
    (hh : ∀ᶠ y in 𝓝 z, (H y).IsHermitian) (hpos : (H z).PosDef)
    (hcurv : ∀ u : X, (mixedHessian H z u -
      (wirtingerDerivative H z u).conjTranspose*(H z)⁻¹*wirtingerDerivative H z u).PosSemidef)
    (v : ι → ℂ) (u : X) (w : ι → ℂ) :
    0 ≤ leviTrace (hermitianQuadratic H) (z,v) (u,w) := by
  rw [hermitianQuadratic_levi hH hh]
  exact mul_nonneg (by norm_num) (matrix_completed_square_nonneg hpos (hcurv u) v w)

theorem chern_positive_dual_norm_psh [DecidableEq ι] [CompleteSpace X]
    {Ω : Set X} (hΩ : IsOpen Ω) {H : X → Matrix ι ι ℂ}
    (hH : ContDiffOn ℝ 2 H Ω) (hpos : ∀ z∈Ω, (H z).PosDef)
    (hcurv : ∀ z∈Ω, ∀ u : X, u ≠ 0 → (mixedHessian H z u -
      (wirtingerDerivative H z u).conjTranspose*(H z)⁻¹*wirtingerDerivative H z u).PosDef) :
    DiskPshOn (Ω ×ˢ Set.univ) (hermitianQuadratic H) := by
  apply DiskPshOn.of_C2_leviTrace_nonneg (hΩ.prod isOpen_univ)
  · intro p hp
    exact (hermitianQuadratic_C2 (hH.contDiffAt (hΩ.mem_nhds hp.1)) p.2).contDiffWithinAt
  · rintro ⟨z,v⟩ hz ⟨u,w⟩
    apply hermitianQuadratic_levi_nonneg (hH.contDiffAt (hΩ.mem_nhds hz.1)) _ (hpos z hz.1)
      (curvature_nonneg_of_strict (hcurv z hz.1))
    filter_upwards [hΩ.mem_nhds hz.1] with y hy
    exact (hpos y hy).isHermitian

end
end QuadricCounterexample

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.RootTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric Complex BigOperators
noncomputable section

variable (m : ℕ) [NeZero m]

attribute [local instance] OAI.QuadricCounterexample.instFintypeSubtypeUnitsComplexMemSubgroupRootsOfUnity_solutions_1
variable {V : Type u13} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [LocallyCompactSpace V]

omit [LocallyCompactSpace V] in

theorem rootTrace_psh_off_zero {U : Set (ℂ × V)} (hU : IsOpen U)
    {F : ℂ × V → ℝ}
    (hF : ContinuousOn F ((fun p : ℂ × V ↦ (p.1^m,p.2)) ⁻¹' U))
    (hp : DiskPshOn ((fun p : ℂ × V ↦ (p.1^m,p.2)) ⁻¹' U) F) :
    DiskPshOn (U ∩ {p | p.1 ≠ 0}) (rootTrace m F) := by
  let π : ℂ × V → ℂ × V := fun p ↦ (p.1^m,p.2)
  have hc := continuousOn_rootTrace m hU hF
  apply DiskPshOn.of_locally (hc.mono inter_subset_left)
  intro x hx
  let W : Set (ℂ × V) := U ∩ {p | p.1/x.1 ∈ Complex.slitPlane}
  have hW : IsOpen W := hU.inter (Complex.isOpen_slitPlane.preimage (by fun_prop))
  have hxW : x ∈ W := by
    refine ⟨hx.1, ?_⟩
    change x.1 / x.1 ∈ Complex.slitPlane
    simpa only [div_self hx.2] using Complex.one_mem_slitPlane
  refine ⟨W, hW, hxW, ?_⟩
  let R : rootsOfUnity m ℂ → (ℂ × V) → (ℂ × V) :=
    fun ζ p ↦ ((ζ.val : ℂ) * centeredRoot m x.1 p.1,p.2)
  have hRd (ζ : rootsOfUnity m ℂ) : DifferentiableOn ℂ (R ζ) W := by
    apply DifferentiableOn.prodMk
    · apply DifferentiableOn.const_mul
      exact (centeredRoot_differentiableOn m).comp differentiableOn_fst (fun p hp ↦ hp.2)
    · exact differentiableOn_snd
  have hRm (ζ : rootsOfUnity m ℂ) : MapsTo (R ζ) W (π ⁻¹' U) := by
    intro p hp
    change (((ζ.val : ℂ) * centeredRoot m x.1 p.1)^m,p.2) ∈ U
    rw [mul_pow, (mem_rootsOfUnity' m ζ.val).mp ζ.property, one_mul,
      centeredRoot_pow m hx.2]
    exact hp.1
  have hsum := DiskPshOn.sum (Finset.univ : Finset (rootsOfUnity m ℂ))
    (fun ζ p ↦ F (R ζ p)) (fun ζ _ ↦ hp.comp (hRd ζ) (hRm ζ))
  have hsumc : ContinuousOn (fun p ↦ ∑ ζ : rootsOfUnity m ℂ, F (R ζ p)) W := by
    apply continuousOn_finsetSum
    intro ζ _
    exact hF.comp (hRd ζ).continuousOn (hRm ζ)
  have hs := hsum.const_mul_of_continuous hsumc (inv_nonneg.mpr (Nat.cast_nonneg m))
  apply hs.congr
  intro p _
  exact (rootTrace_eq_of_pow m F (centeredRoot_pow m hx.2 p.1) p.2).symm

theorem rootTrace_psh {U : Set (ℂ × V)} (hU : IsOpen U)
    {F : ℂ × V → ℝ}
    (hF : ContinuousOn F ((fun p : ℂ × V ↦ (p.1^m,p.2)) ⁻¹' U))
    (hF0 : ∀ p, (p.1^m,p.2) ∈ U → 0 ≤ F p)
    (hp : DiskPshOn ((fun p : ℂ × V ↦ (p.1^m,p.2)) ⁻¹' U) F) :
    DiskPshOn U (rootTrace m F) := by
  apply first_hyperplane_removable hU (continuousOn_rootTrace m hU hF)
  · intro p hpU
    apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg m))
    apply Finset.sum_nonneg
    intro ζ _
    apply hF0
    rw [mul_pow, (mem_rootsOfUnity' m ζ.val).mp ζ.property, one_mul, chosenRoot_pow]
    exact hpU
  · exact rootTrace_psh_off_zero m hU hF hp

end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric Complex BigOperators
noncomputable section
variable {W : Type u14} [NormedAddCommGroup W] [NormedSpace ℂ W]

variable (m : ℕ) [NeZero m]

attribute [local instance] OAI.QuadricCounterexample.instFintypeSubtypeUnitsComplexMemSubgroupRootsOfUnity_solutions_2
variable [LocallyCompactSpace W]

lemma secondRootTrace_psh {U : Set (ℂ × (ℂ × W))} (hU : IsOpen U)
    {F : ℂ × (ℂ × W) → ℝ}
    (hF : ContinuousOn F ((fun p : ℂ × (ℂ × W) ↦ (p.1,(p.2.1^m,p.2.2))) ⁻¹' U))
    (hF0 : ∀ p, (p.1,(p.2.1^m,p.2.2)) ∈ U → 0 ≤ F p)
    (hp : DiskPshOn ((fun p : ℂ × (ℂ × W) ↦ (p.1,(p.2.1^m,p.2.2))) ⁻¹' U) F) :
    DiskPshOn U (secondRootTrace m F) := by
  have hT := differentiable_swapBase (W := W)
  have hc : ContinuousOn (F ∘ swapBase)
      ((fun p : ℂ × (ℂ × W) ↦ (p.1^m,p.2)) ⁻¹' (swapBase ⁻¹' U)) :=
    hF.comp hT.continuous.continuousOn (fun _ h ↦ h)
  have hq : DiskPshOn
      ((fun p : ℂ × (ℂ × W) ↦ (p.1^m,p.2)) ⁻¹' (swapBase ⁻¹' U)) (F ∘ swapBase) :=
    hp.comp hT.differentiableOn (fun _ h ↦ h)
  exact (rootTrace_psh m (hU.preimage hT.continuous) hc
    (fun p h ↦ hF0 (swapBase p) h) hq).comp hT.differentiableOn (fun _ h ↦ h)

theorem doubleRootTrace_psh {U : Set (ℂ × (ℂ × W))} (hU : IsOpen U)
    {F : ℂ × (ℂ × W) → ℝ}
    (hF : ContinuousOn F ((fun p : ℂ × (ℂ × W) ↦ (p.1^m,(p.2.1^m,p.2.2))) ⁻¹' U))
    (hF0 : ∀ p, (p.1^m,(p.2.1^m,p.2.2)) ∈ U → 0 ≤ F p)
    (hp : DiskPshOn ((fun p : ℂ × (ℂ × W) ↦ (p.1^m,(p.2.1^m,p.2.2))) ⁻¹' U) F) :
    DiskPshOn U (doubleRootTrace m F) := by
  apply rootTrace_psh m hU
  · exact continuousOn_secondRootTrace m (hU.preimage (by fun_prop)) hF
  · intro p hpU
    apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg m))
    apply Finset.sum_nonneg
    intro η _
    apply hF0
    change (p.1 ^ m, (((η.val : ℂ) * chosenRoot m p.2.1)^m,p.2.2)) ∈ U
    rw [mul_pow, (mem_rootsOfUnity' m η.val).mp η.property, one_mul, chosenRoot_pow]
    exact hpU
  · exact secondRootTrace_psh m (hU.preimage (by fun_prop)) hF hF0 hp

end
end QuadricCounterexample

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.WeakLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29 u30 u31

noncomputable section

namespace QuadricCounterexample
open Filter Topology Set MeasureTheory Metric
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise

noncomputable def coefficientsQuadraticCLM {n : Type u24} [Fintype n]
    (v : n → ℂ) : EuclideanSpace ℂ (n × n) →L[ℝ] ℝ :=
  (quadraticValueCLM v).comp
    ((coefficientsToMatrix (n := n)).toContinuousLinearMap.restrictScalars ℝ)

end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.TraceMetrics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section

namespace QuadricCounterexample
open Set Filter Topology Metric MeasureTheory Matrix
open scoped ComplexOrder Matrix.Norms.Elementwise
noncomputable section

lemma SmoothHermitianMetric.chart_psh {V : AlgebraicRankTwoBundle}
    (h : SmoothHermitianMetric V) (hp : h.StrictlyGriffithsPositive) (i : ℕ)
    (hi : V.coordinateDomain i=univ) :
    DiskPshOn univ (fun p : BaseCoordinates × FiberCoordinates ↦
      quadraticValue (h.dualMatrix i p.1) p.2) := by
  have hh := chern_positive_dual_norm_psh isOpen_univ
    (H := h.dualMatrix i) (by simpa only [hi] using (h.smooth i).of_le (by exact WithTop.coe_le_coe.mpr le_top))
    (by simpa only [hi] using h.positive i)
    (by simpa only [hi,mixedHessian,wirtingerDerivative,metricMixedHessian,
      holomorphicMetricDerivative] using hp i)
  rw [univ_prod_univ] at hh
  exact hh

lemma continuous_matrix_of_quadratic {X : Type u1} [TopologicalSpace X]
    {n : Type u2} [Fintype n] [DecidableEq n] {H : X → Matrix n n ℂ}
    (hh : ∀ x, (H x).IsHermitian)
    (hc : ∀ v, Continuous (fun x ↦ quadraticValue (H x) v)) : Continuous H := by
  have he : H=fun x ↦ matrixFromQuadratic (quadraticValue (H x)) := by
    funext x; exact (matrixFromQuadratic_value (hh x)).symm
  rw [he]
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  change Continuous (fun x ↦ Complex.equivRealProdCLM.symm
    ((quadraticValue (H x) (Pi.single i 1+Pi.single j 1)-quadraticValue (H x) (Pi.single i 1)-
      quadraticValue (H x) (Pi.single j 1))/2,
     (quadraticValue (H x) (Pi.single i 1)+quadraticValue (H x) (Pi.single j 1)-
       quadraticValue (H x) (Pi.single i 1+Complex.I • Pi.single j 1))/2))
  exact Complex.equivRealProdCLM.symm.continuous.comp
    ((((hc _).sub (hc _) |>.sub (hc _)).div_const 2).prodMk
      (((hc _).add (hc _) |>.sub (hc _)).div_const 2))

section Trace
variable (m : ℕ) [NeZero m]

attribute [local instance] OAI.QuadricCounterexample.instFintypeSubtypeUnitsComplexMemSubgroupRootsOfUnity_solutions_3
def matrixRootTrace (H : BaseCoordinates → TwoMatrix) (z : BaseCoordinates) : TwoMatrix :=
  ((m : ℝ)⁻¹ ^ 2) • ∑ ζ : rootsOfUnity m ℂ, ∑ η : rootsOfUnity m ℂ,
    H ((ζ.val : ℂ)*chosenRoot m z.1,(η.val : ℂ)*chosenRoot m z.2)

lemma matrixRootTrace_quadratic (H : BaseCoordinates → TwoMatrix) (z : BaseCoordinates)
    (v : FiberCoordinates) :
    quadraticValue (matrixRootTrace m H z) v =
      doubleRootTrace m (fun p : ℂ × (ℂ × FiberCoordinates) ↦
        quadraticValue (H (p.1,p.2.1)) p.2.2) (z.1,(z.2,v)) := by
  rw [doubleRootTrace_formula]
  change (quadraticValueCLM v) (((m : ℝ)⁻¹ ^ 2) • ∑ ζ : rootsOfUnity m ℂ,
    ∑ η : rootsOfUnity m ℂ, H ((ζ.val : ℂ)*chosenRoot m z.1,(η.val : ℂ)*chosenRoot m z.2)) = _
  simp only [map_smul,map_sum,smul_eq_mul]
  rfl

lemma matrixRootTrace_posDef {H : BaseCoordinates → TwoMatrix}
    (hH : ∀ z, (H z).PosDef) (z : BaseCoordinates) : (matrixRootTrace m H z).PosDef := by
  unfold matrixRootTrace
  apply Matrix.PosDef.smul
  · apply Matrix.posDef_sum (Finset.univ_nonempty)
    intro ζ _
    exact Matrix.posDef_sum (Finset.univ_nonempty) (fun η _ ↦ hH _)
  · exact pow_pos (inv_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m)))) _

lemma continuous_matrixRootTrace {H : BaseCoordinates → TwoMatrix}
    (hc : Continuous H) (hh : ∀ z, (H z).IsHermitian) :
    Continuous (matrixRootTrace m H) := by
  apply continuous_matrix_of_quadratic
  · intro z
    unfold matrixRootTrace
    exact (IsSelfAdjoint.all ((m : ℝ)⁻¹ ^ 2)).smul
      (isSelfAdjoint_sum _ fun _ _ ↦ isSelfAdjoint_sum _ fun _ _ ↦ hh _)
  · intro v
    have hq : Continuous (fun p : ℂ × (ℂ × FiberCoordinates) ↦
        quadraticValue (H (p.1,p.2.1)) p.2.2) := by
      unfold quadraticValue
      fun_prop
    have htrace := continuousOn_doubleRootTrace m isOpen_univ
      (U := univ) (by simpa only [preimage_univ] using hq.continuousOn)
    have ht : Continuous (fun z : BaseCoordinates ↦
      doubleRootTrace m (fun p : ℂ × (ℂ × FiberCoordinates) ↦
        quadraticValue (H (p.1,p.2.1)) p.2.2) (z.1,(z.2,v))) :=
      continuousOn_univ.mp htrace |>.comp (by fun_prop)
    exact ht.congr (fun z ↦ (matrixRootTrace_quadratic m H z v).symm)

lemma matrixRootTrace_psh {H : BaseCoordinates → TwoMatrix}
    (hc : Continuous H) (hpos : ∀ z, (H z).PosDef)
    (hp : DiskPshOn univ (fun p : BaseCoordinates × FiberCoordinates ↦
      quadraticValue (H p.1) p.2)) :
    DiskPshOn univ (fun p : BaseCoordinates × FiberCoordinates ↦
      quadraticValue (matrixRootTrace m H p.1) p.2) := by
  let F := fun p : ℂ × (ℂ × FiberCoordinates) ↦ quadraticValue (H (p.1,p.2.1)) p.2.2
  have hF : Continuous F := by unfold F quadraticValue; fun_prop
  have hFp : DiskPshOn univ F := hp.comp
    (by fun_prop : DifferentiableOn ℂ (fun p : ℂ × (ℂ × FiberCoordinates) ↦ ((p.1,p.2.1),p.2.2)) univ)
    (fun _ _ ↦ mem_univ _)
  have ht := doubleRootTrace_psh m isOpen_univ (U := univ)
    (by simpa only [preimage_univ] using hF.continuousOn)
    (fun p _ ↦ quadraticValue_nonneg (hpos _).posSemidef _)
    (by simpa only [preimage_univ] using hFp)
  have ha := ht.comp
    (by fun_prop : DifferentiableOn ℂ (fun p : BaseCoordinates × FiberCoordinates ↦ (p.1.1,(p.1.2,p.2))) univ)
    (fun _ _ ↦ mem_univ _)
  convert ha using 1
  funext p
  exact matrixRootTrace_quadratic m H p.1 p.2

lemma matrixRootTrace_anyRoot (H : BaseCoordinates → TwoMatrix)
    (x : BaseCoordinates) :
    matrixRootTrace m H (x.1^m,x.2^m) =
      ((m : ℝ)⁻¹ ^ 2) • ∑ ζ : rootsOfUnity m ℂ, ∑ η : rootsOfUnity m ℂ,
        H ((ζ.val : ℂ)*x.1,(η.val : ℂ)*x.2) := by
  obtain ⟨a,ha⟩ := same_power_orbit m (chosenRoot_pow m (x.1^m))
  obtain ⟨b,hb⟩ := same_power_orbit m (chosenRoot_pow m (x.2^m))
  unfold matrixRootTrace
  rw [ha,hb]
  congr 1
  have he := Equiv.sum_comp ((Equiv.mulRight a).prodCongr (Equiv.mulRight b))
    (fun p : rootsOfUnity m ℂ × rootsOfUnity m ℂ ↦
      H ((p.1.val : ℂ)*x.1,(p.2.val : ℂ)*x.2))
  simp only [Fintype.sum_prod_type] at he
  change (∑ ζ : rootsOfUnity m ℂ, ∑ η : rootsOfUnity m ℂ,
    H ((((ζ*a).val : ℂ))*x.1,(((η*b).val : ℂ))*x.2)) = _ at he
  simpa only [Subgroup.coe_mul,Units.val_mul,mul_assoc] using he

omit [NeZero m] in
lemma scalarCoordinateChange_root (i j : Fin 2) (ζ : rootsOfUnity m ℂ) (x : ℂ) :
    scalarCoordinateChange i j ((ζ.val : ℂ)*x) =
      ((rootSwitchEquiv m i j ζ).val : ℂ)*scalarCoordinateChange i j x := by
  by_cases hij : i=j <;>
    simp [scalarCoordinateChange,rootSwitchEquiv,hij,_root_.mul_inv_rev,mul_comm]

omit [NeZero m] in
lemma coordinateChange_pow (i j : StandardChart) (x : BaseCoordinates) :
    coordinateChange i j (x.1^m,x.2^m) =
      ((coordinateChange i j x).1^m,(coordinateChange i j x).2^m) := by
  ext <;> simp only [coordinateChange,scalarCoordinateChange] <;> split_ifs <;> simp

lemma coordinateOverlap_pow (i j : StandardChart) (x : BaseCoordinates) :
    (x.1^m,x.2^m) ∈ coordinateOverlap i j ↔ x ∈ coordinateOverlap i j := by
  simp only [coordinateOverlap_iff,ne_eq,pow_eq_zero_iff (NeZero.ne m)]

lemma polarizationTransition_root_norm (i j : StandardChart) (x : BaseCoordinates)
    (ζ η : rootsOfUnity m ℂ) :
    ‖polarizationTransition i j (affineQuadric i ((ζ.val : ℂ)*x.1,(η.val : ℂ)*x.2))‖ =
      ‖polarizationTransition i j (affineQuadric i x)‖ := by
  simp only [polarizationTransition_affine,norm_mul,firstFactor,secondFactor,scalarFactor]
  split_ifs <;> simp only [root_norm]

lemma matrixRootTrace_change (H : BaseCoordinates → TwoMatrix) (i j : StandardChart)
    (x : BaseCoordinates) :
    matrixRootTrace m H (coordinateChange i j (x.1^m,x.2^m)) =
      ((m : ℝ)⁻¹ ^ 2) • ∑ ζ : rootsOfUnity m ℂ, ∑ η : rootsOfUnity m ℂ,
        H (coordinateChange i j ((ζ.val : ℂ)*x.1,(η.val : ℂ)*x.2)) := by
  rw [coordinateChange_pow,matrixRootTrace_anyRoot]
  congr 1
  have he := Equiv.sum_comp ((rootSwitchEquiv m i.1 j.1).prodCongr
      (rootSwitchEquiv m i.2 j.2))
    (fun p : rootsOfUnity m ℂ × rootsOfUnity m ℂ ↦
      H ((p.1.val : ℂ)*(coordinateChange i j x).1,
        (p.2.val : ℂ)*(coordinateChange i j x).2))
  simpa only [Fintype.sum_prod_type,Equiv.prodCongr_apply,Prod.map,coordinateChange,
    scalarCoordinateChange_root] using he.symm

lemma quadraticValue_scalar (H : TwoMatrix) (c : ℂ) (v : FiberCoordinates) :
    quadraticValue H (c • v)=‖c‖^2*quadraticValue H v := by
  simp only [quadraticValue,star_smul,mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul,
    ← mul_assoc,Complex.star_def]
  rw [Complex.mul_conj,Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

lemma quadraticValue_sum_smul (H : rootsOfUnity m ℂ → rootsOfUnity m ℂ → TwoMatrix)
    (v : FiberCoordinates) :
    quadraticValue (((m : ℝ)⁻¹^2) • ∑ ζ, ∑ η, H ζ η) v =
      ((m : ℝ)⁻¹^2)*∑ ζ, ∑ η, quadraticValue (H ζ η) v := by
  change (quadraticValueCLM v) _ = _
  simp only [map_smul,map_sum,smul_eq_mul]
  rfl

omit [NeZero m] in
lemma SmoothHermitianMetric.twist_quadratic_change {D : EqualizerData} {hm : 0 < m}
    (h : SmoothHermitianMetric (powerPullbackTwist D.bundle m hm))
    (i j : StandardChart) {x : BaseCoordinates} (hx : x ∈ coordinateOverlap i j)
    (v : FiberCoordinates) :
    quadraticValue (h.dualMatrix (standardChartIndex i) x) v =
      ‖polarizationTransition i j (affineQuadric i x)‖^2*
        quadraticValue (h.dualMatrix (standardChartIndex j) (coordinateChange i j x))
          ((D.coordinateTransition i j (x.1^m,x.2^m)).transpose.mulVec v) := by
  have hi : affineQuadric i x ∈ (powerPullbackTwist D.bundle m hm).domain (standardChartIndex i) := by
    rw [D.twist_domain]; exact ⟨x,rfl⟩
  have hj : affineQuadric i x ∈ (powerPullbackTwist D.bundle m hm).domain (standardChartIndex j) := by
    rw [D.twist_domain]; exact (affineQuadric_mem_range _ _ _).mpr hx
  have he := h.compatible (standardChartIndex j) (standardChartIndex i) (affineQuadric i x) hj hi
  simp only [D.twist_chart,coordQuadric_affine,coordinateChange_coord] at he
  rw [he,quadraticValue_congruence]
  change quadraticValue (h.dualMatrix (standardChartIndex j) (coordinateChange i j x))
    (((polarizationTransition _ _ _ • D.globalTransition _ _ (powerQuadric m (affineQuadric i x))).transpose).mulVec v)=_
  simp only [EqualizerData.bundle,standardChartNat_index,powerQuadric_affine hm,
    EqualizerData.globalTransition,coordQuadric_affine,Matrix.transpose_smul,smul_mulVec]
  exact quadraticValue_scalar _ _ _

lemma SmoothHermitianMetric.trace_quadratic_change {D : EqualizerData} {hm : 0 < m}
    (h : SmoothHermitianMetric (powerPullbackTwist D.bundle m hm))
    (i j : StandardChart) {x : BaseCoordinates} (hx : x ∈ coordinateOverlap i j)
    (v : FiberCoordinates) :
    quadraticValue (matrixRootTrace m (h.dualMatrix (standardChartIndex i)) (x.1^m,x.2^m)) v =
      ‖polarizationTransition i j (affineQuadric i x)‖^2*
        quadraticValue (matrixRootTrace m (h.dualMatrix (standardChartIndex j))
          (coordinateChange i j (x.1^m,x.2^m)))
          ((D.coordinateTransition i j (x.1^m,x.2^m)).transpose.mulVec v) := by
  rw [matrixRootTrace_anyRoot,matrixRootTrace_change,quadraticValue_sum_smul,
    quadraticValue_sum_smul]
  have hs : ∀ ζ η : rootsOfUnity m ℂ,
      quadraticValue (h.dualMatrix (standardChartIndex i) ((ζ.val : ℂ)*x.1,(η.val : ℂ)*x.2)) v =
        ‖polarizationTransition i j (affineQuadric i x)‖^2*
          quadraticValue (h.dualMatrix (standardChartIndex j)
            (coordinateChange i j ((ζ.val : ℂ)*x.1,(η.val : ℂ)*x.2)))
            ((D.coordinateTransition i j (x.1^m,x.2^m)).transpose.mulVec v) := by
    intro ζ η
    have hr : ((ζ.val : ℂ)*x.1,(η.val : ℂ)*x.2) ∈ coordinateOverlap i j := by
      rw [← coordinateOverlap_pow m]
      simpa only [root_pow] using (coordinateOverlap_pow m i j x).mpr hx
    simpa only [root_pow,polarizationTransition_root_norm] using h.twist_quadratic_change m i j hr v
  simp_rw [hs,← Finset.mul_sum]
  ring

omit [NeZero m] in
lemma polarizationTransition_power (i j : StandardChart) (x : BaseCoordinates) :
    polarizationTransition i j (affineQuadric i (x.1^m,x.2^m)) =
      polarizationTransition i j (affineQuadric i x)^m := by
  simp only [polarizationTransition_affine,firstFactor,secondFactor,scalarFactor]
  split_ifs <;> simp [mul_pow]

lemma traceScalar_power (i j : StandardChart) (x : BaseCoordinates) :
    traceScalar m i j (x.1^m,x.2^m) =
      ‖polarizationTransition i j (affineQuadric i x)‖^2 := by
  unfold traceScalar
  rw [polarizationTransition_power,norm_pow]
  have he : (2/(m : ℝ))=(m : ℝ)⁻¹*(2 : ℕ) := by simp only [Nat.cast_ofNat]; ring
  rw [he,Real.rpow_mul_natCast (by positivity),Real.pow_rpow_inv_natCast (norm_nonneg _) (NeZero.ne m)]

lemma SmoothHermitianMetric.trace_change {D : EqualizerData} {hm : 0 < m}
    (h : SmoothHermitianMetric (powerPullbackTwist D.bundle m hm))
    (i j : StandardChart) {z : BaseCoordinates} (hz : z ∈ coordinateOverlap i j)
    (v : FiberCoordinates) :
    quadraticValue (matrixRootTrace m (h.dualMatrix (standardChartIndex i)) z) v =
      traceScalar m i j z *
        quadraticValue (matrixRootTrace m (h.dualMatrix (standardChartIndex j))
          (coordinateChange i j z))
          ((D.coordinateTransition i j z).transpose.mulVec v) := by
  let x : BaseCoordinates := (chosenRoot m z.1,chosenRoot m z.2)
  have hx : (x.1^m,x.2^m)=z := Prod.ext (chosenRoot_pow m _) (chosenRoot_pow m _)
  have hr : x ∈ coordinateOverlap i j := (coordinateOverlap_pow m i j x).mp (hx ▸ hz)
  have he := h.trace_quadratic_change m i j hr v
  rw [← traceScalar_power m i j x,hx] at he
  exact he
end Trace
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology Metric MeasureTheory Matrix
open scoped ComplexOrder Matrix.Norms.Elementwise
noncomputable section

def SmoothHermitianMetric.tracedForm {D : EqualizerData} {m : ℕ} (hm : 0 < m)
    (h : SmoothHermitianMetric (powerPullbackTwist D.bundle m hm)) (hp : h.StrictlyGriffithsPositive) :
    TwistedPshForm D m := by
  letI : NeZero m := ⟨ne_of_gt hm⟩
  have hc (i : StandardChart) : Continuous (h.dualMatrix (standardChartIndex i)) :=
    continuousOn_univ.mp (D.twist_coordinateDomain m hm i ▸ (h.smooth _).continuousOn)
  have hpos (i : StandardChart) (z : BaseCoordinates) :
      (h.dualMatrix (standardChartIndex i) z).PosDef := h.positive _ z
        (by rw [D.twist_coordinateDomain]; exact mem_univ _)
  exact {
    matrix i := matrixRootTrace m (h.dualMatrix (standardChartIndex i))
    continuous i := continuous_matrixRootTrace m (hc i) (fun z ↦ (hpos i z).isHermitian)
    positive i z := matrixRootTrace_posDef m (hpos i) z
    psh i := matrixRootTrace_psh m (hc i) (hpos i)
      (h.chart_psh hp _ (D.twist_coordinateDomain m hm i))
    compatible i j z hz v := h.trace_change m i j hz v }
end
end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.MatrixDynamics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4

noncomputable section

namespace QuadricCounterexample
open Matrix OnePoint Filter Topology MeasureTheory

lemma source_product_lower_left_ne_zero : (source_A * source_B) 1 0 ≠ 0 := by
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
  simp [source_A, source_B, Matrix.mul_apply, source_a_ne_zero, hn]

noncomputable def source_eigenbasis : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (hyperbolicBasis (source_A * source_B) (1 + Real.sqrt 2))
    (hyperbolicBasis_det_ne_zero (by
      have hn := Real.sqrt_nonneg (2 : ℝ)
      have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith) source_product_lower_left_ne_zero)

end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.DualForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section

namespace QuadricCounterexample
open Set Filter Topology Metric Matrix
noncomputable section
open scoped ComplexOrder

def homogeneousCoordinate (i : Fin 2) (v : FiberCoordinates) : ℂ :=
  v (otherIndex i)/v i

namespace PshLine24
variable (L : PshLine24)

def homogeneousNorm (v : FiberCoordinates) : ℝ :=
  if v 0=0 then L.value 1 (homogeneousCoordinate 1 v,(v 1)^24)
  else L.value 0 (homogeneousCoordinate 0 v,(v 0)^24)

end PshLine24

end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology Metric Matrix MeasureTheory
open scoped ComplexOrder
noncomputable section

@[simp] lemma homogeneousCoordinate_affineRepresentative (i : Fin 2) (z : ℂ) :
    homogeneousCoordinate i (affineRepresentative i z)=z := by
  fin_cases i <;> simp [homogeneousCoordinate,affineRepresentative,otherIndex]

end
end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.ProjectiveEquations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

noncomputable section

namespace QuadricCounterexample
open Set MvPolynomial Matrix LaurentCech BinaryForms
open scoped BigOperators
noncomputable section

namespace PolynomialGeneration
variable {n : ℕ} {ι : Type u1} [Fintype ι] (B : PolynomialGeneration n ι)

def normalize (j : ProjectiveIndex ι) (y : ProjectiveIndex ι → ℂ) : ProjectiveIndex ι → ℂ := fun k ↦ y k/y j

def patchCoordinates (i : StandardChart) (q : ι) (y : ProjectiveIndex ι → ℂ) : BaseCoordinates :=
  (y (index (flipFirst i,q)),y (index (flipSecond i,q)))
def block (i : StandardChart) (y : ProjectiveIndex ι → ℂ) : ι → ℂ := fun q ↦ y (index (i,q))
def patchRecovery (i : StandardChart) (q : ι) (y : ProjectiveIndex ι → ℂ) : Fin (n+1) → ℂ :=
  (B.recover i (patchCoordinates i q y)).mulVec (block i y)
end PolynomialGeneration
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set MvPolynomial Matrix LaurentCech BinaryForms
open scoped BigOperators
noncomputable section
namespace PolynomialGeneration
variable {n : ℕ} {ι : Type u3} [Fintype ι] (B : PolynomialGeneration n ι)

def liftPatchPolynomial (i : StandardChart) (q : ι) (p : BasePolynomial) :
    MvPolynomial (ProjectiveIndex ι) ℂ :=
  MvPolynomial.bind₁ (fun k : Fin 2 ↦ if k=0 then X (index (flipFirst i,q)) else X (index (flipSecond i,q))) p

def recoveryPolynomial (i : StandardChart) (q : ι) (k : Fin (n+1)) :
    MvPolynomial (ProjectiveIndex ι) ℂ :=
  ∑ r : ι,liftPatchPolynomial i q (B.recovery i k r)*X (index (i,r))

def patchEquations (hn : 0<n) (i : StandardChart) (q : ι) :
    Set (MvPolynomial (ProjectiveIndex ι) ℂ) :=
  range (fun j : ProjectiveIndex ι ↦
    X j-liftPatchPolynomial i q (lineGenerator (1,1) (label j).1 i)*
      ∑ k : Fin (n+1),liftPatchPolynomial i q (B.coefficient i k (label j).2)*B.recoveryPolynomial i q k) ∪
  range (fun k : Fin (n+1) ↦ B.recoveryPolynomial i q k^n-
    B.recoveryPolynomial i q (Fin.last n)^k.val*B.recoveryPolynomial i q 0^(n-k.val)) ∪
  range (fun k : Fin n ↦ B.recoveryPolynomial i q k.succ*B.recoveryPolynomial i q 0-
    B.recoveryPolynomial i q k.castSucc*B.recoveryPolynomial i q (veroneseOne n hn))
end PolynomialGeneration
end
end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.Embedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

noncomputable section

namespace QuadricCounterexample
open Set MvPolynomial Matrix LaurentCech BinaryForms PolynomialGeneration
open scoped BigOperators
noncomputable section
namespace SegreSectionSystem
variable {V : AlgebraicRankTwoBundle} {n : ℕ} {ι : Type u3} [Fintype ι] (S : SegreSectionSystem V n ι)

def inverseNumerator (hn : 0<n) (i : ℕ) (q : ι) (b : Fin 2) :
    Fin 3 → MvPolynomial (ProjectiveIndex ι) ℂ :=
  ![X (index (flipFirst (V.chart i),q)),X (index (flipSecond (V.chart i),q)),
    S.generation.recoveryPolynomial (V.chart i) q (veroneseAdjacent n hn b)]
def inverseDenominator (i : ℕ) (q : ι) (b : Fin 2) :
    Fin 3 → MvPolynomial (ProjectiveIndex ι) ℂ :=
  ![1,1,S.generation.recoveryPolynomial (V.chart i) q (veroneseEndpoint n b)]
end SegreSectionSystem
end
end QuadricCounterexample

end

end OAI
end


