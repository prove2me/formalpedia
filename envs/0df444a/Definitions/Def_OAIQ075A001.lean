-- Prove2me | Definitions.Def_OAIQ075A001
-- name    : OAIQ075A001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T07:54:42.620734+00:00
-- url     : https://prove2.me/theorems/92e37f85-8cb0-4625-90cd-c20553c9d453
-- title:
--   Definitions bundle OAIQ075A001 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 161 declarations of OpenAI's Lean: 45 definitions, 1 inductive type or structure, 3 instances and 112 theorems. The definitions and types are `OAI.BoundedHochschild.KadisonRingrose.compressOperatorSystem`, `OAI.BoundedHochschild.KadisonRingrose.compressionPositive`, `OAI.BoundedHochschild.KadisonRingrose.entrywiseMatrixLinear`, `OAI.BoundedHochschild.KadisonRingrose.isometryDefect`, `OAI.BoundedHochschild.KadisonRingrose.positiveFunctionalCLM`, `OAI.BoundedHochschild.KadisonRingrose.predualNormalEquiv`, `OAI.BoundedHochschild.KadisonRingrose.unitaryDualEquiv`, `OAI.BoundedHochschild.KadisonRingrose.unitaryOrbitHull`, `OAI.BoundedHochschild.KadisonRingrose.unitaryPullback`, `OAI.BoundedHochschild.KadisonRingrose.weakFunctionalClosure`, `OAI.BoundedHochschild.KadisonRingrose.weakIsometry`, `OAI.BoundedHochschild.KadisonRingrose.weakPredualMap`, `OAI.BoundedHochschild.KadisonRingrose.weakPredualRealMap`, `OAI.BoundedHochschild.WeakAlgebra.linearClosure`, `OAI.BoundedHochschild.WeakAlgebra.weakEquiv`, `OAI.BoundedHochschild.WeakSubspace.preannihilator`, `OAI.BoundedHochschild.WeakSubspace.quotientDual`, `OAI.BoundedHochschild.WeakSubspace.quotientDualEquiv`, `OAI.BoundedHochschild.WeakSubspace.strong`, `OAI.HochschildDixmier.conjugate`, `OAI.HochschildDixmier.gnsVector`, `OAI.HochschildNormalPart.FourHilbert`, `OAI.HochschildNormalPart.FunctionalModel`, `OAI.HochschildNormalPart.coefficient`, `OAI.HochschildNormalPart.coefficientLeft`, `OAI.HochschildNormalPart.cyclicSpace`, `OAI.HochschildNormalPart.fourLeft`, `OAI.HochschildNormalPart.fourRepresentation`, `OAI.HochschildNormalPart.fourRight`, `OAI.HochschildNormalPart.functionalModel`, `OAI.HochschildNormalPart.normalDual`, `OAI.HochschildNormalPart.normalPartRaw`, `OAI.HochschildNormalPart.normalProjection`, `OAI.HochschildNormalPart.normalVectors`, `OAI.HochschildNormalPart.positiveVector`, `OAI.HochschildNormalPart.predualEmbedding`, `OAI.HochschildNormalPart.sumOperator`, `OAI.HochschildNormalPart.sumRepresentation`, `OAI.HochschildPositiveDecomposition.complexify`, `OAI.HochschildPositiveDecomposition.complexifyPositive` and 6 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BoundedHochschild_CentralComparison`, `BoundedHochschild_CompactConvexCenter`, `BoundedHochschild_CompactInvariantSets`, `BoundedHochschild_DiffuseProjections`, `BoundedHochschild_Dixmier`, `BoundedHochschild_FiniteNormalState`, `BoundedHochschild_FiniteNormalTrace`, `BoundedHochschild_Frames`, `BoundedHochschild_IsometricFixedPoint`, `BoundedHochschild_IsometryDefectColumns`, `BoundedHochschild_MinimalIsometricOrbit`, `BoundedHochschild_NormalMultiplication`, `BoundedHochschild_NormalOperators`, `BoundedHochschild_NormalOrbitHull`, `BoundedHochschild_NormalOrbitInvariance`, `BoundedHochschild_NormalVectors`, `BoundedHochschild_OperatorSystemCompression`, `BoundedHochschild_OrthogonalProjectionSums`, `BoundedHochschild_PositiveCompleteAdditivity`, `BoundedHochschild_PositiveCompression`, `BoundedHochschild_PositiveDecomposition`, `BoundedHochschild_PositiveOrbitCompactness`, `BoundedHochschild_ProjectionJoinComparison`, `BoundedHochschild_ScalarMatrixActions`, `BoundedHochschild_TraceExpectations`, `BoundedHochschild_TypeIIStructure`, `BoundedHochschild_Ultrapowers`, `BoundedHochschild_UniformProjectionSums`, `BoundedHochschild_UnitaryPredualAction`, `BoundedHochschild_WeakAlgebras`, `BoundedHochschild_WeakCompactFragment`, `BoundedHochschild_WeakIsometricFixedPoint`, `BoundedHochschild_WeakPredual`, `BoundedHochschild_WeakSubspaces`, `TracialCohomology_CenterTrace`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ075A007`, `OAIQ075A008`, `OAIQ075A009` and `OAIQ075A011`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib

section
-- module Solutions.OAIQ075_KS.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
open scoped ComplexOrder in
/-- d13f23b's `PositiveLinearMap.norm_map_star_mul_sq_le`: Cauchy–Schwarz for a positive functional
(Kadison similarity, oaiq-075). -/
theorem _root_.PositiveLinearMap.norm_map_star_mul_sq_le {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (ψ : A →ₚ[ℂ] ℂ) (a b : A) :
    ‖ψ (star a * b)‖ ^ 2 ≤ ‖ψ (star a * a)‖ * ‖ψ (star b * b)‖ := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (ψ.toPreGNS a) (ψ.toPreGNS b)
  rw [PositiveLinearMap.preGNS_inner_def] at h
  have ha := ψ.preGNS_norm_sq (ψ.toPreGNS a)
  have hb := ψ.preGNS_norm_sq (ψ.toPreGNS b)
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS] at h ha hb
  have h2 := mul_self_le_mul_self (norm_nonneg _) h
  rw [← ha, ← hb]
  simpa [sq, mul_mul_mul_comm] using h2
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_Ultrapowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tracial ultrapowers, quotient traces and bounded-ball maps. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
namespace HochschildUltrapower
open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a))
include h1

lemma norm_trace_le (a : A) : ‖τ a‖ ≤ ‖τ.toPreGNS a‖ := by
  have hin : inner ℂ (τ.toPreGNS 1) (τ.toPreGNS a) = τ a := by
    simp [PositiveLinearMap.preGNS_inner_def]
  rw [← hin]
  have hone : ‖τ.toPreGNS 1‖ = 1 := by
    rw [PositiveLinearMap.preGNS_norm_def]
    simp [h1]
  simpa only [hone,one_mul] using norm_inner_le_norm (𝕜 := ℂ) (τ.toPreGNS 1) (τ.toPreGNS a)

end HochschildUltrapower

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_TraceExpectations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace pairing norms, predual vectors and trace-preserving expectations. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder
namespace HochschildTraceNorm
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma norm_mul_eq_abs_mul (b d : A) : ‖b*d‖=‖CFC.abs b*d‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [pow_two,pow_two,← CStarRing.norm_star_mul_self,← CStarRing.norm_star_mul_self]
  congr 1
  simp only [star_mul,(IsSelfAdjoint.of_nonneg (CFC.abs_nonneg b)).star_eq]
  rw [mul_assoc,← mul_assoc (star b),← CFC.abs_mul_abs b]
  simp only [mul_assoc]

 

theorem exists_approx_polar (b : A) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : A, ‖v‖ ≤ 1 ∧ ‖b-v*CFC.abs b‖ ≤ ε ∧
      ‖CFC.abs b-star v*b‖ ≤ ε := by
  let a := CFC.abs b
  have ha0 : 0 ≤ a := CFC.abs_nonneg b
  have ha : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg ha0
  let f : ℝ → ℝ := fun t => (t+ε)⁻¹
  have hf : ContinuousOn f (spectrum ℝ a) := by
    apply ContinuousOn.inv₀ ((continuous_id.add continuous_const).continuousOn)
    intro t ht
    have ht0 := spectrum_nonneg_of_nonneg ha0 ht
    exact (show 0 < t+ε from by linarith).ne'
  let q := cfc f a
  have hq : IsSelfAdjoint q := cfc_predicate f a
  have hqa : Commute q a := (Commute.refl a).cfc_real f
  have hab : a*a=star b*b := CFC.abs_mul_abs b
  have haq : a*q=cfc (fun t => t*f t) a := by
    change a*cfc f a = cfc (fun t => id t*f t) a
    rw [cfc_mul id f a continuousOn_id hf,cfc_id ℝ a ha]
  have hnormaq : ‖a*q‖ ≤ 1 := by
    rw [haq]
    apply norm_cfc_le (by positivity)
    intro t ht
    have ht0 : 0 ≤ t := spectrum_nonneg_of_nonneg ha0 ht
    have hp : 0 < t+ε := by linarith
    dsimp [f]
    rw [abs_of_nonneg (mul_nonneg ht0 (inv_nonneg.mpr hp.le))]
    exact (mul_inv_le_iff₀ hp).mpr (by linarith)
  have hres : a-q*a*a=cfc (fun t => t-f t*t*t) a := by
    change a-cfc f a*a*a=cfc (fun t => id t - (fun s => f s * id s * id s) t) a
    rw [cfc_sub id (fun s => f s * id s * id s) a continuousOn_id ((hf.mul continuousOn_id).mul continuousOn_id),
      cfc_mul (fun t => f t * id t) id a (hf.mul continuousOn_id) continuousOn_id,
      cfc_mul f id a hf continuousOn_id,cfc_id ℝ a ha]
  have hresnorm : ‖a-q*a*a‖ ≤ ε := by
    rw [hres]
    apply norm_cfc_le hε.le
    intro t ht
    have ht0 : 0 ≤ t := spectrum_nonneg_of_nonneg ha0 ht
    have hp : 0 < t+ε := by linarith
    have heq : t-(t+ε)⁻¹*t*t=ε*t/(t+ε) := by field_simp; ring
    dsimp [f]
    rw [heq,abs_of_nonneg (div_nonneg (mul_nonneg hε.le ht0) hp.le)]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  refine ⟨b*q,?_,?_,?_⟩
  · have hh : ‖b*q‖^2 ≤ 1 := by
      rw [pow_two,← CStarRing.norm_star_mul_self]
      have heq : star (b*q)*(b*q)=(a*q)*(a*q) := by
        rw [star_mul,hq.star_eq]
        calc
          q*star b*(b*q)=q*(star b*b)*q := by simp only [mul_assoc]
          _ = q*(a*a)*q := by rw [hab]
          _ = (a*q)*(a*q) := by rw [← mul_assoc q a,hqa.eq]; simp only [mul_assoc]
      rw [heq]
      exact (norm_mul_le _ _).trans ((mul_le_mul hnormaq hnormaq (norm_nonneg _) (by positivity)).trans_eq (by norm_num))
    nlinarith [norm_nonneg (b*q)]
  · have heq : b-b*q*a=b*(1-q*a) := by simp only [mul_sub,mul_one,mul_assoc]
    rw [heq,norm_mul_eq_abs_mul]
    change ‖a*(1-q*a)‖ ≤ ε
    have heq' : a*(1-q*a)=a-q*a*a := by
      rw [mul_sub,mul_one,← mul_assoc,hqa.eq]
    rw [heq']
    exact hresnorm
  · simp only [star_mul,hq.star_eq]
    rw [mul_assoc q (star b),← hab]
    simpa only [mul_assoc] using hresnorm
end HochschildTraceNorm

 

open scoped ComplexOrder



open scoped ComplexOrder



open scoped ComplexOrder



open scoped ComplexOrder



open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_WeakSubspaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Preannihilators, quotient duals and weak-star closed subspaces. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open Filter Topology
namespace BoundedHochschild
namespace WeakSubspace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

def preannihilator (S : Submodule ℂ (WeakDual ℂ X)) : Submodule ℂ X where
  carrier := {z | ∀ f ∈ S, f z=0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy f hf; simp [map_add,hx f hf,hy f hf]
  smul_mem' := by intro c x hx f hf; simp [map_smul,hx f hf]

lemma preannihilator_closed (S : Submodule ℂ (WeakDual ℂ X)) :
    IsClosed (preannihilator S : Set X) := by
  change IsClosed {z | ∀ f, f ∈ S → f z=0}
  simpa only [Set.ofPred_forall,WeakDual.toStrongDual_apply] using
    (isClosed_iInter fun (f : WeakDual ℂ X) => isClosed_iInter fun (_ : f ∈ S) =>
      isClosed_eq (WeakDual.toStrongDual f).continuous (continuous_const (y := (0 : ℂ))))

 

lemma mem_iff_annihilates (S : Submodule ℂ (WeakDual ℂ X))
    (hS : IsClosed (S : Set (WeakDual ℂ X))) (f : WeakDual ℂ X) :
    f ∈ S ↔ ∀ z ∈ preannihilator S, f z=0 := by
  let : IsScalarTower ℝ ℂ (WeakDual ℂ X) :=
    inferInstanceAs (IsScalarTower ℝ ℂ (StrongDual ℂ X))
  let hc : LocallyConvexSpace ℝ (WeakDual ℂ X) :=
    @WeakBilin.locallyConvexSpace ℂ (StrongDual ℂ X) X _ _ _ _ _ _ _ _ _
  constructor
  · intro hf z hz
    exact hz f hf
  · intro hf
    by_contra hnot
    obtain ⟨F,c,hFc,hcf⟩ := @RCLike.geometric_hahn_banach_closed_point ℂ (WeakDual ℂ X)
      _ _ _ (S : Set (WeakDual ℂ X)) f _ _ _ _ _ hc
      (S.restrictScalars ℝ).convex hS hnot
    have hzero (a : WeakDual ℂ X) (ha : a ∈ S) : F a=0 := by
      by_contra hne
      have hb := hFc ((((c+1 : ℝ) : ℂ) / F a) • a) (S.smul_mem _ ha)
      rw [map_smul,smul_eq_mul,div_mul_cancel₀ _ hne] at hb
      simp only [RCLike.re_to_complex,Complex.ofReal_re] at hb
      linarith
    obtain ⟨z,hz⟩ := LinearMap.dualEmbedding_surjective (topDualPairing ℂ X) F
    have heval (a : WeakDual ℂ X) : F a=a z := by
      rw [← hz]
      rfl
    have hmem : z ∈ preannihilator S := by
      intro a ha
      rw [← heval]
      exact hzero a ha
    have hf0 := hf z hmem
    have hc0 := hFc 0 S.zero_mem
    simp only [map_zero] at hc0
    rw [heval,hf0] at hcf
    simp only [RCLike.zero_re] at hcf
    linarith

 
def strong (S : Submodule ℂ (WeakDual ℂ X)) : Submodule ℂ (StrongDual ℂ X) :=
  S.map WeakDual.toStrongDual.toLinearMap

lemma mem_strong (S : Submodule ℂ (WeakDual ℂ X)) (f : StrongDual ℂ X) :
    f ∈ strong S ↔ StrongDual.toWeakDual f ∈ S := by
  constructor
  · rintro ⟨g,hg,hgf⟩
    change WeakDual.toStrongDual g=f at hgf
    rw [← hgf]
    exact hg
  · intro hf
    exact ⟨StrongDual.toWeakDual f,hf,rfl⟩

instance preannihilator_closed_instance (S : Submodule ℂ (WeakDual ℂ X)) :
    IsClosed (preannihilator S : Set X) := preannihilator_closed S

lemma quotient_dual_norm (K : Submodule ℂ X) [IsClosed (K : Set X)]
    (F : StrongDual ℂ (X ⧸ K)) : ‖F.comp K.mkQL‖=‖F‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound (F.comp K.mkQL) (norm_nonneg F)
    intro x
    exact (F.le_opNorm (K.mkQL x)).trans
      (mul_le_mul_of_nonneg_left (Submodule.Quotient.norm_mk_le K x) (norm_nonneg _))
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro q
    apply le_of_forall_pos_le_add
    intro ε hε
    let C := ‖F.comp K.mkQL‖
    have hC : 0 ≤ C := norm_nonneg _
    obtain ⟨x,hx,hxn⟩ := Submodule.Quotient.norm_mk_lt q (show 0 < ε/(C+1) by positivity)
    have hb := (F.comp K.mkQL).le_opNorm x
    change ‖F (Submodule.Quotient.mk x)‖ ≤ C*‖x‖ at hb
    rw [hx] at hb
    have hd : C*(ε/(C+1)) ≤ ε := by
      rw [← mul_div_assoc,div_le_iff₀ (by positivity)]
      nlinarith
    calc
      ‖F q‖ ≤ C*‖x‖ := hb
      _ ≤ C*(‖q‖+ε/(C+1)) := mul_le_mul_of_nonneg_left hxn.le hC
      _ ≤ C*‖q‖+ε := by nlinarith

 

def quotientDual (S : Submodule ℂ (WeakDual ℂ X))
    (hS : IsClosed (S : Set (WeakDual ℂ X))) :
    StrongDual ℂ (X ⧸ preannihilator S) →ₗᵢ[ℂ] strong S where
  toFun F := ⟨F.comp (preannihilator S).mkQL,by
    rw [mem_strong,mem_iff_annihilates S hS]
    intro z hz
    change F (Submodule.Quotient.mk z)=0
    rw [(Submodule.Quotient.mk_eq_zero (preannihilator S)).mpr hz,map_zero]⟩
  map_add' F G := by ext z; rfl
  map_smul' c F := by ext z; rfl
  norm_map' F := quotient_dual_norm (preannihilator S) F

lemma quotientDual_surjective (S : Submodule ℂ (WeakDual ℂ X))
    (hS : IsClosed (S : Set (WeakDual ℂ X))) :
    Function.Surjective (quotientDual S hS) := by
  intro f
  have hk : preannihilator S ≤ f.val.ker := by
    intro z hz
    exact hz (StrongDual.toWeakDual f.val) ((mem_strong S f.val).mp f.property)
  refine ⟨(preannihilator S).liftQL f.val hk,?_⟩
  apply Subtype.ext
  ext z
  rfl

 

def quotientDualEquiv (S : Submodule ℂ (WeakDual ℂ X))
    (hS : IsClosed (S : Set (WeakDual ℂ X))) :
    StrongDual ℂ (X ⧸ preannihilator S) ≃ₗᵢ[ℂ] strong S :=
  { LinearEquiv.ofBijective (quotientDual S hS).toLinearMap
      ⟨by
        intro a b hab
        ext q
        obtain ⟨z,rfl⟩ := (preannihilator S).mkQ_surjective q
        exact congrArg (fun f : strong S => f.val z) hab,
       quotientDual_surjective S hS⟩ with
    norm_map' := (quotientDual S hS).norm_map }

end WeakSubspace
end BoundedHochschild

 

open Filter Topology
open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_NormalMultiplication
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Preadjoints for left and right multiplication. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open Filter Topology
namespace HochschildSakai
open BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

 
def leftMatrixFunctional (z : X) (b : M) : StrongDual ℂ (StrongDual ℂ X) :=
  let L : StrongDual ℂ X →ₗ[ℂ] ℂ :=
    { toFun := fun f => e.symm (star b*e f) z
      map_add' := by intro f g; simp [mul_add]
      map_smul' := by intro r f; simp [map_smulₛₗ] }
  L.mkContinuous (‖b‖*‖z‖) (by
    intro f
    change ‖e.symm (star b*e f) z‖ ≤ _
    calc
      _ ≤ ‖e.symm (star b*e f)‖*‖z‖ := (e.symm (star b*e f)).le_opNorm z
      _ = ‖star b*e f‖*‖z‖ := by rw [e.symm.norm_map]
      _ ≤ (‖star b‖*‖e f‖)*‖z‖ := by gcongr; exact norm_mul_le _ _
      _ = (‖b‖*‖z‖)*‖f‖ := by rw [norm_star,e.norm_map]; ring)

lemma leftMatrixFunctional_apply (z : X) (b : M) (f : StrongDual ℂ X) :
    leftMatrixFunctional e z b f=e.symm (star b*e f) z := rfl

lemma leftMatrixFunctional_norm (z : X) (b : M) :
    ‖leftMatrixFunctional e z b‖ ≤ ‖z‖*‖b‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg z) (norm_nonneg b))
  intro f
  rw [leftMatrixFunctional_apply]
  calc
    _ ≤ ‖e.symm (star b*e f)‖*‖z‖ := (e.symm (star b*e f)).le_opNorm z
    _ = ‖star b*e f‖*‖z‖ := by rw [e.symm.norm_map]
    _ ≤ (‖star b‖*‖e f‖)*‖z‖ := by gcongr; exact norm_mul_le _ _
    _ = (‖z‖*‖b‖)*‖f‖ := by rw [norm_star,e.norm_map]; ring

def starLeftMatrixMap (z : X) : M →L[ℂ] StrongDual ℂ (StrongDual ℂ X) := by
  let : NormedAddCommGroup (StrongDual ℂ X) := inferInstance
  let : NormedSpace ℂ (StrongDual ℂ X) := inferInstance
  let : NormedAddCommGroup (StrongDual ℂ (StrongDual ℂ X)) := inferInstance
  let : NormedSpace ℂ (StrongDual ℂ (StrongDual ℂ X)) := inferInstance
  let K : M →ₗ[ℂ] StrongDual ℂ (StrongDual ℂ X) :=
    { toFun := leftMatrixFunctional e z
      map_add' := by
        intro b c
        ext f
        simp only [leftMatrixFunctional_apply,star_add,add_mul,map_add,
          add_apply]
      map_smul' := by
        intro r b
        ext f
        simp only [leftMatrixFunctional_apply,star_smul,smul_mul_assoc,map_smulₛₗ,
          smul_apply,RingHom.id_apply,starRingEnd_apply,
          star_star] }
  exact K.mkContinuous ‖z‖ (leftMatrixFunctional_norm e z)

end HochschildSakai

 

open Filter Topology
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_NormalVectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal vectors and projections for Hilbert-space representations. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
namespace HochschildNormalPart
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

 

def predualEmbedding : X →ₗᵢ⋆[ℂ] StrongDual ℂ M where
  toFun z := (starL ℂ).toContinuousLinearMap.comp (((ContinuousLinearMap.apply ℂ ℂ) z).comp
    e.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  map_add' z w := by ext a; simp
  map_smul' r z := by ext a; simp
  norm_map' z := by
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro a
      change ‖star (e.symm a z)‖ ≤ ‖z‖*‖a‖
      simpa only [norm_star,e.symm.norm_map,mul_comm] using (e.symm a).le_opNorm z
    · apply NormedSpace.norm_le_dual_bound ℂ z (norm_nonneg _)
      intro f
      have := ((starL ℂ).toContinuousLinearMap.comp (((ContinuousLinearMap.apply ℂ ℂ) z).comp
        e.symm.toContinuousLinearEquiv.toContinuousLinearMap)).le_opNorm (e f)
      change ‖f z‖ ≤ ‖(starL ℂ).toContinuousLinearMap.comp
        (((ContinuousLinearMap.apply ℂ ℂ) z).comp
        e.symm.toContinuousLinearEquiv.toContinuousLinearMap)‖ * ‖f‖
      simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,
        ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        starL_apply,e.symm_apply_apply,norm_star,e.norm_map] using this

@[simp] lemma predualEmbedding_apply (z : X) (a : M) :
    predualEmbedding e z a=star (e.symm a z) := rfl

 
def normalDual : Submodule ℂ (StrongDual ℂ M) := (predualEmbedding e).toLinearMap.range

lemma mem_normalDual (φ : StrongDual ℂ M) :
    φ ∈ normalDual e ↔ ∃ z : X, ∀ a : M, φ a=star (e.symm a z) := by
  constructor
  · rintro ⟨z,rfl⟩; exact ⟨z,fun _ => rfl⟩
  · rintro ⟨z,hz⟩; exact ⟨z,ContinuousLinearMap.ext (fun a => (hz a).symm)⟩

variable [CompleteSpace X]

lemma normalDual_closed : IsClosed (normalDual e : Set (StrongDual ℂ M)) :=
  (predualEmbedding e).isometry.isClosedEmbedding.isClosed_range

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (π : M →⋆ₐ[ℂ] (H →L[ℂ] H))

 
def coefficient (η : H) : H →L[ℂ] StrongDual ℂ M := by
  let L : H →ₗ[ℂ] StrongDual ℂ M :=
    { toFun := fun ξ => (innerSL ℂ η).comp
        (((ContinuousLinearMap.apply ℂ H) ξ).comp (π.toAlgHom.toLinearMap.mkContinuous 1 (fun a => by simpa using NonUnitalStarAlgHom.norm_apply_le π a)))
      map_add' := by intro ξ ζ; ext a; simp
      map_smul' := by intro r ξ; ext a; simp }
  exact L.mkContinuous ‖η‖ (by
    intro ξ
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    intro a
    change ‖⟪η,π a ξ⟫_ℂ‖ ≤ (‖η‖*‖ξ‖)*‖a‖
    calc
      _ ≤ ‖η‖*‖π a ξ‖ := norm_inner_le_norm _ _
      _ ≤ ‖η‖*(‖π a‖*‖ξ‖) := mul_le_mul_of_nonneg_left ((π a).le_opNorm ξ) (norm_nonneg _)
      _ ≤ ‖η‖*(‖a‖*‖ξ‖) := by gcongr; exact NonUnitalStarAlgHom.norm_apply_le π a
      _ = _ := by ring)

@[simp] lemma coefficient_apply (η ξ : H) (a : M) :
    coefficient π η ξ a=⟪η,π a ξ⟫_ℂ := rfl

lemma coefficient_norm (η ξ : H) : ‖coefficient π η ξ‖ ≤ ‖η‖*‖ξ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro a
  calc
    _ ≤ ‖η‖*‖π a ξ‖ := norm_inner_le_norm _ _
    _ ≤ ‖η‖*(‖π a‖*‖ξ‖) := by gcongr; exact (π a).le_opNorm ξ
    _ ≤ ‖η‖*(‖a‖*‖ξ‖) := by gcongr; exact NonUnitalStarAlgHom.norm_apply_le π a
    _ = _ := by ring

 
def normalVectors : Submodule ℂ H := ⨅ η : H, (normalDual e).comap (coefficient π η).toLinearMap

omit [CompleteSpace X] in
lemma mem_normalVectors (ξ : H) :
    ξ ∈ normalVectors e π ↔ ∀ η, coefficient π η ξ ∈ normalDual e := by
  simp only [normalVectors,Submodule.mem_iInf,Submodule.mem_comap,ContinuousLinearMap.coe_coe]

lemma normalVectors_closed : IsClosed (normalVectors e π : Set H) := by
  have hs : (normalVectors e π : Set H)=⋂ η : H, (coefficient π η) ⁻¹' (normalDual e : Set (StrongDual ℂ M)) := by
    ext ξ; simp only [Set.mem_iInter,Set.mem_preimage,SetLike.mem_coe,mem_normalVectors]
  rw [hs]
  exact isClosed_iInter fun η => (normalDual_closed e).preimage (coefficient π η).continuous

instance normalVectors_complete : CompleteSpace (normalVectors e π) :=
  (normalVectors_closed e π).completeSpace_coe

omit [CompleteSpace X] in
lemma normalVectors_commutant {ξ : H} (hξ : ξ ∈ normalVectors e π)
    (T : H →L[ℂ] H) (hT : ∀ a : M, T * π a=π a*T) :
    T ξ ∈ normalVectors e π := by
  rw [mem_normalVectors] at hξ ⊢
  intro η
  have hc : coefficient π η (T ξ)=coefficient π (star T η) ξ := by
    ext a
    change ⟪η,π a (T ξ)⟫_ℂ=⟪T.adjoint η,π a ξ⟫_ℂ
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact congrArg (inner ℂ η) (congrArg (fun S : H →L[ℂ] H => S ξ) (hT a).symm)
  rw [hc]
  exact hξ _

 

lemma projection_commutes (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (T : H →L[ℂ] H)
    (hT : ∀ ξ ∈ K, T ξ ∈ K) (hTstar : ∀ ξ ∈ K, star T ξ ∈ K) :
    K.starProjection*T=T*K.starProjection := by
  ext ξ
  change K.starProjection (T ξ)=T (K.starProjection ξ)
  apply Submodule.eq_starProjection_of_mem_orthogonal (hT _ (by simp))
  intro η hη
  change ⟪η,T ξ-T (K.starProjection ξ)⟫_ℂ=0
  rw [← map_sub]
  rw [← ContinuousLinearMap.adjoint_inner_left]
  exact K.sub_starProjection_mem_orthogonal ξ _ (hTstar η hη)

 
def normalProjection : H →L[ℂ] H := (normalVectors e π).starProjection

lemma normalProjection_commutant (T : H →L[ℂ] H)
    (hT : ∀ a : M, T*π a=π a*T) :
    normalProjection e π*T=T*normalProjection e π := by
  apply projection_commutes
  · intro ξ hξ; exact normalVectors_commutant e π hξ T hT
  · intro ξ hξ
    apply normalVectors_commutant e π hξ
    intro a
    have h := congrArg star (hT (star a))
    simpa only [star_mul,← map_star,star_star] using h.symm

 
def coefficientLeft (ξ : H) : H →L⋆[ℂ] StrongDual ℂ M := by
  let L : H →ₗ⋆[ℂ] StrongDual ℂ M :=
    { toFun := fun η => coefficient π η ξ
      map_add' := by intro η ζ; ext a; simp
      map_smul' := by intro r η; ext a; simp [mul_comm] }
  exact L.mkContinuous ‖ξ‖ (fun η => by
    change ‖coefficient π η ξ‖ ≤ ‖ξ‖*‖η‖
    simpa only [mul_comm] using coefficient_norm π η ξ)

@[simp] lemma coefficientLeft_apply (ξ η : H) :
    coefficientLeft π ξ η=coefficient π η ξ := rfl

 
def cyclicSpace (ξ : H) : Submodule ℂ H :=
  (Submodule.span ℂ (Set.range fun a : M => π a ξ)).topologicalClosure

lemma cyclicSpace_closed (ξ : H) : IsClosed (cyclicSpace π ξ : Set H) :=
  Submodule.isClosed_topologicalClosure _

instance cyclicSpace_complete (ξ : H) : CompleteSpace (cyclicSpace π ξ) :=
  (cyclicSpace_closed π ξ).completeSpace_coe

lemma cyclicSpace_mem (ξ : H) : ξ ∈ cyclicSpace π ξ := by
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  exact ⟨1,by simp⟩

lemma cyclicSpace_mul (ξ : H) (b : M) {ζ : H} (hζ : ζ ∈ cyclicSpace π ξ) :
    π b ζ ∈ cyclicSpace π ξ := by
  let S := cyclicSpace π ξ
  have hle : (Submodule.span ℂ (Set.range fun a : M => π a ξ)).topologicalClosure ≤
      S.comap (π b).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨a,rfl⟩
      change π b (π a ξ) ∈ S
      change π b (π a ξ) ∈ (Submodule.span ℂ (Set.range fun a : M => π a ξ)).topologicalClosure
      apply Submodule.le_topologicalClosure
      rw [← mul_apply_eq_comp,← map_mul]
      exact Submodule.subset_span (Set.mem_range_self (b*a))
    · exact (cyclicSpace_closed π ξ).preimage (π b).continuous
  exact hle hζ

lemma cyclicProjection_mul (ξ : H) (a : M) :
    (cyclicSpace π ξ).starProjection*π a=π a*(cyclicSpace π ξ).starProjection := by
  apply projection_commutes
  · intro ζ hζ; exact cyclicSpace_mul π ξ a hζ
  · intro ζ hζ
    rw [← map_star]
    exact cyclicSpace_mul π ξ (star a) hζ



end HochschildNormalPart

 

open scoped InnerProductSpace
namespace HochschildNormalPart
universe u v w
variable {M : Type u} [CStarAlgebra M]
variable {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

 
def sumOperator (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
    WithLp 2 (H × K) →L[ℂ] WithLp 2 (H × K) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H K).symm.toContinuousLinearMap.comp
    ((T.prodMap S).comp (WithLp.prodContinuousLinearEquiv 2 ℂ H K).toContinuousLinearMap)

omit [CompleteSpace H] [CompleteSpace K] in
@[simp] lemma sumOperator_apply (T : H →L[ℂ] H) (S : K →L[ℂ] K) (x : WithLp 2 (H×K)) :
    sumOperator T S x=WithLp.toLp 2 (T x.fst,S x.snd) := rfl

 
def sumRepresentation (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : M →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    M →⋆ₐ[ℂ] (WithLp 2 (H×K) →L[ℂ] WithLp 2 (H×K)) where
  toFun a := sumOperator (π a) (ρ a)
  map_zero' := by ext x; simp
  map_one' := by ext x; simp; rfl
  map_add' a b := by ext x; simp; rfl
  map_mul' a b := by ext x; simp [map_mul,mul_apply_eq_comp]
  commutes' c := by ext x; simp [Algebra.algebraMap_eq_smul_one]; rfl
  map_star' a := by
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro x y
    simp only [sumOperator_apply,WithLp.prod_inner_apply,
      map_star,ContinuousLinearMap.star_eq_adjoint]
    simp only [ContinuousLinearMap.adjoint_inner_left]
    rfl

@[simp] lemma sumRepresentation_apply (π : M →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ρ : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (a : M) (x : WithLp 2 (H×K)) :
    sumRepresentation π ρ a x=WithLp.toLp 2 (π a x.fst,ρ a x.snd) := rfl

lemma coefficient_sum (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (η ξ : WithLp 2 (H×K)) :
    coefficient (sumRepresentation π ρ) η ξ=
      coefficient π η.fst ξ.fst+coefficient ρ η.snd ξ.snd := by
  ext a; rfl

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
  (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : M →⋆ₐ[ℂ] (K →L[ℂ] K))

omit [CompleteSpace X] in
lemma mem_normalVectors_sum (ξ : WithLp 2 (H×K)) :
    ξ ∈ normalVectors e (sumRepresentation π ρ) ↔
      ξ.fst ∈ normalVectors e π ∧ ξ.snd ∈ normalVectors e ρ := by
  simp only [mem_normalVectors,coefficient_sum]
  constructor
  · intro h
    constructor
    · intro η
      have h' := h (WithLp.toLp 2 (η,0))
      change coefficient π η ξ.fst+coefficient ρ 0 ξ.snd ∈ normalDual e at h'
      have hz : coefficient ρ 0 ξ.snd=0 := by ext a; simp
      simpa only [hz,add_zero] using h'
    · intro η
      have h' := h (WithLp.toLp 2 (0,η))
      change coefficient π 0 ξ.fst+coefficient ρ η ξ.snd ∈ normalDual e at h'
      have hz : coefficient π 0 ξ.fst=0 := by ext a; simp
      simpa only [hz,zero_add] using h'
  · rintro ⟨hπ,hρ⟩ η
    exact (normalDual e).add_mem (hπ η.fst) (hρ η.snd)

 
lemma normalProjection_sum (ξ : WithLp 2 (H×K)) :
    normalProjection e (sumRepresentation π ρ) ξ=
      WithLp.toLp 2 (normalProjection e π ξ.fst,normalProjection e ρ ξ.snd) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · rw [mem_normalVectors_sum]
    change normalProjection e π ξ.fst ∈ normalVectors e π ∧
      normalProjection e ρ ξ.snd ∈ normalVectors e ρ
    exact ⟨by simp [normalProjection],by simp [normalProjection]⟩
  · intro η hη
    obtain ⟨hη₁,hη₂⟩ := (mem_normalVectors_sum e π ρ η).mp hη
    change ⟪η,ξ-WithLp.toLp 2 (normalProjection e π ξ.fst,normalProjection e ρ ξ.snd)⟫_ℂ=0
    change ⟪η.fst,ξ.fst-normalProjection e π ξ.fst⟫_ℂ+
      ⟪η.snd,ξ.snd-normalProjection e ρ ξ.snd⟫_ℂ=0
    unfold normalProjection
    rw [(normalVectors e π).sub_starProjection_mem_orthogonal ξ.fst η.fst hη₁,
      (normalVectors e ρ).sub_starProjection_mem_orthogonal ξ.snd η.snd hη₂,add_zero]



end HochschildNormalPart
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PositiveDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Decomposition of continuous functionals into positive functionals. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
namespace HochschildPositiveDecomposition
universe u
variable {M : Type u} [CStarAlgebra M]

 
lemma norm_pair_shift [Nontrivial M] (a : selfAdjoint M) (t : ℝ) :
    ‖a‖ + |t| ≤ ‖(a + t • (1 : selfAdjoint M), -a + t • (1 : selfAdjoint M))‖ := by
  let C := ‖(a + t • (1 : selfAdjoint M), -a + t • (1 : selfAdjoint M))‖
  have h₁ : ‖(a : M) + algebraMap ℝ M t‖ ≤ C := by
    rw [Algebra.algebraMap_eq_smul_one]
    change ‖(a : M) + t • (1:M)‖ ≤ max ‖(a : M)+t • (1:M)‖ ‖-(a : M)+t • (1:M)‖
    exact le_max_left _ _
  have h₂ : ‖-(a : M) + algebraMap ℝ M t‖ ≤ C := by
    rw [Algebra.algebraMap_eq_smul_one]
    change ‖-(a : M) + t • (1:M)‖ ≤ max ‖(a : M)+t • (1:M)‖ ‖-(a : M)+t • (1:M)‖
    exact le_max_right _ _
  have hs (r : ℝ) (hr : r ∈ spectrum ℝ (a : M)) : |r+t| ≤ C ∧ |-r+t| ≤ C := by
    constructor
    · have h := spectrum.norm_le_norm_of_mem (spectrum.add_mem_add_iff.mpr hr : r+t ∈ spectrum ℝ (algebraMap ℝ M t+(a : M)))
      exact h.trans (by simpa [add_comm] using h₁)
    · have hn : -r ∈ spectrum ℝ (-(a : M)) := by rw [← spectrum.neg_eq]; exact Set.neg_mem_neg.mpr hr
      have h := spectrum.norm_le_norm_of_mem (spectrum.add_mem_add_iff.mpr hn : -r+t ∈ spectrum ℝ (algebraMap ℝ M t+ -(a : M)))
      exact h.trans (by simpa [sub_eq_add_neg,add_comm] using h₂)
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum a.property with ha|ha
  · obtain ⟨h₁,h₂⟩ := hs ‖a‖ ha
    rcases le_total 0 t with ht|ht
    · rw [abs_of_nonneg ht]; linarith [le_abs_self (‖a‖+t)]
    · rw [abs_of_nonpos ht]; linarith [neg_le_abs (-‖a‖+t)]
  · obtain ⟨h₁,h₂⟩ := hs (-‖a‖) ha
    rcases le_total 0 t with ht|ht
    · rw [abs_of_nonneg ht]; linarith [le_abs_self (-(-‖a‖)+t)]
    · rw [abs_of_nonpos ht]; linarith [neg_le_abs (-‖a‖+t)]

def shiftEmbedding : selfAdjoint M × ℝ →ₗ[ℝ] selfAdjoint M × selfAdjoint M where
  toFun p := (p.1+p.2 • 1,-p.1+p.2 • 1)
  map_add' p q := by ext <;> simp <;> module
  map_smul' r p := by ext <;> simp <;> module

lemma shiftEmbedding_injective [Nontrivial M] : Function.Injective (shiftEmbedding (M := M)) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro p hp
  have h := norm_pair_shift p.1 p.2
  have he : shiftEmbedding p=0 := hp
  change ‖p.1‖+|p.2|≤‖shiftEmbedding p‖ at h
  rw [he,norm_zero] at h
  have hp₁ : p.1=0 := norm_eq_zero.mp (by linarith [norm_nonneg p.1,abs_nonneg p.2])
  have hp₂ : p.2=0 := abs_eq_zero.mp (by linarith [norm_nonneg p.1,abs_nonneg p.2])
  exact Prod.ext hp₁ hp₂

 
lemma exists_pair_extension [Nontrivial M] (l : StrongDual ℝ (selfAdjoint M)) :
    ∃ g : StrongDual ℝ (selfAdjoint M × selfAdjoint M),
      ‖g‖ ≤ ‖l‖ ∧ g (1,1)=‖l‖ ∧ ∀ a, g (a,-a)=l a := by
  let j := LinearEquiv.ofInjective (shiftEmbedding (M := M)) shiftEmbedding_injective
  let L : selfAdjoint M × ℝ →ₗ[ℝ] ℝ := l.toLinearMap.coprod (‖l‖ • LinearMap.id)
  let L' := L.comp j.symm.toLinearMap
  have hbound (p : (shiftEmbedding (M := M)).range) : ‖L' p‖ ≤ ‖l‖*‖p‖ := by
    obtain ⟨q,rfl⟩ := j.surjective p
    change ‖L (j.symm (j q))‖ ≤ ‖l‖*‖shiftEmbedding q‖
    rw [j.symm_apply_apply]
    change ‖l q.1+‖l‖*q.2‖ ≤ ‖l‖*‖shiftEmbedding q‖
    calc
      _ ≤ ‖l q.1‖+‖‖l‖*q.2‖ := norm_add_le _ _
      _ ≤ ‖l‖*‖q.1‖+‖l‖*|q.2| := by simpa [abs_of_nonneg (norm_nonneg l)] using add_le_add (l.le_opNorm q.1) (le_refl ‖‖l‖*q.2‖)
      _ = ‖l‖*(‖q.1‖+|q.2|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (norm_pair_shift q.1 q.2) (norm_nonneg l)
  let F := L'.mkContinuous ‖l‖ hbound
  obtain ⟨g,hg,hgn⟩ := exists_extension_norm_eq (shiftEmbedding (M := M)).range F
  refine ⟨g,?_,?_,?_⟩
  · rw [hgn]; exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg l) hbound
  · have h := hg (j (0,1))
    change g (shiftEmbedding (0,1))=L (j.symm (j (0,1))) at h
    rw [j.symm_apply_apply] at h
    simpa [L,shiftEmbedding] using h
  · intro a
    have h := hg (j (a,0))
    change g (shiftEmbedding (a,0))=L (j.symm (j (a,0))) at h
    rw [j.symm_apply_apply] at h
    simpa [L,shiftEmbedding] using h

section Ordered
variable [PartialOrder M] [StarOrderedRing M]

lemma norm_orderUnit_sub (a : selfAdjoint M) (ha : 0≤(a:M)) {r : ℝ}
    (hr : 0 ≤ r) (har : ‖a‖ ≤ r) : ‖r • (1:selfAdjoint M)-a‖ ≤ r := by
  change ‖r • (1:M)-(a:M)‖ ≤ r
  have hle : (a:M)≤algebraMap ℝ M r := by
    exact (CStarAlgebra.norm_le_iff_le_algebraMap (a:M) hr ha).mp har
  rw [Algebra.algebraMap_eq_smul_one] at hle
  exact (CStarAlgebra.norm_le_iff_le_algebraMap _ hr (sub_nonneg.mpr hle)).mpr (by
    rw [Algebra.algebraMap_eq_smul_one]
    exact sub_le_self _ ha)

 

lemma pair_nonneg (g : StrongDual ℝ (selfAdjoint M × selfAdjoint M)) {C : ℝ}
    (hC : 0≤C) (hgn : ‖g‖≤C) (hg1 : g (1,1)=C)
    (a b : selfAdjoint M) (ha : 0≤(a:M)) (hb : 0≤(b:M)) : 0≤g (a,b) := by
  let r := ‖(a,b)‖
  have hr : 0 ≤ r := norm_nonneg _
  have hn : ‖r • (1,1)-(a,b)‖ ≤ r := by
    change max ‖r • (1:selfAdjoint M)-a‖ ‖r • (1:selfAdjoint M)-b‖ ≤ r
    exact max_le (norm_orderUnit_sub a ha hr (le_max_left _ _))
      (norm_orderUnit_sub b hb hr (le_max_right _ _))
  have h := (le_abs_self (g (r • (1,1)-(a,b)))).trans
    ((g.le_opNorm _).trans (mul_le_mul hgn hn (norm_nonneg _) hC))
  rw [map_sub,map_smul,hg1] at h
  change r*C-g (a,b)≤C*r at h
  nlinarith

 

lemma exists_real_positive_difference [Nontrivial M] (l : StrongDual ℝ (selfAdjoint M)) :
    ∃ p q : StrongDual ℝ (selfAdjoint M),
      (∀ a : selfAdjoint M, 0≤(a:M) → 0≤p a) ∧ (∀ a : selfAdjoint M, 0≤(a:M) → 0≤q a) ∧
      (∀ a, l a=p a-q a) ∧ p 1≤‖l‖ ∧ q 1≤‖l‖ := by
  obtain ⟨g,hgn,hg1,hgl⟩ := exists_pair_extension l
  let p := g.comp (ContinuousLinearMap.inl ℝ (selfAdjoint M) (selfAdjoint M))
  let q := g.comp (ContinuousLinearMap.inr ℝ (selfAdjoint M) (selfAdjoint M))
  refine ⟨p,q,?_,?_,?_,?_,?_⟩
  · intro a ha; exact pair_nonneg g (norm_nonneg l) hgn hg1 a 0 ha (by simp)
  · intro a ha; exact pair_nonneg g (norm_nonneg l) hgn hg1 0 a (by simp) ha
  · intro a
    rw [← hgl]
    change g (a,-a)=g (a,0)-g (0,a)
    rw [← map_sub]; congr 1; simp
  · have h := (le_abs_self (g (1,0))).trans (g.le_opNorm (1,0))
    have hn : ‖((1:selfAdjoint M), (0:selfAdjoint M))‖≤1 := by
      change max ‖(1:M)‖ ‖(0:M)‖≤1
      simp
    exact h.trans ((mul_le_mul_of_nonneg_left hn (norm_nonneg g)).trans (by simpa using hgn))
  · have h := (le_abs_self (g (0,1))).trans (g.le_opNorm (0,1))
    have hn : ‖((0:selfAdjoint M), (1:selfAdjoint M))‖≤1 := by
      change max ‖(0:M)‖ ‖(1:M)‖≤1
      simp
    exact h.trans ((mul_le_mul_of_nonneg_left hn (norm_nonneg g)).trans (by simpa using hgn))

end Ordered

 
def complexify (l : selfAdjoint M →ₗ[ℝ] ℝ) : M →ₗ[ℂ] ℂ where
  toFun a := (l (ℜ a):ℂ)+Complex.I*(l (ℑ a):ℂ)
  map_add' a b := by simp; ring
  map_smul' c a := by
    apply Complex.ext <;> simp [realPart_smul,imaginaryPart_smul]

@[simp] lemma complexify_apply (l : selfAdjoint M →ₗ[ℝ] ℝ) (a : M) :
    complexify l a=(l (ℜ a):ℂ)+Complex.I*(l (ℑ a):ℂ) := rfl

@[simp] lemma complexify_selfAdjoint (l : selfAdjoint M →ₗ[ℝ] ℝ) (a : selfAdjoint M) :
    complexify l (a:M)=(l a:ℂ) := by
  have h : ℜ (a:M)=a := Subtype.ext a.property.coe_realPart
  simp [h,a.property.imaginaryPart]

section Ordered
variable [PartialOrder M] [StarOrderedRing M]
open scoped ComplexOrder

def complexifyPositive (l : selfAdjoint M →ₗ[ℝ] ℝ)
    (hl : ∀ a : selfAdjoint M,0≤(a:M) → 0≤l a) : M →ₚ[ℂ] ℂ where
  toLinearMap := complexify l
  monotone' := by
    intro a b hab
    change complexify l a ≤ complexify l b
    rw [← sub_nonneg,← map_sub]
    have hp := sub_nonneg.mpr hab
    have hs : IsSelfAdjoint (b-a) := .of_nonneg hp
    have he := complexify_selfAdjoint l ⟨b-a,hs⟩
    rw [he]
    exact_mod_cast hl ⟨b-a,hs⟩ hp

@[simp] lemma complexifyPositive_apply (l : selfAdjoint M →ₗ[ℝ] ℝ)
    (hl : ∀ a : selfAdjoint M,0≤(a:M) → 0≤l a) (a : M) :
    complexifyPositive l hl a=complexify l a := rfl

end Ordered

 
def realRestriction (φ : StrongDual ℂ M) : StrongDual ℝ (selfAdjoint M) :=
  Complex.reCLM.comp ((φ.restrictScalars ℝ).comp (selfAdjoint.submodule ℝ M).subtypeL)

def imagRestriction (φ : StrongDual ℂ M) : StrongDual ℝ (selfAdjoint M) :=
  Complex.imCLM.comp ((φ.restrictScalars ℝ).comp (selfAdjoint.submodule ℝ M).subtypeL)

@[simp] lemma realRestriction_apply (φ : StrongDual ℂ M) (a : selfAdjoint M) :
    realRestriction φ a=(φ (a:M)).re := rfl
@[simp] lemma imagRestriction_apply (φ : StrongDual ℂ M) (a : selfAdjoint M) :
    imagRestriction φ a=(φ (a:M)).im := rfl

lemma realRestriction_norm (φ : StrongDual ℂ M) : ‖realRestriction φ‖≤‖φ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg φ)
  intro a
  exact (Complex.abs_re_le_norm _).trans (φ.le_opNorm (a:M))
lemma imagRestriction_norm (φ : StrongDual ℂ M) : ‖imagRestriction φ‖≤‖φ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg φ)
  intro a
  exact (Complex.abs_im_le_norm _).trans (φ.le_opNorm (a:M))

lemma real_imag_restriction_decomposition (φ : StrongDual ℂ M) (a : M) :
    φ a=complexify (realRestriction φ).toLinearMap a+
      Complex.I*complexify (imagRestriction φ).toLinearMap a := by
  have h := congrArg φ (realPart_add_I_smul_imaginaryPart a)
  rw [map_add,map_smul] at h
  rw [← h]
  simp only [complexify_apply,ContinuousLinearMap.coe_coe,realRestriction_apply,imagRestriction_apply]
  apply Complex.ext <;> simp
  ring

section Ordered
variable [PartialOrder M] [StarOrderedRing M]
open scoped ComplexOrder

 

theorem exists_four_positive (φ : StrongDual ℂ M) :
    ∃ ψ : Fin 4 → (M →ₚ[ℂ] ℂ), (∀ i,‖ψ i 1‖≤‖φ‖) ∧
      ∀ a,φ a=ψ 0 a-ψ 1 a+Complex.I*(ψ 2 a-ψ 3 a) := by
  classical
  obtain hsub|hnontriv := subsingleton_or_nontrivial M
  · refine ⟨0,?_,?_⟩
    · simp
    · intro a; simp [Subsingleton.elim a 0]
  let := hnontriv
  obtain ⟨p,q,hp,hq,hpr,hp1,hq1⟩ := exists_real_positive_difference (realRestriction φ)
  obtain ⟨r,s,hr,hs,hrs,hr1,hs1⟩ := exists_real_positive_difference (imagRestriction φ)
  let P := complexifyPositive p.toLinearMap hp
  let Q := complexifyPositive q.toLinearMap hq
  let R := complexifyPositive r.toLinearMap hr
  let S := complexifyPositive s.toLinearMap hs
  have hn (l : StrongDual ℝ (selfAdjoint M)) (hl : ∀ a : selfAdjoint M,0≤(a:M) → 0≤l a) :
      ‖complexifyPositive l.toLinearMap hl 1‖=l 1 := by
    change ‖complexify l.toLinearMap (1:M)‖=l 1
    have h := complexify_selfAdjoint l.toLinearMap (1:selfAdjoint M)
    change complexify l.toLinearMap (1:M)=(l 1:ℂ) at h
    rw [h,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hl 1 (by simp))]
  refine ⟨![P,Q,R,S],?_,?_⟩
  · intro i
    fin_cases i
    · exact (le_of_eq (hn p hp)).trans (hp1.trans (realRestriction_norm φ))
    · exact (le_of_eq (hn q hq)).trans (hq1.trans (realRestriction_norm φ))
    · exact (le_of_eq (hn r hr)).trans (hr1.trans (imagRestriction_norm φ))
    · exact (le_of_eq (hn s hs)).trans (hs1.trans (imagRestriction_norm φ))
  · intro a
    change φ a=P a-Q a+Complex.I*(R a-S a)
    rw [real_imag_restriction_decomposition φ a]
    simp only [P,Q,R,S,complexifyPositive_apply,complexify_apply,
      ContinuousLinearMap.coe_coe,hpr,hrs,Complex.ofReal_sub]
    ring

end Ordered
end HochschildPositiveDecomposition
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_NormalOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal parts of scalar functionals and bounded operators. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
namespace HochschildNormalPart
universe u
variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

 
def positiveVector (ψ : M →ₚ[ℂ] ℂ) : ψ.GNS := (ψ.toPreGNS 1 : ψ.PreGNS)

lemma positiveVector_coefficient (ψ : M →ₚ[ℂ] ℂ) (a : M) :
    coefficient ψ.gnsStarAlgHom (positiveVector ψ) (positiveVector ψ) a=ψ a := by
  change ⟪(ψ.toPreGNS 1 : ψ.GNS),ψ.gnsNonUnitalStarAlgHom a (ψ.toPreGNS 1)⟫_ℂ=ψ a
  rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe,UniformSpace.Completion.inner_coe]
  simp [PositiveLinearMap.preGNS_inner_def]

lemma positiveVector_norm_sq (ψ : M →ₚ[ℂ] ℂ) : ‖positiveVector ψ‖^2=‖ψ 1‖ := by
  have hv := positiveVector_coefficient ψ (1:M)
  simp only [coefficient_apply,map_one] at hv
  change ⟪positiveVector ψ,positiveVector ψ⟫_ℂ=ψ 1 at hv
  rw [inner_self_eq_norm_sq_to_K] at hv
  rw [← hv,norm_pow]
  simp

abbrev FourHilbert (ψ : Fin 4 → M →ₚ[ℂ] ℂ) :=
  WithLp 2 ((WithLp 2 ((ψ 0).GNS × (ψ 1).GNS)) ×
    (WithLp 2 ((ψ 2).GNS × (ψ 3).GNS)))

def fourRepresentation (ψ : Fin 4 → M →ₚ[ℂ] ℂ) :
    M →⋆ₐ[ℂ] (FourHilbert ψ →L[ℂ] FourHilbert ψ) :=
  sumRepresentation (sumRepresentation (ψ 0).gnsStarAlgHom (ψ 1).gnsStarAlgHom)
    (sumRepresentation (ψ 2).gnsStarAlgHom (ψ 3).gnsStarAlgHom)

def fourLeft (ψ : Fin 4 → M →ₚ[ℂ] ℂ) : FourHilbert ψ :=
  WithLp.toLp 2 (WithLp.toLp 2 (positiveVector (ψ 0),-positiveVector (ψ 1)),
    WithLp.toLp 2 (-Complex.I • positiveVector (ψ 2),Complex.I • positiveVector (ψ 3)))

def fourRight (ψ : Fin 4 → M →ₚ[ℂ] ℂ) : FourHilbert ψ :=
  WithLp.toLp 2 (WithLp.toLp 2 (positiveVector (ψ 0),positiveVector (ψ 1)),
    WithLp.toLp 2 (positiveVector (ψ 2),positiveVector (ψ 3)))

lemma four_coefficient (ψ : Fin 4 → M →ₚ[ℂ] ℂ) (a : M) :
    coefficient (fourRepresentation ψ) (fourLeft ψ) (fourRight ψ) a=
      ψ 0 a-ψ 1 a+Complex.I*(ψ 2 a-ψ 3 a) := by
  rw [fourRepresentation,coefficient_sum,add_apply]
  simp only [fourLeft,fourRight,WithLp.toLp_fst,WithLp.toLp_snd,coefficient_sum,
    add_apply,coefficient_apply,inner_neg_left,inner_smul_left]
  simp only [← coefficient_apply,positiveVector_coefficient,map_neg,Complex.conj_I]
  ring

lemma four_norm_bound (φ : StrongDual ℂ M) (ψ : Fin 4 → M →ₚ[ℂ] ℂ)
    (hψ : ∀ i,‖ψ i 1‖≤‖φ‖) : ‖fourLeft ψ‖*‖fourRight ψ‖≤4*‖φ‖ := by
  have hr : ‖fourRight ψ‖^2=‖ψ 0 1‖+‖ψ 1 1‖+(‖ψ 2 1‖+‖ψ 3 1‖) := by
    simp only [fourRight,WithLp.prod_norm_sq_eq_of_L2,WithLp.toLp_fst,WithLp.toLp_snd,
      positiveVector_norm_sq]
  have hl : ‖fourLeft ψ‖^2=‖fourRight ψ‖^2 := by
    rw [hr]
    simp only [fourLeft,WithLp.prod_norm_sq_eq_of_L2,WithLp.toLp_fst,WithLp.toLp_snd,
      norm_neg,norm_smul,Complex.norm_I,one_mul,positiveVector_norm_sq]
  have he : ‖fourLeft ψ‖=‖fourRight ψ‖ := by nlinarith [norm_nonneg (fourLeft ψ),norm_nonneg (fourRight ψ)]
  rw [he,← sq,hr]
  linarith [hψ 0,hψ 1,hψ 2,hψ 3]

 
structure FunctionalModel (φ : StrongDual ℂ M) where
  H : Type u
  [normed : NormedAddCommGroup H]
  [innerSpace : InnerProductSpace ℂ H]
  [complete : CompleteSpace H]
  representation : M →⋆ₐ[ℂ] (H →L[ℂ] H)
  leftVector : H
  rightVector : H
  realizes : coefficient representation leftVector rightVector=φ
  bound : ‖leftVector‖*‖rightVector‖≤4*‖φ‖
attribute [instance] FunctionalModel.normed FunctionalModel.innerSpace FunctionalModel.complete

lemma functionalModel_nonempty (φ : StrongDual ℂ M) : Nonempty (FunctionalModel φ) := by
  obtain ⟨ψ,hψ,hφ⟩ := HochschildPositiveDecomposition.exists_four_positive φ
  refine ⟨{ H := FourHilbert ψ
            representation := fourRepresentation ψ
            leftVector := fourLeft ψ
            rightVector := fourRight ψ
            realizes := ?_
            bound := four_norm_bound φ ψ hψ }⟩
  ext a
  exact (four_coefficient ψ a).trans (hφ a).symm

end HochschildNormalPart

 

namespace HochschildNormalPart
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def functionalModel (φ : StrongDual ℂ M) : FunctionalModel φ := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  exact Classical.choice (functionalModel_nonempty φ)

 
def normalPartRaw (φ : StrongDual ℂ M) : StrongDual ℂ M :=
  coefficient (functionalModel φ).representation (functionalModel φ).leftVector
    (normalProjection e (functionalModel φ).representation (functionalModel φ).rightVector)

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma normalPartRaw_norm (φ : StrongDual ℂ M) : ‖normalPartRaw e φ‖≤4*‖φ‖ := by
  let m := functionalModel φ
  exact (coefficient_norm _ _ _).trans
    ((mul_le_mul_of_nonneg_left ((normalVectors e m.representation).norm_starProjection_apply_le _)
      (norm_nonneg m.leftVector)).trans m.bound)



end HochschildNormalPart



end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_Dixmier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hilbert-space averaging and central elements in unitary orbit closures. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open Filter Topology
open scoped ComplexOrder
namespace HochschildDixmier
open BoundedHochschild
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
  (τ : M →ₚ[ℂ] ℂ)

def gnsVector : M →ₗ[ℝ] τ.GNS :=
  (UniformSpace.Completion.toComplₗᵢ.toLinearMap.comp τ.toPreGNS.toLinearMap).restrictScalars ℝ

lemma gnsVector_norm (a : M) : ‖gnsVector τ a‖=‖τ.toPreGNS a‖ :=
  UniformSpace.Completion.norm_coe _

def conjugate (u : unitary M) : M →ₗ[ℝ] M where
  toFun a := (u : M)*a*star (u : M)
  map_add' := by intro a b; simp only [mul_add,add_mul]
  map_smul' := by intro r a; simp only [mul_smul_comm,smul_mul_assoc,RingHom.id_apply]

omit [PartialOrder M] [StarOrderedRing M] in
lemma conjugate_apply (u : unitary M) (a : M) :
    conjugate u a=(u : M)*a*star (u : M) := rfl

omit [PartialOrder M] [StarOrderedRing M] in
lemma conjugate_norm (u : unitary M) (a : M) : ‖conjugate u a‖=‖a‖ := by
  change ‖(u : M)*a*(star u : unitary M)‖=‖a‖
  rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul]

omit [PartialOrder M] [StarOrderedRing M] in
lemma conjugate_mul (u v : unitary M) (a : M) : conjugate u (conjugate v a)=conjugate (u*v) a := by
  simp only [conjugate_apply,Submonoid.coe_mul,star_mul,mul_assoc]

lemma conjugate_gns_norm (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (u : unitary M) (a : M) :
    ‖gnsVector τ (conjugate u a)‖=‖gnsVector τ a‖ := by
  rw [gnsVector_norm,gnsVector_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  apply Complex.ofReal_injective
  rw [Complex.ofReal_pow,Complex.ofReal_pow,τ.preGNS_norm_sq,τ.preGNS_norm_sq]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS,conjugate_apply,star_mul,star_star]
  have he : (u : M)*(star a*star (u : M))*((u : M)*a*star (u : M))=
      (u : M)*(star a*a)*star (u : M) := by
    calc
      _ = (u : M)*(star a*((star (u : M)*(u : M))*a))*star (u : M) := by noncomm_ring
      _ = _ := by rw [Unitary.star_mul_self_of_mem u.prop,one_mul]
  rw [he,htr,← mul_assoc,Unitary.star_mul_self_of_mem u.prop,one_mul]

omit [PartialOrder M] [StarOrderedRing M] in
lemma conjugate_hull (a : M) (u : unitary M) :
    conjugate u '' convexHull ℝ (Set.range (fun v : unitary M => conjugate v a)) ⊆
      convexHull ℝ (Set.range (fun v : unitary M => conjugate v a)) := by
  rw [LinearMap.image_convexHull]
  apply convexHull_mono
  rintro _ ⟨_,⟨v,rfl⟩,rfl⟩
  exact ⟨u*v,(conjugate_mul u v a).symm⟩

omit [PartialOrder M] [StarOrderedRing M] in
lemma orbit_hull_bounded (a : M) :
    convexHull ℝ (Set.range (fun v : unitary M => conjugate v a)) ⊆
      Metric.closedBall (0 : M) ‖a‖ := by
  apply convexHull_min _ (convex_closedBall _ _)
  rintro _ ⟨v,rfl⟩
  simp only [Metric.mem_closedBall,dist_zero_right,conjugate_norm,le_refl]

lemma conjugate_mem_orbit_closure (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (a b : M)
    (hb : gnsVector τ b ∈ closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun v : unitary M => conjugate v a)))) (u : unitary M) :
    gnsVector τ (conjugate u b) ∈ closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun v : unitary M => conjugate v a))) := by
  obtain ⟨y,hy,hyt⟩ := mem_closure_iff_seq_limit.mp hb
  choose c hc hcy using hy
  have ht : Tendsto (fun n => gnsVector τ (conjugate u (c n))) atTop
      (𝓝 (gnsVector τ (conjugate u b))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [← map_sub,conjugate_gns_norm τ htr]
    have hh := (tendsto_iff_norm_sub_tendsto_zero.mp hyt)
    simpa only [← hcy,← map_sub] using hh
  apply isClosed_closure.mem_of_tendsto ht
  exact Filter.Eventually.of_forall fun n => subset_closure
    ⟨conjugate u (c n),conjugate_hull a u ⟨c n,hc n,rfl⟩,rfl⟩

lemma orbit_gns_convex (a : M) :
    Convex ℝ (closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun v : unitary M => conjugate v a)))) := by
  exact ((convex_convexHull ℝ _).linear_image (gnsVector τ)).closure

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma exists_min_norm {K : Set H} (hne : K.Nonempty) (hcl : IsClosed K) (hc : Convex ℝ K) :
    ∃ z ∈ K, ∀ w ∈ K, ‖z‖ ≤ ‖w‖ := by
  obtain ⟨z,hz,hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hc 0
  refine ⟨z,hz,fun w hw => ?_⟩
  simp only [zero_sub,norm_neg] at hmin
  rw [hmin]
  apply ciInf_le (f := fun w : K => ‖(w : H)‖) _ ⟨w,hw⟩
  exact ⟨(0 : ℝ),by rintro _ ⟨v,rfl⟩; exact norm_nonneg _⟩

omit [CompleteSpace H] in
lemma min_norm_unique {K : Set H} (hc : Convex ℝ K) {z w : H} (hz : z ∈ K) (hw : w ∈ K)
    (hmin : ∀ y ∈ K, ‖z‖ ≤ ‖y‖) (he : ‖w‖=‖z‖) : w=z := by
  have hm := hmin ((1/2 : ℝ) • z+(1/2 : ℝ) • w)
    (hc hz hw (by norm_num) (by norm_num) (by norm_num))
  rw [← smul_add,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<1/2)] at hm
  have hsq : (2*‖z‖)^2 ≤ ‖z+w‖^2 := by
    apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr
    linarith
  have hp := parallelogram_law_with_norm ℝ z w
  rw [he] at hp
  have hz0 : ‖z-w‖=0 := by nlinarith [sq_nonneg ‖z-w‖,norm_nonneg (z-w)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz0)).symm
end Hilbert

omit [StarOrderedRing M] in
lemma trace_conjugate (htr : ∀ x y : M, τ (x*y)=τ (y*x))
    (u : unitary M) (a : M) : τ (conjugate u a)=τ a := by
  rw [conjugate_apply,htr,← mul_assoc,Unitary.star_mul_self_of_mem u.prop,one_mul]

end HochschildDixmier
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_DiffuseProjections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diffuse projections of prescribed trace and conjugation estimates. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open Filter Topology
open scoped ComplexOrder
namespace HochschildDiffuse
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  (τ : M →ₚ[ℂ] ℂ)



lemma projection_trace_pos (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) : 0 < (τ p).re := by
  have hpos : 0 ≤ τ p := τ.map_nonneg hp.nonneg
  have hre : 0 ≤ (τ p).re := Complex.nonneg_iff.mp hpos |>.1
  apply lt_of_le_of_ne hre
  intro hz
  have he : τ p=0 := Complex.ext hz.symm (Complex.nonneg_iff.mp hpos).2.symm
  apply hp0
  apply hfaith p
  simpa only [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq] using he



end HochschildDiffuse

 

open Filter Topology
open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_WeakAlgebras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak-star algebra closures, inherited traces and generated finite-path primitives. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open Filter Topology
namespace BoundedHochschild
namespace WeakAlgebra
universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def weakEquiv : WeakDual ℂ X ≃ₗ⋆[ℂ] M :=
  WeakDual.toStrongDual.trans e.toLinearEquiv

def linearClosure (A : StarSubalgebra ℂ M) : Submodule ℂ (WeakDual ℂ X) :=
  (A.toSubalgebra.toSubmodule.map (weakEquiv e).symm.toLinearMap).topologicalClosure

end WeakAlgebra
end BoundedHochschild

 

open Filter Topology
open scoped ComplexOrder



open Filter Topology
open scoped ComplexOrder




open Filter Topology
open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_TypeIIStructure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Projection comparison and matrix structure in finite type-II algebras. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace HochschildTypeII
open BoundedHochschild HochschildDiffuse
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
  (τ : M →ₚ[ℂ] ℂ)
  (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

lemma projection_orthogonal_of_le_complement {s c : M}
    (hs : IsStarProjection s) (hc : IsStarProjection c) (hcs : c ≤ 1-s) : s*c=0 := by
  have h := (hc.le_iff_mul_eq_right hs.one_sub).mp hcs
  rw [sub_mul,one_mul] at h
  exact sub_eq_self.mp h

end HochschildTypeII

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_Frames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonal frames of partial isometries and maximal frame construction. -/

noncomputable section

open scoped ComplexOrder
namespace HochschildComparison
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

lemma projection_orthogonal_mono {p q r s : M}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hr : IsStarProjection r) (hs : IsStarProjection s)
    (hpr : p ≤ r) (hqs : q ≤ s) (hrs : r*s=0) : p*q=0 := by
  calc
    p*q = (p*r)*(s*q) := by
      rw [(hp.le_iff_mul_eq_left hr).mp hpr,(hq.le_iff_mul_eq_right hs).mp hqs]
    _ = p*(r*s)*q := by simp only [mul_assoc]
    _ = 0 := by rw [hrs,mul_zero,zero_mul]

end HochschildComparison

open Filter Topology
open scoped ComplexOrder

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_CentralComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Comparison of projections using central weighted traces. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace HochschildCentralComparison
open BoundedHochschild HochschildComparison
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
  (τ : M →ₚ[ℂ] ℂ)
  (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

lemma orthogonal_of_le_sub {p r t : M}
    (hp : IsStarProjection p) (hr : IsStarProjection r) (ht : IsStarProjection t)
    (hrp : r ≤ p) (htr : t ≤ p-r) : r*t=0 := by
  have hpr := (hr.le_iff_sub hp).mp hrp
  have hh := (ht.le_iff_mul_eq_right hpr).mp htr
  calc
    r*t = r*((p-r)*t) := by rw [hh]
    _ = (r*p-r*r)*t := by noncomm_ring
    _ = 0 := by rw [(hr.le_iff_mul_eq_left hp).mp hrp,hr.isIdempotentElem.eq,sub_self,zero_mul]

end HochschildCentralComparison

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_CompactConvexCenter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact nontrivial set has a convex average strictly closer than its diameter. -/

noncomputable section

open Topology

namespace BoundedHochschild
namespace KadisonRingrose

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The elementary normal-structure argument needed for the isometric
fixed-point theorem. -/
theorem compact_convex_center (K : Set E) (hK : IsCompact K) (hnt : K.Nontrivial) :
    ∃ z ∈ convexHull ℝ K, ∃ r : ℝ, r < Metric.diam K ∧
      ∀ y ∈ K, ‖z - y‖ ≤ r := by
  classical
  have hne : K.Nonempty := hnt.nonempty
  have hD : 0 < Metric.diam K := Metric.diam_pos hnt hK.isBounded
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun x : K => Metric.ball x.val (Metric.diam K))
    (fun _ => Metric.isOpen_ball) (fun x hx =>
      Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self hD⟩)
  have hsne : s.Nonempty := by
    obtain ⟨y, hy⟩ := hne
    obtain ⟨x, hxs, _⟩ := Set.mem_iUnion₂.mp (hs hy)
    exact ⟨x, hxs⟩
  have hN : 0 < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hsne
  let z : E := s.centerMass (fun _ => (1 : ℝ)) (fun x => x.val)
  have hz : z ∈ convexHull ℝ K := by
    apply s.centerMass_mem_convexHull (fun _ _ => zero_le_one) _ (fun x _ => x.property)
    simpa using hN
  have hzclose (y : E) (hy : y ∈ K) : ‖z - y‖ < Metric.diam K := by
    obtain ⟨a, has, hay⟩ := Set.mem_iUnion₂.mp (hs hy)
    have hsum : (∑ x ∈ s, ‖x.val - y‖) < (s.card : ℝ) * Metric.diam K := by
      calc
        (∑ x ∈ s, ‖x.val - y‖) < ∑ _x ∈ s, Metric.diam K := by
          apply Finset.sum_lt_sum
          · intro x _
            simpa only [dist_eq_norm] using Metric.dist_le_diam_of_mem hK.isBounded x.property hy
          · refine ⟨a, has, ?_⟩
            simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hay
        _ = (s.card : ℝ) * Metric.diam K := by simp
    have heq : z - y = (s.card : ℝ)⁻¹ • ∑ x ∈ s, (x.val - y) := by
      dsimp [z, Finset.centerMass]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, one_smul, Finset.sum_sub_distrib,
        smul_sub]
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hN.ne', one_smul]
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hN)]
    calc
      (s.card : ℝ)⁻¹ * ‖∑ x ∈ s, (x.val - y)‖ ≤
          (s.card : ℝ)⁻¹ * ∑ x ∈ s, ‖x.val - y‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hN.le)
      _ < (s.card : ℝ)⁻¹ * ((s.card : ℝ) * Metric.diam K) :=
        mul_lt_mul_of_pos_left hsum (inv_pos.mpr hN)
      _ = Metric.diam K := by rw [← mul_assoc, inv_mul_cancel₀ hN.ne', one_mul]
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn hne
    (show ContinuousOn (fun y : E => ‖z - y‖) K from (continuous_const.sub continuous_id).norm.continuousOn)
  exact ⟨z, hz, ‖z - y‖, hzclose y hy, fun a ha => hmax ha⟩

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_CompactInvariantSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Minimal compact invariant subsets and their open covers. -/

noncomputable section

open Topology

namespace BoundedHochschild
namespace KadisonRingrose

universe u v

variable {A : Type u} [TopologicalSpace A] [T2Space A]
variable {G : Type v} [Group G]

omit [Group G] in
/-- A nonempty compact invariant set contains a minimal nonempty closed
invariant subset. -/
theorem exists_minimal_compact_invariant (T : G → A → A)
    (C : Set A) (hC : IsCompact C) (hne : C.Nonempty)
    (hinv : ∀ g, Set.MapsTo (T g) C C) :
    ∃ K : Set A, K ⊆ C ∧ K.Nonempty ∧ IsClosed K ∧
      (∀ g, Set.MapsTo (T g) K K) ∧
      ∀ L : Set A, L ⊆ K → L.Nonempty → IsClosed L →
        (∀ g, Set.MapsTo (T g) L L) → K ⊆ L := by
  classical
  let S : Set (Set A) := {K | K ⊆ C ∧ K.Nonempty ∧ IsClosed K ∧
    ∀ g, Set.MapsTo (T g) K K}
  have hCS : C ∈ S := ⟨Set.Subset.rfl, hne, hC.isClosed, hinv⟩
  obtain ⟨K, hKC, hK⟩ := zorn_superset_nonempty S (fun c hc hchain hcne => by
    have : Nonempty c := hcne.to_subtype
    have hn : (⋂₀ c).Nonempty :=
      IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
        (fun L hL J hJ => by
          rcases hchain.total hL hJ with h | h
          · exact ⟨L, hL, Set.Subset.rfl, h⟩
          · exact ⟨J, hJ, h, Set.Subset.rfl⟩)
        (fun L hL => (hc hL).2.1)
        (fun L hL => hC.of_isClosed_subset (hc hL).2.2.1 (hc hL).1)
        (fun L hL => (hc hL).2.2.1)
    refine ⟨⋂₀ c, ⟨?_, hn, ?_, ?_⟩, fun L hL => Set.sInter_subset_of_mem hL⟩
    · obtain ⟨L, hL⟩ := hcne
      exact (Set.sInter_subset_of_mem hL).trans (hc hL).1
    · exact isClosed_sInter (fun L hL => (hc hL).2.2.1)
    · intro g x hx
      apply Set.mem_sInter.mpr
      intro L hL
      exact (hc hL).2.2.2 g (Set.mem_sInter.mp hx L hL)) C hCS
  refine ⟨K, hKC, hK.1.2.1, hK.1.2.2.1, hK.1.2.2.2, ?_⟩
  intro L hLK hLn hLc hLi
  exact hK.2 ⟨hLK.trans hKC, hLn, hLc, hLi⟩ hLK

omit [T2Space A] in
/-- Every orbit in a minimal compact invariant set meets each nonempty
relatively open part of that set. -/
theorem minimal_invariant_open_cover (T : G → A → A)
    (hcont : ∀ g, Continuous (T g))
    (hone : ∀ x, T 1 x = x) (hmul : ∀ g h x, T (g * h) x = T g (T h x))
    (K : Set A) (hKc : IsClosed K) (hinv : ∀ g, Set.MapsTo (T g) K K)
    (hmin : ∀ L : Set A, L ⊆ K → L.Nonempty → IsClosed L →
      (∀ g, Set.MapsTo (T g) L L) → K ⊆ L)
    (U : Set A) (hU : IsOpen U) (hne : (K ∩ U).Nonempty) :
    K ⊆ ⋃ g, (T g) ⁻¹' U := by
  classical
  intro x hx
  by_contra hnot
  have hxnone : ∀ g, T g x ∉ U := by simpa only [Set.mem_iUnion, Set.mem_preimage, not_exists] using hnot
  let L : Set A := K ∩ ⋂ g, (T g) ⁻¹' Uᶜ
  have hLK : L ⊆ K := Set.inter_subset_left
  have hLn : L.Nonempty := ⟨x, hx, Set.mem_iInter.mpr hxnone⟩
  have hLc : IsClosed L := hKc.inter (isClosed_iInter (fun g => hU.isClosed_compl.preimage (hcont g)))
  have hLi : ∀ g, Set.MapsTo (T g) L L := by
    intro g y hy
    refine ⟨hinv g hy.1, Set.mem_iInter.mpr (fun h => ?_)⟩
    change T h (T g y) ∉ U
    rw [← hmul]
    exact Set.mem_iInter.mp hy.2 (h * g)
  obtain ⟨y, hyK, hyU⟩ := hne
  have hyL := hmin L hLK hLn hLc hLi hyK
  have hyout := Set.mem_iInter.mp hyL.2 1
  apply hyout
  simpa only [hone] using hyU

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialCohomology_CenterTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Center trace for bounded Hochschild cohomology. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildDixmier
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def Central (a : M) : Prop := ∀ x : M, Commute a x
omit [PartialOrder M] [StarOrderedRing M] in
lemma central_star {a : M} (ha : Central a) : Central (star a) := by
  intro x
  change star a*x=x*star a
  have h := congrArg star (ha (star x)).eq
  simpa only [star_mul,star_star] using h.symm
omit [PartialOrder M] [StarOrderedRing M] in
lemma central_sub {a b : M} (ha : Central a) (hb : Central b) : Central (a-b) :=
  fun x => (ha x).sub_left (hb x)

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
  (τ : M →ₚ[ℂ] ℂ)
  (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

variable (h1 : τ 1=1)
include htr in
omit [StarOrderedRing M] in
lemma central_pair_hull {z : M} (hz : Central z) (a : M) :
    convexHull ℝ (Set.range (fun v : unitary M => conjugate v a)) ⊆
      {b | τ (z*b)=τ (z*a)} := by
  apply convexHull_min
  · rintro _ ⟨v,rfl⟩
    change τ (z*conjugate v a)=τ (z*a)
    rw [conjugate_apply]
    have he : z*((v:M)*a*star (v:M))=(v:M)*(z*a)*star (v:M) := by
      calc
        _=(z*(v:M))*a*star (v:M) := by simp only [mul_assoc]
        _=((v:M)*z)*a*star (v:M) := by rw [(hz (v:M)).eq]
        _=_ := by simp only [mul_assoc]
    rw [he]
    exact trace_conjugate τ htr v (z*a)
  · intro x hx y hy r s _hr _hs hrs
    change τ (z*(r • x+s • y))=τ (z*a)
    rw [mul_add,mul_smul_comm,mul_smul_comm,map_add,τ.map_smul_of_tower,
      τ.map_smul_of_tower,hx,hy,←add_smul,hrs,one_smul]

include h1

omit h1 in
include hfaith in
omit [StarOrderedRing M] in
lemma central_unique {b c : M} (hb : Central b) (hc : Central c)
    (h : ∀ z : M, Central z → τ (z*b)=τ (z*c)) : b=c := by
  apply sub_eq_zero.mp
  apply hfaith
  rw [mul_sub,map_sub,h _ (central_star (central_sub hb hc)),sub_self]

end PopaCenter

open Filter Topology
open scoped ComplexOrder

open Filter Topology
open scoped ComplexOrder

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_FiniteNormalState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normal states and the remaining tracial averaging step

A normal state faithful on central projections is faithful on positive
central elements. The property passes to its actual central corner.
Composing such a state with a faithful normal positive central averaging
map gives a faithful normal tracial state. Constructing that map from
finiteness is a separate remaining theorem; no such map is postulated here.
-/

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- A positive functional vanishing on a positive contraction annihilates its left multiples. -/
lemma positive_contraction_zero_mul (ψ : M →ₚ[ℂ] ℂ) {c : M}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hψc : ψ c = 0) (b : M) : ψ (c * b) = 0 := by
  have hcc : c * c ≤ c := by
    simpa only [pow_two, pow_one] using
      CStarAlgebra.pow_antitone (ha₀ := hc0) (ha₁ := hc1) (by omega : 1 ≤ 2)
  have hψcc : ψ (c * c) = 0 := le_antisymm
    ((ψ.monotone hcc).trans_eq hψc)
    (ψ.map_nonneg hc0.isSelfAdjoint.mul_self_nonneg)
  have h := PositiveLinearMap.norm_map_star_mul_sq_le ψ c b
  rw [hc0.isSelfAdjoint.star_eq, hψcc, norm_zero, zero_mul] at h
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (ψ (c * b))])

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_WeakCompactFragment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A small weakly open piece of a norm-separable compact set

The Baire-category step of the isometric fixed-point argument. It is used
only on the compact orbit hull of a countably generated unitary subgroup.
-/

noncomputable section

open Topology TopologicalSpace

namespace BoundedHochschild
namespace KadisonRingrose

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma weak_closedBall (a : E) (r : ℝ) :
    IsClosed ((toWeakSpace ℂ E) '' Metric.closedBall a r) := by
  rw [← closure_eq_iff_isClosed, ← (convex_closedBall a r).toWeakSpace_closure ℂ,
    Metric.isClosed_closedBall.closure_eq]

/-- A nonempty weakly compact, norm-separable set has a nonempty relatively
weakly open subset of arbitrarily small norm diameter. -/
theorem weakCompact_small_open_piece (K : Set (WeakSpace ℂ E))
    (hK : IsCompact K) (hne : K.Nonempty)
    (hsep : IsSeparable ((toWeakSpace ℂ E).symm '' K))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set (WeakSpace ℂ E), IsOpen U ∧ (K ∩ U).Nonempty ∧
      ∀ x ∈ K ∩ U, ∀ y ∈ K ∩ U,
        ‖(toWeakSpace ℂ E).symm x - (toWeakSpace ℂ E).symm y‖ < ε := by
  classical
  obtain ⟨S, _hSK, hcount, hdense⟩ := hsep.exists_countable_dense_subset
  have : Countable S := hcount.to_subtype
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : Nonempty K := hne.to_subtype
  let B (a : S) : Set K := {x | (toWeakSpace ℂ E).symm x.val ∈ Metric.closedBall a.val (ε / 3)}
  have hc (a : S) : IsClosed (B a) := by
    have heq : B a = Subtype.val ⁻¹' ((toWeakSpace ℂ E) '' Metric.closedBall a.val (ε / 3)) := by
      ext x
      simp only [B, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_image]
      exact ⟨fun hx => ⟨_, hx, (toWeakSpace ℂ E).apply_symm_apply x.val⟩,
        fun ⟨z, hz, he⟩ => by simpa only [← he, LinearEquiv.symm_apply_apply] using hz⟩
    rw [heq]
    exact (weak_closedBall a.val (ε / 3)).preimage continuous_subtype_val
  have hcover : ⋃ a : S, B a = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : (toWeakSpace ℂ E).symm x.val ∈ closure S := hdense ⟨x.val, x.property, rfl⟩
    obtain ⟨a, haS, hdist⟩ := Metric.mem_closure_iff.mp hx (ε / 3) (by positivity)
    exact Set.mem_iUnion.mpr ⟨⟨a, haS⟩, hdist.le⟩
  obtain ⟨a, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hc hcover
  obtain ⟨U, hU, heq⟩ := isOpen_induced_iff.mp (show IsOpen (interior (B a)) from isOpen_interior)
  refine ⟨U, hU, ⟨x.val, x.property, ?_⟩, ?_⟩
  · have : x ∈ Subtype.val ⁻¹' U := heq ▸ hx
    exact this
  · intro y hy z hz
    have hyB : (toWeakSpace ℂ E).symm y ∈ Metric.closedBall a.val (ε / 3) := by
      change (⟨y, hy.1⟩ : K) ∈ B a
      apply interior_subset (s := B a)
      rw [← heq]
      exact hy.2
    have hzB : (toWeakSpace ℂ E).symm z ∈ Metric.closedBall a.val (ε / 3) := by
      change (⟨z, hz.1⟩ : K) ∈ B a
      apply interior_subset (s := B a)
      rw [← heq]
      exact hz.2
    have hy' := Metric.mem_closedBall.mp hyB
    have hz' := Metric.mem_closedBall.mp hzB
    have hd := dist_triangle ((toWeakSpace ℂ E).symm y) a.val ((toWeakSpace ℂ E).symm z)
    rw [dist_comm a.val] at hd
    rw [← dist_eq_norm]
    linarith

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_MinimalIsometricOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Minimal weakly compact isometric orbits are norm compact in a separable space. -/

noncomputable section

open Topology TopologicalSpace

namespace BoundedHochschild
namespace KadisonRingrose

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {G : Type v} [Group G]

/-- The weak action associated to a linear isometry. -/
def weakIsometry (T : E ≃ₗᵢ[ℂ] E) : WeakSpace ℂ E → WeakSpace ℂ E :=
  WeakSpace.map T.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] lemma weakIsometry_apply (T : E ≃ₗᵢ[ℂ] E) (x : WeakSpace ℂ E) :
    (toWeakSpace ℂ E).symm (weakIsometry T x) = T ((toWeakSpace ℂ E).symm x) := rfl

/-- Minimality and the Baire small-piece lemma give a finite norm net. -/
theorem minimal_isometric_orbit_finite_net (T : G → E ≃ₗᵢ[ℂ] E)
    (hone : ∀ x, T 1 x = x) (hmul : ∀ g h x, T (g * h) x = T g (T h x))
    (K : Set (WeakSpace ℂ E)) (hK : IsCompact K) (hne : K.Nonempty)
    (hsep : IsSeparable ((toWeakSpace ℂ E).symm '' K))
    (hinv : ∀ g, Set.MapsTo (weakIsometry (T g)) K K)
    (hmin : ∀ L : Set (WeakSpace ℂ E), L ⊆ K → L.Nonempty → IsClosed L →
      (∀ g, Set.MapsTo (weakIsometry (T g)) L L) → K ⊆ L)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset E, (↑s : Set E) ⊆ (toWeakSpace ℂ E).symm '' K ∧
      ∀ x ∈ K, ∃ y ∈ s, ‖(toWeakSpace ℂ E).symm x - y‖ < ε := by
  classical
  obtain ⟨U, hU, hKU, hdiam⟩ := weakCompact_small_open_piece K hK hne hsep ε hε
  have hcov : K ⊆ ⋃ g, weakIsometry (T g) ⁻¹' U := by
    apply minimal_invariant_open_cover (fun g => weakIsometry (T g))
      (fun g => (WeakSpace.map (T g).toContinuousLinearEquiv.toContinuousLinearMap).continuous)
      _ _ K hK.isClosed hinv hmin U hU hKU
    · intro x
      apply (toWeakSpace ℂ E).symm.injective
      exact hone _
    · intro g h x
      apply (toWeakSpace ℂ E).symm.injective
      exact hmul g h _
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun g => weakIsometry (T g) ⁻¹' U)
    (fun g => hU.preimage (WeakSpace.map (T g).toContinuousLinearEquiv.toContinuousLinearMap).continuous) hcov
  obtain ⟨y, hyK, hyU⟩ := hKU
  let z (g : G) : E := T g⁻¹ ((toWeakSpace ℂ E).symm y)
  refine ⟨s.image z, ?_, ?_⟩
  · intro a ha
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨weakIsometry (T g⁻¹) y, hinv g⁻¹ hyK, rfl⟩
  · intro x hx
    obtain ⟨g, hgs, hxU⟩ := Set.mem_iUnion₂.mp (hs hx)
    refine ⟨z g, Finset.mem_image.mpr ⟨g, hgs, rfl⟩, ?_⟩
    have hgzy : T g (z g) = (toWeakSpace ℂ E).symm y := by
      dsimp [z]
      rw [← hmul, mul_inv_cancel, hone]
    have hd := hdiam (weakIsometry (T g) x) ⟨hinv g hx, hxU⟩ y ⟨hyK, hyU⟩
    change ‖T g ((toWeakSpace ℂ E).symm x) - (toWeakSpace ℂ E).symm y‖ < ε at hd
    rwa [← hgzy, ← map_sub, (T g).norm_map] at hd

/-- A minimal weakly compact orbit inside a norm-separable Banach space is
compact for the norm topology as well. -/
theorem minimal_isometric_orbit_normCompact [CompleteSpace E]
    (T : G → E ≃ₗᵢ[ℂ] E)
    (hone : ∀ x, T 1 x = x) (hmul : ∀ g h x, T (g * h) x = T g (T h x))
    (K : Set (WeakSpace ℂ E)) (hK : IsCompact K) (hne : K.Nonempty)
    (hsep : IsSeparable ((toWeakSpace ℂ E).symm '' K))
    (hinv : ∀ g, Set.MapsTo (weakIsometry (T g)) K K)
    (hmin : ∀ L : Set (WeakSpace ℂ E), L ⊆ K → L.Nonempty → IsClosed L →
      (∀ g, Set.MapsTo (weakIsometry (T g)) L L) → K ⊆ L) :
    IsCompact ((toWeakSpace ℂ E).symm '' K) := by
  have hc : IsClosed ((toWeakSpace ℂ E).symm '' K) := by
    have heq : (toWeakSpace ℂ E).symm '' K = (toWeakSpace ℂ E) ⁻¹' K := by
      ext x
      simp only [Set.mem_image, Set.mem_preimage]
      exact ⟨fun ⟨y, hy, he⟩ => he ▸ by simpa using hy,
        fun hx => ⟨toWeakSpace ℂ E x, hx, rfl⟩⟩
    rw [heq]
    exact hK.isClosed.preimage (toWeakSpaceCLM ℂ E).continuous
  apply TotallyBounded.isCompact_of_isComplete _ hc.isComplete
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨s, _, hs⟩ := minimal_isometric_orbit_finite_net T hone hmul K hK hne hsep hinv hmin ε hε
  refine ⟨s, s.finite_toSet, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hdist⟩ := hs y hy
  apply Set.mem_iUnion₂.mpr
  exact ⟨z, hz, by simpa only [Metric.mem_ball, dist_eq_norm] using hdist⟩

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_WeakIsometricFixedPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The separable isometric fixed-point argument

This is the specialization of the Ryll-Nardzewski argument needed for the
normal-state orbit: a linear isometric group acting on a weakly compact,
norm-separable convex set has a common fixed point.
-/

noncomputable section

open Topology TopologicalSpace

namespace BoundedHochschild
namespace KadisonRingrose

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {G : Type v} [Group G]

omit [Group G] in
theorem minimal_weak_convex_invariant (T : G → E ≃ₗᵢ[ℂ] E)
    (C : Set (WeakSpace ℂ E)) (hC : IsCompact C) (hne : C.Nonempty)
    (hconv : Convex ℝ C) (hinv : ∀ g, Set.MapsTo (weakIsometry (T g)) C C) :
    ∃ L : Set (WeakSpace ℂ E), L ⊆ C ∧ L.Nonempty ∧ IsClosed L ∧ Convex ℝ L ∧
      (∀ g, Set.MapsTo (weakIsometry (T g)) L L) ∧
      ∀ D : Set (WeakSpace ℂ E), D ⊆ L → D.Nonempty → IsClosed D → Convex ℝ D →
        (∀ g, Set.MapsTo (weakIsometry (T g)) D D) → L ⊆ D := by
  classical
  let S : Set (Set (WeakSpace ℂ E)) := {L | L ⊆ C ∧ L.Nonempty ∧ IsClosed L ∧
    Convex ℝ L ∧ ∀ g, Set.MapsTo (weakIsometry (T g)) L L}
  have hCS : C ∈ S := ⟨Set.Subset.rfl, hne, hC.isClosed, hconv, hinv⟩
  obtain ⟨L, hLC, hL⟩ := zorn_superset_nonempty S (fun c hc hchain hcne => by
    have : Nonempty c := hcne.to_subtype
    have hn : (⋂₀ c).Nonempty :=
      IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
        (fun A hA B hB => by
          rcases hchain.total hA hB with h | h
          · exact ⟨A, hA, Set.Subset.rfl, h⟩
          · exact ⟨B, hB, h, Set.Subset.rfl⟩)
        (fun A hA => (hc hA).2.1)
        (fun A hA => hC.of_isClosed_subset (hc hA).2.2.1 (hc hA).1)
        (fun A hA => (hc hA).2.2.1)
    refine ⟨⋂₀ c, ⟨?_, hn, ?_, ?_, ?_⟩, fun A hA => Set.sInter_subset_of_mem hA⟩
    · obtain ⟨A, hA⟩ := hcne
      exact (Set.sInter_subset_of_mem hA).trans (hc hA).1
    · exact isClosed_sInter (fun A hA => (hc hA).2.2.1)
    · exact convex_sInter (fun A hA => (hc hA).2.2.2.1)
    · intro g x hx
      apply Set.mem_sInter.mpr
      intro A hA
      exact (hc hA).2.2.2.2 g (Set.mem_sInter.mp hx A hA)) C hCS
  refine ⟨L, hLC, hL.1.2.1, hL.1.2.2.1, hL.1.2.2.2.1, hL.1.2.2.2.2, ?_⟩
  intro D hDL hDn hDc hDv hDi
  exact hL.2 ⟨hDL.trans hLC, hDn, hDc, hDv, hDi⟩ hDL

/-- Common fixed point for the norm-separable weakly compact case. -/
theorem weakCompact_separable_isometric_fixedPoint [CompleteSpace E]
    (T : G → E ≃ₗᵢ[ℂ] E)
    (hone : ∀ x, T 1 x = x) (hmul : ∀ g h x, T (g * h) x = T g (T h x))
    (C : Set (WeakSpace ℂ E)) (hC : IsCompact C) (hne : C.Nonempty)
    (hconv : Convex ℝ C) (hsep : IsSeparable ((toWeakSpace ℂ E).symm '' C))
    (hinv : ∀ g, Set.MapsTo (weakIsometry (T g)) C C) :
    ∃ x ∈ C, ∀ g, weakIsometry (T g) x = x := by
  classical
  obtain ⟨L, hLC, hLn, hLc, hLv, hLi, hLmin⟩ :=
    minimal_weak_convex_invariant T C hC hne hconv hinv
  have hLcompact : IsCompact L := hC.of_isClosed_subset hLc hLC
  obtain ⟨K, hKL, hKn, hKc, hKi, hKmin⟩ :=
    exists_minimal_compact_invariant (fun g => weakIsometry (T g)) L hLcompact hLn hLi
  have hKcompact : IsCompact K := hLcompact.of_isClosed_subset hKc hKL
  have hKsep : IsSeparable ((toWeakSpace ℂ E).symm '' K) :=
    hsep.mono (Set.image_mono (hKL.trans hLC))
  have hKnorm := minimal_isometric_orbit_normCompact T hone hmul K hKcompact hKn hKsep hKi hKmin
  have hsingle : K.Subsingleton := by
    by_contra hnonsingle
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.not_subsingleton_iff.mp hnonsingle
    have hnt : ((toWeakSpace ℂ E).symm '' K).Nontrivial :=
      ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, fun h => hxy ((toWeakSpace ℂ E).symm.injective h)⟩
    obtain ⟨z, hz, r, hr, hzr⟩ := compact_convex_center _ hKnorm hnt
    let B (y : K) : Set (WeakSpace ℂ E) :=
      (toWeakSpace ℂ E) '' Metric.closedBall ((toWeakSpace ℂ E).symm y.val) r
    let D : Set (WeakSpace ℂ E) := L ∩ ⋂ y : K, B y
    have hzL : toWeakSpace ℂ E z ∈ L := by
      have hcv : Convex ℝ ((toWeakSpace ℂ E).symm '' L) :=
        hLv.linear_image ((toWeakSpace ℂ E).symm.restrictScalars ℝ).toLinearMap
      obtain ⟨w, hw, heq⟩ := convexHull_min (Set.image_mono hKL) hcv hz
      simpa only [← heq, LinearEquiv.apply_symm_apply] using hw
    have hDz : toWeakSpace ℂ E z ∈ D := by
      refine ⟨hzL, Set.mem_iInter.mpr (fun y => ?_)⟩
      exact ⟨z, by simpa only [Metric.mem_closedBall, dist_eq_norm] using
        (hzr _ ⟨y.val, y.property, rfl⟩), rfl⟩
    have hDc : IsClosed D := hLc.inter (isClosed_iInter (fun y => weak_closedBall _ _))
    have hDv : Convex ℝ D := hLv.inter (convex_iInter (fun y =>
      (convex_closedBall ((toWeakSpace ℂ E).symm y.val) r).linear_image
        ((toWeakSpace ℂ E).restrictScalars ℝ).toLinearMap))
    have hDi : ∀ g, Set.MapsTo (weakIsometry (T g)) D D := by
      intro g a ha
      refine ⟨hLi g ha.1, Set.mem_iInter.mpr (fun y => ?_)⟩
      let b : K := ⟨weakIsometry (T g⁻¹) y.val, hKi g⁻¹ y.property⟩
      obtain ⟨w, hw, heq⟩ := Set.mem_iInter.mp ha.2 b
      have hab : ‖(toWeakSpace ℂ E).symm a - (toWeakSpace ℂ E).symm b.val‖ ≤ r := by
        simpa only [Metric.mem_closedBall, dist_eq_norm, ← heq, LinearEquiv.symm_apply_apply] using hw
      refine ⟨T g ((toWeakSpace ℂ E).symm a), ?_, rfl⟩
      rw [Metric.mem_closedBall, dist_eq_norm]
      change ‖T g ((toWeakSpace ℂ E).symm a) - (toWeakSpace ℂ E).symm y.val‖ ≤ r
      have hgb : T g ((toWeakSpace ℂ E).symm b.val) = (toWeakSpace ℂ E).symm y.val := by
        change T g (T g⁻¹ ((toWeakSpace ℂ E).symm y.val)) = _
        rw [← hmul, mul_inv_cancel, hone]
      rw [← hgb, ← map_sub, (T g).norm_map]
      exact hab
    have hLD : L ⊆ D := hLmin D Set.inter_subset_left ⟨_, hDz⟩ hDc hDv hDi
    have hdiam : Metric.diam ((toWeakSpace ℂ E).symm '' K) ≤ r := by
      apply Metric.diam_le_of_forall_dist_le_of_nonempty hnt.nonempty
      rintro a ⟨a', ha', rfl⟩ b ⟨b', hb', rfl⟩
      obtain ⟨w, hw, heq⟩ := Set.mem_iInter.mp (hLD (hKL ha')).2 ⟨b', hb'⟩
      simpa only [Metric.mem_closedBall, ← heq, LinearEquiv.symm_apply_apply] using hw
    exact (not_le_of_gt hr) hdiam
  obtain ⟨x, hx⟩ := hKn
  exact ⟨x, hLC (hKL hx), fun g => hsingle (hKi g hx) hx⟩

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_IsometricFixedPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Common fixed points for weakly compact linear isometric actions

A countable orbit generates a norm-separable closed convex hull. Applying
the separable argument to free groups on finitely many prescribed elements,
then using compactness, removes the separability restriction.
-/

noncomputable section

open Topology TopologicalSpace

namespace BoundedHochschild
namespace KadisonRingrose

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {G : Type v} [Group G]

/-- A countable acting group can be restricted to the separable closed
convex hull of one orbit. -/
theorem weakCompact_countable_isometric_fixedPoint [Countable G]
    (T : G → E ≃ₗᵢ[ℂ] E)
    (hone : ∀ x, T 1 x = x) (hmul : ∀ g h x, T (g * h) x = T g (T h x))
    (C : Set (WeakSpace ℂ E)) (hC : IsCompact C) (hne : C.Nonempty)
    (hconv : Convex ℝ C) (hinv : ∀ g, Set.MapsTo (weakIsometry (T g)) C C) :
    ∃ x ∈ C, ∀ g, weakIsometry (T g) x = x := by
  classical
  obtain ⟨x, hx⟩ := hne
  let S : Set E := Set.range (fun g : G => T g ((toWeakSpace ℂ E).symm x))
  let D : Set E := closure (convexHull ℝ S)
  let W : Set (WeakSpace ℂ E) := (toWeakSpace ℂ E) '' D
  have hDc : IsClosed D := isClosed_closure
  have hDv : Convex ℝ D := (convex_convexHull ℝ S).closure
  have hWc : IsClosed W := by
    rw [show W = closure ((toWeakSpace ℂ E) '' convexHull ℝ S) from
      (convex_convexHull ℝ S).toWeakSpace_closure ℂ]
    exact isClosed_closure
  have hWC : W ⊆ C := by
    rintro _ ⟨y, hy, rfl⟩
    have hsub : D ⊆ (toWeakSpace ℂ E) ⁻¹' C := by
      apply closure_minimal _ (hC.isClosed.preimage (toWeakSpaceCLM ℂ E).continuous)
      apply convexHull_min _ (hconv.linear_preimage ((toWeakSpace ℂ E).restrictScalars ℝ).toLinearMap)
      rintro _ ⟨g, rfl⟩
      exact hinv g hx
    exact hsub hy
  have hWn : W.Nonempty := by
    refine ⟨x, (toWeakSpace ℂ E).symm x, ?_, (toWeakSpace ℂ E).apply_symm_apply x⟩
    apply subset_closure
    apply subset_convexHull ℝ S
    exact ⟨1, hone _⟩
  have hWs : IsSeparable ((toWeakSpace ℂ E).symm '' W) := by
    have hS : S.Countable := Set.countable_range _
    have hDsep : IsSeparable D := by
      apply (hS.isSeparable.span (R := ℝ)).closure.mono
      exact closure_mono (convexHull_min (Submodule.subset_span) (Submodule.span ℝ S).convex)
    have heq : (toWeakSpace ℂ E).symm '' W = D := by
      simp only [W, Set.image_image, LinearEquiv.symm_apply_apply, Set.image_id']
    rw [heq]
    exact hDsep
  have hWi : ∀ g, Set.MapsTo (weakIsometry (T g)) W W := by
    intro g a ha
    obtain ⟨y, hy, rfl⟩ := ha
    refine ⟨T g y, ?_, rfl⟩
    have hsub : D ⊆ (T g) ⁻¹' D := by
      apply closure_minimal _ (hDc.preimage (T g).continuous)
      apply convexHull_min _ (hDv.linear_preimage ((T g).toLinearMap.restrictScalars ℝ))
      rintro _ ⟨h, rfl⟩
      apply subset_closure
      apply subset_convexHull ℝ S
      exact ⟨g * h, hmul g h _⟩
    exact hsub hy
  obtain ⟨y, hy, hfix⟩ := weakCompact_separable_isometric_fixedPoint T hone hmul W
    (hC.of_isClosed_subset hWc hWC) hWn
    (hDv.linear_image ((toWeakSpace ℂ E).restrictScalars ℝ).toLinearMap) hWs hWi
  exact ⟨y, hWC hy, hfix⟩

/-- The linear-isometric case of the Ryll-Nardzewski fixed-point theorem,
without separability assumptions. -/
theorem weakCompact_isometric_fixedPoint
    (T : G → E ≃ₗᵢ[ℂ] E)
    (hone : ∀ x, T 1 x = x) (hmul : ∀ g h x, T (g * h) x = T g (T h x))
    (C : Set (WeakSpace ℂ E)) (hC : IsCompact C) (hne : C.Nonempty)
    (hconv : Convex ℝ C) (hinv : ∀ g, Set.MapsTo (weakIsometry (T g)) C C) :
    ∃ x ∈ C, ∀ g, weakIsometry (T g) x = x := by
  classical
  have hfinite (s : Finset G) : ∃ x ∈ C, ∀ g ∈ s, weakIsometry (T g) x = x := by
    let ρ : FreeGroup s →* G := FreeGroup.lift (fun g : s => g.val)
    have : Countable (FreeGroup s) := inferInstanceAs (Countable (Quot _))
    obtain ⟨x, hx, hfix⟩ := weakCompact_countable_isometric_fixedPoint (fun g => T (ρ g))
      (fun x => by simpa only [map_one] using hone x)
      (fun g h x => by simpa only [map_mul] using hmul (ρ g) (ρ h) x)
      C hC hne hconv (fun g => hinv (ρ g))
    refine ⟨x, hx, fun g hg => ?_⟩
    simpa only [ρ, FreeGroup.lift_apply_of] using hfix (FreeGroup.of ⟨g, hg⟩)
  let F (g : G) : Set (WeakSpace ℂ E) := {x | weakIsometry (T g) x = x}
  have hc (g) : IsClosed (F g) := isClosed_eq
    (WeakSpace.map (T g).toContinuousLinearEquiv.toContinuousLinearMap).continuous continuous_id
  obtain ⟨x, hx, hfix⟩ := hC.inter_iInter_nonempty F hc (fun s => by
    obtain ⟨x, hx, hfix⟩ := hfinite s
    exact ⟨x, hx, Set.mem_iInter₂.mpr hfix⟩)
  exact ⟨x, hx, fun g => Set.mem_iInter.mp hfix g⟩

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_ProjectionJoinComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Comparison bounds for joins, independent of any scalar trace. -/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [PartialOrder M] [StarOrderedRing M] in
lemma orthogonal_projection_sum_range (q : ℕ → M)
    (hq : ∀ n, IsStarProjection (q n))
    (horth : ∀ i j, i ≠ j → q i * q j = 0) (n : ℕ) :
    IsStarProjection (∑ i ∈ Finset.range n, q i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      apply ih.add (hq n)
      rw [Finset.sum_mul]
      apply Finset.sum_eq_zero
      intro i hi
      exact horth i n (Nat.ne_of_lt (Finset.mem_range.mp hi))

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_NormalOrbitHull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The norm-closed convex orbit of a normal positive functional

This family remains normal and positive, preserves values on the center,
and satisfies the uniform orthogonal-projection decay in Ringrose Lemma 5.2.
-/

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The bounded functional underlying a positive functional. -/
def positiveFunctionalCLM (ψ : M →ₚ[ℂ] ℂ) : StrongDual ℂ M :=
  ⟨ψ.toLinearMap, map_continuous ψ⟩

/-- Pull a functional back along conjugation by a unitary. -/
def unitaryPullback (F : StrongDual ℂ M) (u : unitary M) : StrongDual ℂ M :=
  (F.comp ((ContinuousLinearMap.mul ℂ M).flip (star (u : M)))).comp
    (ContinuousLinearMap.mul ℂ M (u : M))

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma unitaryPullback_apply (F : StrongDual ℂ M) (u : unitary M) (a : M) :
    unitaryPullback F u a = F ((u : M) * a * star (u : M)) := rfl

/-- The closed convex orbit used in the fixed-point construction of a trace. -/
def unitaryOrbitHull (F : StrongDual ℂ M) : Set (StrongDual ℂ M) :=
  closure (convexHull ℝ (Set.range (unitaryPullback F)))

omit [PartialOrder M] [StarOrderedRing M] in
lemma unitaryOrbitHull_eval_bound (F : StrongDual ℂ M) (a : M) (C : ℝ)
    (hbound : ∀ u : unitary M, ‖unitaryPullback F u a‖ ≤ C) :
    ∀ G ∈ unitaryOrbitHull F, ‖G a‖ ≤ C := by
  let E := (ContinuousLinearMap.apply ℂ ℂ a : StrongDual ℂ M →L[ℂ] ℂ)
  have hc : convexHull ℝ (Set.range (unitaryPullback F)) ⊆
      E ⁻¹' Metric.closedBall 0 C := by
    apply convexHull_min
    · rintro _ ⟨u, rfl⟩
      simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, E, ContinuousLinearMap.apply_apply] using hbound u
    · exact (convex_closedBall (0 : ℂ) C).linear_preimage (E.restrictScalars ℝ).toLinearMap
  have hh := closure_minimal hc (Metric.isClosed_closedBall.preimage E.continuous)
  intro G hG
  simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, E, ContinuousLinearMap.apply_apply] using hh hG

omit [PartialOrder M] [StarOrderedRing M] in
lemma unitaryOrbitHull_eval_eq (F : StrongDual ℂ M) (a : M) (c : ℂ)
    (hbound : ∀ u : unitary M, unitaryPullback F u a = c) :
    ∀ G ∈ unitaryOrbitHull F, G a = c := by
  let E := (ContinuousLinearMap.apply ℂ ℂ a : StrongDual ℂ M →L[ℂ] ℂ)
  have hc : convexHull ℝ (Set.range (unitaryPullback F)) ⊆ {G | E G = c} := by
    apply convexHull_min
    · rintro _ ⟨u, rfl⟩
      exact hbound u
    · intro G hG H hH r t _hr _ht hrt
      change r • E G + t • E H = c
      rw [hG, hH, ← add_smul, hrt, one_smul]
  exact closure_minimal hc (isClosed_eq E.continuous continuous_const)

lemma unitaryOrbitHull_positive (ψ : M →ₚ[ℂ] ℂ) :
    ∀ G ∈ unitaryOrbitHull (positiveFunctionalCLM ψ), ∀ a : M, 0 ≤ a → 0 ≤ G a := by
  intro G hG a ha
  let E := (ContinuousLinearMap.apply ℂ ℂ a : StrongDual ℂ M →L[ℂ] ℂ)
  have hc : convexHull ℝ (Set.range (unitaryPullback (positiveFunctionalCLM ψ))) ⊆
      E ⁻¹' Set.Ici 0 := by
    apply convexHull_min
    · rintro _ ⟨u, rfl⟩
      exact ψ.map_nonneg (star_right_conjugate_nonneg ha (u : M))
    · intro F hF H hH r t hr ht _
      change 0 ≤ r • E F + t • E H
      exact add_nonneg (smul_nonneg hr hF) (smul_nonneg ht hH)
  exact (closure_minimal hc (isClosed_Ici.preimage E.continuous)) hG

omit [PartialOrder M] [StarOrderedRing M] in
lemma unitaryOrbitHull_central (F : StrongDual ℂ M) {a : M}
    (hc : ∀ b : M, a * b = b * a) :
    ∀ G ∈ unitaryOrbitHull F, G a = F a := by
  apply unitaryOrbitHull_eval_eq F a (F a)
  intro u
  rw [unitaryPullback_apply, ← hc (u : M), mul_assoc,
    (Unitary.mem_iff.mp u.property).2, mul_one]

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_OrthogonalProjectionSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrary orthogonal projection sums and their weak-star convergence. -/

noncomputable section

open Filter Topology

namespace BoundedHochschild
namespace KadisonRingrose

universe u v

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {I : Type v}

omit [PartialOrder M] [StarOrderedRing M] in
lemma orthogonal_projection_finset_sum (p : I → M)
    (hp : ∀ i, IsStarProjection (p i))
    (horth : ∀ i j, i ≠ j → p i * p j = 0) (s : Finset I) :
    IsStarProjection (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
      rw [Finset.sum_insert his]
      apply (hp i).add ih
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro j hj
      exact horth i j (fun hij => his (hij ▸ hj))

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PositiveCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normality of positive functionals localized to a projection corner. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Two-sided compression of a positive functional. -/
def compressionPositive {p : M} (hp : IsStarProjection p) (ψ : M →ₚ[ℂ] ℂ) : M →ₚ[ℂ] ℂ where
  toLinearMap :=
    { toFun := fun a => ψ (p * a * p)
      map_add' := by intro a b; simp only [mul_add, add_mul, map_add]
      map_smul' := by intro c a; simp only [mul_smul_comm, smul_mul_assoc, map_smul, RingHom.id_apply] }
  monotone' := fun _ _ hab => ψ.monotone (by
    simpa only [hp.isSelfAdjoint.star_eq] using star_right_conjugate_le_conjugate hab p)

lemma compressionPositive_clm {p : M} (hp : IsStarProjection p) (ψ : M →ₚ[ℂ] ℂ) :
    positiveFunctionalCLM (compressionPositive hp ψ) =
      ((positiveFunctionalCLM ψ).comp ((ContinuousLinearMap.mul ℂ M).flip p)).comp
        (ContinuousLinearMap.mul ℂ M p) := rfl

@[simp] lemma compressionPositive_one {p : M} (hp : IsStarProjection p) (ψ : M →ₚ[ℂ] ℂ) :
    compressionPositive hp ψ 1 = ψ p := by
  change ψ (p * 1 * p) = ψ p
  rw [mul_one, hp.isIdempotentElem.eq]

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PositiveCompleteAdditivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Complete additivity implies normality for positive functionals

The positive-functional case of Takesaki's criterion, as proved in Ringrose,
*Lectures on the trace in a finite von Neumann algebra*, Lemmas 4.1--4.3.
Only this case is needed for the normal-state orbit in the trace construction.
-/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma positiveFunctional_zero_of_one_zero (ψ : M →ₚ[ℂ] ℂ) (hψ : ψ 1 = 0) :
    positiveFunctionalCLM ψ = 0 := by
  ext a
  change ψ a = 0
  have h := PositiveLinearMap.norm_map_star_mul_sq_le ψ (1 : M) a
  simp only [star_one, one_mul, hψ, norm_zero, zero_mul] at h
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (ψ a)])

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_UniformProjectionSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform summation of orthogonal projections

The positive case of the gliding-block argument in Ringrose, Theorem 4.7:
uniform decay on orthogonal sequences implies uniform complete additivity.
-/

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

universe u v

lemma disjoint_finset_sequence {I : Type v} (B : Finset I → Prop)
    (hB : ∀ s : Finset I, ∃ t : Finset I, Disjoint s t ∧ B t) :
    ∃ b : ℕ → Finset I, (∀ m n, m ≠ n → Disjoint (b m) (b n)) ∧ ∀ n, B (b n) := by
  classical
  let next (s : Finset I) := (hB s).choose
  have hn (s) : Disjoint s (next s) ∧ B (next s) := (hB s).choose_spec
  let c : ℕ → Finset I := Nat.rec ∅ (fun _ s => s ∪ next s)
  have hc (n) : c (n + 1) = c n ∪ next (c n) := rfl
  have hm : Monotone c := monotone_nat_of_le_succ (fun n => by
    rw [hc]; exact Finset.subset_union_left)
  let b (n : ℕ) := next (c n)
  have hlt (m n : ℕ) (hmn : m < n) : Disjoint (b m) (b n) := by
    apply (hn (c n)).1.mono_left
    exact (show b m ⊆ c (m + 1) by rw [hc]; exact Finset.subset_union_right).trans
      (hm (Nat.succ_le_iff.mpr hmn))
  refine ⟨b, ?_, fun n => (hn (c n)).2⟩
  intro m n hmn
  rcases lt_or_gt_of_ne hmn with h | h
  · exact hlt m n h
  · exact (hlt n m h).symm

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma orthogonal_projection_finset_sum_le {I : Type v} (p : I → M)
    (hp : ∀ i, IsStarProjection (p i))
    (ho : ∀ i j, i ≠ j → p i * p j = 0)
    {P : M} (hP : IsStarProjection P) (hu : ∀ i, p i ≤ P) (s : Finset I) :
    (∑ i ∈ s, p i) ≤ P := by
  classical
  apply ((orthogonal_projection_finset_sum p hp ho s).le_iff_mul_eq_left hP).mpr
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => ((hp i).le_iff_mul_eq_left hP).mp (hu i))

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PositiveOrbitCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weak compactness of positive normal orbits

The positive-functional specialization of Ringrose, Theorem 4.7 and Lemma 5.3.
The gliding-block estimate and complete-additivity criterion ensure that no
singular functional enters the weak-star closure.
-/

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Weak-star closure of a family of bounded functionals. -/
def weakFunctionalClosure (K : Set (StrongDual ℂ M)) : Set (WeakDual ℂ M) :=
  closure (StrongDual.toWeakDual '' K)

omit [StarOrderedRing M] in
lemma weakFunctionalClosure_positive (K : Set (StrongDual ℂ M))
    (hpos : ∀ F ∈ K, ∀ a : M, 0 ≤ a → 0 ≤ F a)
    {F : WeakDual ℂ M} (hF : F ∈ weakFunctionalClosure K) :
    ∀ a : M, 0 ≤ a → 0 ≤ F a := by
  intro a ha
  apply closure_minimal (t := {G : WeakDual ℂ M | 0 ≤ G a}) _
    (isClosed_le continuous_const (WeakDual.eval_continuous a)) hF
  rintro _ ⟨G, hGK, rfl⟩
  exact hpos G hGK a ha

omit [PartialOrder M] [StarOrderedRing M] in
lemma unitaryPullback_norm_le (F : StrongDual ℂ M) (u : unitary M) :
    ‖unitaryPullback F u‖ ≤ ‖F‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro a
  have hn : ‖(u : M) * a * star (u : M)‖ = ‖a‖ := by
    rw [show star (u : M) = (star u : unitary M) from rfl,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
  simpa only [unitaryPullback_apply, hn] using F.le_opNorm ((u : M) * a * star (u : M))

omit [PartialOrder M] [StarOrderedRing M] in
lemma unitaryOrbitHull_norm_le (F : StrongDual ℂ M) {G : StrongDual ℂ M}
    (hG : G ∈ unitaryOrbitHull F) : ‖G‖ ≤ ‖F‖ := by
  have hsubset : unitaryOrbitHull F ⊆ Metric.closedBall 0 ‖F‖ := by
    apply closure_minimal _ Metric.isClosed_closedBall
    apply convexHull_min _ (convex_closedBall (0 : StrongDual ℂ M) ‖F‖)
    rintro _ ⟨u, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using unitaryPullback_norm_le F u
  simpa only [Metric.mem_closedBall, dist_zero_right] using hsubset hG

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_WeakPredual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normal dual, with its weak-star topology, is the weak predual. -/

noncomputable section

open Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The normal-functional embedding with both weak topologies. -/
def weakPredualMap (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (x : WeakSpace ℂ X) : WeakDual ℂ M :=
  StrongDual.toWeakDual (predualEmbedding e ((toWeakSpace ℂ X).symm x))

@[simp] lemma weakPredualMap_apply (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (x : WeakSpace ℂ X) (a : M) :
    weakPredualMap e x a = star (e.symm a ((toWeakSpace ℂ X).symm x)) := rfl

lemma weakPredualMap_continuous (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    Continuous (weakPredualMap e) := by
  apply WeakDual.continuous_of_continuous_eval
  intro a
  exact (WeakBilin.eval_continuous (topDualPairing ℂ X).flip (e.symm a)).star

/-- Evaluating against every algebra element recovers the weak topology on
its predual; hence the normal embedding is a topological embedding. -/
theorem weakPredualMap_isEmbedding (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    Topology.IsEmbedding (weakPredualMap e) := by
  let g (F : WeakDual ℂ M) (f : StrongDual ℂ X) : ℂ := star (F (e f))
  have hg : Continuous g := continuous_pi (fun f => (WeakDual.eval_continuous (e f)).star)
  have heq : g ∘ weakPredualMap e = fun x : WeakSpace ℂ X =>
      fun f : StrongDual ℂ X => f ((toWeakSpace ℂ X).symm x) := by
    funext x f
    simp only [Function.comp_apply, g, weakPredualMap_apply, e.symm_apply_apply, star_star]
  apply Topology.IsEmbedding.of_comp (weakPredualMap_continuous e) hg
  rw [heq]
  exact WeakBilin.isEmbedding (B := (topDualPairing ℂ X).flip) (fun x y h => by
    apply (toWeakSpace ℂ X).symm.injective
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
    intro f
    exact congrArg (fun L : StrongDual ℂ X →ₗ[ℂ] ℂ => L f) h)

lemma range_weakPredualMap (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    Set.range (weakPredualMap e) =
      {F : WeakDual ℂ M | WeakDual.toStrongDual F ∈ normalDual e} := by
  ext F
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(toWeakSpace ℂ X).symm x, rfl⟩
  · intro hF
    obtain ⟨x, hx⟩ := hF
    refine ⟨toWeakSpace ℂ X x, ?_⟩
    exact congrArg StrongDual.toWeakDual hx

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_UnitaryPredualAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The isometric unitary action on a von Neumann predual. -/

noncomputable section

open Topology

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma unitaryPullback_one (F : StrongDual ℂ M) : unitaryPullback F 1 = F := by
  ext a
  simp only [unitaryPullback_apply, OneMemClass.coe_one, star_one, one_mul, mul_one]

lemma unitaryPullback_mul (F : StrongDual ℂ M) (u v : unitary M) :
    unitaryPullback (unitaryPullback F u) v = unitaryPullback F (u * v) := by
  ext a
  simp only [unitaryPullback_apply, Submonoid.coe_mul, star_mul, mul_assoc]

/-- Unitary conjugation acts isometrically on bounded scalar functionals. -/
def unitaryDualEquiv (u : unitary M) : StrongDual ℂ M ≃ₗᵢ[ℂ] StrongDual ℂ M where
  toFun F := unitaryPullback F u
  invFun F := unitaryPullback F (star u)
  left_inv F := by
    change unitaryPullback (unitaryPullback F u) (star u) = F
    rw [unitaryPullback_mul, Unitary.mul_star_self, unitaryPullback_one]
  right_inv F := by
    change unitaryPullback (unitaryPullback F (star u)) u = F
    rw [unitaryPullback_mul, Unitary.star_mul_self, unitaryPullback_one]
  map_add' F G := by ext a; rfl
  map_smul' c F := by ext a; rfl
  norm_map' F := by
    apply le_antisymm (unitaryPullback_norm_le F u)
    have h := unitaryPullback_norm_le (unitaryPullback F u) (star u)
    simpa only [unitaryPullback_mul, Unitary.mul_star_self, unitaryPullback_one] using h

variable [PartialOrder M] [StarOrderedRing M]

/-- Identification of the predual with the normal functionals. -/
def predualNormalEquiv (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) : X ≃ₗᵢ⋆[ℂ] normalDual e :=
  (predualEmbedding e).equivRange

omit [CompleteSpace X] [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma predualNormalEquiv_coe (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (x : X) :
    (predualNormalEquiv e x).val = predualEmbedding e x := rfl

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_NormalOrbitInvariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convexity and invariance of the compact normal-state orbit. -/

noncomputable section

open Topology

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma weakOrbitClosure_convex (F : StrongDual ℂ M) :
    Convex ℝ (weakFunctionalClosure (unitaryOrbitHull F)) := by
  have hsmul : ContinuousConstSMul ℝ (WeakDual ℂ M) :=
    ⟨fun r => WeakDual.continuous_of_continuous_eval (fun a =>
      (WeakDual.eval_continuous a).const_smul r)⟩
  have hHull : Convex ℝ (unitaryOrbitHull F) :=
    (convex_convexHull ℝ (Set.range (unitaryPullback F))).closure
  let L : StrongDual ℂ M →ₗ[ℝ] WeakDual ℂ M :=
    { toFun := StrongDual.toWeakDual
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hImage : Convex ℝ (L '' unitaryOrbitHull F) := hHull.linear_image L
  have hClosed : Convex ℝ (closure (L '' unitaryOrbitHull F)) :=
    @Convex.closure ℝ (WeakDual ℂ M) _ _ _ _ _ _ hsmul _ hImage
  exact hClosed

/-- The weak predual embedding is real-linear. -/
def weakPredualRealMap (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    WeakSpace ℂ X →ₗ[ℝ] WeakDual ℂ M where
  toFun := weakPredualMap e
  map_add' x y := by
    apply WeakDual.toStrongDual.injective
    ext a
    change star (e.symm a ((toWeakSpace ℂ X).symm (x + y))) = _
    simp only [map_add, star_add]
    rfl
  map_smul' r x := by
    apply WeakDual.toStrongDual.injective
    ext a
    change star (e.symm a ((r : ℂ) • (toWeakSpace ℂ X).symm x)) =
      (r : ℂ) • star (e.symm a ((toWeakSpace ℂ X).symm x))
    rw [map_smul, star_smul]
    simp only [Complex.star_def, Complex.conj_ofReal]

variable [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
lemma weakFunctionalClosure_eval_eq (K : Set (StrongDual ℂ M)) (a : M) (c : ℂ)
    (h : ∀ G ∈ K, G a = c) {F : WeakDual ℂ M} (hF : F ∈ weakFunctionalClosure K) :
    F a = c := by
  apply closure_minimal (t := {G : WeakDual ℂ M | G a = c}) _
    (isClosed_eq (WeakDual.eval_continuous a) continuous_const) hF
  rintro _ ⟨G, hG, rfl⟩
  exact h G hG

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_FiniteNormalTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normal traces in finite von Neumann algebras

Ringrose, Theorem 5.4: the compact convex unitary orbit of a positive normal
functional contains a normal trace with the same values on the center.
This construction assumes no scalar or center-valued trace.
-/

noncomputable section

open Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma tracial_of_unitary_invariant (F : StrongDual ℂ M)
    (hinv : ∀ (u : unitary M) (a : M), F ((u : M) * a * star (u : M)) = F a) :
    ∀ a b : M, F (a * b) = F (b * a) := by
  classical
  have hu (u : unitary M) (b : M) : F ((u : M) * b) = F (b * (u : M)) := by
    calc
      F ((u : M) * b) = F ((u : M) * (b * (u : M)) * star (u : M)) := by
        simp only [mul_assoc, Unitary.mul_star_self_of_mem u.property, mul_one]
      _ = F (b * (u : M)) := hinv u _
  intro a b
  obtain ⟨u, c, ha, _⟩ := CStarAlgebra.exists_sum_four_unitary a
  rw [ha, Finset.sum_mul, Finset.mul_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_mul_assoc, mul_smul_comm, map_smul, map_smul, hu]

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_IsometryDefectColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Orthogonal columns from an isometry defect

A nonunitary isometry supplies countably many equivalent, orthogonal defect
projections. This is an algebraic ingredient of the properly infinite case.
-/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M]

def isometryDefect (v : M) : M := 1 - v * star v

lemma isometryDefect_mul {v : M} (hv : star v * v = 1) :
    isometryDefect v * v = 0 := by
  rw [isometryDefect, sub_mul, one_mul, mul_assoc, hv, mul_one, sub_self]

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_OperatorSystemCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compression of positive matrix levels on a unital linear subspace. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A H K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def compressOperatorSystem (S : Submodule ℂ A) (φ : S →ₗ[ℂ] (H →L[ℂ] H))
    (V : K →L[ℂ] H) : S →ₗ[ℂ] (K →L[ℂ] K) where
  toFun a := V.adjoint.comp ((φ a).comp V)
  map_add' a b := by ext ξ; simp
  map_smul' z a := by ext ξ; simp

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_ScalarMatrixActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entrywise scalar matrices and their action on matrix amplifications. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def entrywiseMatrixLinear (T : A →ₗ[ℂ] B) (n : ℕ) :
    CStarMatrix (Fin n) (Fin n) A →ₗ[ℂ] CStarMatrix (Fin n) (Fin n) B :=
  CStarMatrix.mapₗ T

end BoundedHochschild.KadisonRingrose

end

end OAI
end


