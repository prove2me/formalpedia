-- Prove2me | Definitions.Def_OAIQ025S001
-- name    : OAIQ025S001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T21:45:34.95399+00:00
-- url     : https://prove2.me/theorems/6022a018-f544-4051-855c-482eade0a374
-- title:
--   Definitions bundle OAIQ025S001 of the split of OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Release061.main`, carved from OpenAI's openai/math development (OpenAI, *Symmetry of semialgebraic bounded domains with compact quotient (result family 058)*, OpenAI Math Release, September 24, 2026, result family 58, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 321 declarations of OpenAI's Lean: 123 definitions, 6 inductive types or structures, 1 instance and 191 theorems. The definitions and types are `OAI.Release061.Biholomorph.ofEntireHomeomorph`, `OAI.Release061.Biholomorph.ofOpenPartialHomeomorph`, `OAI.Release061.BoundaryOffsetData`, `OAI.Release061.Complexify.coefficient`, `OAI.Release061.Complexify.monomial`, `OAI.Release061.Complexify.series`, `OAI.Release061.Flatten.imaginaryPart`, `OAI.Release061.Flatten.realEmbedding`, `OAI.Release061.Flatten.realPart`, `OAI.Release061.Flatten.shearEquiv`, `OAI.Release061.HasAnalyticNashCover`, `OAI.Release061.HasFiniteNashCover`, `OAI.Release061.Hermitian.axisNormalization`, `OAI.Release061.Hermitian.heisenbergHomeomorph`, `OAI.Release061.Hermitian.heisenbergShift`, `OAI.Release061.Hermitian.hermLinearLeft`, `OAI.Release061.Hermitian.hermPart`, `OAI.Release061.Hermitian.hermQuadratic`, `OAI.Release061.Hermitian.holBilinear`, `OAI.Release061.Hermitian.holContinuous`, `OAI.Release061.Hermitian.holPart`, `OAI.Release061.Hermitian.holQuadratic`, `OAI.Release061.Hermitian.normalTranslation`, `OAI.Release061.Hermitian.quadraticShear`, `OAI.Release061.Hermitian.symmetrize`, `OAI.Release061.NashBoundaryChart`, `OAI.Release061.NashBoundaryChart.GoodAt`, `OAI.Release061.NashBoundaryChart.family`, `OAI.Release061.NashBoundaryChart.normalInjection`, `OAI.Release061.NashBoundaryChart.oldOffset`, `OAI.Release061.NashBoundaryChart.oldOffsetDerivative`, `OAI.Release061.NashBoundaryChart.oldParameter`, `OAI.Release061.NashBoundaryChart.oldPosition`, `OAI.Release061.NashBoundaryChart.sliceDomain`, `OAI.Release061.NashBoundaryChart.sliceGraph`, `OAI.Release061.NashBoundaryChart.sliceLift`, `OAI.Release061.NashBoundaryChart.sliceParameter`, `OAI.Release061.NashBoundaryScalingChart`, `OAI.Release061.NashBoundaryScalingChart.HasCutoffs`, `OAI.Release061.NashBoundaryScalingChart.backward` and 89 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `SymmetricDomains_AffineBand`, `SymmetricDomains_AffineProductCoordinates`, `SymmetricDomains_AnalyticMulZeroGerm`, `SymmetricDomains_AnalyticNashRefinement`, `SymmetricDomains_AnalyticReparameterization`, `SymmetricDomains_BishopAnalyticDiscs`, `SymmetricDomains_BishopBoundarySolution`, `SymmetricDomains_BishopDiscRadialExpansion`, `SymmetricDomains_BishopPathInterior`, `SymmetricDomains_BoundaryInjective`, `SymmetricDomains_CayleyTangentBound`, `SymmetricDomains_Centered`, `SymmetricDomains_CocompactChartDiscContinuity`, `SymmetricDomains_ContinuityPrinciple`, `SymmetricDomains_CosineBumpWeightedSummable`, `SymmetricDomains_DecayWeightDeriv`, `SymmetricDomains_DiscCompactness`, `SymmetricDomains_DiscRelationCompactLocal`, `SymmetricDomains_EventualOffsetBall`, `SymmetricDomains_FiniteCoveringRamifiedSection`, `SymmetricDomains_FiniteProperMapOpen`, `SymmetricDomains_FiniteUnion`, `SymmetricDomains_ForwardBackwardGerm`, `SymmetricDomains_GenericNashNormalCoordinates`, `SymmetricDomains_GenericNormalGraphProjection`, `SymmetricDomains_GenericSurjectiveRealNormal`, `SymmetricDomains_GoodNashBoundary`, `SymmetricDomains_HeisenbergShiftAxis`, `SymmetricDomains_HermPartUnit`, `SymmetricDomains_HermiteSignature`, `SymmetricDomains_HolQuadraticSmul`, `SymmetricDomains_HorizontalGraphComplexification`, `SymmetricDomains_IndependentConormals`, `SymmetricDomains_InterpolateRealUpper`, `SymmetricDomains_LocallySmallSlopeGood`, `SymmetricDomains_NoncollapsedSupportedBoundary`, `SymmetricDomains_NormalOffsetFamilyJoint`, `SymmetricDomains_NormalizedLocalInverse`, `SymmetricDomains_OffsetDerivative`, `SymmetricDomains_OldOffsetOldPosition`, `SymmetricDomains_Pair`, `SymmetricDomains_PolynomialEmptyInterior`, `SymmetricDomains_PolynomialSignSetFinite`, `SymmetricDomains_PolynomialSignSetProjection`, `SymmetricDomains_PolynomialSignSetProjection2`, `SymmetricDomains_PolynomialSignSetQuery`, `SymmetricDomains_PolynomialSignSetRoot`, `SymmetricDomains_PolynomialSignSetSigns`, `SymmetricDomains_ProjectionNashChartGerms`, `SymmetricDomains_ProperEventuallyFiberSubset`, `SymmetricDomains_QuadraticModelResidualFiber`, `SymmetricDomains_RawQuadraticModelNormalization`, `SymmetricDomains_RootEvaluationSurjective`, `SymmetricDomains_RootMomentCoefficients`, `SymmetricDomains_RootSignPattern`, `SymmetricDomains_SampleAllChambers`, `SymmetricDomains_ScaledModelC1Limit`, `SymmetricDomains_ScaledRadialOperatorApply`, `SymmetricDomains_SemialgebraicBoundaryFiniteNash`, `SymmetricDomains_SemialgebraicPolynomialNonzero`, `SymmetricDomains_SignVariationsPositiveRoots`, `SymmetricDomains_SignatureRootValues`, `SymmetricDomains_SliceGraphDerivativeBound`, `SymmetricDomains_SortedFiberSelection`, `SymmetricDomains_SupportCayleyOpenImage`, `SymmetricDomains_TarskiQueryCharpoly`, `SymmetricDomains_Vector`, `SymmetricDomains_VerticalPieceBasePolynomial`, `SymmetricDomains_ZeroLocusPolynomialSmooth`.
--
--   **Imports.** It imports the published bundle `Def_SymmetricDomains`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ025S003`; the statements `OAI.Release061.Biholomorph.hermitian_model_bounded_symmetric`, `OAI.Release061.NashBoundaryChart.locally_small_slope_good`, `OAI.Release061.NashBoundaryChart.scaling_chart`, `OAI.Release061.NashBoundaryScalingChart.independent_support_rows`, `OAI.Release061.NashPatch.null_nonsmallgood_generic`, `OAI.Release061.NashPatch.principal_rank_dichotomy`, `OAI.Release061.interior_balls_from_small_slope_graphs`, `OAI.Release061.isSemialgebraic_centered_nash_cover`, `OAI.Release061.original_small_slope_good_supported_boundary`, `OAI.Release061.original_supported_hermitian_model`, `OAI.Release061.prime_boundary_generic_fiber` and `OAI.Release061.semialgebraic_inward_analytic_from_family`; the proofs of `OAI.Release061.NashBoundaryChart.scaling_chart`, `OAI.Release061.NashBoundaryScalingChart.independent_support_rows`, `OAI.Release061.NashPatch.null_nonsmallgood_generic`, `OAI.Release061.original_small_slope_good_supported_boundary` and `OAI.Release061.prime_boundary_generic_fiber`.
-- source:
--   OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 58; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symmetry-of-semialgebraic-bounded-domains-with-compact-quotient-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_SymmetricDomains

section
-- module Solutions.OAIQ025_SD.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_FiniteProperMapOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra


noncomputable def quotientCoordinate {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (j : Fin n) : MvPolynomial (Fin n) ℂ ⧸ I :=
  (Ideal.Quotient.mkₐ ℂ I) (MvPolynomial.X j)

noncomputable def affineCharacter {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (z : MvPolynomial.zeroLocus ℂ I) : (MvPolynomial (Fin n) ℂ ⧸ I) →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ I (MvPolynomial.aeval z.val) (fun p hp => z.property p hp)

@[simp] theorem affineCharacter_mk {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (z : MvPolynomial.zeroLocus ℂ I) (p : MvPolynomial (Fin n) ℂ) :
    affineCharacter I z ((Ideal.Quotient.mkₐ ℂ I) p) = MvPolynomial.eval z.val p := rfl

@[simp] theorem affineCharacter_coordinate {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (z : MvPolynomial.zeroLocus ℂ I) (j : Fin n) :
    affineCharacter I z (quotientCoordinate I j) = z.val j := by
  change MvPolynomial.eval z.val (MvPolynomial.X j) = z.val j
  exact MvPolynomial.eval_X _

theorem character_comp_mk {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (f : (MvPolynomial (Fin n) ℂ ⧸ I) →ₐ[ℂ] ℂ) :
    f.comp (Ideal.Quotient.mkₐ ℂ I) = MvPolynomial.aeval (fun j => f (quotientCoordinate I j)) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp [quotientCoordinate]

noncomputable def pointOfCharacter {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (f : (MvPolynomial (Fin n) ℂ ⧸ I) →ₐ[ℂ] ℂ) : MvPolynomial.zeroLocus ℂ I := by
  refine ⟨fun j => f (quotientCoordinate I j), fun p hp => ?_⟩
  have he := DFunLike.congr_fun (character_comp_mk I f) p
  change f (Ideal.Quotient.mk I p) = MvPolynomial.eval _ p at he
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero] at he
  exact he.symm

noncomputable def affineCharacterEquiv {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    MvPolynomial.zeroLocus ℂ I ≃ ((MvPolynomial (Fin n) ℂ ⧸ I) →ₐ[ℂ] ℂ) where
  toFun := affineCharacter I
  invFun := pointOfCharacter I
  left_inv z := by
    apply Subtype.ext
    funext j
    exact affineCharacter_coordinate I z j
  right_inv f := by
    ext t
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I t
    exact (DFunLike.congr_fun (character_comp_mk I f) p).symm

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ProperEventuallyFiberSubset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra

def ScalarAnalyticAt {n : ℕ} {V : Set (Fin n → ℂ)} (h : V → ℂ) (q : V) : Prop :=
  ∃ F : (Fin n → ℂ) → ℂ, AnalyticAt ℂ F q.val ∧
    h =ᶠ[𝓝 q] (fun x => F x.val)

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ZeroLocusPolynomialSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra


def SmoothAtSubset {n : ℕ} (S : Set (Affine n)) (q : Affine n) : Prop :=
  ∃ (m : ℕ) (W : Set (Affine n)), W ⊆ S ∧
    IsOpen ((Subtype.val : S → Affine n) ⁻¹' W) ∧ q ∈ W ∧
    ∃ D : Set (Affine m), IsOpen D ∧ Nonempty (Biholomorph W D)

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_DiscRelationCompactLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra

noncomputable def actionBiholomorph {n : ℕ} (U : Set (Affine n))
    (Γ : Type*) [Group Γ] [MulAction Γ U] [ContinuousConstSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (γ : Γ) : Biholomorph U U where
  toHomeomorph := Homeomorph.smul γ
  holomorphic_toFun := hhol γ
  holomorphic_invFun := hhol γ⁻¹

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_DiscCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra

open Set

theorem holomorphicOnSubset_const {n m : ℕ} (S : Set (Affine n)) (c : Affine m) :
    HolomorphicOnSubset S (fun _ => c) := by
  intro p
  exact ⟨univ,isOpen_univ,mem_univ _,fun _ => c,analyticOnNhd_const,fun _ _ => rfl⟩

noncomputable def biholomorphOfSubsingleton {n m : ℕ} (S : Set (Affine n))
    (T : Set (Affine m)) [Subsingleton S] [Subsingleton T] [Nonempty S] [Nonempty T] :
    Biholomorph S T where
  toHomeomorph := {
    toFun := fun _ => Classical.choice inferInstance
    invFun := fun _ => Classical.choice inferInstance
    left_inv := fun _ => Subsingleton.elim _ _
    right_inv := fun _ => Subsingleton.elim _ _
    continuous_toFun := continuous_const
    continuous_invFun := continuous_const }
  holomorphic_toFun := holomorphicOnSubset_const S (Classical.choice (inferInstance : Nonempty T)).val
  holomorphic_invFun := holomorphicOnSubset_const T (Classical.choice (inferInstance : Nonempty S)).val

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ContinuityPrinciple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra
open Set

def RelationSteps {X : Type*} (R : X → X → Prop) : ℕ → X → X → Prop
  | 0, x, y => x = y
  | n+1, x, y => RelationSteps R n x y ∨ ∃ z, RelationSteps R n x z ∧ R z y

open Filter
open scoped Topology

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialEmptyInterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology

inductive PolynomialSignSet {X ι : Type*} (c : X → ι → ℝ) : Set X → Prop
  | zero (p : MvPolynomial ι ℝ) : PolynomialSignSet c {x | MvPolynomial.eval (c x) p = 0}
  | positive (p : MvPolynomial ι ℝ) : PolynomialSignSet c {x | 0 < MvPolynomial.eval (c x) p}
  | compl {S : Set X} : PolynomialSignSet c S → PolynomialSignSet c Sᶜ
  | union {S T : Set X} : PolynomialSignSet c S → PolynomialSignSet c T → PolynomialSignSet c (S ∪ T)

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialSignSetFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

namespace PolynomialSignSet
open Set
open scoped Classical
variable {X ι : Type*} {c : X → ι → ℝ}

lemma univ : PolynomialSignSet c Set.univ := by simpa using zero (c := c) 0
lemma empty : PolynomialSignSet c ∅ := by simpa using (univ (c := c)).compl
lemma inter {S T : Set X} (hS : PolynomialSignSet c S) (hT : PolynomialSignSet c T) :
    PolynomialSignSet c (S ∩ T) := by
  simpa only [compl_union,compl_compl] using (hS.compl.union hT.compl).compl
lemma const (p : Prop) : PolynomialSignSet c {_x : X | p} := by
  by_cases h : p
  · simpa [h] using (univ (c := c))
  · simpa [h] using (empty (c := c))

lemma exists_finset {α : Type*} (s : Finset α) (P : α → X → Prop)
    (hP : ∀ a ∈ s, PolynomialSignSet c {x | P a x}) :
    PolynomialSignSet c {x | ∃ a ∈ s, P a x} := by
  induction s using Finset.induction_on with
  | empty => simpa using (empty (c := c))
  | @insert a s ha ih =>
    have he : {x | ∃ b ∈ insert a s, P b x} = {x | P a x} ∪ {x | ∃ b ∈ s, P b x} := by
      ext x
      simp
    rw [he]
    exact (hP a (by simp)).union (ih (fun b hb => hP b (by simp [hb])))

lemma exists_finite {α : Type*} [Finite α] (P : α → X → Prop)
    (hP : ∀ a, PolynomialSignSet c {x | P a x}) :
    PolynomialSignSet c {x | ∃ a, P a x} := by
  let := Fintype.ofFinite α
  simpa using exists_finset Finset.univ P (fun a _ => hP a)

lemma forall_finite {α : Type*} [Finite α] (P : α → X → Prop)
    (hP : ∀ a, PolynomialSignSet c {x | P a x}) :
    PolynomialSignSet c {x | ∀ a, P a x} := by
  convert (exists_finite (fun a x => ¬ P a x) (fun a => (hP a).compl)).compl using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp

lemma sign (p : MvPolynomial ι ℝ) (s : SignType) :
    PolynomialSignSet c {x | SignType.sign (MvPolynomial.eval (c x) p) = s} := by
  cases s
  · simpa only [SignType.zero_eq_zero,sign_eq_zero_iff] using zero (c := c) p
  · simpa only [SignType.neg_eq_neg_one,sign_eq_neg_one_iff,map_neg,neg_pos] using positive (c := c) (-p)
  · simpa only [SignType.pos_eq_one,sign_eq_one_iff] using positive (c := c) p

end PolynomialSignSet

namespace SignElimination
open MvPolynomial Set
open scoped Classical BigOperators

def RationalOn {X ι : Type*} (c : X → ι → ℝ) (S : Set X) (f : X → ℝ) : Prop :=
  ∃ p q : MvPolynomial ι ℝ, ∀ x ∈ S,
    MvPolynomial.eval (c x) q ≠ 0 ∧ f x = MvPolynomial.eval (c x) p / MvPolynomial.eval (c x) q

namespace RationalOn
variable {X ι : Type*} {c : X → ι → ℝ} {S T : Set X} {f g : X → ℝ}

lemma congr (hf : RationalOn c S f) (hfg : ∀ x ∈ S, f x = g x) : RationalOn c S g := by
  obtain ⟨p,q,h⟩ := hf
  exact ⟨p,q,fun x hx => ⟨(h x hx).1,(hfg x hx).symm.trans (h x hx).2⟩⟩

lemma mono (hf : RationalOn c S f) (hTS : T ⊆ S) : RationalOn c T f := by
  obtain ⟨p,q,h⟩ := hf
  exact ⟨p,q,fun x hx => h x (hTS hx)⟩

lemma polynomial (p : MvPolynomial ι ℝ) : RationalOn c S (fun x => MvPolynomial.eval (c x) p) := by
  exact ⟨p,1,fun x hx => by simp⟩

lemma const (a : ℝ) : RationalOn c S (fun _ => a) := by
  simpa using polynomial (c := c) (S := S) (C a)

lemma add (hf : RationalOn c S f) (hg : RationalOn c S g) : RationalOn c S (fun x => f x + g x) := by
  obtain ⟨p,q,hp⟩ := hf
  obtain ⟨r,s,hr⟩ := hg
  refine ⟨p*s+r*q,q*s,fun x hx => ?_⟩
  obtain ⟨hq,hf⟩ := hp x hx
  obtain ⟨hs,hg⟩ := hr x hx
  simp only [map_add,map_mul]
  refine ⟨mul_ne_zero hq hs,?_⟩
  rw [hf,hg]
  field_simp

lemma neg (hf : RationalOn c S f) : RationalOn c S (fun x => -f x) := by
  obtain ⟨p,q,h⟩ := hf
  exact ⟨-p,q,fun x hx => ⟨(h x hx).1,by simp [(h x hx).2,neg_div]⟩⟩

lemma mul (hf : RationalOn c S f) (hg : RationalOn c S g) : RationalOn c S (fun x => f x*g x) := by
  obtain ⟨p,q,hp⟩ := hf
  obtain ⟨r,s,hr⟩ := hg
  refine ⟨p*r,q*s,fun x hx => ?_⟩
  exact ⟨by simp [mul_ne_zero (hp x hx).1 (hr x hx).1],by
    simp only [(hp x hx).2,(hr x hx).2,map_mul,div_mul_div_comm]⟩

lemma inv (hf : RationalOn c S f) (hn : ∀ x ∈ S, f x ≠ 0) : RationalOn c S (fun x => (f x)⁻¹) := by
  obtain ⟨p,q,h⟩ := hf
  refine ⟨q,p,fun x hx => ?_⟩
  have hp : MvPolynomial.eval (c x) p ≠ 0 := by
    intro hz
    have he := (h x hx).2
    simp [hz] at he
    exact hn x hx he
  exact ⟨hp,by simp [(h x hx).2]⟩

lemma div (hf : RationalOn c S f) (hg : RationalOn c S g) (hn : ∀ x ∈ S, g x ≠ 0) :
    RationalOn c S (fun x => f x / g x) := by
  simpa only [div_eq_mul_inv] using hf.mul (hg.inv hn)

lemma sum {α : Type*} (s : Finset α) (f : α → X → ℝ)
    (hf : ∀ a ∈ s, RationalOn c S (f a)) : RationalOn c S (fun x => ∑ a ∈ s, f a x) := by
  induction s using Finset.induction_on with
  | empty => simpa using (const (c := c) (S := S) 0)
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      (hf a (by simp)).add (ih (fun b hb => hf b (by simp [hb])))

lemma eval {α : Type*} (p : MvPolynomial α ℝ) (f : α → X → ℝ)
    (hf : ∀ a, RationalOn c S (f a)) :
    RationalOn c S (fun x => MvPolynomial.eval (fun a => f a x) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using (const (c := c) (S := S) a)
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p a hp => simpa only [map_mul,MvPolynomial.eval_X] using hp.mul (hf a)

lemma sign_inv_real (a : ℝ) : SignType.sign a⁻¹ = SignType.sign a := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rw [sign_neg ha,sign_neg (inv_lt_zero.mpr ha)]
  · simp [ha]
  · rw [sign_pos ha,sign_pos (inv_pos.mpr ha)]

lemma sign_set (hf : RationalOn c S f) (hS : PolynomialSignSet c S) (s : SignType) :
    PolynomialSignSet c (S ∩ {x | SignType.sign (f x) = s}) := by
  obtain ⟨p,q,h⟩ := hf
  have he : S ∩ {x | SignType.sign (f x) = s} =
      S ∩ {x | SignType.sign (MvPolynomial.eval (c x) (p*q)) = s} := by
    ext x
    simp only [mem_inter_iff,mem_ofPred_eq]
    apply and_congr_right
    intro hx
    rw [(h x hx).2,map_mul,div_eq_mul_inv,sign_mul,sign_mul,sign_inv_real]
  rw [he]
  exact hS.inter (PolynomialSignSet.sign _ _)

end RationalOn

lemma polynomialSignSet_finite_signs {X ι α : Type*} [Finite α]
    {c : X → ι → ℝ} {S : Set X} (hS : PolynomialSignSet c S)
    (f : α → X → ℝ) (hf : ∀ a, RationalOn c S (f a)) (W : (α → SignType) → Prop) :
    PolynomialSignSet c (S ∩ {x | W (fun a => SignType.sign (f a x))}) := by
  have h (σ : α → SignType) :
      PolynomialSignSet c {x | x ∈ S ∧ W σ ∧ ∀ a, SignType.sign (f a x) = σ a} := by
    have hsign := PolynomialSignSet.forall_finite
      (fun a x => x ∈ S ∧ SignType.sign (f a x) = σ a)
      (fun a => (hf a).sign_set hS (σ a))
    have hh := (hS.inter (PolynomialSignSet.const (c := c) (W σ))).inter hsign
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [mem_ofPred_eq,mem_inter_iff]
    constructor
    · rintro ⟨hx,hw,hs⟩
      exact ⟨⟨hx,hw⟩,fun a => ⟨hx,hs a⟩⟩
    · rintro ⟨⟨hx,hw⟩,hs⟩
      exact ⟨hx,hw,fun a => (hs a).2⟩
  have hh := PolynomialSignSet.exists_finite _ h
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_ofPred_eq,mem_inter_iff]
  constructor
  · rintro ⟨hx,hw⟩
    exact ⟨_,hx,hw,fun _ => rfl⟩
  · rintro ⟨σ,hx,hw,hs⟩
    exact ⟨hx,(funext hs) ▸ hw⟩

end SignElimination
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_BoundaryInjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Metric Complex
open scoped Topology
noncomputable section
namespace Release061.Wiener
open scoped BigOperators ComplexConjugate Topology
open Set Filter

noncomputable def weight (n : ℤ) : ℝ := 1+|(n : ℝ)|
lemma weight_pos (n : ℤ) : 0 < weight n := by dsimp [weight]; positivity
lemma one_le_weight (n : ℤ) : 1 ≤ weight n := by simp [weight]
lemma weight_add_le (n m : ℤ) : weight (n+m) ≤ weight n*weight m := by
  dsimp [weight]
  rw [Int.cast_add]
  have h := abs_add_le (n : ℝ) (m : ℝ)
  have hnm : 0 ≤ |(n : ℝ)| * |(m : ℝ)| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  nlinarith

instance instFactLtRealOfNat_solutions : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

abbrev Circle := AddCircle (1 : ℝ)

def hilbertSymbol (n : ℤ) : ℂ := if 0 < n then Complex.I else if n < 0 then -Complex.I else 0

lemma hilbertSymbol_bound (n : ℤ) : ‖hilbertSymbol n‖ ≤ 1 := by
  unfold hilbertSymbol
  split_ifs <;> simp

lemma hilbertSymbol_neg (n : ℤ) : hilbertSymbol (-n) = conj (hilbertSymbol n) := by
  unfold hilbertSymbol
  split_ifs <;> simp_all
  all_goals omega

abbrev ClosedDisc := Metric.closedBall (0 : ℂ) 1

def schwarzMode (n : ℤ) (z : ℂ) : ℂ :=
  if 0 < n then Complex.I * (2*z^n.toNat-1) else Complex.I

lemma schwarzMode_continuous (n : ℤ) : Continuous (schwarzMode n) := by
  unfold schwarzMode
  split_ifs <;> fun_prop

lemma schwarzMode_bound (n : ℤ) {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖schwarzMode n z‖ ≤ 3 := by
  unfold schwarzMode
  split_ifs
  · rw [norm_mul,Complex.norm_I,one_mul]
    calc ‖2*z^n.toNat-1‖ ≤ ‖2*z^n.toNat‖+‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2*‖z‖^n.toNat+1 := by simp
      _ ≤ 3 := by have := (pow_le_one₀ (n := n.toNat) (norm_nonneg z) hz); linarith
  · simp

def schwarzModeC (n : ℤ) : C(ClosedDisc,ℂ) :=
  ⟨fun z => schwarzMode n z,(schwarzMode_continuous n).comp continuous_subtype_val⟩

open MeasureTheory

def fourierCLM (n : ℤ) : C(Circle,ℂ) →L[ℂ] ℂ :=
  ({ toFun f := fourierCoeff f n
     map_add' f g := by
       exact congrFun (fourierCoeff.add (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
         (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))) n
     map_smul' c f := fourierCoeff.const_smul f c n } : C(Circle,ℂ) →ₗ[ℂ] ℂ).mkContinuous 1 (by
      intro f
      have h : ∀ᵐ t ∂AddCircle.haarAddCircle, ‖fourier (-n) t • f t‖ ≤ ‖f‖ := by
        filter_upwards [] with t
        rw [norm_smul,fourier_apply,Circle.norm_coe,one_mul]
        exact f.norm_coe_le_norm t
      change ‖fourierCoeff f n‖ ≤ 1*‖f‖
      simpa [fourierCoeff] using norm_integral_le_of_norm_le_const h)

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_InterpolateRealUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.SignElimination
open Polynomial Finset
open scoped BigOperators Classical

noncomputable def realPartPolynomial (P : ℂ[X]) : ℝ[X] :=
  .ofFinsupp ⟨P.toFinsupp.coeff.mapRange Complex.re (by simp)⟩

@[simp] lemma realPartPolynomial_coeff (P : ℂ[X]) (n : ℕ) :
    (realPartPolynomial P).coeff n = (P.coeff n).re := rfl

lemma realPartPolynomial_degree_lt {P : ℂ[X]} {n : ℕ} (hP : P.degree < n) :
    (realPartPolynomial P).degree < n := by
  rw [degree_lt_iff_coeff_zero] at *
  intro k hk
  simp [hP k hk]

lemma realPartPolynomial_map {P : ℂ[X]} (hP : P.map (starRingEnd ℂ) = P) :
    (realPartPolynomial P).map Complex.ofRealHom = P := by
  ext n
  rw [coeff_map,realPartPolynomial_coeff]
  apply Complex.conj_eq_iff_re.mp
  simpa only [coeff_map] using congrArg (fun p : ℂ[X] => p.coeff n) hP

theorem real_interpolation_indexed {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (hx : Function.Injective x) (τ : ι → ι)
    (hτ : ∀ i, x (τ i) = starRingEnd ℂ (x i))
    (v : ι → ℂ) (hv : ∀ i, v (τ i) = starRingEnd ℂ (v i)) :
    ∃ P : ℝ[X], P.degree < Fintype.card ι ∧
      ∀ i, P.eval₂ Complex.ofRealHom (x i) = v i := by
  let P := Lagrange.interpolate univ x v
  have hdeg : P.degree < Fintype.card ι :=
    Lagrange.degree_interpolate_lt _ (fun _ _ _ _ h => hx h)
  have heval : ∀ i, P.eval (x i) = v i := fun i =>
    Lagrange.eval_interpolate_at_node _ (fun _ _ _ _ h => hx h) (mem_univ i)
  have hconj : P.map (starRingEnd ℂ) = P := by
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq univ (fun _ _ _ _ h => hx h)
      (degree_map_le.trans_lt hdeg) hdeg
    intro i _
    have hh := eval_map_apply (starRingEnd ℂ) (starRingEnd ℂ (x i)) (p := P)
    simp only [starRingEnd_apply,star_star] at hh
    rw [hh]
    change (starRingEnd ℂ) (P.eval ((starRingEnd ℂ) (x i))) = P.eval (x i)
    rw [← hτ i,heval,heval,hv]
    simp
  refine ⟨realPartPolynomial P,realPartPolynomial_degree_lt hdeg,fun i => ?_⟩
  rw [eval₂_eq_eval_map,realPartPolynomial_map hconj,heval]

def realComplexNodes {α β : Type*} (r : α → ℝ) (c : β → ℂ) : α ⊕ (β ⊕ β) → ℂ :=
  Sum.elim (fun a => (r a : ℂ)) (Sum.elim c (fun b => starRingEnd ℂ (c b)))

def conjugateSwap {α β : Type*} : α ⊕ (β ⊕ β) → α ⊕ (β ⊕ β) :=
  Sum.elim Sum.inl (Sum.elim (fun b => .inr (.inr b)) (fun b => .inr (.inl b)))

lemma realComplexNodes_conj {α β : Type*} (r : α → ℝ) (c : β → ℂ) (i) :
    realComplexNodes r c (conjugateSwap i) = starRingEnd ℂ (realComplexNodes r c i) := by
  rcases i with a | b
  · simp [realComplexNodes,conjugateSwap]
  · rcases b with b | b <;> simp [realComplexNodes,conjugateSwap]

lemma realComplexNodes_injective {α β : Type*} {r : α → ℝ} {c : β → ℂ}
    (hr : Function.Injective r) (hc : Function.Injective c) (hpos : ∀ b, 0 < (c b).im) :
    Function.Injective (realComplexNodes r c) := by
  intro i j h
  rcases i with a | (b | b) <;> rcases j with a' | (b' | b')
  · apply congrArg Sum.inl
    exact hr (Complex.ofReal_injective h)
  · have hi := congrArg Complex.im h
    simp only [realComplexNodes,Sum.elim_inl,Sum.elim_inr,Complex.ofReal_im] at hi
    exact False.elim ((hpos b').ne' hi.symm)
  · have hi := congrArg Complex.im h
    simp only [realComplexNodes,Sum.elim_inl,Sum.elim_inr,Complex.ofReal_im,
      Complex.conj_im] at hi
    have := hpos b'
    exact False.elim (by linarith)
  · have hi := congrArg Complex.im h
    simp only [realComplexNodes,Sum.elim_inl,Sum.elim_inr,Complex.ofReal_im] at hi
    exact False.elim ((hpos b).ne' hi)
  · exact congrArg (fun b => Sum.inr (Sum.inl b)) (hc h)
  · have hi := congrArg Complex.im h
    simp only [realComplexNodes,Sum.elim_inl,Sum.elim_inr,Complex.conj_im] at hi
    have := hpos b
    have := hpos b'
    exact False.elim (by linarith)
  · have hi := congrArg Complex.im h
    simp only [realComplexNodes,Sum.elim_inl,Sum.elim_inr,Complex.ofReal_im,
      Complex.conj_im] at hi
    have := hpos b
    exact False.elim (by linarith)
  · have hi := congrArg Complex.im h
    simp only [realComplexNodes,Sum.elim_inl,Sum.elim_inr,Complex.conj_im] at hi
    have := hpos b
    have := hpos b'
    exact False.elim (by linarith)
  · exact congrArg (fun b => Sum.inr (Sum.inr b)) (hc ((starRingEnd ℂ).injective h))

theorem interpolate_real_and_upper {α β : Type*} [Fintype α] [Fintype β]
    (r : α → ℝ) (c : β → ℂ) (hr : Function.Injective r) (hc : Function.Injective c)
    (hpos : ∀ b, 0 < (c b).im) (v : α → ℝ) (w : β → ℂ) :
    ∃ P : ℝ[X], P.degree < ((Fintype.card α + 2*Fintype.card β : ℕ) : WithBot ℕ) ∧
      (∀ a, P.eval (r a) = v a) ∧ (∀ b, P.eval₂ Complex.ofRealHom (c b) = w b) := by
  obtain ⟨P,hP,he⟩ := real_interpolation_indexed (realComplexNodes r c)
    (realComplexNodes_injective hr hc hpos) conjugateSwap (realComplexNodes_conj r c)
    (realComplexNodes v w) (realComplexNodes_conj v w)
  refine ⟨P,?_,?_,?_⟩
  · simpa only [Fintype.card_sum,two_mul,add_assoc] using hP
  · intro a
    have h := he (.inl a)
    change P.eval₂ Complex.ofRealHom (r a) = (v a : ℂ) at h
    apply Complex.ofReal_injective
    exact (eval₂_at_apply Complex.ofRealHom (r a) (p := P)).symm.trans h
  · intro b
    exact he (.inr (.inl b))

end Release061.SignElimination

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_RootEvaluationSurjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.SignElimination
open Polynomial Finset
open scoped BigOperators Classical

noncomputable abbrev complexify (P : ℝ[X]) : ℂ[X] := P.map Complex.ofRealHom

lemma complexify_conj (P : ℝ[X]) : (complexify P).map (starRingEnd ℂ) = complexify P := by
  ext n
  simp only [coeff_map,Complex.ofRealHom_eq_coe,Complex.conj_ofReal]

lemma complexify_ne_zero {P : ℝ[X]} (hP : P ≠ 0) : complexify P ≠ 0 :=
  (Polynomial.map_ne_zero_iff Complex.ofReal_injective).mpr hP

lemma complexify_eval_conj (P : ℝ[X]) (z : ℂ) :
    (complexify P).eval (starRingEnd ℂ z) = starRingEnd ℂ ((complexify P).eval z) := by
  have hh := eval_map_apply (starRingEnd ℂ) z (p := complexify P)
  rwa [complexify_conj] at hh

lemma complexify_real_eval (P : ℝ[X]) (x : ℝ) :
    (complexify P).eval (x : ℂ) = ((P.eval x : ℝ) : ℂ) :=
  eval_map_apply Complex.ofRealHom x

lemma complex_root_conj {P : ℝ[X]} (hP : P ≠ 0) {z : ℂ}
    (hz : z ∈ (complexify P).roots.toFinset) :
    starRingEnd ℂ z ∈ (complexify P).roots.toFinset := by
  rw [Multiset.mem_toFinset,mem_roots (complexify_ne_zero hP),IsRoot] at *
  rw [complexify_eval_conj,hz,map_zero]

lemma count_complex_root_conj (P : ℝ[X]) (z : ℂ) :
    (complexify P).roots.count (starRingEnd ℂ z) = (complexify P).roots.count z := by
  simp only [count_roots]
  have h := eq_rootMultiplicity_map (starRingEnd ℂ).injective z (p := complexify P)
  rw [complexify_conj] at h
  exact h.symm

lemma count_complex_root_real (P : ℝ[X]) (x : ℝ) :
    (complexify P).roots.count (x : ℂ) = P.roots.count x := by
  simp only [count_roots]
  exact (eq_rootMultiplicity_map Complex.ofReal_injective x (p := P)).symm

noncomputable abbrev RealRoot (P : ℝ[X]) := {x : ℝ // x ∈ P.roots.toFinset}
noncomputable abbrev UpperRoot (P : ℝ[X]) :=
  {z : ℂ // z ∈ (complexify P).roots.toFinset.filter (fun z => 0 < z.im)}

lemma realRoot_mem_complex {P : ℝ[X]} (hP : P ≠ 0) (a : RealRoot P) :
    (a.val : ℂ) ∈ (complexify P).roots.toFinset := by
  rw [Multiset.mem_toFinset,mem_roots (complexify_ne_zero hP),IsRoot,complexify_real_eval]
  have h := a.property
  rw [Multiset.mem_toFinset,mem_roots hP,IsRoot] at h
  simp [h]

noncomputable def rootNodes {P : ℝ[X]} (hP : P ≠ 0) :
    RealRoot P ⊕ (UpperRoot P ⊕ UpperRoot P) →
      {z : ℂ // z ∈ (complexify P).roots.toFinset} :=
  fun i => ⟨realComplexNodes (fun a : RealRoot P => a.val) (fun b : UpperRoot P => b.val) i,by
    rcases i with a | (b | b)
    · exact realRoot_mem_complex hP a
    · exact (mem_filter.mp b.property).1
    · exact complex_root_conj hP (mem_filter.mp b.property).1⟩

lemma rootNodes_bijective {P : ℝ[X]} (hP : P ≠ 0) : Function.Bijective (rootNodes hP) := by
  constructor
  · intro i j h
    have hh := congrArg Subtype.val h
    exact realComplexNodes_injective Subtype.val_injective Subtype.val_injective
      (fun b => (mem_filter.mp b.property).2) hh
  · intro z
    by_cases hz0 : z.val.im = 0
    · have he : (z.val.re : ℂ) = z.val := by
        apply Complex.ext <;> simp [hz0]
      have hr : z.val.re ∈ P.roots.toFinset := by
        rw [Multiset.mem_toFinset,mem_roots hP,IsRoot]
        apply Complex.ofReal_injective
        have hh := z.property
        rw [Multiset.mem_toFinset,mem_roots (complexify_ne_zero hP),IsRoot] at hh
        change ((P.eval z.val.re : ℝ) : ℂ) = (0:ℂ)
        rw [← complexify_real_eval,he,hh]
      exact ⟨.inl ⟨z.val.re,hr⟩,Subtype.ext he⟩
    · rcases lt_or_gt_of_ne hz0 with hneg | hpos
      · have hc : starRingEnd ℂ z.val ∈
            (complexify P).roots.toFinset.filter (fun z => 0 < z.im) := by
          exact mem_filter.mpr ⟨complex_root_conj hP z.property,by simpa using neg_pos.mpr hneg⟩
        refine ⟨.inr (.inr ⟨starRingEnd ℂ z.val,hc⟩),Subtype.ext ?_⟩
        simp [rootNodes,realComplexNodes]
      · exact ⟨.inr (.inl ⟨z.val,mem_filter.mpr ⟨z.property,hpos⟩⟩),rfl⟩

noncomputable def rootNodesEquiv {P : ℝ[X]} (hP : P ≠ 0) :
    (RealRoot P ⊕ (UpperRoot P ⊕ UpperRoot P)) ≃
      {z : ℂ // z ∈ (complexify P).roots.toFinset} :=
  Equiv.ofBijective (rootNodes hP) (rootNodes_bijective hP)

lemma root_dimension_le {P : ℝ[X]} (hP : P ≠ 0) :
    Fintype.card (RealRoot P) + 2*Fintype.card (UpperRoot P) ≤ P.natDegree := by
  have hc := Fintype.card_congr (rootNodesEquiv hP)
  have hcard : Fintype.card (RealRoot P) + 2*Fintype.card (UpperRoot P) =
      (complexify P).roots.toFinset.card := by
    simpa only [Fintype.card_sum,Fintype.card_coe,two_mul] using hc
  rw [hcard]
  exact (Multiset.toFinset_card_le _).trans (Polynomial.card_roots_map_le_natDegree P)

noncomputable def rootEvaluation (P : ℝ[X]) :
    (degreeLT ℝ P.natDegree) →ₗ[ℝ] ((RealRoot P → ℝ) × (UpperRoot P → ℂ)) where
  toFun A := (fun a => (aeval a.val) A.val,fun b => (aeval b.val) A.val)
  map_add' A B := by ext <;> simp
  map_smul' r A := by ext <;> simp

lemma rootEvaluation_surjective {P : ℝ[X]} (hP : P ≠ 0) :
    Function.Surjective (rootEvaluation P) := by
  rintro ⟨v,w⟩
  obtain ⟨A,hA,hreal,hupper⟩ := interpolate_real_and_upper
    (fun a : RealRoot P => a.val) (fun b : UpperRoot P => b.val)
    Subtype.val_injective Subtype.val_injective (fun b => (mem_filter.mp b.property).2) v w
  have hdeg : A ∈ degreeLT ℝ P.natDegree := mem_degreeLT.mpr
    (hA.trans_le (WithBot.coe_le_coe.mpr (root_dimension_le hP)))
  refine ⟨⟨A,hdeg⟩,?_⟩
  ext i
  · exact (aeval_def _ _).trans ((by simp : A.eval₂ (algebraMap ℝ ℝ) i.val = A.eval i.val).trans (hreal i))
  · exact hupper i

end Release061.SignElimination

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_RootSignPattern
attribute [-instance] _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
namespace SignElimination
open Polynomial Finset
open scoped BigOperators Classical

noncomputable def tarskiQuery (P Q : ℝ[X]) : ℝ :=
  ∑ x ∈ P.roots.toFinset, (SignType.sign (Q.eval x) : ℝ)

noncomputable def signCoefficient (s : SignType) (e : Fin 3) : ℝ :=
  match s with
  | .zero => ![1,0,-1] e
  | .pos => ![0,1/2,1/2] e
  | .neg => ![0,-1/2,1/2] e

lemma sign_indicator (s t : SignType) :
    ∑ e : Fin 3, signCoefficient s e * (t : ℝ)^(e.val) =
      if t = s then 1 else 0 := by
  cases s <;> cases t <;> norm_num [signCoefficient,Fin.sum_univ_three,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail] <;> decide

theorem sign_pattern_count {ι : Type*} [Fintype ι] (P : ℝ[X])
    (Q : ι → ℝ[X]) (σ : ι → SignType) :
    ((P.roots.toFinset.filter (fun x => ∀ i, SignType.sign ((Q i).eval x) = σ i)).card : ℝ) =
      ∑ e : ι → Fin 3, (∏ i, signCoefficient (σ i) (e i)) *
        tarskiQuery P (∏ i, (Q i)^(e i).val) := by
  classical
  have pointwise (x : ℝ) :
      (if ∀ i, SignType.sign ((Q i).eval x) = σ i then (1 : ℝ) else 0) =
      ∑ e : ι → Fin 3, (∏ i, signCoefficient (σ i) (e i)) *
        (SignType.sign ((∏ i, (Q i)^(e i).val).eval x) : ℝ) := by
    have hprod : (if ∀ i, SignType.sign ((Q i).eval x) = σ i then (1 : ℝ) else 0) =
        ∏ i, (if SignType.sign ((Q i).eval x) = σ i then (1 : ℝ) else 0) := by
      split_ifs with h
      · simp only [h,ite_true,prod_const_one]
      · push Not at h
        obtain ⟨i,hi⟩ := h
        symm
        apply prod_eq_zero (mem_univ i)
        simp [hi]
    rw [hprod]
    simp_rw [← sign_indicator, Fintype.prod_sum]
    apply sum_congr rfl
    intro e _
    rw [prod_mul_distrib]
    congr 1
    simp only [eval_prod,eval_pow]
    have he : SignType.sign (∏ i, ((Q i).eval x)^(e i).val) =
        ∏ i, (SignType.sign ((Q i).eval x))^(e i).val := by
      exact map_prod (signHom : ℝ →*₀ SignType) _ _ |>.trans
        (prod_congr rfl fun i _ => map_pow (signHom : ℝ →*₀ SignType) _ _)
    rw [he]
    simpa only [SignType.castHom_apply,SignType.coe_pow] using
      (map_prod (SignType.castHom : SignType →*₀ ℝ)
        (fun i => (SignType.sign ((Q i).eval x))^(e i).val) Finset.univ).symm
  rw [← sum_boole]
  simp_rw [pointwise]
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  simp only [tarskiQuery,mul_sum]

theorem exists_root_sign_pattern_iff {ι : Type*} [Fintype ι]
    {P : ℝ[X]} (hP : P ≠ 0) (Q : ι → ℝ[X]) (σ : ι → SignType) :
    (∃ x : ℝ, P.eval x = 0 ∧ ∀ i, SignType.sign ((Q i).eval x) = σ i) ↔
    0 < ∑ e : ι → Fin 3, (∏ i, signCoefficient (σ i) (e i)) *
      tarskiQuery P (∏ i, (Q i)^(e i).val) := by
  classical
  rw [← sign_pattern_count]
  simp only [Nat.cast_pos,card_pos,Finset.nonempty_iff_ne_empty]
  rw [← Finset.nonempty_iff_ne_empty]
  simp only [Finset.Nonempty,mem_filter,Multiset.mem_toFinset,mem_roots hP,IsRoot]

end SignElimination
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SignatureRootValues
attribute [-instance] _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.SignElimination

section
open QuadraticMap
open scoped Classical

variable {M N : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
  [AddCommGroup N] [Module ℝ N] [FiniteDimensional ℝ N]

lemma sigPos_comp_le (Q : QuadraticForm ℝ N) (f : M →ₗ[ℝ] N) :
    sigPos (Q.comp f) ≤ sigPos Q := by
  obtain ⟨V,hV,hp⟩ := exists_finrank_eq_sigPos_and_posDef (Q.comp f)
  let g := f.domRestrict V
  have hg : Function.Injective g := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm
    · intro v hv
      have he : f v = 0 := hv
      by_contra hn
      have hv0 : v ≠ 0 := by simpa using hn
      have hh := hp v hv0
      simp only [QuadraticMap.restrict_apply,QuadraticMap.comp_apply,he,map_zero] at hh
      exact lt_irrefl _ hh
    · exact bot_le
  let e := LinearEquiv.ofInjective g hg
  have hpos : (Q.restrict g.range).PosDef := by
    intro y hy
    obtain ⟨v,rfl⟩ := e.surjective y
    have hv : v ≠ 0 := by
      intro hv
      apply hy
      simp [hv]
    exact hp v hv
  rw [← hV, e.finrank_eq]
  exact le_sigPos_of_posDef Q hpos

lemma sigPos_comp_surjective (Q : QuadraticForm ℝ N) (f : M →ₗ[ℝ] N)
    (hf : Function.Surjective f) : sigPos (Q.comp f) = sigPos Q := by
  apply le_antisymm (sigPos_comp_le Q f)
  obtain ⟨g,hg⟩ := LinearMap.exists_rightInverse_of_surjective f (LinearMap.range_eq_top.mpr hf)
  have hh := sigPos_comp_le (Q.comp f) g
  have he : (Q.comp f).comp g = Q := by
    ext x
    simpa only [comp_apply,LinearMap.comp_apply,LinearMap.id_apply] using
      congrArg Q (LinearMap.congr_fun hg x)
  rwa [he] at hh

lemma sigNeg_comp_surjective (Q : QuadraticForm ℝ N) (f : M →ₗ[ℝ] N)
    (hf : Function.Surjective f) : sigNeg (Q.comp f) = sigNeg Q := by
  change sigPos (-(Q.comp f)) = sigPos (-Q)
  have he : -(Q.comp f) = (-Q).comp f := by ext; rfl
  rw [he]
  exact sigPos_comp_surjective (-Q) f hf

end

open QuadraticMap Finset
open scoped BigOperators Classical

noncomputable def signedSignature {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticForm ℝ M) : ℝ := (sigPos Q : ℝ) - (sigNeg Q : ℝ)

lemma signature_weightedSumSquares {ι : Type*} [Fintype ι] (w : ι → ℝ) :
    signedSignature (weightedSumSquares ℝ w) = ∑ i, (SignType.sign (w i) : ℝ) := by
  rw [signedSignature,QuadraticForm.sigPos_weightedSumSquares,
    QuadraticForm.sigNeg_weightedSumSquares]
  have hp : (({i | 0 < w i} : Set ι).ncard : ℝ) =
      ∑ i, if 0 < w i then (1:ℝ) else 0 := by simp [Set.ncard_eq_toFinset_card']
  have hn : (({i | w i < 0} : Set ι).ncard : ℝ) =
      ∑ i, if w i < 0 then (1:ℝ) else 0 := by simp [Set.ncard_eq_toFinset_card']
  rw [hp,hn,← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  rcases lt_trichotomy (w i) 0 with h | h | h
  · simp [h,not_lt_of_ge h.le,sign_neg h]
  · simp [h]
  · simp [h,not_lt_of_ge h.le,sign_pos h]

noncomputable def squareRootOrOne (q : ℂ) : ℂ :=
  if q = 0 then 1 else (IsAlgClosed.exists_pow_nat_eq q (by norm_num : 0 < (2:ℕ))).choose

lemma squareRootOrOne_sq {q : ℂ} (h : q ≠ 0) : squareRootOrOne q ^ 2 = q := by
  simp only [squareRootOrOne,ite_eq_right h]
  exact (IsAlgClosed.exists_pow_nat_eq q (by norm_num : 0 < (2:ℕ))).choose_spec

lemma squareRootOrOne_ne_zero (q : ℂ) : squareRootOrOne q ≠ 0 := by
  by_cases h : q = 0
  · simp [squareRootOrOne,h]
  · intro hz
    have hh := squareRootOrOne_sq h
    simp [hz] at hh
    exact h hh.symm

noncomputable def rootCoordinates {α β : Type*} (q : β → ℂ) :
    ((α → ℝ) × (β → ℂ)) ≃ₗ[ℝ] ((α ⊕ (β ⊕ β)) → ℝ) where
  toFun v := Sum.elim v.1 (Sum.elim
    (fun b => (squareRootOrOne (q b) * v.2 b).re)
    (fun b => (squareRootOrOne (q b) * v.2 b).im))
  invFun v := (fun a => v (.inl a),fun b =>
    ((v (.inr (.inl b)) : ℂ) + (v (.inr (.inr b)) : ℂ)*Complex.I) /
      squareRootOrOne (q b))
  left_inv v := by
    ext a
    · rfl
    · simp only [Sum.elim_inr,Sum.elim_inl,Complex.re_add_im]
      exact mul_div_cancel_left₀ _ (squareRootOrOne_ne_zero _)
  right_inv v := by
    funext a
    rcases a with a | b
    · rfl
    · rcases b with b | b <;>
        simp [mul_div_cancel₀ _ (squareRootOrOne_ne_zero _)]
  map_add' v w := by
    ext a
    rcases a with a | b
    · rfl
    · rcases b with b | b <;> simp [mul_add]
  map_smul' r v := by
    ext a
    rcases a with a | b
    · rfl
    · rcases b with b | b <;> simp <;> ring

theorem signature_of_root_values
    {M α β : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
    [Fintype α] [Fintype β] (Q : QuadraticForm ℝ M)
    (f : M →ₗ[ℝ] ((α → ℝ) × (β → ℂ))) (hf : Function.Surjective f)
    (wr : α → ℝ) (m : β → ℝ) (q : β → ℂ)
    (hQ : ∀ v, Q v = ∑ a, wr a * (f v).1 a ^ 2 +
      ∑ b, 2 * m b * (q b * (f v).2 b ^ 2).re) :
    signedSignature Q = ∑ a, (SignType.sign (wr a) : ℝ) := by
  let t : β → ℝ := fun b => if q b = 0 then 0 else 2*m b
  let w : α ⊕ (β ⊕ β) → ℝ := Sum.elim wr (Sum.elim t (fun b => -t b))
  let e := rootCoordinates (α := α) q
  let g := e.toLinearMap.comp f
  have hg : Function.Surjective g := e.surjective.comp hf
  have hpair (b : β) (z : ℂ) :
      t b * (squareRootOrOne (q b) * z).re^2 +
        (-t b) * (squareRootOrOne (q b) * z).im^2 =
          2*m b * (q b * z^2).re := by
    by_cases h : q b = 0
    · simp [t,h]
    · have he : q b * z^2 = (squareRootOrOne (q b) * z)^2 := by
        rw [mul_pow,squareRootOrOne_sq h]
      rw [he]
      simp only [t,ite_eq_right h,pow_two,Complex.mul_re]
      ring
  have he : Q = (weightedSumSquares ℝ w).comp g := by
    ext v
    rw [hQ v,comp_apply,weightedSumSquares_apply]
    simp only [Fintype.sum_sum_type,w,Sum.elim_inl,Sum.elim_inr,
      g,e,LinearMap.comp_apply,rootCoordinates,
      smul_eq_mul]
    simp only [← pow_two]
    rw [← sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro b _
    exact (hpair b ((f v).2 b)).symm
  rw [he,signedSignature,sigPos_comp_surjective _ _ hg,sigNeg_comp_surjective _ _ hg]
  change signedSignature (weightedSumSquares ℝ w) = _
  rw [signature_weightedSumSquares]
  simp only [w,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Left.sign_neg,
    SignType.coe_neg,sum_neg_distrib,add_neg_cancel,add_zero]

end Release061.SignElimination

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_HermiteSignature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.SignElimination
open Polynomial Finset QuadraticMap
open scoped BigOperators Classical

noncomputable def complexEvaluation (n : ℕ) (z : ℂ) : degreeLT ℝ n →ₗ[ℝ] ℂ :=
  (aeval z).toLinearMap.comp (degreeLT ℝ n).subtype

@[simp] lemma complexEvaluation_apply (n : ℕ) (z : ℂ) (A : degreeLT ℝ n) :
    complexEvaluation n z A = (complexify A.val).eval z := by
  simp [complexEvaluation,aeval_def,complexify,eval_map]
  rfl

noncomputable def rootSquare (n : ℕ) (Q : ℝ[X]) (z : ℂ) :
    QuadraticForm ℝ (degreeLT ℝ n) :=
  Complex.reLm.compQuadraticMap
    ((complexify Q).eval z • (sq (R := ℝ) (A := ℂ)).comp (complexEvaluation n z))

@[simp] lemma rootSquare_apply (n : ℕ) (Q : ℝ[X]) (z : ℂ) (A : degreeLT ℝ n) :
    rootSquare n Q z A = ((complexify Q).eval z * (complexify A.val).eval z ^ 2).re := by
  simp [rootSquare,pow_two]

noncomputable def hermiteForm (P Q : ℝ[X]) : QuadraticForm ℝ (degreeLT ℝ P.natDegree) :=
  ((complexify P).roots.map (rootSquare P.natDegree Q)).sum

lemma hermiteForm_apply (P Q : ℝ[X]) (A : degreeLT ℝ P.natDegree) :
    hermiteForm P Q A = ((complexify P).roots.map
      (fun z => ((complexify Q).eval z * (complexify A.val).eval z ^ 2).re)).sum := by
  simp [hermiteForm,Finset.sum_multiset_map_count]

@[simp] lemma rootEvaluation_real (P : ℝ[X]) (A : degreeLT ℝ P.natDegree)
    (a : RealRoot P) : (rootEvaluation P A).1 a = A.val.eval a.val := by
  simp [rootEvaluation,aeval_def]

@[simp] lemma rootEvaluation_upper (P : ℝ[X]) (A : degreeLT ℝ P.natDegree)
    (b : UpperRoot P) : (rootEvaluation P A).2 b = (complexify A.val).eval b.val := by
  change A.val.eval₂ (algebraMap ℝ ℂ) b.val = _
  rw [eval₂_eq_eval_map]
  rfl

lemma hermiteForm_root_values {P : ℝ[X]} (hP : P ≠ 0) (Q : ℝ[X])
    (A : degreeLT ℝ P.natDegree) :
    hermiteForm P Q A =
      ∑ a : RealRoot P, (P.roots.count a.val : ℝ) * Q.eval a.val * (rootEvaluation P A).1 a ^ 2 +
      ∑ b : UpperRoot P, 2 * ((complexify P).roots.count b.val : ℝ) *
        ((complexify Q).eval b.val * (rootEvaluation P A).2 b ^ 2).re := by
  rw [hermiteForm_apply,Finset.sum_multiset_map_count]
  have he := (rootNodesEquiv hP).sum_comp
    (fun z => ((complexify P).roots.count z.val : ℝ) *
      ((complexify Q).eval z.val * (complexify A.val).eval z.val ^ 2).re)
  have he' := he.trans (Finset.sum_coe_sort (complexify P).roots.toFinset
    (fun z => ((complexify P).roots.count z : ℝ) *
      ((complexify Q).eval z * (complexify A.val).eval z ^ 2).re))
  simp only [nsmul_eq_mul]
  rw [← he']
  simp only [Fintype.sum_sum_type,rootNodesEquiv,Equiv.ofBijective_apply,
    rootNodes,realComplexNodes,Sum.elim_inl,Sum.elim_inr]
  rw [← sum_add_distrib]
  congr 1
  · apply sum_congr rfl
    intro a _
    rw [count_complex_root_real,complexify_real_eval,complexify_real_eval]
    rw [rootEvaluation_real]
    simp only [← Complex.ofReal_pow,← Complex.ofReal_mul,Complex.ofReal_re]
    ring
  · apply sum_congr rfl
    intro b _
    rw [count_complex_root_conj,complexify_eval_conj,complexify_eval_conj]
    rw [← map_pow (starRingEnd ℂ),← map_mul (starRingEnd ℂ)]
    simp only [Complex.conj_re,rootEvaluation_upper]
    ring

theorem hermite_signature {P : ℝ[X]} (hP : P ≠ 0) (Q : ℝ[X]) :
    signedSignature (hermiteForm P Q) = tarskiQuery P Q := by
  rw [signature_of_root_values (hermiteForm P Q) (rootEvaluation P)
    (rootEvaluation_surjective hP)
    (fun a => (P.roots.count a.val : ℝ) * Q.eval a.val)
    (fun b => ((complexify P).roots.count b.val : ℝ))
    (fun b => (complexify Q).eval b.val) (hermiteForm_root_values hP Q)]
  rw [tarskiQuery]
  conv_rhs => rw [← Finset.sum_coe_sort]
  apply sum_congr rfl
  intro a _
  have ha : 0 < (P.roots.count a.val : ℝ) := by
    exact_mod_cast Multiset.count_pos.mpr (Multiset.mem_toFinset.mp a.property)
  rw [sign_mul,sign_pos ha,one_mul]

end Release061.SignElimination

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_RootMomentCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.SignElimination
open Polynomial MvPolynomial Finset
open scoped Classical BigOperators

noncomputable def powerSumPolynomial (n k : ℕ) : MvPolynomial (Fin n) ℝ :=
  (MvPolynomial.esymmAlgHom_surjective (σ := Fin n) ℝ (by simp : Fintype.card (Fin n) ≤ n)
    ⟨psum (Fin n) ℝ k, psum_isSymmetric _ _ _⟩).choose

lemma powerSumPolynomial_spec (n k : ℕ) :
    ((esymmAlgHom (Fin n) ℝ n) (powerSumPolynomial n k)).val = psum (Fin n) ℝ k := by
  exact congrArg Subtype.val (Classical.choose_spec
    (MvPolynomial.esymmAlgHom_surjective (σ := Fin n) ℝ
      (by simp : Fintype.card (Fin n) ≤ n) ⟨psum (Fin n) ℝ k, psum_isSymmetric _ _ _⟩))

lemma powerSumPolynomial_eval {n : ℕ} (k : ℕ) (v : Fin n → ℂ) :
    MvPolynomial.aeval (fun i : Fin n => (univ.val.map v).esymm (i.val+1))
      (powerSumPolynomial n k) = ∑ i, v i ^ k := by
  have he := congrArg (MvPolynomial.aeval v) (powerSumPolynomial_spec n k)
  rw [esymmAlgHom_apply] at he
  simpa only [MvPolynomial.comp_aeval_apply,aeval_esymm_eq_multiset_esymm,psum,
    map_sum,map_pow,MvPolynomial.aeval_X] using he

lemma multiset_enumerate {α : Type*} (s : Multiset α) {n : ℕ} (hn : s.card = n) :
    ∃ v : Fin n → α, Finset.univ.val.map v = s := by
  subst n
  refine ⟨fun i => s.toList.get ⟨i.val,by simp⟩, ?_⟩
  rw [Fin.univ_val_map]
  have he : List.ofFn (fun i : Fin s.card => s.toList.get ⟨i.val,by simp⟩) = s.toList := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  rw [he,Multiset.coe_toList]

noncomputable def rootCoefficient (P : ℝ[X]) (i : Fin P.natDegree) : ℝ :=
  (-1)^(i.val+1) * P.coeff (P.natDegree - (i.val+1)) / P.leadingCoeff

lemma roots_esymm_eq_rootCoefficient {P : ℝ[X]} (hP : P ≠ 0) (i : Fin P.natDegree) :
    (P.map Complex.ofRealHom).roots.esymm (i.val+1) = (rootCoefficient P i : ℂ) := by
  have hcard := splits_iff_card_roots.mp (IsAlgClosed.splits (P.map Complex.ofRealHom))
  have he := coeff_eq_esymm_roots_of_card hcard
    (k := P.natDegree-(i.val+1)) (by rw [natDegree_map]; exact Nat.sub_le _ _)
  have hsub : P.natDegree - (P.natDegree - (i.val+1)) = i.val+1 := by omega
  rw [natDegree_map,hsub,Polynomial.coeff_map,leadingCoeff_map] at he
  simp only [Complex.ofRealHom_eq_coe] at he
  have hl : (P.leadingCoeff : ℂ) ≠ 0 := by exact_mod_cast leadingCoeff_ne_zero.mpr hP
  have hpow : ((-1 : ℂ)^(i.val+1))^2 = 1 := by
    rw [← pow_mul, Nat.mul_comm (i.val+1),pow_mul]
    norm_num
  simp only [rootCoefficient,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,
    Complex.ofReal_neg,Complex.ofReal_one]
  apply (eq_div_iff hl).mpr
  rw [he]
  linear_combination -((P.map Complex.ofRealHom).roots.esymm (i.val+1) * (P.leadingCoeff : ℂ)) * hpow

theorem root_moment_coefficients {P : ℝ[X]} (hP : P ≠ 0) (k : ℕ) :
    (((P.map Complex.ofRealHom).roots.map (fun z => z^k)).sum : ℂ) =
      (MvPolynomial.eval (rootCoefficient P) (powerSumPolynomial P.natDegree k) : ℂ) := by
  obtain ⟨v,hv⟩ := multiset_enumerate (P.map Complex.ofRealHom).roots
    (by simpa using splits_iff_card_roots.mp (IsAlgClosed.splits (P.map Complex.ofRealHom)))
  have he := powerSumPolynomial_eval k v
  rw [hv] at he
  simp_rw [roots_esymm_eq_rootCoefficient hP] at he
  rw [← hv,Multiset.map_map]
  change (∑ i, v i ^ k) = _
  rw [← he,MvPolynomial.aeval_def]
  exact (MvPolynomial.eval₂_comp_left Complex.ofRealHom (RingHom.id ℝ)
    (rootCoefficient P) (powerSumPolynomial P.natDegree k)).symm

end Release061.SignElimination

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SignVariationsPositiveRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.SignElimination
open Polynomial
open scoped Classical

lemma coeff_comp_neg (P : ℝ[X]) (k : ℕ) :
    (P.comp (-X)).coeff k = P.coeff k * (-1)^k := by
  simpa using (comp_C_mul_X_coeff (p := P) (r := (-1:ℝ)) (n := k))

lemma natDegree_comp_neg (P : ℝ[X]) : (P.comp (-X)).natDegree = P.natDegree := by
  simp [natDegree_comp]

lemma eraseLead_comp_neg (P : ℝ[X]) :
    (P.comp (-X)).eraseLead = P.eraseLead.comp (-X) := by
  ext k
  simp only [eraseLead_coeff,coeff_comp_neg,natDegree_comp_neg]
  split_ifs <;> simp

lemma sign_pair_indicator (a b t : SignType) (ha : a ≠ 0) (hb : b ≠ 0) (ht : t ≠ 0) :
    (if a = -b then 1 else 0 : ℕ) +
      (if -(t*a) = -(t*b) then 1 else 0) = 1 := by
  cases a <;> cases b <;> cases t <;> simp_all

lemma signVariations_pair_le (P : ℝ[X]) :
    P.signVariations + (P.comp (-X)).signVariations ≤ P.natDegree := by
  induction hd : P.natDegree using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases hp : P = 0
    · simp [hp]
    by_cases he : P.eraseLead = 0
    · rw [signVariations_eq_eraseLead_add_ite hp,
        signVariations_eq_eraseLead_add_ite (P := P.comp (-X)) (by simpa using hp),eraseLead_comp_neg,he]
      simp [hp]
    have hlt : P.eraseLead.natDegree < P.natDegree :=
      P.eraseLead_natDegree_lt_or_eraseLead_eq_zero.resolve_right he
    have hi := ih P.eraseLead.natDegree (hd ▸ hlt) P.eraseLead rfl
    rw [signVariations_eq_eraseLead_add_ite hp,
      signVariations_eq_eraseLead_add_ite (P := P.comp (-X)) (by simpa using hp),eraseLead_comp_neg,
      comp_neg_X_leadingCoeff_eq,comp_neg_X_leadingCoeff_eq]
    by_cases hgap : P.natDegree = P.eraseLead.natDegree + 1
    · have hs := sign_pair_indicator (SignType.sign P.leadingCoeff)
        (SignType.sign P.eraseLead.leadingCoeff)
        (SignType.sign ((-1:ℝ)^P.eraseLead.natDegree))
        (by simpa using hp) (by simpa using he) (by simp)
      simp only [hgap,pow_succ,mul_neg_one,sign_mul,Left.sign_neg,neg_mul]
      omega
    · have hgap' : P.eraseLead.natDegree + 2 ≤ P.natDegree := by omega
      split_ifs <;> omega

lemma coeffList_mul_X (P : ℝ[X]) (hP : P ≠ 0) :
    (P*X).coeffList = P.coeffList ++ [0] := by
  rw [coeffList,coeffList,withBotSucc_degree_eq_natDegree_add_one (mul_ne_zero hP X_ne_zero),
    withBotSucc_degree_eq_natDegree_add_one hP,natDegree_mul_X hP,List.range_succ_eq_map]
  simp only [List.reverse_cons,← List.map_reverse,List.map_append,List.map_map,
    List.map_singleton,coeff_mul_X_zero]
  congr 1
  exact List.map_congr_left (fun k _ => coeff_mul_X P k)

lemma signVariations_mul_X (P : ℝ[X]) : (P*X).signVariations = P.signVariations := by
  by_cases hp : P = 0
  · simp [hp]
  simp [signVariations,coeffList_mul_X P hp,List.filter_append]

lemma positive_negative_roots_card {P : ℝ[X]} (hP : P ≠ 0) (h0 : P.eval 0 ≠ 0) :
    P.roots.countP (0 < ·) + P.roots.countP (· < 0) = P.roots.card := by
  have hz : ∀ x ∈ P.roots, x ≠ 0 := by
    intro x hx h
    subst x
    exact h0 ((mem_roots hP).mp hx)
  rw [Multiset.card_eq_countP_add_countP (0 < ·)]
  congr 1
  apply Multiset.countP_congr rfl
  intro x hx
  have hn := hz x hx
  apply propext
  rcases lt_trichotomy x 0 with hx | hx | hx <;> simp_all <;> linarith

theorem signVariations_eq_positive_roots {P : ℝ[X]} (hP : P.Splits) :
    P.signVariations = P.roots.countP (0 < ·) := by
  induction hd : P.natDegree using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases hp : P = 0
    · simp [hp]
    by_cases h0 : P.eval 0 = 0
    · obtain ⟨Q,hQ⟩ := X_dvd_iff.mpr (by simpa only [coeff_zero_eq_eval_zero] using h0)
      have hqn : Q ≠ 0 := by intro h; simp [h] at hQ; exact hp hQ
      have he : P = Q*X := by simpa [mul_comm] using hQ
      have hdeg : Q.natDegree < P.natDegree := by rw [he,natDegree_mul_X hqn]; omega
      have hs : Q.Splits := hP.of_dvd hp ⟨X,he⟩
      have hi := ih Q.natDegree (hd ▸ hdeg) hs rfl
      rw [he,signVariations_mul_X,hi,roots_mul (mul_ne_zero hqn X_ne_zero)]
      have hz : Multiset.countP (fun x : ℝ => 0 < x) ({0} : Multiset ℝ) = 0 := by
        change Multiset.countP (fun x : ℝ => 0 < x) (0 ::ₘ 0) = 0
        rw [Multiset.countP_cons_of_neg _ (lt_irrefl _), Multiset.countP_zero]
      simp [hz]
    · have hpc := P.roots_countP_pos_le_signVariations
      have hnc := (P.comp (-X)).roots_countP_pos_le_signVariations
      have hsum := positive_negative_roots_card hp h0
      rw [splits_iff_card_roots.mp hP] at hsum
      simp only [roots_comp_neg_X,Multiset.countP_map,neg_pos,← Multiset.countP_eq_card_filter] at hnc
      have hv := signVariations_pair_le P
      omega

end Release061.SignElimination

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_TarskiQueryCharpoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.SignElimination

section
open Matrix QuadraticMap Polynomial
open scoped BigOperators Classical
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma quadratic_matrix_apply (A : Matrix n n ℝ) (v : n → ℝ) :
    A.toQuadraticForm' v = v ⬝ᵥ (A *ᵥ v) := by
  exact Matrix.toLinearMap₂'_apply' _ _ _

lemma quadratic_matrix_comp (A B : Matrix n n ℝ) :
    A.toQuadraticForm'.comp B.mulVecLin = (Bᵀ * A * B).toQuadraticForm' := by
  apply QuadraticMap.ext
  intro v
  change A.toQuadraticForm' (B *ᵥ v) = (Bᵀ * A * B).toQuadraticForm' v
  simp only [quadratic_matrix_apply,← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

lemma diagonal_quadratic (w : n → ℝ) :
    (Matrix.diagonal w).toQuadraticForm' = weightedSumSquares ℝ w := by
  apply QuadraticMap.ext
  intro v
  simp only [quadratic_matrix_apply,dotProduct,
    weightedSumSquares_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mulVec_diagonal]
  ring

lemma quadratic_signature_eigenvalues (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    signedSignature A.toQuadraticForm' = ∑ i, (SignType.sign (hA.eigenvalues i) : ℝ) := by
  let U : Matrix n n ℝ := hA.eigenvectorUnitary
  have hd : Uᵀ * A * U = Matrix.diagonal hA.eigenvalues := by
    simpa only [Unitary.conjStarAlgAut_star_apply,Function.comp_def,RCLike.ofReal_real_eq_id,
      id_eq,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using
      hA.conjStarAlgAut_star_eigenvectorUnitary
  have hsur : Function.Surjective U.mulVecLin := by
    intro v
    refine ⟨(star U) *ᵥ v, ?_⟩
    simp only [Matrix.mulVecLin_apply,Matrix.mulVec_mulVec]
    change ((hA.eigenvectorUnitary : Matrix n n ℝ) * star (hA.eigenvectorUnitary : Matrix n n ℝ)) *ᵥ v = v
    rw [← Unitary.coe_star,Unitary.coe_mul_star_self,Matrix.one_mulVec]
  have hq := quadratic_matrix_comp A U
  rw [hd,diagonal_quadratic] at hq
  rw [← signature_weightedSumSquares,← hq]
  simp only [signedSignature,sigPos_comp_surjective _ _ hsur,sigNeg_comp_surjective _ _ hsur]

lemma signature_matrix_charpoly (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    signedSignature A.toQuadraticForm' =
      (A.charpoly.signVariations : ℝ) - ((A.charpoly.comp (-X)).signVariations : ℝ) := by
  rw [quadratic_signature_eigenvalues A hA,
    signVariations_eq_positive_roots hA.splits_charpoly,
    signVariations_eq_positive_roots hA.splits_charpoly.comp_neg_X]
  simp only [roots_comp_neg_X,hA.roots_charpoly_eq_eigenvalues,
    Multiset.countP_map,neg_pos,← Multiset.countP_eq_card_filter]
  rw [← signature_weightedSumSquares,signedSignature,
    QuadraticForm.sigPos_weightedSumSquares,QuadraticForm.sigNeg_weightedSumSquares]
  congr 1 <;> simp [Set.ncard_eq_toFinset_card',Multiset.countP_eq_card_filter] <;> rfl

end

open Polynomial Matrix QuadraticMap Finset
open scoped BigOperators Classical

noncomputable def hermiteMatrix (P Q : ℝ[X]) : Matrix (Fin P.natDegree) (Fin P.natDegree) ℝ :=
  fun i j => (((complexify P).roots.map
    (fun z => (complexify Q).eval z * z^(i.val+j.val))).sum).re

lemma hermiteMatrix_isHermitian (P Q : ℝ[X]) : (hermiteMatrix P Q).IsHermitian := by
  rw [Matrix.IsHermitian,conjTranspose_eq_transpose_of_trivial]
  ext i j
  simp only [transpose_apply,hermiteMatrix]
  rw [Nat.add_comm]

lemma root_matrix_identity {n : ℕ} (q z : ℂ) (v : Fin n → ℝ) :
    (q * (∑ i, (v i : ℂ)*z^i.val)^2).re =
      ∑ i, ∑ j, v i * (q*z^(i.val+j.val)).re * v j := by
  have he : q * (∑ i, (v i : ℂ)*z^i.val)^2 =
      ∑ i, ∑ j, (v i : ℂ) * (q*z^(i.val+j.val)) * (v j : ℂ) := by
    simp only [pow_two,Finset.mul_sum,Finset.sum_mul]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [pow_add]
    ring
  rw [he]
  simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,mul_zero]

lemma complexify_eval_degreeLT {n : ℕ} (A : degreeLT ℝ n) (z : ℂ) :
    (complexify A.val).eval z = ∑ i : Fin n, ((degreeLTEquiv ℝ n A i : ℝ) : ℂ)*z^i.val := by
  rw [complexify,eval_map,eval₂_eq_sum]
  exact (Polynomial.sum_fin (fun i (a : ℝ) => (a : ℂ)*z^i) (by simp)
    (mem_degreeLT.mp A.property)).symm

lemma hermiteMatrix_quadratic (P Q : ℝ[X]) :
    (hermiteMatrix P Q).toQuadraticForm' =
      (hermiteForm P Q).comp (degreeLTEquiv ℝ P.natDegree).symm.toLinearMap := by
  apply QuadraticMap.ext
  intro v
  rw [QuadraticMap.comp_apply,hermiteForm_apply]
  simp only [complexify_eval_degreeLT,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,
    root_matrix_identity,Finset.sum_multiset_map_count,smul_sum]
  rw [quadratic_matrix_apply]
  simp only [dotProduct,Matrix.mulVec,hermiteMatrix,Finset.sum_multiset_map_count,
    Complex.re_sum,nsmul_eq_mul,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,
    zero_mul,sub_zero,Finset.mul_sum,Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro z _
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

lemma hermiteMatrix_signature {P : ℝ[X]} (hP : P ≠ 0) (Q : ℝ[X]) :
    signedSignature (hermiteMatrix P Q).toQuadraticForm' = tarskiQuery P Q := by
  rw [hermiteMatrix_quadratic,signedSignature,
    sigPos_comp_surjective _ _ (degreeLTEquiv ℝ P.natDegree).symm.surjective,
    sigNeg_comp_surjective _ _ (degreeLTEquiv ℝ P.natDegree).symm.surjective]
  exact hermite_signature hP Q

lemma hermiteMatrix_coefficients {P : ℝ[X]} (hP : P ≠ 0) (Q : ℝ[X])
    {d : ℕ} (hQ : Q.degree < d) (i j : Fin P.natDegree) :
    hermiteMatrix P Q i j = ∑ k : Fin d, Q.coeff k.val *
      MvPolynomial.eval (rootCoefficient P)
        (powerSumPolynomial P.natDegree (k.val+i.val+j.val)) := by
  have hq (z : ℂ) : (complexify Q).eval z =
      ∑ k : Fin d, (Q.coeff k.val : ℂ)*z^k.val := by
    rw [complexify,eval_map,eval₂_eq_sum]
    exact (Polynomial.sum_fin (fun i (a : ℝ) => (a : ℂ)*z^i) (by simp) hQ).symm
  have he : ((complexify P).roots.map
      (fun z => (complexify Q).eval z * z^(i.val+j.val))).sum =
      ∑ k : Fin d, (Q.coeff k.val : ℂ) *
        (((complexify P).roots.map (fun z => z^(k.val+i.val+j.val))).sum) := by
    simp only [hq,Finset.sum_mul,Finset.sum_multiset_map_count,
      smul_sum,nsmul_eq_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro k _
    apply sum_congr rfl
    intro z _
    simp only [pow_add]
    ring
  rw [hermiteMatrix,he]
  simp only [complexify,root_moment_coefficients hP,Complex.re_sum,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]

theorem tarskiQuery_charpoly {P : ℝ[X]} (hP : P ≠ 0) (Q : ℝ[X]) :
    tarskiQuery P Q =
      ((hermiteMatrix P Q).charpoly.signVariations : ℝ) -
      (((hermiteMatrix P Q).charpoly.comp (-X)).signVariations : ℝ) := by
  rw [← hermiteMatrix_signature hP Q]
  exact signature_matrix_charpoly _ (hermiteMatrix_isHermitian P Q)

end Release061.SignElimination

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialSignSetQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.SignElimination
open Polynomial Matrix Finset Set
open scoped Classical BigOperators

lemma signVariations_congr_coeff {P Q : ℝ[X]} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hd : P.natDegree = Q.natDegree)
    (hs : ∀ k ≤ P.natDegree, SignType.sign (P.coeff k) = SignType.sign (Q.coeff k)) :
    P.signVariations = Q.signVariations := by
  have he : P.coeffList.map SignType.sign = Q.coeffList.map SignType.sign := by
    simp only [coeffList,withBotSucc_degree_eq_natDegree_add_one hP,
      withBotSucc_degree_eq_natDegree_add_one hQ,← hd,List.map_map]
    apply List.map_congr_left
    intro k hk
    exact hs k (by simpa only [List.mem_reverse,List.mem_range,Nat.lt_succ_iff] using hk)
  simp only [signVariations, he]

lemma signVariations_neg_congr_coeff {P Q : ℝ[X]} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hd : P.natDegree = Q.natDegree)
    (hs : ∀ k ≤ P.natDegree, SignType.sign (P.coeff k) = SignType.sign (Q.coeff k)) :
    (P.comp (-X)).signVariations = (Q.comp (-X)).signVariations := by
  apply signVariations_congr_coeff (by simpa using hP) (by simpa using hQ)
    (by simpa only [natDegree_comp_neg] using hd)
  intro k hk
  simp only [natDegree_comp_neg] at hk
  rw [coeff_comp_neg,coeff_comp_neg,sign_mul,sign_mul,hs k hk]

noncomputable def charpolyCoefficient {n : Type*} [Fintype n] [DecidableEq n] (k : ℕ) :
    MvPolynomial (n × n) ℝ :=
  (Matrix.charpoly (fun i j : n => (MvPolynomial.X (i,j) : MvPolynomial (n × n) ℝ))).coeff k

lemma eval_charpolyCoefficient {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (k : ℕ) :
    MvPolynomial.eval (fun p : n × n => A p.1 p.2) (charpolyCoefficient (n := n) k) =
      A.charpoly.coeff k := by
  let M : Matrix n n (MvPolynomial (n × n) ℝ) := fun i j => MvPolynomial.X (i,j)
  let f := MvPolynomial.eval (fun p : n × n => A p.1 p.2)
  have he : Matrix.map M f = A := by
    ext i j
    change MvPolynomial.eval _ (MvPolynomial.X (i,j)) = _
    exact MvPolynomial.eval_X _
  have hc := congrArg (fun p : ℝ[X] => p.coeff k) (Matrix.charpoly_map M f)
  rw [he,Polynomial.coeff_map] at hc
  exact hc.symm

lemma rationalOn_charpoly_coefficient {X ι n : Type*} [Fintype n] [DecidableEq n]
    {c : X → ι → ℝ} {S : Set X} (A : X → Matrix n n ℝ)
    (hA : ∀ i j, RationalOn c S (fun x => A x i j)) (k : ℕ) :
    RationalOn c S (fun x => (A x).charpoly.coeff k) := by
  simpa only [eval_charpolyCoefficient] using RationalOn.eval
    (charpolyCoefficient (n := n) k) (fun p x => A x p.1 p.2) (fun p => hA p.1 p.2)

lemma polynomialSignSet_of_sign_invariant {X ι α : Type*} [Finite α]
    {c : X → ι → ℝ} {S : Set X} (hS : PolynomialSignSet c S)
    (f : α → X → ℝ) (hf : ∀ a, RationalOn c S (f a)) (W : X → Prop)
    (hW : ∀ x ∈ S, ∀ y ∈ S,
      (∀ a, SignType.sign (f a x) = SignType.sign (f a y)) → (W x ↔ W y)) :
    PolynomialSignSet c (S ∩ {x | W x}) := by
  have hh := polynomialSignSet_finite_signs hS f hf
    (fun σ => ∃ y ∈ S, W y ∧ ∀ a, SignType.sign (f a y) = σ a)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_inter_iff,mem_ofPred_eq]
  apply and_congr_right
  intro hx
  constructor
  · intro hw
    exact ⟨x,hx,hw,fun _ => rfl⟩
  · rintro ⟨y,hy,hw,hs⟩
    exact (hW y hy x hx hs).mp hw

noncomputable def coefficientHermiteMatrix (n d : ℕ) (P Q : ℝ[X]) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∑ k : Fin d, Q.coeff k.val *
    MvPolynomial.eval (fun l : Fin n => (-1)^(l.val+1)*P.coeff (n-(l.val+1))/P.coeff n)
      (powerSumPolynomial n (k.val+i.val+j.val))

lemma coefficientHermiteMatrix_eq {P : ℝ[X]} (hP : P ≠ 0) (Q : ℝ[X])
    {d : ℕ} (hQ : Q.degree < d) :
    coefficientHermiteMatrix P.natDegree d P Q = hermiteMatrix P Q := by
  ext i j
  rw [hermiteMatrix_coefficients hP Q hQ]
  rfl

lemma rationalOn_coefficientHermite {X ι : Type*} {c : X → ι → ℝ} {S : Set X}
    (n d : ℕ) (P Q : X → ℝ[X])
    (hP : ∀ k, RationalOn c S (fun x => (P x).coeff k))
    (hQ : ∀ k, RationalOn c S (fun x => (Q x).coeff k))
    (hn : ∀ x ∈ S, (P x).coeff n ≠ 0) (i j : Fin n) :
    RationalOn c S (fun x => coefficientHermiteMatrix n d (P x) (Q x) i j) := by
  apply RationalOn.sum
  intro k _
  apply (hQ k.val).mul
  apply RationalOn.eval
  intro l
  exact ((RationalOn.const _).mul (hP (n-(l.val+1)))).div (hP n) hn

lemma tarskiQuery_coefficient_charpoly {P : ℝ[X]} (hP : P ≠ 0) (Q : ℝ[X])
    {n d : ℕ} (hn : P.natDegree = n) (hQ : Q.degree < d) :
    tarskiQuery P Q =
      ((coefficientHermiteMatrix n d P Q).charpoly.signVariations : ℝ) -
      (((coefficientHermiteMatrix n d P Q).charpoly.comp (-X)).signVariations : ℝ) := by
  subst n
  rw [coefficientHermiteMatrix_eq hP Q hQ]
  exact tarskiQuery_charpoly hP Q

theorem polynomialSignSet_query_predicate {X ι α : Type*} [Fintype α]
    {c : X → ι → ℝ} {S : Set X} (hS : PolynomialSignSet c S)
    (n : ℕ) (d : α → ℕ) (P : X → ℝ[X]) (Q : α → X → ℝ[X])
    (hP : ∀ k, RationalOn c S (fun x => (P x).coeff k))
    (hQ : ∀ a k, RationalOn c S (fun x => (Q a x).coeff k))
    (hp : ∀ x ∈ S, P x ≠ 0 ∧ (P x).natDegree = n)
    (hq : ∀ a x, x ∈ S → (Q a x).degree < d a)
    (W : (α → ℝ) → Prop) :
    PolynomialSignSet c (S ∩ {x | W (fun a => tarskiQuery (P x) (Q a x))}) := by
  let A := fun a x => coefficientHermiteMatrix n (d a) (P x) (Q a x)
  have hra (a : α) (i j : Fin n) : RationalOn c S (fun x => A a x i j) := by
    apply rationalOn_coefficientHermite n (d a) P (Q a) hP (hQ a)
    intro x hx
    rw [← (hp x hx).2]
    exact leadingCoeff_ne_zero.mpr (hp x hx).1
  let f : (α × Fin (n+1)) → X → ℝ := fun a x => (A a.1 x).charpoly.coeff a.2.val
  have hrf (a : α × Fin (n+1)) : RationalOn c S (f a) :=
    rationalOn_charpoly_coefficient (A a.1) (hra a.1) a.2.val
  apply polynomialSignSet_of_sign_invariant hS f hrf
  intro x hx y hy he
  have ht (a : α) : tarskiQuery (P x) (Q a x) = tarskiQuery (P y) (Q a y) := by
    rw [tarskiQuery_coefficient_charpoly (hp x hx).1 _ (hp x hx).2 (hq a x hx),
      tarskiQuery_coefficient_charpoly (hp y hy).1 _ (hp y hy).2 (hq a y hy)]
    have hdeg : (A a x).charpoly.natDegree = (A a y).charpoly.natDegree := by
      simp only [Matrix.charpoly_natDegree_eq_dim]
    have hs : ∀ k ≤ (A a x).charpoly.natDegree,
        SignType.sign ((A a x).charpoly.coeff k) = SignType.sign ((A a y).charpoly.coeff k) := by
      intro k hk
      have hk' : k < n+1 := by simpa using Nat.lt_succ_of_le hk
      exact he (a,⟨k,hk'⟩)
    rw [signVariations_congr_coeff (A a x).charpoly_monic.ne_zero (A a y).charpoly_monic.ne_zero hdeg hs,
      signVariations_neg_congr_coeff (A a x).charpoly_monic.ne_zero (A a y).charpoly_monic.ne_zero hdeg hs]
  rw [funext ht]

end Release061.SignElimination

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_DecayWeightDeriv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.SignElimination
open Polynomial Set Filter
open scoped Topology BigOperators Classical

noncomputable def criticalSampler (P : ℝ[X]) : ℝ[X] :=
  P.derivative + X * (X * P.derivative - C (P.natDegree+1 : ℝ) * P)

noncomputable def decayWeight (P : ℝ[X]) (x : ℝ) : ℝ :=
  (P.eval x)^2 / (1+x^2)^(P.natDegree+1)

lemma X_derivative_coeff (P : ℝ[X]) (n : ℕ) :
    (X * P.derivative).coeff n = (n : ℝ)*P.coeff n := by
  cases n with
  | zero => simp
  | succ n => simp [coeff_X_mul,coeff_derivative,mul_comm]

lemma criticalSampler_top_coeff (P : ℝ[X]) :
    (criticalSampler P).coeff (P.natDegree+1) = -P.leadingCoeff := by
  rw [criticalSampler,coeff_add,coeff_X_mul,coeff_sub,X_derivative_coeff,coeff_C_mul]
  have hz : P.derivative.coeff (P.natDegree+1) = 0 := by
    rw [coeff_derivative,coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < P.natDegree+1+1),zero_mul]
  rw [hz,coeff_natDegree]
  ring

lemma criticalSampler_ne_zero {P : ℝ[X]} (hP : P ≠ 0) : criticalSampler P ≠ 0 := by
  intro hz
  have h := criticalSampler_top_coeff P
  rw [hz,coeff_zero,eq_comm,neg_eq_zero] at h
  exact leadingCoeff_ne_zero.mpr hP h

lemma decayWeight_continuous (P : ℝ[X]) : Continuous (decayWeight P) := by
  apply Continuous.div
  · exact P.continuous.pow 2
  · fun_prop
  · intro x
    exact pow_ne_zero _ (by positivity : (1:ℝ)+x^2 ≠ 0)

lemma decayWeight_tendsto (P : ℝ[X]) : Tendsto (decayWeight P) (cocompact ℝ) (𝓝 0) := by
  let A : ℝ[X] := P^2
  let B : ℝ[X] := (1+X^2)^(P.natDegree+1)
  have hd : A.degree < B.degree := by
    apply degree_lt_degree
    dsimp [A,B]
    rw [natDegree_pow,natDegree_pow]
    have hs : (1+X^2 : ℝ[X]).natDegree = 2 := by
      rw [natDegree_add_eq_right_of_natDegree_lt (by norm_num),natDegree_pow]
      simp
    rw [hs]
    omega
  have ht := Polynomial.div_tendsto_atTop_zero_of_degree_lt A B hd
  have hb := Polynomial.div_tendsto_atBot_zero_of_degree_lt A B hd
  change Tendsto (fun x => (P.eval x)^2 / (1+x^2)^(P.natDegree+1)) _ _
  rw [cocompact_eq_atBot_atTop]
  simpa only [A,B,eval_pow,eval_add,eval_one,eval_X] using hb.sup ht

lemma decayWeight_deriv (P : ℝ[X]) (x : ℝ) :
    HasDerivAt (decayWeight P)
      (2 * P.eval x * (criticalSampler P).eval x /
        (1+x^2)^(P.natDegree+2)) x := by
  have hpos : (1:ℝ)+x^2 ≠ 0 := by positivity
  have hden := ((hasDerivAt_id x).pow 2).const_add 1
  have hd := ((P.hasDerivAt x).pow 2).div
    (hden.pow (P.natDegree+1)) (pow_ne_zero _ hpos)
  apply hd.congr_deriv
  simp only [criticalSampler,eval_add,eval_mul,eval_X,eval_sub,eval_C,
    Pi.pow_apply,id_eq,Nat.add_sub_cancel,Nat.reduceSub,pow_one,
    Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,mul_one]
  rw [show P.natDegree+2 = (P.natDegree+1)+1 by omega]
  simp only [pow_succ]
  field_simp
  ring

end Release061.SignElimination

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SampleAllChambers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.SignElimination
open Polynomial Set Filter
open scoped Topology BigOperators Classical

lemma same_sign_of_mul_pos {a b : ℝ} (h : 0 < a*b) :
    SignType.sign a = SignType.sign b := by
  rcases mul_pos_iff.mp h with h | h
  · rw [sign_pos h.1,sign_pos h.2]
  · rw [sign_neg h.1,sign_neg h.2]

theorem sample_nonzero_chamber {ι : Type*} [Fintype ι]
    (Q : ι → ℝ[X]) {x : ℝ} (hx : (∏ i, Q i).eval x ≠ 0) :
    ∃ y : ℝ, (criticalSampler (∏ i, Q i)).eval y = 0 ∧
      ∀ i, SignType.sign ((Q i).eval y) = SignType.sign ((Q i).eval x) := by
  classical
  let P := ∏ i, Q i
  let E : Set ℝ := {y | ∀ i, 0 ≤ (Q i).eval x * (Q i).eval y}
  have hEc : IsClosed E := by
    simp only [E,ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const
      ((Q i).continuous.const_mul ((Q i).eval x))
  have hxE : x ∈ E := fun i => mul_self_nonneg _
  have hxp : 0 < decayWeight P x := by
    exact div_pos (sq_pos_of_ne_zero hx) (by positivity)
  have hbound : ∀ᶠ t in cocompact ℝ ⊓ 𝓟 E, decayWeight P t ≤ decayWeight P x := by
    exact Filter.Eventually.filter_mono inf_le_left
      (((decayWeight_tendsto P).eventually (gt_mem_nhds hxp)).mono fun _ h => h.le)
  obtain ⟨y,hyE,hmax⟩ := (decayWeight_continuous P).continuousOn.exists_isMaxOn' hEc hxE hbound
  have hyp : 0 < decayWeight P y := hxp.trans_le (hmax hxE)
  have hyP : P.eval y ≠ 0 := by
    intro hy
    simp [decayWeight,hy] at hyp
  have hxQ : ∀ i, (Q i).eval x ≠ 0 := by
    simpa only [eval_prod,Finset.prod_ne_zero_iff,Finset.mem_univ,true_implies] using hx
  have hyQ : ∀ i, (Q i).eval y ≠ 0 := by
    simpa only [P,eval_prod,Finset.prod_ne_zero_iff,Finset.mem_univ,true_implies] using hyP
  have hstrict : ∀ i, 0 < (Q i).eval x * (Q i).eval y := by
    intro i
    exact lt_of_le_of_ne (hyE i) (Ne.symm (mul_ne_zero (hxQ i) (hyQ i)))
  have hE_nhds : E ∈ 𝓝 y := by
    have each : ∀ i, ∀ᶠ t in 𝓝 y, 0 ≤ (Q i).eval x * (Q i).eval t := by
      intro i
      exact (((Q i).continuous.const_mul ((Q i).eval x)).continuousAt.eventually_const_lt
        (hstrict i)).mono fun _ h => h.le
    exact Filter.eventually_all.mpr each
  have hd := (hmax.isLocalMax hE_nhds).hasDerivAt_eq_zero (decayWeight_deriv P y)
  have hden : (1+y^2)^(P.natDegree+2) ≠ 0 := pow_ne_zero _ (by positivity)
  have hz : (criticalSampler P).eval y = 0 := by
    rw [div_eq_zero_iff] at hd
    exact (mul_eq_zero.mp (hd.resolve_right hden)).resolve_left (mul_ne_zero (by norm_num) hyP)
  exact ⟨y,hz,fun i => (same_sign_of_mul_pos (hstrict i)).symm⟩

theorem sample_all_chambers {ι : Type*} [Fintype ι]
    (Q : ι → ℝ[X]) (hQ : ∀ i, Q i ≠ 0) :
    let R := (∏ i, Q i) * criticalSampler (∏ i, Q i)
    R ≠ 0 ∧ ∀ x : ℝ, ∃ y : ℝ, R.eval y = 0 ∧
      ∀ i, SignType.sign ((Q i).eval y) = SignType.sign ((Q i).eval x) := by
  classical
  have hP : (∏ i, Q i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hQ i)
  refine ⟨mul_ne_zero hP (criticalSampler_ne_zero hP),fun x => ?_⟩
  by_cases hx : (∏ i, Q i).eval x = 0
  · exact ⟨x,by simp [eval_mul,hx],fun _ => rfl⟩
  · obtain ⟨y,hy,hs⟩ := sample_nonzero_chamber Q hx
    exact ⟨y,by simp [eval_mul,hy],hs⟩

end Release061.SignElimination

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialSignSetRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.SignElimination

open Polynomial Set Finset
open scoped Classical BigOperators

lemma support_eq_of_coeff_sign_eq {P Q : ℝ[X]}
    (h : ∀ k, SignType.sign (P.coeff k) = SignType.sign (Q.coeff k)) :
    P.support = Q.support := by
  ext k
  simp only [mem_support_iff]
  apply not_congr
  simpa only [sign_eq_zero_iff] using (show SignType.sign (P.coeff k) = 0 ↔
    SignType.sign (Q.coeff k) = 0 by rw [h k])

lemma degree_data_of_coeff_sign_eq {P Q : ℝ[X]}
    (h : ∀ k, SignType.sign (P.coeff k) = SignType.sign (Q.coeff k)) :
    (P = 0 ↔ Q = 0) ∧ P.natDegree = Q.natDegree := by
  have hs := support_eq_of_coeff_sign_eq h
  constructor
  · rw [← support_eq_empty,← support_eq_empty,hs]
  · simp only [natDegree,degree,hs]

lemma coeff_sign_ext_of_bound {P Q : ℝ[X]} {N : ℕ}
    (hP : P.natDegree ≤ N) (hQ : Q.natDegree ≤ N)
    (h : ∀ k : Fin (N+1), SignType.sign (P.coeff k) = SignType.sign (Q.coeff k)) :
    ∀ k, SignType.sign (P.coeff k) = SignType.sign (Q.coeff k) := by
  intro k
  by_cases hk : k ≤ N
  · exact h ⟨k,Nat.lt_succ_of_le hk⟩
  · rw [coeff_eq_zero_of_natDegree_lt (hP.trans_lt (Nat.lt_of_not_ge hk)),
      coeff_eq_zero_of_natDegree_lt (hQ.trans_lt (Nat.lt_of_not_ge hk))]

lemma degree_stratum_signSet {X ι : Type*} {c : X → ι → ℝ} {S : Set X}
    (hS : PolynomialSignSet c S) (P : X → ℝ[X]) (N n : ℕ)
    (hP : ∀ k, RationalOn c S (fun x => (P x).coeff k))
    (hd : ∀ x ∈ S, (P x).natDegree ≤ N) :
    PolynomialSignSet c (S ∩ {x | P x ≠ 0 ∧ (P x).natDegree = n}) := by
  apply polynomialSignSet_of_sign_invariant hS
    (fun k : Fin (N+1) => fun x => (P x).coeff k) (fun k => hP k)
  intro x hx y hy he
  have hh := degree_data_of_coeff_sign_eq (coeff_sign_ext_of_bound (hd x hx) (hd y hy) he)
  simp only [ne_eq,hh.1,hh.2]

theorem polynomialSignSet_query_bounded {X ι α : Type*} [Fintype α]
    {c : X → ι → ℝ} {S : Set X} (hS : PolynomialSignSet c S)
    (N : ℕ) (d : α → ℕ) (P : X → ℝ[X]) (Q : α → X → ℝ[X])
    (hP : ∀ k, RationalOn c S (fun x => (P x).coeff k))
    (hQ : ∀ a k, RationalOn c S (fun x => (Q a x).coeff k))
    (hp : ∀ x ∈ S, P x ≠ 0 ∧ (P x).natDegree ≤ N)
    (hq : ∀ a x, x ∈ S → (Q a x).degree < d a)
    (W : (α → ℝ) → Prop) :
    PolynomialSignSet c (S ∩ {x | W (fun a => tarskiQuery (P x) (Q a x))}) := by
  have hh (n : Fin (N+1)) := polynomialSignSet_query_predicate
    (degree_stratum_signSet hS P N n hP (fun x hx => (hp x hx).2)) n d P Q
    (fun k => (hP k).mono inter_subset_left)
    (fun a k => (hQ a k).mono inter_subset_left)
    (fun x hx => hx.2) (fun a x hx => hq a x hx.1) W
  have hh' := PolynomialSignSet.exists_finite _ hh
  convert hh' using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_inter_iff,mem_ofPred_eq]
  constructor
  · rintro ⟨hx,hw⟩
    exact ⟨⟨(P x).natDegree,Nat.lt_succ_of_le (hp x hx).2⟩,⟨hx,(hp x hx).1,rfl⟩,hw⟩
  · rintro ⟨n,⟨hx,_⟩,hw⟩
    exact ⟨hx,hw⟩

def RationalPolynomialOn {X ι : Type*} (c : X → ι → ℝ) (S : Set X)
    (P : X → ℝ[X]) : Prop := ∀ k, RationalOn c S (fun x => (P x).coeff k)

namespace RationalPolynomialOn
variable {X ι : Type*} {c : X → ι → ℝ} {S T : Set X} {P Q : X → ℝ[X]}
lemma mono (h : RationalPolynomialOn c S P) (hT : T ⊆ S) : RationalPolynomialOn c T P :=
  fun k => (h k).mono hT
lemma congr (h : RationalPolynomialOn c S P) (he : ∀ x ∈ S, P x = Q x) :
    RationalPolynomialOn c S Q := fun k => (h k).congr (fun x hx => congrArg (fun p => p.coeff k) (he x hx))
lemma const (P : ℝ[X]) : RationalPolynomialOn c S (fun _ => P) := fun _ => RationalOn.const _
lemma add (hP : RationalPolynomialOn c S P) (hQ : RationalPolynomialOn c S Q) :
    RationalPolynomialOn c S (fun x => P x + Q x) := by
  intro k
  simpa only [coeff_add] using (hP k).add (hQ k)
lemma neg (hP : RationalPolynomialOn c S P) : RationalPolynomialOn c S (fun x => -P x) := by
  intro k
  simpa only [coeff_neg] using (hP k).neg
lemma sub (hP : RationalPolynomialOn c S P) (hQ : RationalPolynomialOn c S Q) :
    RationalPolynomialOn c S (fun x => P x - Q x) := by
  simpa only [sub_eq_add_neg] using hP.add hQ.neg
lemma mul (hP : RationalPolynomialOn c S P) (hQ : RationalPolynomialOn c S Q) :
    RationalPolynomialOn c S (fun x => P x * Q x) := by
  intro k
  simpa only [coeff_mul] using RationalOn.sum (Finset.HasAntidiagonal.antidiagonal k)
    (fun a x => (P x).coeff a.1 * (Q x).coeff a.2) (fun a _ => (hP a.1).mul (hQ a.2))
lemma pow (hP : RationalPolynomialOn c S P) (n : ℕ) :
    RationalPolynomialOn c S (fun x => P x ^ n) := by
  induction n with
  | zero => simpa using (const (c := c) (S := S) 1)
  | succ n ih => simpa only [pow_succ] using ih.mul hP
lemma prod {α : Type*} (s : Finset α) (P : α → X → ℝ[X])
    (hP : ∀ a ∈ s, RationalPolynomialOn c S (P a)) :
    RationalPolynomialOn c S (fun x => ∏ a ∈ s, P a x) := by
  induction s using Finset.induction_on with
  | empty => simpa using (const (c := c) (S := S) 1)
  | @insert a s ha ih =>
    simpa only [Finset.prod_insert ha] using
      (hP a (by simp)).mul (ih (fun b hb => hP b (by simp [hb])))
lemma derivative (hP : RationalPolynomialOn c S P) :
    RationalPolynomialOn c S (fun x => (P x).derivative) := by
  intro k
  simpa only [coeff_derivative] using (hP (k+1)).mul (RationalOn.const (k+1))
lemma criticalSampler (hP : RationalPolynomialOn c S P) (n : ℕ)
    (hn : ∀ x ∈ S, (P x).natDegree = n) :
    RationalPolynomialOn c S (fun x => SignElimination.criticalSampler (P x)) := by
  have hh := hP.derivative.add ((const Polynomial.X).mul
    (((const Polynomial.X).mul hP.derivative).sub ((const (Polynomial.C (n+1 : ℝ))).mul hP)))
  apply hh.congr
  intro x hx
  simp only [SignElimination.criticalSampler,hn x hx]
end RationalPolynomialOn

lemma degree_lt_bound {P : ℝ[X]} {N : ℕ} (h : P.natDegree ≤ N) : P.degree < (N+1 : ℕ) :=
  degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le h)

theorem polynomialSignSet_root_signs {X ι α : Type*} [Fintype α]
    {c : X → ι → ℝ} {S : Set X} (hS : PolynomialSignSet c S)
    (N : ℕ) (d : α → ℕ) (P : X → ℝ[X]) (Q : α → X → ℝ[X])
    (hP : RationalPolynomialOn c S P) (hQ : ∀ a, RationalPolynomialOn c S (Q a))
    (hp : ∀ x ∈ S, P x ≠ 0 ∧ (P x).natDegree ≤ N)
    (hq : ∀ a x, x ∈ S → (Q a x).natDegree ≤ d a)
    (σ : α → SignType) :
    PolynomialSignSet c (S ∩ {x | ∃ y : ℝ, (P x).eval y = 0 ∧
      ∀ a, SignType.sign ((Q a x).eval y) = σ a}) := by
  let R := fun e : α → Fin 3 => fun x => ∏ a, (Q a x) ^ (e a).val
  have hr (e : α → Fin 3) : RationalPolynomialOn c S (R e) :=
    RationalPolynomialOn.prod univ _ (fun a _ => (hQ a).pow _)
  have hd (e : α → Fin 3) (x : X) (hx : x ∈ S) :
      (R e x).degree < ((∑ a, (e a).val * d a)+1 : ℕ) := by
    apply degree_lt_bound
    exact (natDegree_prod_le _ _).trans (sum_le_sum (fun a _ =>
      natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hq a x hx))))
  have hh := polynomialSignSet_query_bounded hS N (fun e => (∑ a, (e a).val*d a)+1)
    P R hP hr hp hd (fun t => 0 < ∑ e, (∏ a, signCoefficient (σ a) (e a))*t e)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_inter_iff,mem_ofPred_eq]
  apply and_congr_right
  intro hx
  exact exists_root_sign_pattern_iff (hp x hx).1 (fun a => Q a x) σ

end Release061.SignElimination

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialSignSetSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.SignElimination
open Polynomial Set Finset
open scoped Classical BigOperators

lemma criticalSampler_natDegree_le (P : ℝ[X]) :
    (criticalSampler P).natDegree ≤ P.natDegree+2 := by
  have hd : P.derivative.natDegree ≤ P.natDegree := (natDegree_derivative_le P).trans (Nat.sub_le _ _)
  unfold criticalSampler
  apply natDegree_add_le_of_degree_le (hd.trans (by omega))
  apply natDegree_mul_le.trans
  rw [natDegree_X]
  have hh : (X * P.derivative - C (P.natDegree+1 : ℝ)*P).natDegree ≤ P.natDegree+1 := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact natDegree_mul_le.trans (by simpa only [natDegree_X,Nat.add_comm] using Nat.add_le_add_left hd 1)
    · exact (natDegree_C_mul_le _ _).trans (by omega)
  omega

lemma polynomialSignSet_nonzero_mask {X ι α : Type*} [Fintype α]
    {c : X → ι → ℝ} {S : Set X} (hS : PolynomialSignSet c S)
    (d : α → ℕ) (Q : α → X → ℝ[X])
    (hQ : ∀ a, RationalPolynomialOn c S (Q a))
    (hq : ∀ a x, x ∈ S → (Q a x).natDegree ≤ d a) (J : Finset α) :
    PolynomialSignSet c (S ∩ {x | ∀ a, Q a x ≠ 0 ↔ a ∈ J}) := by
  apply polynomialSignSet_of_sign_invariant hS
    (fun a : Σ a : α, Fin (d a+1) => fun x => (Q a.1 x).coeff a.2)
    (fun a => hQ a.1 a.2)
  intro x hx y hy he
  apply forall_congr'
  intro a
  have hh := degree_data_of_coeff_sign_eq (coeff_sign_ext_of_bound
    (hq a x hx) (hq a y hy) (fun k => he ⟨a,k⟩))
  simp only [ne_eq,hh.1]

theorem polynomialSignSet_exists_signs {X ι α : Type*} [Fintype α]
    {c : X → ι → ℝ} {S : Set X} (hS : PolynomialSignSet c S)
    (d : α → ℕ) (Q : α → X → ℝ[X])
    (hQ : ∀ a, RationalPolynomialOn c S (Q a))
    (hq : ∀ a x, x ∈ S → (Q a x).natDegree ≤ d a)
    (σ : α → SignType) :
    PolynomialSignSet c (S ∩ {x | ∃ y : ℝ, ∀ a, SignType.sign ((Q a x).eval y) = σ a}) := by
  classical
  let T := fun J : Finset α => S ∩ {x | ∀ a, Q a x ≠ 0 ↔ a ∈ J}
  have hT (J : Finset α) : PolynomialSignSet c (T J) :=
    polynomialSignSet_nonzero_mask hS d Q hQ hq J
  have hJ (J : Finset α) : PolynomialSignSet c
      (T J ∩ {x | ∃ y : ℝ, ∀ a, SignType.sign ((Q a x).eval y) = σ a}) := by
    let P := fun x => ∏ a : J, Q a.val x
    let N := ∑ a : J, d a.val
    have hp : RationalPolynomialOn c (T J) P :=
      RationalPolynomialOn.prod univ _ (fun a _ => (hQ a.val).mono inter_subset_left)
    have hpn (x : X) (hx : x ∈ T J) : P x ≠ 0 :=
      prod_ne_zero_iff.mpr (fun a _ => (hx.2 a.val).mpr a.property)
    have hpd (x : X) (hx : x ∈ T J) : (P x).natDegree ≤ N :=
      (natDegree_prod_le _ _).trans (sum_le_sum (fun a _ => hq a.val x hx.1))
    let U := fun n : Fin (N+1) => T J ∩ {x | P x ≠ 0 ∧ (P x).natDegree = n.val}
    have hU (n : Fin (N+1)) : PolynomialSignSet c (U n) :=
      degree_stratum_signSet (hT J) P N n hp hpd
    have hn (n : Fin (N+1)) : PolynomialSignSet c
        (U n ∩ {x | ∃ y : ℝ, ∀ a, SignType.sign ((Q a x).eval y) = σ a}) := by
      let R := fun x => P x * criticalSampler (P x)
      have hrp : RationalPolynomialOn c (U n) P := hp.mono inter_subset_left
      have hrr : RationalPolynomialOn c (U n) R :=
        hrp.mul (hrp.criticalSampler n (fun x hx => hx.2.2))
      have hrs (x : X) (hx : x ∈ U n) : R x ≠ 0 ∧ ∀ y : ℝ, ∃ z : ℝ,
          (R x).eval z = 0 ∧ ∀ a, SignType.sign ((Q a x).eval z) = SignType.sign ((Q a x).eval y) := by
        have hs := sample_all_chambers (fun a : J => Q a.val x)
          (fun a => (hx.1.2 a.val).mpr a.property)
        refine ⟨hs.1,fun y => ?_⟩
        obtain ⟨z,hz,hsg⟩ := hs.2 y
        refine ⟨z,hz,fun a => ?_⟩
        by_cases ha : a ∈ J
        · exact hsg ⟨a,ha⟩
        · have ha0 : Q a x = 0 := by simpa only [not_ne_iff] using mt (hx.1.2 a).mp ha
          simp only [ha0,eval_zero]
      have hrd (x : X) (hx : x ∈ U n) : (R x).natDegree ≤ 2*n.val+2 := by
        have hb := natDegree_mul_le (p := P x) (q := criticalSampler (P x))
        have hc := criticalSampler_natDegree_le (P x)
        rw [hx.2.2] at hb hc
        change (P x * criticalSampler (P x)).natDegree ≤ _
        omega
      have hh := polynomialSignSet_root_signs (hU n) (2*n.val+2) d R Q hrr
        (fun a => (hQ a).mono (inter_subset_left.trans inter_subset_left))
        (fun x hx => ⟨(hrs x hx).1,hrd x hx⟩) (fun a x hx => hq a x hx.1.1) σ
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      ext x
      simp only [mem_inter_iff,mem_ofPred_eq]
      apply and_congr_right
      intro hx
      constructor
      · rintro ⟨y,hy⟩
        obtain ⟨z,hz,hs⟩ := (hrs x hx).2 y
        exact ⟨z,hz,fun a => (hs a).trans (hy a)⟩
      · rintro ⟨y,_,hy⟩
        exact ⟨y,hy⟩
    have hh := PolynomialSignSet.exists_finite _ hn
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [mem_inter_iff,mem_ofPred_eq]
    constructor
    · rintro ⟨hx,hy⟩
      exact ⟨⟨(P x).natDegree,Nat.lt_succ_of_le (hpd x hx)⟩,⟨hx,hpn x hx,rfl⟩,hy⟩
    · rintro ⟨n,⟨hx,_⟩,hy⟩
      exact ⟨hx,hy⟩
  have hh := PolynomialSignSet.exists_finite _ hJ
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_inter_iff,mem_ofPred_eq]
  constructor
  · rintro ⟨hx,hy⟩
    refine ⟨univ.filter (fun a => Q a x ≠ 0),⟨hx,fun a => ?_⟩,hy⟩
    simp
  · rintro ⟨J,⟨hx,_⟩,hy⟩
    exact ⟨hx,hy⟩

end Release061.SignElimination

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialSignSetProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.PolynomialSignSet
open Set
open scoped Classical

theorem finite_sign_description {X ι : Type*} {c : X → ι → ℝ} {S : Set X}
    (hS : PolynomialSignSet c S) :
    ∃ (s : Finset (MvPolynomial ι ℝ)) (W : (s → SignType) → Prop),
      ∀ x, x ∈ S ↔ W (fun p => SignType.sign (MvPolynomial.eval (c x) p.val)) := by
  induction hS with
  | zero p =>
    refine ⟨{p},fun σ => σ ⟨p,by simp⟩ = 0,fun x => ?_⟩
    simp only [mem_ofPred_eq,sign_eq_zero_iff]
  | positive p =>
    refine ⟨{p},fun σ => σ ⟨p,by simp⟩ = 1,fun x => ?_⟩
    simp only [mem_ofPred_eq,sign_eq_one_iff]
  | @compl S _ ih =>
    obtain ⟨s,W,h⟩ := ih
    exact ⟨s,fun σ => ¬ W σ,fun x => by simp only [mem_compl_iff,h x]⟩
  | @union S T _ _ ihS ihT =>
    obtain ⟨s,W,hs⟩ := ihS
    obtain ⟨t,V,ht⟩ := ihT
    refine ⟨s ∪ t,fun σ =>
      W (fun p => σ ⟨p.val,Finset.mem_union_left _ p.property⟩) ∨
      V (fun p => σ ⟨p.val,Finset.mem_union_right _ p.property⟩),fun x => ?_⟩
    simp only [mem_union,hs x,ht x]

end Release061.PolynomialSignSet

namespace Release061.SignElimination
open Polynomial Set
open scoped Classical BigOperators

lemma eval_optionEquivLeft {ι : Type*} (p : MvPolynomial (Option ι) ℝ)
    (x : ι → ℝ) (y : ℝ) :
    (((MvPolynomial.optionEquivLeft ℝ ι) p).map (MvPolynomial.eval x)).eval y =
      MvPolynomial.eval (fun o => Option.elim o y x) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add,Polynomial.map_add,eval_add,hp,hq]
  | mul_X p a hp =>
    cases a with
    | none => simp only [map_mul,Polynomial.map_mul,MvPolynomial.optionEquivLeft_X_none,map_X,eval_mul,eval_X,
        hp,MvPolynomial.eval_X,Option.elim_none]
    | some a => simp only [map_mul,Polynomial.map_mul,MvPolynomial.optionEquivLeft_X_some,map_C,eval_mul,eval_C,
        hp,MvPolynomial.eval_X,Option.elim_some]

theorem polynomialSignSet_projection_one {X ι : Type*} {c : X → ι → ℝ}
    {A : Set (X × ℝ)}
    (hA : PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)) A) :
    PolynomialSignSet c {x | ∃ y : ℝ, (x,y) ∈ A} := by
  classical
  obtain ⟨s,W,hW⟩ := hA.finite_sign_description
  let Q : s → X → ℝ[X] := fun p x =>
    (((MvPolynomial.optionEquivLeft ℝ ι) p.val).map (MvPolynomial.eval (c x)))
  let d : s → ℕ := fun p => ((MvPolynomial.optionEquivLeft ℝ ι) p.val).natDegree
  have hQ (p : s) : RationalPolynomialOn c univ (Q p) := by
    intro k
    simpa only [Q,coeff_map] using RationalOn.polynomial
      (((MvPolynomial.optionEquivLeft ℝ ι) p.val).coeff k)
  have hd (p : s) (x : X) (_hx : x ∈ (univ : Set X)) : (Q p x).natDegree ≤ d p := natDegree_map_le
  have hσ (σ : s → SignType) : PolynomialSignSet c
      {x | W σ ∧ ∃ y : ℝ, ∀ p : s, SignType.sign ((Q p x).eval y) = σ p} := by
    have hh := polynomialSignSet_exists_signs (PolynomialSignSet.univ (c := c)) d Q hQ hd σ
    simpa only [univ_inter,← ofPred_and] using (PolynomialSignSet.const (c := c) (W σ)).inter hh
  have hh := PolynomialSignSet.exists_finite _ hσ
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨y,hy⟩
    refine ⟨fun p => SignType.sign ((Q p x).eval y),?_,y,fun _ => rfl⟩
    simpa only [Q,eval_optionEquivLeft] using (hW (x,y)).mp hy
  · rintro ⟨σ,hσ,y,hy⟩
    refine ⟨y,(hW (x,y)).mpr ?_⟩
    have he : (fun p : s => SignType.sign (MvPolynomial.eval (fun o => Option.elim o y (c x)) p.val)) = σ := by
      funext p
      simpa only [Q,eval_optionEquivLeft] using hy p
    rwa [he]

end Release061.SignElimination

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialSignSetProjection2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.PolynomialSignSet
open Set
open scoped Classical

lemma eval_substitution {ι κ : Type*} (d : κ → ℝ) (q : ι → MvPolynomial κ ℝ)
    (p : MvPolynomial ι ℝ) :
    MvPolynomial.eval d (MvPolynomial.eval₂Hom MvPolynomial.C q p) =
      MvPolynomial.eval (fun i => MvPolynomial.eval d (q i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => simp only [map_add,hp,hr]
  | mul_X p i hp => simp only [map_mul,MvPolynomial.eval₂Hom_X',MvPolynomial.eval_X,hp]

theorem polynomial_preimage {X Y ι κ : Type*} {c : X → ι → ℝ} {d : Y → κ → ℝ}
    {S : Set X} (hS : PolynomialSignSet c S) (f : Y → X)
    (q : ι → MvPolynomial κ ℝ)
    (hc : ∀ y i, c (f y) i = MvPolynomial.eval (d y) (q i)) :
    PolynomialSignSet d (f ⁻¹' S) := by
  have hv (p : MvPolynomial ι ℝ) (y : Y) :
      MvPolynomial.eval (d y) (MvPolynomial.eval₂Hom MvPolynomial.C q p) =
        MvPolynomial.eval (c (f y)) p := by
    rw [eval_substitution]
    rw [show (fun i => MvPolynomial.eval (d y) (q i)) = c (f y) from
      funext (fun i => (hc y i).symm)]
  induction hS with
  | zero p =>
    convert PolynomialSignSet.zero (c := d) (MvPolynomial.eval₂Hom MvPolynomial.C q p) using 1
    all_goals try with_reducible_and_instances rfl
    ext y
    simp only [mem_preimage,mem_ofPred_eq,hv]
  | positive p =>
    convert PolynomialSignSet.positive (c := d) (MvPolynomial.eval₂Hom MvPolynomial.C q p) using 1
    all_goals try with_reducible_and_instances rfl
    ext y
    simp only [mem_preimage,mem_ofPred_eq,hv]
  | compl _ ih => simpa only [preimage_compl] using ih.compl
  | union _ _ ih ih' => simpa only [preimage_union] using ih.union ih'

theorem coordinate_preimage {X Y ι κ : Type*} {c : X → ι → ℝ} {d : Y → κ → ℝ}
    {S : Set X} (hS : PolynomialSignSet c S) (f : Y → X)
    (r : ι → κ) (hc : ∀ y i, c (f y) i = d y (r i)) :
    PolynomialSignSet d (f ⁻¹' S) :=
  hS.polynomial_preimage f (fun i => MvPolynomial.X (r i)) (by simpa using hc)

end Release061.PolynomialSignSet

namespace Release061.SignElimination
open Set
open scoped Classical

universe uX uI uK

theorem polynomialSignSet_projection_finite {X : Type uX} {ι : Type uI} {κ : Type uK} [Finite κ]
    {c : X → ι → ℝ} {A : Set (X × (κ → ℝ))}
    (hA : PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2) A) :
    PolynomialSignSet c {x | ∃ y : κ → ℝ, (x,y) ∈ A} := by
  classical
  suffices hh : ∀ (κ : Type uK) [Finite κ], ∀ {X : Type uX} {ι : Type uI} (c : X → ι → ℝ)
      (A : Set (X × (κ → ℝ))),
      PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2) A →
        PolynomialSignSet c {x | ∃ y : κ → ℝ, (x,y) ∈ A} from hh κ c A hA
  intro κ _
  induction κ using Finite.induction_empty_option with
  | @of_equiv α β e ih =>
    intro X ι c A hA
    let f : (X × (α → ℝ)) → X × (β → ℝ) := fun z => (z.1,z.2 ∘ e.symm)
    have hp := hA.coordinate_preimage f (Sum.map id e.symm)
      (d := fun z => Sum.elim (c z.1) z.2) (by intro z i; cases i <;> rfl)
    have hh := ih c (f ⁻¹' A) hp
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [mem_ofPred_eq,mem_preimage]
    constructor
    · rintro ⟨y,hy⟩
      exact ⟨y ∘ e,by simpa [f,Function.comp_def] using hy⟩
    · rintro ⟨y,hy⟩
      exact ⟨y ∘ e.symm,hy⟩
  | h_empty =>
    intro X ι c A hA
    let f : X → X × (PEmpty.{uK+1} → ℝ) := fun x => (x,fun a => a.elim)
    have hp := hA.coordinate_preimage f (Sum.elim id PEmpty.elim)
      (d := c) (by intro x i; cases i with | inl i => rfl | inr a => exact a.elim)
    convert hp using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [mem_ofPred_eq,mem_preimage]
    constructor
    · rintro ⟨y,hy⟩
      have he : y = fun a : PEmpty.{uK+1} => a.elim := funext fun a => a.elim
      simpa only [f,he] using hy
    · intro hx
      exact ⟨_,hx⟩
  | @h_option κ _ ih =>
    intro X ι c A hA
    let f : ((X × (κ → ℝ)) × ℝ) → X × (Option κ → ℝ) :=
      fun z => (z.1.1,fun o => o.elim z.2 z.1.2)
    let d : (X × (κ → ℝ)) → (ι ⊕ κ) → ℝ := fun z => Sum.elim (c z.1) z.2
    let r : (ι ⊕ Option κ) → Option (ι ⊕ κ) :=
      Sum.elim (fun i => some (Sum.inl i)) (Option.map Sum.inr)
    have hp := hA.coordinate_preimage f r
      (d := fun z : (X × (κ → ℝ)) × ℝ => fun o => o.elim z.2 (d z.1)) (by
        intro z i
        cases i with
        | inl i => rfl
        | inr o => cases o <;> rfl)
    have ho := polynomialSignSet_projection_one hp
    have hh := ih c _ ho
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [mem_ofPred_eq,mem_preimage]
    constructor
    · rintro ⟨y,hy⟩
      refine ⟨fun k => y (some k),y none,?_⟩
      have he : (fun o : Option κ => o.elim (y none) (fun k => y (some k))) = y := by
        funext o
        cases o <;> rfl
      simpa only [f,he] using hy
    · rintro ⟨y,t,hy⟩
      exact ⟨_,hy⟩

end Release061.SignElimination

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_NormalOffsetFamilyJoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter

namespace Release061
open Set Metric Filter Topology Classical SignElimination

def normalOffsetFamily {ι κ : Type*} [Fintype κ]
    (U : Set ((ι → ℝ) × (κ → ℝ))) (B : Set (ι → ℝ))
    (φ : (ι → ℝ) → (κ → ℝ)) (ρ : ℝ) (s : ι → ℝ) : Set (κ → ℝ) :=
  {v | s ∈ B ∧ ‖v‖ < ρ ∧ (s,φ s+v) ∈ U}

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_Pair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set
open SignElimination
open scoped Classical

def SemialgebraicOn {ι κ : Type*} (B : Set (ι → ℝ)) (f : (ι → ℝ) → (κ → ℝ)) : Prop :=
  PolynomialSignSet (fun z : (ι → ℝ) × (κ → ℝ) => Sum.elim z.1 z.2)
    {z | z.1 ∈ B ∧ z.2 = f z.1}

namespace SemialgebraicOn
variable {ι κ δ : Type*}
variable {B C : Set (ι → ℝ)} {f : (ι → ℝ) → (κ → ℝ)}

lemma congr (hf : SemialgebraicOn B f) {g : (ι → ℝ) → (κ → ℝ)} (hfg : EqOn f g B) :
    SemialgebraicOn B g := by
  have he : {z : (ι → ℝ) × (κ → ℝ) | z.1 ∈ B ∧ z.2 = f z.1} =
      {z | z.1 ∈ B ∧ z.2 = g z.1} := by
    ext z
    constructor <;> rintro ⟨hz,he⟩ <;> refine ⟨hz,?_⟩
    · exact he.trans (hfg hz)
    · exact he.trans (hfg hz).symm
  unfold SemialgebraicOn at hf ⊢
  exact he ▸ hf

lemma polynomial [Finite κ] (hB : PolynomialSignSet id B) (p : κ → MvPolynomial ι ℝ) :
    SemialgebraicOn B (fun x j => MvPolynomial.eval x (p j)) := by
  have hb := hB.coordinate_preimage (fun z : (ι → ℝ) × (κ → ℝ) => z.1) Sum.inl
    (d := fun z => Sum.elim z.1 z.2) (by intro z i; rfl)
  have hj (j : κ) : PolynomialSignSet (fun z : (ι → ℝ) × (κ → ℝ) => Sum.elim z.1 z.2)
      {z | z.2 j = MvPolynomial.eval z.1 (p j)} := by
    convert PolynomialSignSet.zero (c := fun z : (ι → ℝ) × (κ → ℝ) => Sum.elim z.1 z.2)
      (MvPolynomial.X (Sum.inr j) - MvPolynomial.rename Sum.inl (p j)) using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp [MvPolynomial.eval_rename,sub_eq_zero]
  unfold SemialgebraicOn
  convert hb.inter (PolynomialSignSet.forall_finite _ hj) using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp only [mem_inter_iff,mem_preimage,mem_ofPred_eq,funext_iff]

lemma identity [Finite ι] (hB : PolynomialSignSet id B) : SemialgebraicOn B (id : (ι → ℝ) → _) := by
  exact (polynomial hB (MvPolynomial.X (R := ℝ))).congr (fun x _ => by
    funext j
    simp)

lemma comp [Finite κ] {D : Set (κ → ℝ)} {g : (κ → ℝ) → (δ → ℝ)}
    (hg : SemialgebraicOn D g) (hf : SemialgebraicOn B f) (hBD : MapsTo f B D) :
    SemialgebraicOn B (g ∘ f) := by
  let c : ((ι → ℝ) × (δ → ℝ)) → (ι ⊕ δ) → ℝ := fun z => Sum.elim z.1 z.2
  have hf' := hf.coordinate_preimage
    (fun z : ((ι → ℝ) × (δ → ℝ)) × (κ → ℝ) => (z.1.1,z.2))
    (Sum.map Sum.inl id) (d := fun z => Sum.elim (c z.1) z.2)
    (by intro z i; cases i <;> rfl)
  have hg' := hg.coordinate_preimage
    (fun z : ((ι → ℝ) × (δ → ℝ)) × (κ → ℝ) => (z.2,z.1.2))
    (Sum.elim Sum.inr (fun j => Sum.inl (Sum.inr j)))
    (d := fun z => Sum.elim (c z.1) z.2) (by intro z i; cases i <;> rfl)
  have hh := polynomialSignSet_projection_finite (c := c) (hf'.inter hg')
  unfold SemialgebraicOn
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp only [mem_preimage,mem_ofPred_eq,mem_inter_iff,Function.comp_apply]
  constructor
  · rintro ⟨hz,he⟩
    exact ⟨f z.1,⟨hz,rfl⟩,hBD hz,he⟩
  · rintro ⟨y,⟨hz,rfl⟩,_,he⟩
    exact ⟨hz,he⟩

lemma pair {g : (ι → ℝ) → (δ → ℝ)} (hf : SemialgebraicOn B f) (hg : SemialgebraicOn B g) :
    SemialgebraicOn B (fun x => Sum.elim (f x) (g x)) := by
  have hf' := hf.coordinate_preimage
    (fun z : (ι → ℝ) × ((κ ⊕ δ) → ℝ) => (z.1,fun j => z.2 (Sum.inl j)))
    (Sum.map id Sum.inl) (d := fun z => Sum.elim z.1 z.2)
    (by intro z i; cases i <;> rfl)
  have hg' := hg.coordinate_preimage
    (fun z : (ι → ℝ) × ((κ ⊕ δ) → ℝ) => (z.1,fun j => z.2 (Sum.inr j)))
    (Sum.map id Sum.inr) (d := fun z => Sum.elim z.1 z.2)
    (by intro z i; cases i <;> rfl)
  unfold SemialgebraicOn
  convert hf'.inter hg' using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp only [mem_preimage,mem_ofPred_eq,mem_inter_iff]
  constructor
  · rintro ⟨hz,he⟩
    refine ⟨⟨hz,?_⟩,hz,?_⟩ <;> rw [he] <;> rfl
  · rintro ⟨⟨hz,hf⟩,_,hg⟩
    refine ⟨hz,funext fun i => ?_⟩
    cases i with
    | inl i => exact congrFun hf i
    | inr i => exact congrFun hg i

end SemialgebraicOn
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_FiniteUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology MeasureTheory
open scoped Classical

structure NashPatch (n : ℕ) where
  dim : ℕ
  domain : Set (Fin dim → ℝ)
  isOpen_domain : IsOpen domain
  isConnected_domain : IsConnected domain
  semialgebraic_domain : PolynomialSignSet id domain
  toFun : (Fin dim → ℝ) → (Fin n → ℝ)
  semialgebraic_toFun : SemialgebraicOn domain toFun
  analytic_toFun : AnalyticOnNhd ℝ toFun domain
  injective_fderiv : ∀ x ∈ domain, Function.Injective (fderiv ℝ toFun x)

namespace NashPatch
variable {n : ℕ}

def image (p : NashPatch n) : Set (Fin n → ℝ) := p.toFun '' p.domain

noncomputable def identity (B : Set (Fin n → ℝ)) (hB : IsOpen B) (hc : IsConnected B)
    (hs : PolynomialSignSet id B) : NashPatch n where
  dim := n
  domain := B
  isOpen_domain := hB
  isConnected_domain := hc
  semialgebraic_domain := hs
  toFun := id
  semialgebraic_toFun := SemialgebraicOn.identity hs
  analytic_toFun := analyticOnNhd_id
  injective_fderiv x _ := by simpa only [fderiv_id,ContinuousLinearMap.coe_id',id_eq] using Function.injective_id

noncomputable def comp (p : NashPatch n) (q : NashPatch p.dim) (hqp : q.image ⊆ p.domain) :
    NashPatch n where
  dim := q.dim
  domain := q.domain
  isOpen_domain := q.isOpen_domain
  isConnected_domain := q.isConnected_domain
  semialgebraic_domain := q.semialgebraic_domain
  toFun := p.toFun ∘ q.toFun
  semialgebraic_toFun := p.semialgebraic_toFun.comp q.semialgebraic_toFun
    (fun x hx => hqp ⟨x,hx,rfl⟩)
  analytic_toFun x hx := (p.analytic_toFun _ (hqp ⟨x,hx,rfl⟩)).comp (q.analytic_toFun x hx)
  injective_fderiv x hx := by
    rw [fderiv_comp x (p.analytic_toFun _ (hqp ⟨x,hx,rfl⟩)).differentiableAt
      (q.analytic_toFun x hx).differentiableAt]
    exact (p.injective_fderiv _ (hqp ⟨x,hx,rfl⟩)).comp (q.injective_fderiv x hx)

end NashPatch

def HasFiniteNashCover {n : ℕ} (S : Set (Fin n → ℝ)) : Prop :=
  ∃ P : Finset (NashPatch n), ∀ x, x ∈ S ↔ ∃ p ∈ P, x ∈ p.image

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AffineBand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology
open scoped Classical

namespace SemialgebraicOn
variable {ι κ δ : Type*} {B : Set (ι → ℝ)} {f g : (ι → ℝ) → (κ → ℝ)}
lemma reindex [Finite κ] [Finite δ] (hf : SemialgebraicOn B f) (r : δ → κ) :
    SemialgebraicOn B (fun x j => f x (r j)) := by
  have hp := (polynomial (B := (univ : Set (κ → ℝ))) PolynomialSignSet.univ
    (fun j => MvPolynomial.X (r j))).comp hf (fun _ _ => mem_univ _)
  simpa only [Function.comp_def,MvPolynomial.eval_X] using hp

lemma add [Finite κ] (hf : SemialgebraicOn B f) (hg : SemialgebraicOn B g) :
    SemialgebraicOn B (fun x => f x + g x) := by
  have hp := (polynomial (B := (univ : Set ((κ ⊕ κ) → ℝ))) PolynomialSignSet.univ
    (fun j => MvPolynomial.X (Sum.inl j) + MvPolynomial.X (Sum.inr j))).comp
      (hf.pair hg) (fun _ _ => mem_univ _)
  exact hp.congr (fun x _ => by ext j; simp)

lemma mul [Finite κ] (hf : SemialgebraicOn B f) (hg : SemialgebraicOn B g) :
    SemialgebraicOn B (fun x => f x * g x) := by
  have hp := (polynomial (B := (univ : Set ((κ ⊕ κ) → ℝ))) PolynomialSignSet.univ
    (fun j => MvPolynomial.X (Sum.inl j) * MvPolynomial.X (Sum.inr j))).comp
      (hf.pair hg) (fun _ _ => mem_univ _)
  exact hp.congr (fun x _ => by ext j; simp)

lemma finCons {n : ℕ} {a : (ι → ℝ) → (Fin 1 → ℝ)} {f : (ι → ℝ) → (Fin n → ℝ)}
    (ha : SemialgebraicOn B a) (hf : SemialgebraicOn B f) :
    SemialgebraicOn B (fun x => Fin.cons (a x 0) (f x)) := by
  apply ((ha.pair hf).reindex (Fin.cases (Sum.inl 0) Sum.inr)).congr
  intro x _
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl
end SemialgebraicOn

namespace NashPatch

noncomputable def graph {n : ℕ} (p : NashPatch n)
    (a : (Fin p.dim → ℝ) → (Fin 1 → ℝ)) (hs : SemialgebraicOn p.domain a)
    (ha : AnalyticOnNhd ℝ a p.domain) : NashPatch (n+1) where
  dim := p.dim
  domain := p.domain
  isOpen_domain := p.isOpen_domain
  isConnected_domain := p.isConnected_domain
  semialgebraic_domain := p.semialgebraic_domain
  toFun := fun x => Fin.cons (a x 0) (p.toFun x)
  semialgebraic_toFun := hs.finCons p.semialgebraic_toFun
  analytic_toFun x hx := by
    apply analyticAt_pi_iff.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (analyticAt_pi_iff.mp (ha x hx)) 0
    · exact (analyticAt_pi_iff.mp (p.analytic_toFun x hx)) j
  injective_fderiv x hx := by
    have hd := ((analyticAt_pi_iff.mp (ha x hx) 0).differentiableAt.hasFDerivAt).finCons (F' := fun _ : Fin (n+1) => ℝ)
      (p.analytic_toFun x hx).differentiableAt.hasFDerivAt
    rw [hd.fderiv]
    intro u v huv
    apply p.injective_fderiv x hx
    exact congrArg Fin.tail huv

def cylinderDomain {d : ℕ} (B : Set (Fin d → ℝ)) (I : Set ℝ) : Set (Fin (d+1) → ℝ) :=
  {x | Fin.tail x ∈ B ∧ x 0 ∈ I}

lemma cylinderDomain_open {d : ℕ} {B : Set (Fin d → ℝ)} {I : Set ℝ}
    (hB : IsOpen B) (hI : IsOpen I) : IsOpen (cylinderDomain B I) :=
  (hB.preimage (by fun_prop)).inter (hI.preimage (continuous_apply 0))

lemma cylinderDomain_connected {d : ℕ} {B : Set (Fin d → ℝ)} {I : Set ℝ}
    (hB : IsConnected B) (hI : IsConnected I) : IsConnected (cylinderDomain B I) := by
  have he : (fun x : ℝ × (Fin d → ℝ) => Fin.cons x.1 x.2) '' (I ×ˢ B) = cylinderDomain B I := by
    ext x
    constructor
    · rintro ⟨⟨t,y⟩,⟨ht,hy⟩,rfl⟩
      exact ⟨hy,ht⟩
    · rintro ⟨hx,ht⟩
      exact ⟨(x 0,Fin.tail x),⟨ht,hx⟩,Fin.cons_self_tail x⟩
  rw [← he]
  exact (hI.prod hB).image _ (by fun_prop)

lemma cylinderDomain_semialgebraic {d : ℕ} {B : Set (Fin d → ℝ)} {I : Set ℝ}
    (hB : PolynomialSignSet id B) (hI : PolynomialSignSet (fun t : ℝ => fun _ : Fin 1 => t) I) :
    PolynomialSignSet id (cylinderDomain B I) := by
  exact (hB.coordinate_preimage Fin.tail Fin.succ (d := id) (by intro x i; rfl)).inter
    (hI.coordinate_preimage (fun x => x 0) (fun _ => 0) (d := id) (by intro x i; rfl))

lemma semialgebraic_tail {d : ℕ} {B : Set (Fin d → ℝ)} {I : Set ℝ}
    (hB : PolynomialSignSet id B) (hI : PolynomialSignSet (fun t : ℝ => fun _ : Fin 1 => t) I) :
    SemialgebraicOn (cylinderDomain B I) (@Fin.tail d (fun _ => ℝ)) := by
  exact (SemialgebraicOn.polynomial
    (cylinderDomain_semialgebraic hB hI) (fun i : Fin d => MvPolynomial.X i.succ)).congr
    (fun x _ => by ext i; simp [Fin.tail])

noncomputable def affineBand {n : ℕ} (p : NashPatch n) (I : Set ℝ)
    (hI : IsOpen I) (hcI : IsConnected I)
    (hsI : PolynomialSignSet (fun t : ℝ => fun _ : Fin 1 => t) I)
    (a b : (Fin p.dim → ℝ) → (Fin 1 → ℝ))
    (hsa : SemialgebraicOn p.domain a) (hsb : SemialgebraicOn p.domain b)
    (haa : AnalyticOnNhd ℝ a p.domain) (hab : AnalyticOnNhd ℝ b p.domain)
    (hb : ∀ x ∈ p.domain, b x 0 ≠ 0) : NashPatch (n+1) where
  dim := p.dim+1
  domain := cylinderDomain p.domain I
  isOpen_domain := cylinderDomain_open p.isOpen_domain hI
  isConnected_domain := cylinderDomain_connected p.isConnected_domain hcI
  semialgebraic_domain := cylinderDomain_semialgebraic p.semialgebraic_domain hsI
  toFun := fun x => Fin.cons (a (Fin.tail x) 0 + b (Fin.tail x) 0 * x 0) (p.toFun (Fin.tail x))
  semialgebraic_toFun := by
    have ht := semialgebraic_tail p.semialgebraic_domain hsI
    have ha := hsa.comp ht (fun _ hx => hx.1)
    have hb := hsb.comp ht (fun _ hx => hx.1)
    have hv : SemialgebraicOn (cylinderDomain p.domain I) (fun x => fun _ : Fin 1 => x 0) := by
      simpa only [MvPolynomial.eval_X] using SemialgebraicOn.polynomial
        (cylinderDomain_semialgebraic p.semialgebraic_domain hsI) (fun _ : Fin 1 => MvPolynomial.X 0)
    exact (ha.add (hb.mul hv)).finCons (p.semialgebraic_toFun.comp ht (fun _ hx => hx.1))
  analytic_toFun x hx := by
    have ht : AnalyticAt ℝ (@Fin.tail p.dim (fun _ => ℝ)) x :=
      (Pi.compRightL ℝ (fun _ : Fin (p.dim+1) => ℝ) Fin.succ).analyticAt x
    have ha := (analyticAt_pi_iff.mp (haa _ hx.1) 0).comp ht
    have hb := (analyticAt_pi_iff.mp (hab _ hx.1) 0).comp ht
    apply analyticAt_pi_iff.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ha.add (hb.mul ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (p.dim+1) => ℝ) 0).analyticAt x))
    · exact (analyticAt_pi_iff.mp (p.analytic_toFun _ hx.1) j).comp ht
  injective_fderiv x hx := by
    let T : (Fin (p.dim+1) → ℝ) →L[ℝ] (Fin p.dim → ℝ) := Pi.compRightL ℝ (fun _ => ℝ) Fin.succ
    let Z : (Fin (p.dim+1) → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
    have ht : HasFDerivAt (@Fin.tail p.dim (fun _ => ℝ)) T x := T.hasFDerivAt
    have hz : HasFDerivAt (fun x : Fin (p.dim+1) → ℝ => x 0) Z x := Z.hasFDerivAt
    have ha := ((analyticAt_pi_iff.mp (haa _ hx.1) 0).differentiableAt.hasFDerivAt).comp x ht
    have hb' := ((analyticAt_pi_iff.mp (hab _ hx.1) 0).differentiableAt.hasFDerivAt).comp x ht
    have hp := (p.analytic_toFun _ hx.1).differentiableAt.hasFDerivAt.comp x ht
    have hd := (ha.add (hb'.mul hz)).finCons (F' := fun _ : Fin (n+1) => ℝ) hp
    simp only [Function.comp_def,Pi.add_apply,Pi.mul_apply] at hd
    rw [hd.fderiv]
    intro u v huv
    have htail : Fin.tail u = Fin.tail v := by
      apply p.injective_fderiv _ hx.1
      exact congrArg Fin.tail huv
    have hzero := congrFun huv 0
    change fderiv ℝ (fun y => a y 0) (Fin.tail x) (T u) +
      (b (Fin.tail x) 0 * Z u + x 0 * fderiv ℝ (fun y => b y 0) (Fin.tail x) (T u)) =
      fderiv ℝ (fun y => a y 0) (Fin.tail x) (T v) +
      (b (Fin.tail x) 0 * Z v + x 0 * fderiv ℝ (fun y => b y 0) (Fin.tail x) (T v)) at hzero
    change T u = T v at htail
    rw [htail] at hzero
    dsimp [Z] at hzero
    have hzuv : u 0 = v 0 := mul_left_cancel₀ (hb _ hx.1) (by linarith [hzero])
    funext i
    exact Fin.cases hzuv (fun j => congrFun htail j) i

end NashPatch
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AffineProductCoordinates
attribute [-instance] _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set

def chartSubsetHomeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) (S : Set X) (hS : S ⊆ e.source) : S ≃ₜ e '' S where
  toFun x := ⟨e x,mem_image_of_mem e x.property⟩
  invFun y := ⟨e.symm y,by
    obtain ⟨x,hx,hxy⟩ := y.property
    rw [← hxy,e.left_inv (hS hx)]
    exact hx⟩
  left_inv x := Subtype.ext (e.left_inv (hS x.property))
  right_inv y := by
    apply Subtype.ext
    apply e.right_inv
    obtain ⟨x,hx,hxy⟩ := y.property
    rw [← hxy]
    exact e.map_source (hS hx)
  continuous_toFun := (e.continuousOn.mono hS).domRestrict.subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply ContinuousOn.domRestrict
    apply e.symm.continuousOn.mono
    rintro _ ⟨x,hx,rfl⟩
    exact e.map_source (hS hx)

@[simp] lemma chartSubsetHomeomorph_apply
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) (S : Set X) (hS : S ⊆ e.source) (x : S) :
    (chartSubsetHomeomorph e S hS x : Y) = e x := rfl

@[simp] lemma chartSubsetHomeomorph_symm_apply
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) (S : Set X) (hS : S ⊆ e.source) (y : e '' S) :
    ((chartSubsetHomeomorph e S hS).symm y : X) = e.symm y := rfl

def Biholomorph.ofOpenPartialHomeomorph {n m : ℕ}
    (e : OpenPartialHomeomorph (Affine n) (Affine m))
    (ha : AnalyticOnNhd ℂ e e.source) (hai : AnalyticOnNhd ℂ e.symm e.target)
    (S : Set (Affine n)) (hS : S ⊆ e.source) : Biholomorph S (e '' S) where
  toHomeomorph := chartSubsetHomeomorph e S hS
  holomorphic_toFun := by
    intro p
    exact ⟨e.source,e.open_source,hS p.property,e,ha,fun _ _ => rfl⟩
  holomorphic_invFun := by
    intro p
    have hp : (p : Affine m) ∈ e.target := by
      obtain ⟨x,hx,hxp⟩ := p.property
      rw [← hxp]
      exact e.map_source (hS hx)
    exact ⟨e.target,e.open_target,hp,e.symm,hai,fun _ _ => rfl⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticMulZeroGerm
attribute [-instance] _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set Filter Topology

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analyticAt_mul_eq_zero_germ {f g : E → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hfg : f*g =ᶠ[𝓝 (0 : E)] 0) :
    f =ᶠ[𝓝 (0 : E)] 0 ∨ g =ᶠ[𝓝 (0 : E)] 0 := by
  classical
  by_cases h : f =ᶠ[𝓝 (0 : E)] 0
  · exact Or.inl h
  right
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp
    (hf.eventually_analyticAt.and (hg.eventually_analyticAt.and hfg))
  have hfball : AnalyticOnNhd ℂ f (Metric.ball 0 r) := fun z hz => (hball hz).1
  have hgball : AnalyticOnNhd ℂ g (Metric.ball 0 r) := fun z hz => (hball hz).2.1
  have hex : ∃ z ∈ Metric.ball (0 : E) r, f z ≠ 0 := by
    by_contra hn
    push Not at hn
    exact h (Filter.eventually_of_mem (Metric.ball_mem_nhds _ hr) hn)
  obtain ⟨z,hz,hfz⟩ := hex
  have hgn : g =ᶠ[𝓝 z] 0 := by
    filter_upwards [(hfball z hz).continuousAt.eventually_ne hfz,
      Metric.isOpen_ball.mem_nhds hz] with w hw hwball
    exact (mul_eq_zero.mp (hball hwball).2.2).resolve_left hw
  have hgzero := hgball.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball (0 : E) r).isPreconnected hz hgn
  exact Filter.eventually_of_mem (Metric.ball_mem_nhds _ hr) hgzero

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_EventualOffsetBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
namespace Release061
open Set Filter Metric
open scoped Topology

def offsetScaled {S E : Type*} [SMul ℝ E] (A : S → Set E) (s : S) (t : ℝ) : Set E :=
  {v | t • v ∈ A s}

def offsetDistance {S E : Type*} [MetricSpace E] [SMul ℝ E]
    (A : S → Set E) (s : S) (t : ℝ) (v : E) : ℝ :=
  min 1 (infDist v (offsetScaled A s t)ᶜ)

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_FiniteCoveringRamifiedSection
attribute [-instance] _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Function

open Complex
open scoped UpperHalfPlane
open Function.Periodic

def PuncturedUnitDisk := {z : ℂ // z ≠ 0 ∧ ‖z‖ < 1}

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CayleyTangentBound
attribute [-instance] _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Complex Set Filter Metric
open scoped Topology

def normalCayley (u : ℂ) : ℂ := (u-I)/(u+I)
def normalUncayley (v : ℂ) : ℂ := I*(1+v)/(1-v)

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_BishopBoundarySolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter

namespace Release061.Wiener

abbrev BishopParams (k : ℕ) := (Fin k → ℝ) × (Fin k → ℝ) × ℝ × ℝ

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_BishopAnalyticDiscs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter

namespace Release061.Wiener

def constantDisc : ℝ →L[ℝ] C(ClosedDisc,ℂ) :=
  ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) 1

lemma fourier_mem_closedDisc (θ : Circle) : fourier 1 θ ∈ ClosedDisc := by
  simpa only [ClosedDisc,Metric.mem_closedBall,dist_zero_right,fourier_one] using
    (_root_.Circle.norm_coe (AddCircle.toCircle θ)).le

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CosineBumpWeightedSummable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
namespace Release061.Wiener

def circleCos : C(Circle,ℝ) :=
  ⟨fun θ => (fourier 1 θ).re,Complex.continuous_re.comp (fourier 1).continuous⟩

def cosineBump (r R : ℝ) (hr : 0 < r) (hR : r < R) : C(Circle,ℝ) :=
  let B : ContDiffBump (-1 : ℝ) := ⟨r,R,hr,hR⟩
  ⟨fun θ => B (circleCos θ),B.continuous.comp circleCos.continuous⟩

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_BishopDiscRadialExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter

namespace Release061.Wiener

lemma radial_mem_closedDisc {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    1-(t : ℂ) ∈ ClosedDisc := by
  simp only [ClosedDisc,Metric.mem_closedBall,dist_zero_right]
  rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr ht1)]
  linarith

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_BishopPathInterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
namespace Release061.Wiener
open scoped Topology
open Set Filter Metric

def graphPoint {k : ℕ} (f : (Fin (k+1) → ℝ) → Fin k → ℝ)
    (q : (Fin k → ℝ) × ℝ) : Fin k → ℂ :=
  fun i => (q.1 i : ℂ)+Complex.I*(f (Fin.cons q.2 q.1) i : ℂ)

def imaginaryVector {k : ℕ} (e : Fin k → ℝ) : Fin k → ℂ :=
  fun i => Complex.I*(e i : ℂ)

def DiscContinuityWithin (k : ℕ) (Ω : Set (Fin k → ℂ)) (ε : ℝ) : Prop :=
  ∀ A : Icc (0 : ℝ) 1 → ClosedDisc → Fin k → ℂ,
    Continuous (Function.uncurry A) →
    (∀ s, ∃ g : ℂ → Fin k → ℂ, AnalyticOnNhd ℂ g (ball 0 1) ∧ ∀ z : ClosedDisc, A s z = g z) →
    (∀ s z, ‖A s z‖ < ε) →
    (∀ s (z : ClosedDisc), ‖(z : ℂ)‖ = 1 → A s z ∈ Ω) →
    (∀ z, A ⟨0,by simp⟩ z ∈ Ω) → ∀ s z, A s z ∈ Ω

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_Vector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric

open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.Complexify
variable {d j : ℕ}

def monomial (σ : Fin j → Fin d) : ContinuousMultilinearMap ℂ (fun _ : Fin j => Fin d → ℂ) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℂ j ℂ).compContinuousLinearMap
    (fun i => ContinuousLinearMap.proj (σ i))

def coefficient (p : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin d → ℝ) ℝ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin j => Fin d → ℂ) ℂ :=
  ∑ σ : Fin j → Fin d, (p (fun i => Pi.single (σ i) 1)) • monomial σ

def series (p : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ) :
    FormalMultilinearSeries ℂ (Fin d → ℂ) ℂ := fun j => coefficient (p j)

end Release061.Complexify

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_HorizontalGraphComplexification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.Flatten
open Set Filter
open scoped Topology

def realEmbedding (k : ℕ) : (Fin k → ℝ) →L[ℝ] (Fin k → ℂ) :=
  ContinuousLinearMap.pi (fun i => Complex.ofRealCLM.comp (ContinuousLinearMap.proj i))

def realPart (k : ℕ) : (Fin k → ℂ) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi (fun i => Complex.reCLM.comp (ContinuousLinearMap.proj i))

def imaginaryPart (k : ℕ) : (Fin k → ℂ) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi (fun i => Complex.imCLM.comp (ContinuousLinearMap.proj i))

end Release061.Flatten

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticReparameterization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.Flatten
open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def shearEquiv (b : E) : (E × ℝ) ≃L[ℝ] (E × ℝ) := by
  let X := ContinuousLinearMap.fst ℝ E ℝ
  let u := ContinuousLinearMap.snd ℝ E ℝ
  exact ContinuousLinearEquiv.equivOfInverse
    ((X + u.smulRight b).prod u) ((X - u.smulRight b).prod u)
    (by intro q; ext <;> simp [X,u]) (by intro q; ext <;> simp [X,u])

end Release061.Flatten

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ScaledRadialOperatorApply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
namespace Release061.Wiener
open scoped Topology
open Set Filter Metric

def radialPoint (t : ℝ) : ClosedDisc :=
  ⟨1-(max 0 (min 1 t) : ℝ),radial_mem_closedDisc (le_max_left _ _)
    (max_le (by norm_num) (min_le_left _ _))⟩

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ScaledModelC1Limit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
namespace Release061.Wiener
open scoped Topology
open Set Filter Metric
abbrev RealDiscParams (k : ℕ) := (Fin k → ℝ) × (Fin k → ℝ)

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticNashRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology MeasureTheory
open scoped Classical

def HasAnalyticNashCover {n k : ℕ} (S : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → (Fin k → ℝ)) : Prop :=
  ∃ P : Finset (NashPatch n), (∀ x, x ∈ S ↔ ∃ p ∈ P, x ∈ p.image) ∧
    ∀ p ∈ P, AnalyticOnNhd ℝ (f ∘ p.toFun) p.domain

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_Centered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology
open scoped Classical

namespace NashPatch
variable {n : ℕ}

noncomputable def recenter (p : NashPatch n) (x : Fin p.dim → ℝ) : NashPatch n where
  dim := p.dim
  domain := (fun y => y+x) ⁻¹' p.domain
  isOpen_domain := p.isOpen_domain.preimage (continuous_id.add continuous_const)
  isConnected_domain := (Homeomorph.addRight x).isConnected_preimage.mpr p.isConnected_domain
  semialgebraic_domain := p.semialgebraic_domain.polynomial_preimage (fun y => y+x)
    (fun i => MvPolynomial.X i + MvPolynomial.C (x i)) (by intros; simp)
  toFun := fun y => p.toFun (y+x)
  semialgebraic_toFun := by
    have hB := p.semialgebraic_domain.polynomial_preimage (d := id) (fun y => y+x)
      (fun i => MvPolynomial.X i + MvPolynomial.C (x i)) (by intros; simp)
    have ht : SemialgebraicOn ((fun y => y+x) ⁻¹' p.domain) (fun y => y+x) := by
      exact (SemialgebraicOn.polynomial hB (fun i => MvPolynomial.X i + MvPolynomial.C (x i))).congr
        (by intro y _; funext i; simp)
    exact p.semialgebraic_toFun.comp ht (fun _ h => h)
  analytic_toFun := by
    intro y hy
    exact (p.analytic_toFun (y+x) hy).comp (f := fun z => z+x) (x := y) (analyticAt_id.add analyticAt_const)
  injective_fderiv := by
    intro y hy
    have htr : HasFDerivAt (fun z : Fin p.dim → ℝ => z+x) (ContinuousLinearMap.id ℝ _) y :=
      (hasFDerivAt_id y).add_const x
    have hd := (p.analytic_toFun (y+x) hy).differentiableAt.hasFDerivAt.comp y htr
    change Function.Injective (fderiv ℝ (p.toFun ∘ (fun z => z+x)) y)
    rw [hd.fderiv]
    simpa only [ContinuousLinearMap.comp_id] using p.injective_fderiv (y+x) hy

noncomputable def centered (p : NashPatch n) : NashPatch n :=
  p.recenter p.isConnected_domain.nonempty.choose

end NashPatch

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CocompactChartDiscContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
namespace Release061
open scoped Topology
open Set Filter Metric

lemma norm_affine_one (x : Affine 1) : ‖x‖ = ‖x 0‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    simpa only [Subsingleton.elim i (0 : Fin 1)] using le_refl ‖x 0‖
  · exact norm_le_pi_norm x 0

def affineClosedDiscCoordinate (x : closedBall (0 : Affine 1) 1) : Wiener.ClosedDisc :=
  ⟨x.val 0,by
    have hx := mem_closedBall_zero_iff.mp x.property
    rw [norm_affine_one] at hx
    exact mem_closedBall_zero_iff.mpr hx⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SortedFiberSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set
open scoped Classical

def SortedFiber {X : Type*} (R : Set (X × ℝ)) (r : ℕ) : Set (X × (Fin r → ℝ)) :=
  {z | StrictMono z.2 ∧ ∀ y : ℝ, (z.1,y) ∈ R ↔ ∃ i, y = z.2 i}

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_VerticalPieceBasePolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set
open scoped Classical

abbrev VerticalPiece (r : ℕ) := Fin r ⊕ (Option (Fin r) × Option (Fin r))

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SemialgebraicBoundaryFiniteNash
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open SignElimination
open scoped Classical

noncomputable def realCoordinatesEquiv (n : ℕ) : Affine n ≃L[ℝ] (Fin n ⊕ Fin n → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
  { toFun := realCoordinates
    invFun := fun x j => ⟨x (.inl j),x (.inr j)⟩
    left_inv := by intro z; ext j; rfl
    right_inv := by intro x; funext j; cases j <;> rfl
    map_add' := by intro x y; funext j; cases j <;> rfl
    map_smul' := by intro r x; funext j; cases j <;> simp [realCoordinates] }

noncomputable def complexRealEquiv (n : ℕ) : Affine n ≃L[ℝ] (Fin (n+n) → ℝ) :=
  (realCoordinatesEquiv n).trans
    (LinearEquiv.funCongrLeft ℝ ℝ finSumFinEquiv.symm).toContinuousLinearEquiv

namespace NashPatch
variable {n : ℕ}

noncomputable def complexMap (p : NashPatch (n+n)) : (Fin p.dim → ℝ) → Affine n :=
  (complexRealEquiv n).symm ∘ p.toFun

end NashPatch

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_GenericNormalGraphProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology
open scoped Classical

noncomputable def complexGraphRealEquiv (r k : ℕ) :
    (Affine r × Affine k) ≃L[ℝ] ((Fin ((r+r)+k) → ℝ) × (Fin k → ℝ)) :=
  LinearEquiv.toContinuousLinearEquiv
  { toFun := fun p =>
      ((fun j => Sum.elim (complexRealEquiv r p.1) (fun i => (p.2 i).re)
          (finSumFinEquiv.symm j)), fun i => (p.2 i).im)
    invFun := fun p =>
      ((complexRealEquiv r).symm (fun j => p.1 (finSumFinEquiv (.inl j))),
        fun j => ⟨p.1 (finSumFinEquiv (.inr j)),p.2 j⟩)
    left_inv := by
      intro p
      apply Prod.ext
      · simpa only [Equiv.symm_apply_apply,Sum.elim_inl] using
          (complexRealEquiv r).symm_apply_apply p.1
      · funext j
        apply Complex.ext
        · simp only [Equiv.symm_apply_apply,Sum.elim_inr]
        · rfl
    right_inv := by
      intro p
      apply Prod.ext
      · funext j
        obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
        cases j with
        | inl j => simp only [Equiv.symm_apply_apply,Sum.elim_inl,
            (complexRealEquiv r).apply_symm_apply]
        | inr j => simp only [Equiv.symm_apply_apply,Sum.elim_inr]
      · rfl
    map_add' := by
      intro p q
      apply Prod.ext
      · funext j
        obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
        cases j <;> simp [map_add]
      · rfl
    map_smul' := by
      intro a p
      apply Prod.ext
      · funext j
        obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
        cases j <;> simp [map_smul]
      · funext j
        exact Complex.smul_im a (p.2 j) }

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SemialgebraicPolynomialNonzero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Topology MeasureTheory
open scoped Classical

namespace NashPatch
noncomputable def complexRank {n : ℕ} (p : NashPatch (n+n)) (x : Fin p.dim → ℝ) : ℕ :=
  Matrix.rank (fun j i => fderiv ℝ (fun y => p.complexMap y j) x (Pi.single i 1))

end NashPatch
end

open Set
open scoped Classical

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_GenericNashNormalCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open scoped Classical

structure NashNormalCoordinates {d m : ℕ}
    (B : Set (Fin d → ℝ)) (q : (Fin d → ℝ) → Affine m) (a : Fin d → ℝ) where
  tangentDim : ℕ
  normalDim : ℕ
  complex_dimension : tangentDim + normalDim = m
  real_dimension : d = (tangentDim+tangentDim)+normalDim
  coordinates : Affine m ≃L[ℂ] (Affine tangentDim × Affine normalDim)
  parameters : OpenPartialHomeomorph (Fin d → ℝ) (Fin ((tangentDim+tangentDim)+normalDim) → ℝ)
  radius : ℝ
  radius_pos : 0 < radius
  graph : (Fin ((tangentDim+tangentDim)+normalDim) → ℝ) → (Fin normalDim → ℝ)
  parameter_eq : (parameters : (Fin d → ℝ) → _) =
    fun x => (complexGraphRealEquiv tangentDim normalDim (coordinates (q x-q a))).1
  source_mem : a ∈ parameters.source
  inverse_zero : parameters.symm 0 = a
  ball_target : ball 0 radius ⊆ parameters.target
  inverse_mapsTo : MapsTo parameters.symm (ball 0 radius) B
  inverse_analytic : AnalyticOnNhd ℝ parameters.symm (ball 0 radius)
  inverse_semialgebraic : SemialgebraicOn (ball 0 radius) parameters.symm
  graph_analytic : AnalyticOnNhd ℝ graph (ball 0 radius)
  graph_semialgebraic : SemialgebraicOn (ball 0 radius) graph
  graph_zero : graph 0 = 0
  derivative_zero : fderiv ℝ graph 0 = 0
  graph_identity : ∀ s ∈ ball 0 radius,
    complexGraphRealEquiv tangentDim normalDim (coordinates (q (parameters.symm s)-q a)) = (s,graph s)
  local_graph_identity : ∀ᶠ x in 𝓝 a, parameters x ∈ ball 0 radius ∧
    complexGraphRealEquiv tangentDim normalDim (coordinates (q x-q a)) =
      (parameters x,graph (parameters x))

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ProjectionNashChartGerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set Filter Topology Metric
open scoped Classical

structure ProjectionNashChart {N : ℕ} (V : Set (Affine N)) (p : Affine N) (m : ℕ) where
  projection : Affine N →L[ℂ] Affine m
  inverse : Affine m → Affine N
  radius : ℝ
  radius_pos : 0 < radius
  inverse_zero : inverse 0 = p
  inverse_analytic : AnalyticOnNhd ℂ inverse {z | ‖complexRealEquiv m z‖ < radius}
  inverse_semialgebraic : SemialgebraicOn {x : Fin (m+m) → ℝ | ‖x‖ < radius}
    (fun x => complexRealEquiv N (inverse ((complexRealEquiv m).symm x)))
  left_inverse : ∀ z, ‖complexRealEquiv m z‖ < radius → projection (inverse z-p) = z
  right_inverse : ∀ᶠ y in 𝓝[V] p, inverse (projection (y-p)) = y
  inverse_mem : ∀ z, ‖complexRealEquiv m z‖ < radius → inverse z ∈ V

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_GoodNashBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric MeasureTheory
open scoped Classical

def BoundaryOffsetData {s k : ℕ}
    (A : (Fin s → ℝ) → Set (Fin k → ℝ)) (B : Set (Fin s → ℝ))
    (x : Fin s → ℝ) : Prop :=
  (∃ r > 0, ∃ η > 0, ∃ ψ : (Fin s → ℝ) × ℝ → (Fin k → ℝ),
    ball x r ⊆ B ∧ AnalyticOnNhd ℝ ψ (ball x r ×ˢ ball 0 η) ∧
    (∀ y ∈ ball x r, ψ (y,0) = 0) ∧
    ∀ y ∈ ball x r, ∀ t ∈ Ioo (0 : ℝ) η, ψ (y,t) ∈ A y) ∧
  ∃ f : (Fin k → ℝ) → ℝ, LipschitzWith 1 f ∧
    (∀ y, f y ∈ Icc (0 : ℝ) 1) ∧
    (∀ y, Tendsto (fun p : (Fin s → ℝ) × ℝ => offsetDistance A p.1 p.2 y)
      (𝓝[{p : (Fin s → ℝ) × ℝ | 0 < p.2}] (x,0)) (𝓝 (f y))) ∧
    (∀ K : Set (Fin k → ℝ), IsCompact K →
      TendstoUniformlyOn (fun p : (Fin s → ℝ) × ℝ => offsetDistance A p.1 p.2) f
        (𝓝[{p : (Fin s → ℝ) × ℝ | 0 < p.2}] (x,0)) K) ∧
    IsClosed {y | f y = 0} ∧ (0 : Fin k → ℝ) ∈ {y | f y = 0} ∧
    ∀ c : ℝ, 0 < c → ∀ y, f y = 0 ↔ f (c • y) = 0

noncomputable def NashNormalCoordinates.realCoordinates {d m : ℕ}
    {B : Set (Fin d → ℝ)} {q : (Fin d → ℝ) → Affine m} {a : Fin d → ℝ}
    (c : NashNormalCoordinates B q a) :
    Affine m ≃L[ℝ] ((Fin ((c.tangentDim+c.tangentDim)+c.normalDim) → ℝ) × (Fin c.normalDim → ℝ)) :=
  (c.coordinates.toLinearEquiv.restrictScalars ℝ).toContinuousLinearEquiv.trans
    (complexGraphRealEquiv c.tangentDim c.normalDim)

noncomputable def ProjectionNashChart.coordinateDomain {N m s k : ℕ}
    {V : Set (Affine N)} {p : Affine N}
    (c : ProjectionNashChart V p m) (U : Set (Affine N))
    (e : Affine m ≃L[ℝ] ((Fin s → ℝ) × (Fin k → ℝ))) :
    Set ((Fin s → ℝ) × (Fin k → ℝ)) :=
  {z | ‖complexRealEquiv m (e.symm z)‖ < c.radius ∧ c.inverse (e.symm z) ∈ U}

structure NashBoundaryChart {d m N : ℕ} (U V : Set (Affine N))
    (B : Set (Fin d → ℝ)) (q : (Fin d → ℝ) → Affine N) where
  center : Fin d → ℝ
  center_mem : center ∈ B
  chart : ProjectionNashChart V (q center) m
  normal : NashNormalCoordinates B (fun x => chart.projection (q x-q center)) center
  graphRadius : ℝ
  graphRadius_pos : 0 < graphRadius
  graphRadius_le : graphRadius ≤ normal.radius
  domain_semialgebraic : PolynomialSignSet (fun z => Sum.elim z.1 z.2)
    (chart.coordinateDomain U normal.realCoordinates)
  graph_boundary : ∀ s ∈ ball 0 graphRadius,
    (s,normal.graph s) ∈ closure (chart.coordinateDomain U normal.realCoordinates) \
      (chart.coordinateDomain U normal.realCoordinates) ∧
    ‖complexRealEquiv m (normal.realCoordinates.symm (s,normal.graph s))‖ < chart.radius ∧
    chart.inverse (normal.realCoordinates.symm (s,normal.graph s)) = q (normal.parameters.symm s)

namespace NashBoundaryChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N}
noncomputable def family (c : NashBoundaryChart (m := m) U V B q) :=
  normalOffsetFamily (c.chart.coordinateDomain U c.normal.realCoordinates)
    (ball 0 c.graphRadius) c.normal.graph 1

def GoodAt (c : NashBoundaryChart (m := m) U V B q) (x : Fin d → ℝ) : Prop :=
  x ∈ c.normal.parameters.source ∧ c.normal.parameters x ∈ ball 0 c.graphRadius ∧
  BoundaryOffsetData c.family (ball 0 c.graphRadius) (c.normal.parameters x)

end NashBoundaryChart

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_OldOffsetOldPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open scoped Classical

namespace NashBoundaryChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N}

noncomputable def oldPosition (c : NashBoundaryChart (m := m) U V B q)
    (s : Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ) : Affine m :=
  c.normal.realCoordinates.symm (s,c.normal.graph s)

noncomputable def oldParameter (c : NashBoundaryChart (m := m) U V B q) (z : Affine m) :=
  (c.normal.realCoordinates z).1

noncomputable def oldOffset (c : NashBoundaryChart (m := m) U V B q) (z : Affine m) :=
  (c.normal.realCoordinates z).2-c.normal.graph (c.oldParameter z)

@[simp] theorem oldParameter_oldPosition (c : NashBoundaryChart (m := m) U V B q) (s) :
    c.oldParameter (c.oldPosition s) = s := by
  simp only [oldParameter,oldPosition,ContinuousLinearEquiv.apply_symm_apply]

@[simp] theorem oldOffset_oldPosition (c : NashBoundaryChart (m := m) U V B q) (s) :
    c.oldOffset (c.oldPosition s) = 0 := by
  simp only [oldOffset,oldParameter,oldPosition,ContinuousLinearEquiv.apply_symm_apply,sub_self]

end NashBoundaryChart
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_GenericSurjectiveRealNormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.NashBoundaryChart
open Set Filter Topology Metric
open scoped Classical
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N}

noncomputable def oldOffsetDerivative (c : NashBoundaryChart (m := m) U V B q)
    (s : Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ) :
    Affine m →L[ℝ] (Fin c.normal.normalDim → ℝ) :=
  (ContinuousLinearMap.snd ℝ _ _).comp c.normal.realCoordinates.toContinuousLinearMap -
    (fderiv ℝ c.normal.graph s).comp
      ((ContinuousLinearMap.fst ℝ _ _).comp c.normal.realCoordinates.toContinuousLinearMap)

end Release061.NashBoundaryChart

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_OffsetDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set Filter Topology Metric
open scoped Classical

structure NashBoundaryScalingChart {d m N : ℕ} {U V : Set (Affine N)}
    {B : Set (Fin d → ℝ)} {q : (Fin d → ℝ) → Affine N}
    (c : NashBoundaryChart (m := m) U V B q) (x : Fin d → ℝ) where
  tangentDim : ℕ
  normalDim : ℕ
  dimension : tangentDim+normalDim=m
  normal_dimension : normalDim=c.normal.normalDim
  coordinates : Affine m ≃L[ℂ] (Affine tangentDim × Affine normalDim)
  normalMap : (Fin normalDim → ℝ) ≃L[ℝ] (Fin c.normal.normalDim → ℝ)
  differential : ∀ z, c.oldOffsetDerivative (c.normal.parameters x) (coordinates.symm z) =
    normalMap (Flatten.imaginaryPart normalDim z.2)
  offsets : OpenPartialHomeomorph (Affine tangentDim × Affine normalDim)
    ((Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ) × (Fin c.normal.normalDim → ℝ))
  offsets_eq : ∀ z, offsets z =
    (c.oldParameter (coordinates.symm z+c.oldPosition (c.normal.parameters x)),
     c.oldOffset (coordinates.symm z+c.oldPosition (c.normal.parameters x)))
  source_zero : (0 : Affine tangentDim × Affine normalDim) ∈ offsets.source
  offsets_zero : offsets 0 = (c.normal.parameters x,0)
  inverse_analytic : AnalyticAt ℝ offsets.symm (c.normal.parameters x,0)
  analytic : AnalyticAt ℝ offsets 0

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ForwardBackwardGerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open scoped Classical
namespace NashBoundaryScalingChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N} {c : NashBoundaryChart (m := m) U V B q}
variable {x : Fin d → ℝ}

noncomputable def forward (s : NashBoundaryScalingChart c x)
    (z : Affine s.tangentDim × Affine s.normalDim) : Affine N :=
  c.chart.inverse (s.coordinates.symm z+c.oldPosition (c.normal.parameters x))

noncomputable def backward (s : NashBoundaryScalingChart c x) (y : Affine N) :
    Affine s.tangentDim × Affine s.normalDim :=
  s.coordinates (c.chart.projection (y-q c.center)-c.oldPosition (c.normal.parameters x))

def HasCutoffs (s : NashBoundaryScalingChart c x) : Prop :=
  ∀ z ∈ s.offsets.source,
    c.oldParameter (s.coordinates.symm z+c.oldPosition (c.normal.parameters x)) ∈ ball 0 c.graphRadius ∧
    ‖complexRealEquiv m (s.coordinates.symm z+c.oldPosition (c.normal.parameters x))‖ < c.chart.radius ∧
    ‖c.oldOffset (s.coordinates.symm z+c.oldPosition (c.normal.parameters x))‖ < 1

theorem backward_analytic (s : NashBoundaryScalingChart c x) : AnalyticOnNhd ℂ s.backward univ := by
  intro y _
  exact (s.coordinates.toContinuousLinearMap.analyticAt _).comp
    (((c.chart.projection.analyticAt _).comp (analyticAt_id.sub analyticAt_const)).sub analyticAt_const)

theorem forward_analytic (s : NashBoundaryScalingChart c x) (hcut : s.HasCutoffs) :
    AnalyticOnNhd ℂ s.forward s.offsets.source := by
  intro z hz
  exact (c.chart.inverse_analytic _ (hcut z hz).2.1).comp
    (f := fun z => s.coordinates.symm z+c.oldPosition (c.normal.parameters x)) (x := z)
    ((s.coordinates.symm.toContinuousLinearMap.analyticAt _).add analyticAt_const)

theorem backward_forward (s : NashBoundaryScalingChart c x) (hcut : s.HasCutoffs)
    {z : Affine s.tangentDim × Affine s.normalDim} (hz : z ∈ s.offsets.source) :
    s.backward (s.forward z)=z := by
  unfold backward forward
  rw [c.chart.left_inverse _ (hcut z hz).2.1,add_sub_cancel_right,s.coordinates.apply_symm_apply]

end NashBoundaryScalingChart
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_HermPartUnit
attribute [-instance] _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.Hermitian
open Complex
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [Module ℂ E]
  [IsScalarTower ℝ ℂ E]

lemma complex_smul_split (c : ℂ) (x : E) :
    c • x = c.re • x + c.im • (I • x) := by
  calc
    c • x = ((c.re:ℂ)+(c.im:ℂ)*I) • x := by rw [re_add_im]
    _ = (c.re:ℂ) • x + (c.im:ℂ) • (I • x) := by rw [add_smul,mul_smul]
    _ = _ := congrArg₂ (fun u v : E => u+v)
      (RCLike.real_smul_eq_coe_smul (K := ℂ) c.re x).symm
      (RCLike.real_smul_eq_coe_smul (K := ℂ) c.im (I • x)).symm

def holPart (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (z w : E) : ℂ :=
  ((B z w-B (I • z) (I • w))/2 : ℝ) -
    I*(( (B (I • z) w+B z (I • w))/2 : ℝ) : ℂ)

def hermPart (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (z w : E) : ℂ :=
  ((B z w+B (I • z) (I • w))/2 : ℝ) +
    I*(( (B z (I • w)-B (I • z) w)/2 : ℝ) : ℂ)

omit [IsScalarTower ℝ ℂ E] in
lemma holPart_add_left (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x y z : E) :
    holPart B (x+y) z = holPart B x z+holPart B y z := by
  simp only [holPart,smul_add,map_add,LinearMap.add_apply,ofReal_div,
    ofReal_sub,ofReal_add,ofReal_ofNat]
  ring

omit [IsScalarTower ℝ ℂ E] in
lemma holPart_add_right (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x y z : E) :
    holPart B x (y+z) = holPart B x y+holPart B x z := by
  simp only [holPart,smul_add,map_add,ofReal_div,ofReal_sub,ofReal_add,ofReal_ofNat]
  ring

lemma holPart_real_left (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (r : ℝ) (x y : E) :
    holPart B (r • x) y = r • holPart B x y := by
  simp only [holPart,smul_comm I r,map_smul,LinearMap.smul_apply,smul_eq_mul,
    ofReal_div,ofReal_sub,ofReal_add,ofReal_mul,ofReal_ofNat,Complex.real_smul]
  ring

lemma holPart_real_right (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (r : ℝ) (x y : E) :
    holPart B x (r • y) = r • holPart B x y := by
  simp only [holPart,smul_comm I r,map_smul,smul_eq_mul,
    ofReal_div,ofReal_sub,ofReal_add,ofReal_mul,ofReal_ofNat,Complex.real_smul]
  ring

omit [IsScalarTower ℝ ℂ E] in
lemma holPart_I_left (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x y : E) :
    holPart B (I • x) y = I*holPart B x y := by
  simp only [holPart,smul_smul,I_mul_I,neg_smul,one_smul,map_neg,
    LinearMap.neg_apply,ofReal_div,ofReal_sub,ofReal_add,ofReal_neg,ofReal_ofNat]
  linear_combination ((B (I • x) y : ℂ)+(B x (I • y) : ℂ))/2*I_sq

omit [IsScalarTower ℝ ℂ E] in
lemma holPart_I_right (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x y : E) :
    holPart B x (I • y) = I*holPart B x y := by
  simp only [holPart,smul_smul,I_mul_I,neg_smul,one_smul,map_neg,
    ofReal_div,ofReal_sub,ofReal_add,ofReal_neg,ofReal_ofNat]
  linear_combination ((B (I • x) y : ℂ)+(B x (I • y) : ℂ))/2*I_sq

lemma holPart_smul_left (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (c : ℂ) (x y : E) :
    holPart B (c • x) y = c*holPart B x y := by
  rw [complex_smul_split,holPart_add_left,holPart_real_left,holPart_real_left,holPart_I_left]
  simp only [Complex.real_smul]
  conv_rhs => rw [← re_add_im c]
  ring

lemma holPart_smul_right (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (c : ℂ) (x y : E) :
    holPart B x (c • y) = c*holPart B x y := by
  rw [complex_smul_split,holPart_add_right,holPart_real_right,holPart_real_right,holPart_I_right]
  simp only [Complex.real_smul]
  conv_rhs => rw [← re_add_im c]
  ring

def holBilinear (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) : E →ₗ[ℂ] E →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (holPart B) (holPart_add_left B) (holPart_smul_left B)
    (holPart_add_right B) (holPart_smul_right B)

omit [IsScalarTower ℝ ℂ E] in
lemma hermPart_add_left (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x y z : E) :
    hermPart B (x+y) z = hermPart B x z+hermPart B y z := by
  simp only [hermPart,smul_add,map_add,LinearMap.add_apply,ofReal_div,
    ofReal_sub,ofReal_add,ofReal_ofNat]
  ring

omit [IsScalarTower ℝ ℂ E] in
lemma hermPart_add_right (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x y z : E) :
    hermPart B x (y+z) = hermPart B x y+hermPart B x z := by
  simp only [hermPart,smul_add,map_add,ofReal_div,ofReal_sub,ofReal_add,ofReal_ofNat]
  ring

lemma hermPart_real_left (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (r : ℝ) (x y : E) :
    hermPart B (r • x) y = r • hermPart B x y := by
  simp only [hermPart,smul_comm I r,map_smul,LinearMap.smul_apply,smul_eq_mul,
    ofReal_div,ofReal_sub,ofReal_add,ofReal_mul,ofReal_ofNat,Complex.real_smul]
  ring

lemma hermPart_real_right (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (r : ℝ) (x y : E) :
    hermPart B x (r • y) = r • hermPart B x y := by
  simp only [hermPart,smul_comm I r,map_smul,smul_eq_mul,
    ofReal_div,ofReal_sub,ofReal_add,ofReal_mul,ofReal_ofNat,Complex.real_smul]
  ring

omit [IsScalarTower ℝ ℂ E] in
lemma hermPart_I_left (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x y : E) :
    hermPart B (I • x) y = I*hermPart B x y := by
  simp only [hermPart,smul_smul,I_mul_I,neg_smul,one_smul,map_neg,
    LinearMap.neg_apply,ofReal_div,ofReal_sub,ofReal_add,ofReal_neg,ofReal_ofNat]
  linear_combination ((B (I • x) y : ℂ)-(B x (I • y) : ℂ))/2*I_sq

omit [IsScalarTower ℝ ℂ E] in
lemma hermPart_I_right (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x y : E) :
    hermPart B x (I • y) = -I*hermPart B x y := by
  simp only [hermPart,smul_smul,I_mul_I,neg_smul,one_smul,map_neg,
    ofReal_div,ofReal_sub,ofReal_add,ofReal_neg,ofReal_ofNat]
  linear_combination ((B x (I • y) : ℂ)-(B (I • x) y : ℂ))/2*I_sq

lemma hermPart_smul_left (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (c : ℂ) (x y : E) :
    hermPart B (c • x) y = c*hermPart B x y := by
  rw [complex_smul_split,hermPart_add_left,hermPart_real_left,hermPart_real_left,hermPart_I_left]
  simp only [Complex.real_smul]
  conv_rhs => rw [← re_add_im c]
  ring

lemma hermPart_smul_right (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (c : ℂ) (x y : E) :
    hermPart B x (c • y) = (starRingEnd ℂ c)*hermPart B x y := by
  rw [complex_smul_split,hermPart_add_right,hermPart_real_right,hermPart_real_right,hermPart_I_right]
  simp only [Complex.real_smul]
  conv_rhs => rw [← re_add_im c]
  simp only [map_add,map_mul,conj_ofReal,conj_I]
  ring

omit [IsScalarTower ℝ ℂ E] in
lemma hermPart_diag_real (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hs : ∀ x y, B x y = B y x)
    (x : E) : (hermPart B x x).im = 0 := by
  simp [hermPart,hs (I • x) x]

def symmetrize (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  (1/2 : ℝ) • (B+B.flip)

omit [IsScalarTower ℝ ℂ E] [Module ℂ E] in
lemma symmetrize_symm (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x y : E) :
    symmetrize B x y = symmetrize B y x := by
  simp [symmetrize,add_comm]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F]

def holContinuous (B : F →ₗ[ℝ] F →ₗ[ℝ] ℝ) : F →L[ℂ] F →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp (holBilinear B))

lemma holPart_analytic (B : F →ₗ[ℝ] F →ₗ[ℝ] ℝ) (z : F) :
    AnalyticAt ℂ (fun x => holPart B x x) z := by
  exact (holContinuous B |>.analyticAt_bilinear (z,z)).comp (f := fun x : F => (x,x))
    (analyticAt_id.prod analyticAt_id)

end Release061.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_HolQuadraticSmul
attribute [-instance] _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.Hermitian
open Set Complex
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  {k : ℕ}

def holQuadratic (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (z : E) : Fin k → ℂ :=
  fun i => holPart (symmetrize (B i)) z z

def hermQuadratic (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (z : E) : Fin k → ℝ :=
  fun i => (hermPart (symmetrize (B i)) z z).re

lemma holQuadratic_analytic (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (z : E) :
    AnalyticAt ℂ (holQuadratic B) z := by
  exact analyticAt_pi_iff.mpr (fun i => holPart_analytic (symmetrize (B i)) z)

lemma holQuadratic_continuous (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) :
    Continuous (holQuadratic B) :=
  continuous_iff_continuousAt.mpr fun z => (holQuadratic_analytic B z).continuousAt

def quadraticShear (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) :
    E × (Fin k → ℂ) ≃ₜ E × (Fin k → ℂ) where
  toFun x := (x.1,x.2-I • holQuadratic B x.1)
  invFun x := (x.1,x.2+I • holQuadratic B x.1)
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := continuous_fst.prodMk
    (continuous_snd.sub ((holQuadratic_continuous B).comp continuous_fst |>.const_smul I))
  continuous_invFun := continuous_fst.prodMk
    (continuous_snd.add ((holQuadratic_continuous B).comp continuous_fst |>.const_smul I))

omit [FiniteDimensional ℂ E] in
lemma hermQuadratic_real_smul (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (r : ℝ) (z : E) :
    hermQuadratic B (r • z) = r^2 • hermQuadratic B z := by
  funext i
  simp only [hermQuadratic,hermPart_real_left,hermPart_real_right,Pi.smul_apply,
    Complex.real_smul,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero,smul_eq_mul]
  ring

end Release061.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_HeisenbergShiftAxis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.Hermitian
open Set Complex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] {k : ℕ}

def heisenbergShift (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (a : E)
    (p : E × (Fin k → ℂ)) : E × (Fin k → ℂ) :=
  (p.1+a,fun i => p.2 i + 2*I*hermPart (symmetrize (B i)) p.1 a +
    I*(hermQuadratic B a i : ℂ))

def hermLinearLeft (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (a : E) : E →ₗ[ℂ] ℂ where
  toFun z := hermPart B z a
  map_add' x y := hermPart_add_left B x y a
  map_smul' c x := hermPart_smul_left B c x a

lemma heisenbergShift_analytic
    (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (a : E) :
    AnalyticOnNhd ℂ (heisenbergShift B a) univ := by
  intro p _
  apply AnalyticAt.prod
  · exact analyticAt_fst.add analyticAt_const
  · apply analyticAt_pi_iff.mpr
    intro i
    have hh : AnalyticAt ℂ (fun q : E × (Fin k → ℂ) =>
        hermPart (symmetrize (B i)) q.1 a) p :=
      ((hermLinearLeft (symmetrize (B i)) a).toContinuousLinearMap.analyticAt p.1).comp
        analyticAt_fst
    exact ((((ContinuousLinearMap.proj i).analyticAt p.2).comp analyticAt_snd).add
      (analyticAt_const.mul hh)).add analyticAt_const

omit [FiniteDimensional ℂ E] in
lemma hermPart_neg_right (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x y : E) :
    hermPart B x (-y) = -hermPart B x y := by
  rw [show -y = (-1 : ℂ) • y by simp,hermPart_smul_right]
  simp

omit [FiniteDimensional ℂ E] in
lemma heisenbergShift_left_inverse
    (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (a : E) :
    Function.LeftInverse (heisenbergShift B (-a)) (heisenbergShift B a) := by
  intro p
  apply Prod.ext
  · simp [heisenbergShift]
  · funext i
    have hQ : hermQuadratic B (-a) = hermQuadratic B a := by
      simpa using hermQuadratic_real_smul B (-1) a
    have hdiag : hermPart (symmetrize (B i)) a a = (hermQuadratic B a i : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa using hermPart_diag_real (symmetrize (B i)) (symmetrize_symm (B i)) a
    simp only [heisenbergShift,hermPart_neg_right,hermPart_add_left,hQ]
    rw [hdiag]
    ring

def heisenbergHomeomorph
    (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (a : E) :
    (E × (Fin k → ℂ)) ≃ₜ (E × (Fin k → ℂ)) where
  toFun := heisenbergShift B a
  invFun := heisenbergShift B (-a)
  left_inv := heisenbergShift_left_inverse B a
  right_inv p := by simpa only [neg_neg] using heisenbergShift_left_inverse B (-a) p
  continuous_toFun := continuous_iff_continuousAt.mpr
    (fun p => (heisenbergShift_analytic B a p (mem_univ _)).continuousAt)
  continuous_invFun := continuous_iff_continuousAt.mpr
    (fun p => (heisenbergShift_analytic B (-a) p (mem_univ _)).continuousAt)

end Release061.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_IndependentConormals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology MeasureTheory
open scoped Classical

noncomputable def affineMapCodRestrict
    {E G : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup G] [Module ℝ G]
    (A : E →ᵃ[ℝ] G) (W : Submodule ℝ G) (hA : ∀ x, A x ∈ W) : E →ᵃ[ℝ] W where
  toFun x := ⟨A x,hA x⟩
  linear := A.linear.codRestrict W (fun x => by
    have he : A.linear x = A x - A 0 := by
      simpa only [vsub_eq_sub,sub_zero] using A.linearMap_vsub x 0
    rw [he]
    exact W.sub_mem (hA x) (hA 0))
  map_vadd' x v := by
    apply Subtype.ext
    exact A.map_vadd x v

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_LocallySmallSlopeGood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set Filter Topology Metric MeasureTheory
open scoped Classical

def SmallSlopeGoodNashBoundary {d N : ℕ} (m : ℕ) (U V : Set (Affine N))
    (B : Set (Fin d → ℝ)) (q : (Fin d → ℝ) → Affine N) (x : Fin d → ℝ) : Prop :=
  ∃ c : NashBoundaryChart (m := m) U V B q, c.GoodAt x ∧
    ‖fderiv ℝ c.normal.graph (c.normal.parameters x)‖ < 1/2

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SliceGraphDerivativeBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open scoped Classical

noncomputable def normalParameterInjection (r k : ℕ) :
    (Fin k → ℝ) →L[ℝ] (Fin ((r+r)+k) → ℝ) :=
  LinearMap.toContinuousLinearMap
  { toFun := fun x j => Sum.elim (fun _ => 0) x (finSumFinEquiv.symm j)
    map_add' := by
      intro x y
      funext j
      cases h : finSumFinEquiv.symm j <;> simp [h]
    map_smul' := by
      intro a x
      funext j
      cases h : finSumFinEquiv.symm j <;> simp [h] }

namespace NashBoundaryChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N}

noncomputable def normalInjection (c : NashBoundaryChart (m := m) U V B q) :
    Affine c.normal.normalDim →L[ℂ] Affine m :=
  c.normal.coordinates.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℂ (Affine c.normal.tangentDim) (Affine c.normal.normalDim))

noncomputable def sliceLift (c : NashBoundaryChart (m := m) U V B q)
    (s : Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ)
    (w : Affine c.normal.normalDim) : Affine m :=
  c.normal.realCoordinates.symm (s,c.normal.graph s)+c.normalInjection w

noncomputable def sliceParameter (c : NashBoundaryChart (m := m) U V B q)
    (s : Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ)
    (x : Fin c.normal.normalDim → ℝ) : Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ :=
  s+normalParameterInjection c.normal.tangentDim c.normal.normalDim x

noncomputable def sliceGraph (c : NashBoundaryChart (m := m) U V B q)
    (s : Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ)
    (x : Fin c.normal.normalDim → ℝ) : Fin c.normal.normalDim → ℝ :=
  c.normal.graph (c.sliceParameter s x)-c.normal.graph s

noncomputable def sliceDomain (c : NashBoundaryChart (m := m) U V B q)
    (s : Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ) : Set (Affine c.normal.normalDim) :=
  {w | c.normal.realCoordinates (c.sliceLift s w) ∈ c.chart.coordinateDomain U c.normal.realCoordinates}

end NashBoundaryChart
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_NoncollapsedSupportedBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric MeasureTheory
open scoped Classical

def NoncollapsedGoodNashBoundary {d N : ℕ} (m : ℕ)
    (U V : Set (Affine N)) (B : Set (Fin d → ℝ))
    (q : (Fin d → ℝ) → Affine N) (x : Fin d → ℝ) : Prop :=
  ∃ c : NashBoundaryChart (m := m) U V B q,
    c.GoodAt x ∧ ‖fderiv ℝ c.normal.graph (c.normal.parameters x)‖ < 1/2 ∧
      ∀ f : (Fin c.normal.normalDim → ℝ) → ℝ,
        (∀ y, Tendsto (fun p : (Fin (c.normal.tangentDim+c.normal.tangentDim+c.normal.normalDim) → ℝ) × ℝ =>
            offsetDistance c.family p.1 p.2 y)
          (𝓝[{p | 0 < p.2}] (c.normal.parameters x,0)) (𝓝 (f y))) → {y | f y = 0} ≠ univ

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_NormalizedLocalInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology
open scoped Classical

noncomputable def ambientAction {n : ℕ} (U : Set (Affine n)) (Γ : Type*)
    [Group Γ] [MulAction Γ U] (γ : Γ) (y : Affine n) : Affine n :=
  if hy : y ∈ U then (γ • (⟨y,hy⟩ : U)).val else y

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_QuadraticModelResidualFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.Hermitian
open Set Complex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] {k : ℕ}

def normalTranslation (a : Fin k → ℝ) : (E × (Fin k → ℂ)) ≃ₜ (E × (Fin k → ℂ)) :=
  Homeomorph.addRight (0,fun i => (a i : ℂ))

def axisNormalization (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (p : E × (Fin k → ℂ)) : (E × (Fin k → ℂ)) ≃ₜ (E × (Fin k → ℂ)) :=
  (heisenbergHomeomorph B (-p.1)).trans
    (normalTranslation (fun i => -(p.2 i).re))

end Release061.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_RawQuadraticModelNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open scoped Classical

def Biholomorph.ofEntireHomeomorph {n m : ℕ} (e : Affine n ≃ₜ Affine m)
    (he : ∀ x, AnalyticAt ℂ e x) (hei : ∀ x, AnalyticAt ℂ e.symm x)
    (S : Set (Affine n)) : Biholomorph S (e '' S) :=
  Biholomorph.ofOpenPartialHomeomorph e.toOpenPartialHomeomorph
    (fun x _ => he x) (fun x _ => hei x) S (subset_univ _)

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SupportCayleyOpenImage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Complex Set Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {k : ℕ}

def supportCayley (x : E × (Fin (k+1) → ℂ)) : E × (Fin (k+1) → ℂ) :=
  ((x.2 0+I)⁻¹ • x.1,fun i => normalCayley (x.2 i))

def supportUncayley (x : E × (Fin (k+1) → ℂ)) : E × (Fin (k+1) → ℂ) :=
  ((normalUncayley (x.2 0)+I) • x.1,fun i => normalUncayley (x.2 i))

end Release061

end

end OAI
end


