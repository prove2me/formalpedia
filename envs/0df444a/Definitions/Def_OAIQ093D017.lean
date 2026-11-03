-- Prove2me | Definitions.Def_OAIQ093D017
-- name    : OAIQ093D017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-02T18:15:03.988638+00:00
-- url     : https://prove2.me/theorems/52782b5d-a03d-412f-859f-25d3fc7652d6
-- title:
--   Definitions bundle OAIQ093D017 of the split of OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 46 declarations of OpenAI's Lean: 19 definitions, 1 inductive type or structure, 5 instances and 21 theorems. The definitions and types are `OAI.PolycyclicRecognition.CartanWordModel.NeighborSamplingRow.withAffinity`, `OAI.PolycyclicRecognition.CartanWordModel.residualGroupAutomorphism`, `OAI.PolycyclicRecognition.NilpotentLatticeCoordinates`, `OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.of_equiv`, `OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.of_subsingleton`, `OAI.PolycyclicRecognition.abelianRealLattice`, `OAI.PolycyclicRecognition.abelianRealLatticeEquiv`, `OAI.PolycyclicRecognition.abelianRealLatticeMap`, `OAI.PolycyclicRecognition.cartanIdealResidualAutomorphism`, `OAI.PolycyclicRecognition.cartanIdealResidualDerivation`, `OAI.PolycyclicRecognition.chosenIntegralKernelCover`, `OAI.PolycyclicRecognition.chosenIntegralResolution`, `OAI.PolycyclicRecognition.chosenIntegralResolutionAugmentation`, `OAI.PolycyclicRecognition.chosenIntegralResolutionComplex`, `OAI.PolycyclicRecognition.chosenIntegralResolutionSuccessorIso`, `OAI.PolycyclicRecognition.chosenIntegralStep`, `OAI.PolycyclicRecognition.chosenIntegralSuccessor`, `OAI.PolycyclicRecognition.inducedExhaustionColimit`, `OAI.PolycyclicRecognition.realShadowCartanHom`, `OAI.PolycyclicRecognition.shadowCartanParameter`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `PolycyclicRecognition_Algebra_AbelianRealSpace`, `PolycyclicRecognition_Analysis_NilpotentHaarAutomorphisms`, `PolycyclicRecognition_Finiteness_ChosenIntegralResolution`, `PolycyclicRecognition_Finiteness_InductionExhaustionVanishing`, `PolycyclicRecognition_Geometry_CartanGroupConjugation`, `PolycyclicRecognition_Geometry_CartanNeighborSamplingRow`, `PolycyclicRecognition_Geometry_CartanResidualDerivation`, `PolycyclicRecognition_Geometry_CartanResidualExponential`, `PolycyclicRecognition_Geometry_FactorRotationCharacter`, `PolycyclicRecognition_Geometry_RealRotationDerivation`, `PolycyclicRecognition_Geometry_RealShadowCartan`, `PolycyclicRecognition_Geometry_ShadowExponentialCoordinates`, `PolycyclicRecognition_Geometry_SmoothIndividualRotations`, `PolycyclicRecognition_Lattices_NilpotentLatticeCoordinates`.
--
--   **Imports.** It imports the published bundle `Def_PolycyclicRecognition`; the bundles `OAIQ093D012`, `OAIQ093D026`, `OAIQ093D014` and `OAIQ093D015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ093D020` and `OAIQ093D027`; the statements `OAI_PolycyclicRecognition_CartanWordModel_exists_basepoint_geometry_of_factor_bounds`, `OAI_PolycyclicRecognition_CartanWordModel_exists_sequence_path_quotient_restriction` and `OAI_PolycyclicRecognition_CartanWordModel_exists_small_metric_cartan_factor_bound`; the proofs of `OAI_PolycyclicRecognition_CartanWordModel_exists_basepoint_geometry_of_factor_bounds`, `OAI_PolycyclicRecognition_CartanWordModel_exists_metric_basepoint_comparison`, `OAI_PolycyclicRecognition_CartanWordModel_exists_sequence_path_quotient_restriction`, `OAI_PolycyclicRecognition_CartanWordModel_exists_small_metric_cartan_factor_bound`, `OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_published_chain_concentration`, `OAI_PolycyclicRecognition_cartan_cocycle_compact_words`, `OAI.PolycyclicRecognition.dekimpeLatticeRealizationInput`, `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition`, `OAI.PolycyclicRecognition.polycyclic_of_nilpotent_by_abelian_duality` and `OAI.PolycyclicRecognition.virtuallyPolycyclic_of_coarse_rational_bounds`.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D012
import Definitions.Def_OAIQ093D026
import Definitions.Def_OAIQ093D014
import Definitions.Def_OAIQ093D015

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AbelianRealSpace
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.derivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.groupAutomorphism_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The real abelian coordinate space and its explicit integer lattice -/

noncomputable section
namespace PolycyclicRecognition

instance abelianRealNormedLie (n : ℕ) : RealNormedLieAlgebra (AbelianRealSpace n) := by
  let : NormedAddCommGroup (AbelianRealSpace n) :=
    inferInstanceAs (NormedAddCommGroup (Fin n → ℝ))
  let : NormedSpace ℝ (AbelianRealSpace n) :=
    inferInstanceAs (NormedSpace ℝ (Fin n → ℝ))
  let lr : LieRing (AbelianRealSpace n) :=
    { toAddCommGroup := inferInstanceAs (AddCommGroup (Fin n → ℝ))
      bracket := fun _ _ => 0
      add_lie := by intros; simp
      lie_add := by intros; simp
      lie_self := by intro; rfl
      leibniz_lie := by intros; simp }
  let : LieRing (AbelianRealSpace n) := lr
  let la : LieAlgebra ℝ (AbelianRealSpace n) :=
    { toModule := inferInstanceAs (Module ℝ (Fin n → ℝ))
      lie_smul := by
        intro r x y
        change (0 : AbelianRealSpace n) = r • (0 : AbelianRealSpace n)
        exact (smul_zero r).symm }
  exact
    { (inferInstance : NormedAddCommGroup (AbelianRealSpace n)), lr,
      (inferInstance : NormedSpace ℝ (AbelianRealSpace n)), la with }

instance abelianRealFiniteDimensional (n : ℕ) : FiniteDimensional ℝ (AbelianRealSpace n) :=
  inferInstanceAs (FiniteDimensional ℝ (Fin n → ℝ))

instance abelianRealLieAbelian (n : ℕ) : IsLieAbelian (AbelianRealSpace n) where
  trivial _ _ := rfl

instance abelianRealCoordinates (n : ℕ) : PolynomialExponentialCoordinates (AbelianRealSpace n) :=
  abelianPolynomialCoordinates

instance abelianRealCommGroup (n : ℕ) : CommGroup (AbelianRealSpace n) :=
  inferInstanceAs (CommGroup (Multiplicative (Fin n → ℝ)))

def abelianRealLattice (n : ℕ) : Subgroup (AbelianRealSpace n) :=
  (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))).toAddSubgroup.toSubgroup

theorem abelianRealLattice_uniform (n : ℕ) : IsUniformLattice (abelianRealLattice n) :=
  standardVectorLattice_uniform n

def abelianRealLatticeMap (n : ℕ) : Multiplicative (Fin n → ℤ) →* abelianRealLattice n where
  toFun x := ⟨integerVectorMap n x.toAdd, integerVectorMap_mem n x.toAdd⟩
  map_one' := by apply Subtype.ext; exact (integerVectorMap n).map_zero
  map_mul' x y := by apply Subtype.ext; exact (integerVectorMap n).map_add x.toAdd y.toAdd

def abelianRealLatticeEquiv (n : ℕ) : Multiplicative (Fin n → ℤ) ≃* abelianRealLattice n :=
  MulEquiv.ofBijective (abelianRealLatticeMap n) ⟨
    fun x y h => Multiplicative.ext (integerVectorMap_injective n (congrArg Subtype.val h)),
    fun y => by
      obtain ⟨x, hx⟩ := exists_integerVectorMap_of_mem n y.val y.property
      exact ⟨Multiplicative.ofAdd x, Subtype.ext hx⟩⟩

@[simp] theorem abelianRealLatticeEquiv_apply (n : ℕ) (x : Multiplicative (Fin n → ℤ)) :
    (abelianRealLatticeEquiv n x : AbelianRealSpace n) = integerVectorMap n x.toAdd := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_NilpotentHaarAutomorphisms
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Haar preservation for the integrated automorphisms

A determinant-one Lie automorphism preserves Lebesgue measure in exponential
coordinates. The global chart transfers this identity to actual group Haar
measure; no invariant-measure premise for the automorphism is assumed.
-/

noncomputable section

namespace PolycyclicRecognition

open Module MeasureTheory
open scoped Manifold

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hbij : Function.Bijective Exp)
  (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
  {n : ℕ} (b : Basis (Fin n) ℝ L)

omit [FiniteDimensional ℝ L] [T2Space G] in
include hchart in
/-- The same explicit coordinate measure has the exact weighted-box volume.
Thus its automorphism invariance and its box normalization are compatible. -/
theorem exponentialCoordinate_weighted_box_measure
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    {I : Type*} (X : I → L) (S : Finset (FreeMagma I))
    (cost : S → ℝ) (β : WordBasisSelections X S) (r R : ℝ) (hR : 0 ≤ R) :
    (Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)
      (exponentialCoordinateBox (Exp ∘ e)
        (exponentialRescaleBasis (WordBasisSelections.basis X S β)
          (fun i => cost (β.val i)) r) R) =
      ENNReal.ofReal |(columnBasisMatrix (wordListCoordinates X S b₀) β.val).det| *
        ENNReal.ofReal (Real.exp (r * columnBasisWeight cost β.val)) *
          ENNReal.ofReal (2 * R) ^ finrank ℝ L := by
  let f := (Exp ∘ e) ∘ b₀.equivFun.symm
  let c : (Fin (finrank ℝ L) → ℝ) ≃ₜ G :=
    (b₀.equivFun.symm.trans e.toLinearEquiv).toContinuousLinearEquiv.toHomeomorph.trans chart
  have hf : f = c := by
    funext t
    exact (hchart _).symm
  have hm : MeasurableEmbedding f := by rw [hf]; exact c.measurableEmbedding
  rw [exponentialCoordinateBox_eq_weighted_image X S b₀ β cost r R hR (Exp ∘ e)]
  change (Measure.map f volume) (f '' _) = _
  rw [hm.map_apply, Set.preimage_image_eq _ hm.injective]
  exact volume_weightedCoordinateBox _ _ _ _ _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ChosenIntegralResolution
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.booleanPartitionStage_projective _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.horseshoeCover_projective _root_.OAI.PolycyclicRecognition.integralRepresentationSum_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalizedSyzygy_projective _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalizedGroupIdentityClass_comparison _root_.OAI.PolycyclicRecognition.rationalCoefficientInclusion_apply _root_.OAI.PolycyclicRecognition.resolutionStableSyzygyTransition_class _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A resolution with finitely generated covers whenever available

The initial free term is the regular module. Every subsequent term covers the
kernel of the preceding differential. The chosen presentation retains finite
generation whenever that kernel is finitely generated.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
variable {G : Type} [Group G]

def chosenIntegralKernelCover {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    ProjectivePresentation (kernel f) := chosenIntegralPresentation (kernel f)

def chosenIntegralStep {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    (chosenIntegralKernelCover f).p ⟶ A :=
  (chosenIntegralKernelCover f).f ≫ kernel.ι f

@[simp] theorem chosenIntegralStep_comp {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    chosenIntegralStep f ≫ f = 0 := by
  simp [chosenIntegralStep]

theorem chosenIntegralStep_exact {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    (ShortComplex.mk (chosenIntegralStep f) f (chosenIntegralStep_comp f)).Exact := by
  let S := ShortComplex.mk (chosenIntegralStep f) f (chosenIntegralStep_comp f)
  let T := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  let φ : S ⟶ T :=
    { τ₁ := (chosenIntegralKernelCover f).f
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [S, T, chosenIntegralStep]
      comm₂₃ := by simp [S, T] }
  have : Epi φ.τ₁ := (chosenIntegralKernelCover f).epi
  have : IsIso φ.τ₂ := by change IsIso (𝟙 _); infer_instance
  have : Mono φ.τ₃ := by change Mono (𝟙 _); infer_instance
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr
    (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel f))

def chosenIntegralSuccessor {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    Σ' (C : Rep.{0} ℤ G) (d : C ⟶ A), d ≫ f = 0 :=
  ⟨(chosenIntegralKernelCover f).p, chosenIntegralStep f, chosenIntegralStep_comp f⟩

def chosenIntegralResolutionComplex (G : Type) [Group G] : ChainComplex (Rep ℤ G) ℕ :=
  ChainComplex.mk' (Rep.leftRegular ℤ G)
    (chosenIntegralKernelCover (integralFreeAugmentation (G := G))).p
    (chosenIntegralStep (integralFreeAugmentation (G := G))) chosenIntegralSuccessor

def chosenIntegralResolutionSuccessorIso (n : ℕ) :
    (chosenIntegralResolutionComplex G).X (n + 2) ≅
      (chosenIntegralKernelCover ((chosenIntegralResolutionComplex G).d (n + 1) n)).p :=
  ChainComplex.mk'XIso _ _ _ _ n

theorem chosenIntegralResolution_projective (n : ℕ) :
    Projective ((chosenIntegralResolutionComplex G).X n) := by
  rcases n with _ | (_ | n)
  · change Projective (Rep.leftRegular ℤ G)
    infer_instance
  · exact (chosenIntegralKernelCover (integralFreeAugmentation (G := G))).projective
  · exact Projective.of_iso (chosenIntegralResolutionSuccessorIso n).symm
      (chosenIntegralKernelCover ((chosenIntegralResolutionComplex G).d (n + 1) n)).projective

theorem chosenIntegralResolution_d_succ (n : ℕ) :
    (chosenIntegralResolutionComplex G).d (n + 2) (n + 1) =
      (chosenIntegralResolutionSuccessorIso n).hom ≫
        chosenIntegralStep ((chosenIntegralResolutionComplex G).d (n + 1) n) :=
  ChainComplex.mk'_d _ _ _ _ n

theorem chosenIntegralResolution_exact (n : ℕ) :
    (chosenIntegralResolutionComplex G).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  apply (rep_shortComplex_exact_iff _).mpr
  intro x hx
  obtain ⟨y, hy⟩ := (rep_shortComplex_exact_iff _).mp
    (chosenIntegralStep_exact ((chosenIntegralResolutionComplex G).d (n + 1) n)) x hx
  let e := chosenIntegralResolutionSuccessorIso (G := G) n
  refine ⟨e.inv.hom y, ?_⟩
  change ((chosenIntegralResolutionComplex G).d (n + 2) (n + 1)).hom (e.inv.hom y) = x
  rw [chosenIntegralResolution_d_succ]
  change (chosenIntegralStep ((chosenIntegralResolutionComplex G).d (n + 1) n)).hom
    (e.hom.hom (e.inv.hom y)) = x
  have he : e.hom.hom (e.inv.hom y) = y := congrArg (fun f => f.hom y) e.inv_hom_id
  rwa [he]

def chosenIntegralResolutionAugmentation :
    chosenIntegralResolutionComplex G ⟶ (ChainComplex.single₀ (Rep ℤ G)).obj (trivialIntegral G) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨integralFreeAugmentation, by
      change chosenIntegralStep (integralFreeAugmentation (G := G)) ≫
        integralFreeAugmentation = 0
      exact chosenIntegralStep_comp _⟩

theorem chosenIntegralResolutionAugmentation_quasiIso :
    QuasiIso (chosenIntegralResolutionAugmentation (G := G)) where
  quasiIsoAt i := by
    cases i with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,
        ShortComplex.quasiIso_iff_of_zeros' _ (by rfl) rfl rfl]
      constructor
      · exact chosenIntegralStep_exact (integralFreeAugmentation (G := G))
      · rw [Rep.epi_iff_surjective]
        change Function.Surjective (integralFreeAugmentation (G := G)).hom
        intro z
        refine ⟨MonoidAlgebra.single 1 z, ?_⟩
        exact (Rep.leftRegularHom_hom_single 1 1 z).trans (by simp)
    | succ n =>
      rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..)]
      exact chosenIntegralResolution_exact n

def chosenIntegralResolution (G : Type) [Group G] : ProjectiveResolution (trivialIntegral G) where
  complex := chosenIntegralResolutionComplex G
  projective := chosenIntegralResolution_projective
  π := chosenIntegralResolutionAugmentation
  quasiIso := chosenIntegralResolutionAugmentation_quasiIso

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_InductionExhaustionVanishing
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.telescopeAugmentation_epi _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complete vanishing for induction along a subgroup exhaustion

The finite stages may have arbitrarily large projective dimensions. The
ambient group's FP-infinity hypothesis supplies continuity of its completed
cohomology for the actual induced-coefficient colimit.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

variable (A : Rep.{0} ℤ G) (H : ℕ → Subgroup G) (K : Subgroup G)
variable (hmono : Monotone H) (hHK : ∀ n, H n ≤ K)
variable (hcover : ∀ g ∈ K, ∃ n, g ∈ H n)

def inducedExhaustionColimit :
    (inducedExhaustionDiagram A H hmono).ColimitCocone
      (Rep.ind K.subtype (Rep.res K.subtype A)) :=
  (ascendingQuotientColimit (inductionAmbient A)
    (fun n => subgroupCoinvariantRelations (inductionDiagonalAction A) (H n))
    (fun n => inductionRelations_invariant A (H n))
    (fun _ _ h => subgroupCoinvariantRelations_mono _ (hmono h))
    (subgroupCoinvariantRelations (inductionDiagonalAction A) K)
    (inductionRelations_invariant A K)
    (fun n => subgroupCoinvariantRelations_mono _ (hHK n))
    (fun _ hx => subgroupCoinvariantRelations_exhaustion _ H K hmono hcover hx)).transportIso
      (inductionAmbientQuotientIso A K)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanResidualDerivation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual nilpotent residual derivation

Subtracting the scalar weight derivation from the Cartan adjoint action gives
one globally nilpotent derivation, not merely separate nilpotent operators on
its root spaces. Its finite exponential is therefore an actual Lie automorphism.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped DirectSum

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
/-- The scalar derivation preserves the actual nilpotent Cartan ideal. -/
theorem cartanScalarOperator_mem_ideal (h : H) {x : L} (hx : x ∈ cartanRootIdeal H) :
    cartanScalarOperator T H h x ∈ cartanRootIdeal H := by
  have heq := cartanRootSubalgebra_eq_ideal H T
  have hx' : x ∈ cartanRootSubalgebra H := by
    change x ∈ (cartanRootSubalgebra H).toSubmodule
    rwa [heq]
  suffices cartanScalarOperator T H h x ∈ cartanRootSubalgebra H by
    change cartanScalarOperator T H h x ∈ (cartanRootIdeal H).toSubmodule
    rwa [← heq]
  clear hx
  change x ∈ LieSubalgebra.lieSpan ℝ L
    {v | ∃ χ : Weight ℝ H L, χ.IsNonZero ∧ v ∈ rootSpace H χ} at hx'
  induction hx' using LieSubalgebra.lieSpan_induction with
  | mem x hx =>
    obtain ⟨χ, hχ, hx⟩ := hx
    rw [cartanScalarOperator_apply_root T H h χ hx]
    exact (cartanRootSubalgebra H).smul_mem _ (LieSubalgebra.subset_lieSpan ⟨χ, hχ, hx⟩)
  | zero => simp only [map_zero]; exact (cartanRootSubalgebra H).zero_mem
  | add x y _ _ hx hy =>
    rw [map_add]
    exact (cartanRootSubalgebra H).add_mem hx hy
  | smul a x _ hx =>
    rw [map_smul]
    exact (cartanRootSubalgebra H).smul_mem a hx
  | lie x y hx hy ihx ihy =>
    rw [cartanScalarOperator_leibniz]
    exact (cartanRootSubalgebra H).add_mem
      ((cartanRootSubalgebra H).lie_mem hx ihy) ((cartanRootSubalgebra H).lie_mem ihx hy)

set_option maxHeartbeats 1000000 in
/-- Consequently the full residual derivation preserves the ideal. -/
theorem cartanResidualDerivation_mem_ideal (h : H) {x : L} (hx : x ∈ cartanRootIdeal H) :
    cartanResidualDerivation T H h x ∈ cartanRootIdeal H := by
  change -⁅x, (h : L)⁆ - cartanScalarOperator T H h x ∈ cartanRootIdeal H
  rw [lie_skew (h : L) x]
  exact (cartanRootIdeal H).sub_mem ((cartanRootIdeal H).lie_mem hx)
    (cartanScalarOperator_mem_ideal T H h hx)

set_option maxHeartbeats 1000000 in
/-- Restrict the residual derivation before taking its finite exponential. -/
def cartanIdealResidualDerivation (h : H) :
    LieDerivation ℝ (cartanRootIdeal H) (cartanRootIdeal H) where
  toFun x := ⟨cartanResidualDerivation T H h x,
    cartanResidualDerivation_mem_ideal T H h x.property⟩
  map_add' x y := by apply Subtype.ext; exact map_add (cartanResidualDerivation T H h) (x : L) (y : L)
  map_smul' a x := by apply Subtype.ext; exact map_smul (cartanResidualDerivation T H h) a (x : L)
  leibniz' x y := by
    apply Subtype.ext
    exact (cartanResidualDerivation T H h).leibniz' (x : L) (y : L)

set_option maxHeartbeats 1000000 in
theorem cartanIdealResidualDerivation_pow_coe (h : H) (k : ℕ) (x : cartanRootIdeal H) :
    (((cartanIdealResidualDerivation T H h).toLinearMap ^ k) x : L) =
      ((cartanResidualDerivation T H h).toLinearMap ^ k) (x : L) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
    rfl

set_option maxHeartbeats 1000000 in
theorem cartanIdealResidualDerivation_pow_eq_zero (h : H) :
    (cartanIdealResidualDerivation T H h).toLinearMap ^ finrank ℝ L = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (((cartanIdealResidualDerivation T H h).toLinearMap ^ finrank ℝ L) x : L) = 0
  rw [cartanIdealResidualDerivation_pow_coe, cartanResidualDerivation_pow_eq_zero]
  rfl

set_option maxHeartbeats 1000000 in
/-- The residual automorphism of the nilpotent factor used in box estimates. -/
def cartanIdealResidualAutomorphism (h : H) : cartanRootIdeal H ≃ₗ⁅ℝ⁆ cartanRootIdeal H := by
  letI : Module ℚ (cartanRootIdeal H) := Module.compHom _ (algebraMap ℚ ℝ)
  letI : LieAlgebra ℚ (cartanRootIdeal H) :=
    { lie_smul := fun t x y => lie_smul (algebraMap ℚ ℝ t) x y }
  exact (cartanIdealResidualDerivation T H h).exp
    ⟨finrank ℝ L, cartanIdealResidualDerivation_pow_eq_zero T H h⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanResidualExponential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.stationaryL2SMulComm _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial formulas for the residual Cartan automorphism

The global residual Lie automorphism agrees with the analytic exponential of
the nilpotent residual operator on every root. This connects its algebraic
construction to the root-space estimates.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
/-- The residual automorphism is an explicit finite real Lie polynomial. -/
theorem cartanIdealResidualAutomorphism_apply (h : H) (x : cartanRootIdeal H) :
    cartanIdealResidualAutomorphism T H h x =
      ∑ k ∈ Finset.range (finrank ℝ L), ((k.factorial : ℝ)⁻¹) •
        ((cartanIdealResidualDerivation T H h).toLinearMap ^ k) x := by
  let : Module ℚ (cartanRootIdeal H) := Module.compHom _ (algebraMap ℚ ℝ)
  change IsNilpotent.exp (cartanIdealResidualDerivation T H h).toLinearMap x = _
  rw [IsNilpotent.exp_eq_sum (cartanIdealResidualDerivation_pow_eq_zero T H h)]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Rat.cast_smul_eq_qsmul ℝ]
  simp only [Rat.cast_inv, Rat.cast_natCast]

set_option maxHeartbeats 1000000 in
/-- Every residual power preserves its actual generalized root space. -/
theorem cartanIdealResidualDerivation_pow_root_mem (h : H) (χ : Weight ℝ H L)
    (k : ℕ) (x : cartanRootIdeal H) (hx : (x : L) ∈ rootSpace H χ) :
    (((cartanIdealResidualDerivation T H h).toLinearMap ^ k) x : L) ∈ rootSpace H χ := by
  rw [cartanIdealResidualDerivation_pow_coe]
  induction k generalizing x with
  | zero => exact hx
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply]
    exact ih (cartanIdealResidualDerivation T H h x)
      (cartanResidualDerivation_root_mem T H h χ hx)

set_option maxHeartbeats 1000000 in
/-- The finite exponential preserves each root space. -/
theorem cartanIdealResidualAutomorphism_root_mem (h : H) (χ : Weight ℝ H L)
    (x : cartanRootIdeal H) (hx : (x : L) ∈ rootSpace H χ) :
    (cartanIdealResidualAutomorphism T H h x : L) ∈ rootSpace H χ := by
  rw [cartanIdealResidualAutomorphism_apply]
  change (cartanRootIdeal H).incl (∑ k ∈ Finset.range (finrank ℝ L),
    ((k.factorial : ℝ)⁻¹) • ((cartanIdealResidualDerivation T H h).toLinearMap ^ k) x) ∈ _
  rw [map_sum]
  simp only [map_smul]
  apply (rootSpace H χ).sum_mem
  intro k _
  exact (rootSpace H χ).smul_mem _
    (cartanIdealResidualDerivation_pow_root_mem T H h χ k x hx)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanGroupConjugation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Group-box bounds for Cartan actions

The finite Dynkin identity integrates the residual Lie automorphism. Its
polynomial box bound and exact weight dilation yield a shifted-box bound.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra
open scoped Manifold

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)
  (hbij : Function.Bijective Exp) (dynkin : NilpotentDynkinExpansionInput EN N)

set_option maxHeartbeats 1000000 in
/-- The actual group automorphism induced by the Cartan residual derivation. -/
def residualGroupAutomorphism (h : H) : N ≃* N :=
  integrateNilpotentLieEquiv eN Exp hbij dynkin hExp M.bound_zero
    (cartanIdealResidualAutomorphism T H h)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanNeighborSamplingRow
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original neighboring samples before their affine limit is identified -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier] [SecondCountableTopology F.N.carrier]
  [Fintype I] [DecidableEq I]
  (π : G →* Multiplicative W)
  (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
  (cell : Set W) (β : M.Bases)
  (X : I → H) {d : ℕ} (βD : WordBasisSelections X (boundedBracketWords d))
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (pivot : Fin M.letterCount → H) (c B δ : ℝ)
  (Profiles : Set C((Fin (finrank ℝ H) → ℝ), W))
  [MeasurableSpace Profiles] [BorelSpace Profiles] [BorelSpace (Profiles × Profiles)]
  {Λ : ℝ≥0}

variable (D : NeighborSamplingRow T M F hunimod eW π bN cell β X βD
  haarN chartN hchartN pivot B δ Profiles (Λ := Λ))

set_option maxHeartbeats 1000000 in
/-- Insert a proved common affine description into the exact original row.
This changes neither its weak law nor either sampled profile. -/
def NeighborSamplingRow.withAffinity
    (A : templateSymmetryGroup (M.supportIn T hunimod eW)) (b₁ b₂ : W)
    (haffine : ∀ z, eW (heightProjection T.character
      ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - c * δ) • w) '' interior cell →
      D.point.1.val z = A.val (eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₁ ∧
      D.point.2.val z = A.val (eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₂) :
    AffineNeighborRow T M F hunimod eW π bN cell β X βD
      haarN chartN hchartN pivot c B δ Profiles (Λ := Λ) where
  scale := D.scale
  grows := D.grows
  pair := D.pair
  center := D.center
  radius := D.radius
  radius_nonneg := D.radius_nonneg
  radius_subexponential := D.radius_subexponential
  base := D.base
  step := D.step
  basis := fun _ => β
  base_mem := D.base_mem
  step_mem := D.step_mem
  mode := D.mode
  time := D.time
  time_bound := D.time_bound
  root_step := D.root_step
  profile := fun n q => (D.profile n q, D.profile n (q * D.step n))
  measurable_profile := fun n => (D.measurable_profile n).prodMk
    ((D.measurable_profile n).comp (measurable_id.mul_const _))
  actual := by
    intro n q hq z
    have hlog : max (Real.log (D.scale n)) 0 = Real.log (D.scale n) :=
      max_eq_left (Real.log_nonneg (D.scale_ge_one n))
    have hc (b : Basis (Fin (finrank ℝ H)) ℝ H) :
        F.profileChart b = fun z => Exp (b.equivFun.symm z) := by
      funext z
      exact F.compatibleD _
    constructor
    · simpa only [hlog, hc] using D.actual n q (Or.inl hq) z
    · have hqs : q * D.step n ∈ (fun v => v * D.base n * D.step n) ''
          M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell β (D.scale n) 1 := by
        rcases hq with ⟨v, hv, rfl⟩
        exact ⟨v, hv, rfl⟩
      simpa only [hlog, hc] using D.actual n (q * D.step n) (Or.inr hqs) z
  law := D.law
  converges := D.converges
  point := D.point
  supported := D.supported
  label₁ := A
  label₂ := A
  offset₁ := b₁
  offset₂ := b₂
  affine₁ := fun z hz => (haffine z hz).1
  affine₂ := fun z hz => (haffine z hz).2

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FactorRotationCharacter
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The invariant compact character for the actual Cartan factors -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp)

/- The actual quotient character followed by its compact rotational part. -/

theorem continuous_rotationCharacter : Continuous F.rotationCharacter :=
  T.continuous_liftRotationCharacter H F.weightCharacter F.continuousWeightCharacter

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RealRotationDerivation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.realRotationTorus_compactSpace _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Infinitesimal Cartan rotations on the real Lie algebra -/

noncomputable section
namespace PolycyclicRecognition
open LieAlgebra LieModule Module
open scoped TensorProduct

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

theorem realImaginaryOperator_cartan (h k : H) : realImaginaryOperator L H h k = 0 := by
  apply complexificationLieHom_injective L
  change (1 : ℂ) ⊗ₜ[ℝ] _ = (1 : ℂ) ⊗ₜ[ℝ] (0 : L)
  rw [realImaginaryOperator_complexify,TensorProduct.tmul_zero]
  exact ComplexCartan.imaginaryOperator_cartan (complexifiedSubalgebra L H)
    (realCartanInComplex L H h) (realCartanInComplex L H k)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RealShadowCartan
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The unchanged Cartan factor and its corrected adjoint action -/

noncomputable section
namespace PolycyclicRecognition
open LieAlgebra Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {a : ℕ} (T : ComplexTriangularAdjoint L a)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
/-- Every imaginary Cartan derivation annihilates the whole Cartan algebra. -/
theorem weightImaginaryAction_apply_cartan (x : L) (h : H) :
    T.weightImaginaryAction H x h = 0 :=
  realImaginaryOperator_cartan L H _ h

set_option maxHeartbeats 1000000 in
/-- The Cartan factor retains its original Lie bracket. -/
def realShadowCartanHom : H →ₗ⁅ℝ⁆ CartanRealShadow T H where
  toLinearMap := (cartanRealShadowEquiv T H).toLinearMap.comp H.subtype
  map_lie' {x y} := by
    apply (cartanRealShadowEquiv T H).symm.injective
    change ⁅(x : L),(y : L)⁆ =
      (cartanRealShadowEquiv T H).symm
        ⁅cartanRealShadowEquiv T H x,cartanRealShadowEquiv T H y⁆
    rw [cartanRealShadow_bracket, weightImaginaryAction_apply_cartan,
      weightImaginaryAction_apply_cartan, sub_zero, add_zero]

set_option maxHeartbeats 1000000 in
@[simp] theorem realShadowCartanHom_apply (h : H) :
    realShadowCartanHom T H h = cartanRealShadowEquiv T H h := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ShadowExponentialCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear coordinates for the two real-shadow exponential factors -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L A : Type} [LieRing L] [LieAlgebra ℝ L]
  [FiniteDimensional ℝ L]
  [NormedRing A] [NormedAlgebra ℝ A]
  {a : ℕ} (T : ComplexTriangularAdjoint L a)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]
  (j : CartanRealShadow T H →ₗ⁅ℝ⁆ A)

def shadowCartanParameter : L →ₗ[ℝ] A := (shadowRepresentationParameter T H j).comp
  (H.subtype.comp (T.cartanComponent H))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SmoothIndividualRotations
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Differentiating the individual compact rotations -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
  (β : realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H →* MulAut G)
  (hβ : ∀ z (x : T.kernelIdeal) d,
    β z (F.inclusionN (F.ExpN (F.N.equiv x)) * F.inclusionD d) =
      F.inclusionN (F.ExpN (F.N.equiv (T.nilradicalRotation H z x))) * F.inclusionD d)

include hβ in
theorem rotation_fixes_cartan_factor
    (z : realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H) (d : F.D.carrier) :
    β z (F.inclusionD d) = F.inclusionD d := by
  have hh := hβ z 0 d
  simpa only [map_zero,F.isExpN.map_zero,map_one,one_mul] using hh

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_NilpotentLatticeCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ordered polynomial coordinates for a nilpotent lattice

This record retains the integer parameter alongside the real Lie model.
It is the induction data, not an additional realization hypothesis.
-/

noncomputable section
namespace PolycyclicRecognition
open Module

structure NilpotentLatticeCoordinates (H : Type) [Group H] where
  carrier : Type
  [realNormed : RealNormedLieAlgebra carrier]
  [finiteDimensional : FiniteDimensional ℝ carrier]
  [lieNilpotent : LieRing.IsNilpotent carrier]
  [coordinates : PolynomialExponentialCoordinates carrier]
  [solvable : Group.IsSolvable carrier]
  dimension : ℕ
  basis : Basis (Fin dimension) ℝ carrier
  parameter : carrier ≃ carrier
  polynomial : IsPolynomialInBasis basis basis parameter
  polynomial_symm : IsPolynomialInBasis basis basis parameter.symm
  lattice : Subgroup carrier
  uniform : IsUniformLattice lattice
  equiv : H ≃* lattice
  generators : Fin dimension → H
  word_surjective : Function.Surjective (orderedWord generators)
  integer_parameter : ∀ z : Fin dimension → ℤ,
    parameter (basis.equivFun.symm (fun i => (z i : ℝ))) =
      (equiv (orderedWord generators z) : carrier)

attribute [instance] NilpotentLatticeCoordinates.realNormed
  NilpotentLatticeCoordinates.finiteDimensional NilpotentLatticeCoordinates.lieNilpotent
  NilpotentLatticeCoordinates.coordinates NilpotentLatticeCoordinates.solvable

namespace NilpotentLatticeCoordinates
variable {H K : Type} [Group H] [Group K]

def of_equiv (C : NilpotentLatticeCoordinates H) (e : H ≃* K) :
    NilpotentLatticeCoordinates K where
  carrier := C.carrier
  dimension := C.dimension
  basis := C.basis
  parameter := C.parameter
  polynomial := C.polynomial
  polynomial_symm := C.polynomial_symm
  lattice := C.lattice
  uniform := C.uniform
  equiv := e.symm.trans C.equiv
  generators := fun i => e (C.generators i)
  word_surjective := by
    intro x
    obtain ⟨z, hz⟩ := C.word_surjective (e.symm x)
    refine ⟨z, ?_⟩
    exact (orderedWord_map e.toMonoidHom C.generators z).trans
      ((congrArg e hz).trans (e.apply_symm_apply x))
  integer_parameter := by
    intro z
    have hw : orderedWord (fun i => e (C.generators i)) z =
        e (orderedWord C.generators z) := orderedWord_map e.toMonoidHom C.generators z
    rw [C.integer_parameter, hw]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

def of_subsingleton [Subsingleton H] : NilpotentLatticeCoordinates H := by
  let L := AbelianRealSpace 0
  let : Subsingleton L := inferInstanceAs (Subsingleton (Fin 0 → ℝ))
  let : Unique H := uniqueOfSubsingleton 1
  let : Unique (abelianRealLattice 0) := uniqueOfSubsingleton 1
  let e : H ≃* abelianRealLattice 0 := MulEquiv.ofUnique
  refine {
    carrier := L
    dimension := 0
    basis := Pi.basisFun ℝ (Fin 0)
    parameter := Equiv.refl L
    polynomial := IsPolynomialInBasis.linear (LinearMap.id)
    polynomial_symm := IsPolynomialInBasis.linear (LinearMap.id)
    lattice := abelianRealLattice 0
    uniform := abelianRealLattice_uniform 0
    equiv := e
    generators := Fin.elim0
    word_surjective := ?_
    integer_parameter := ?_ }
  · intro x
    exact ⟨Fin.elim0, Subsingleton.elim _ _⟩
  · intro z
    exact Subsingleton.elim _ _

end NilpotentLatticeCoordinates
end PolycyclicRecognition

end

end OAI
end


