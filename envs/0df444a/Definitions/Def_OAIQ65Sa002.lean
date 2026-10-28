-- Prove2me | Definitions.Def_OAIQ65Sa002
-- name    : OAIQ65Sa002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T01:23:23.71236+00:00
-- url     : https://prove2.me/theorems/534c3e0c-193e-45e7-a08a-2e40b3942b92
-- title:
--   Definitions bundle OAIQ65Sa002 of the split of OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 535 declarations of OpenAI's Lean: 242 definitions, 6 inductive types or structures, 25 instances and 262 theorems. The definitions and types are `OAI.SimpleAmenable.CommutingFactors`, `OAI.SimpleAmenable.CommutingFactors.productEquiv`, `OAI.SimpleAmenable.CommutingFactors.productHom`, `OAI.SimpleAmenable.CommutingFactors.projectLeft`, `OAI.SimpleAmenable.ConfigurationChains.Admissible`, `OAI.SimpleAmenable.ConfigurationChains.Chain`, `OAI.SimpleAmenable.ConfigurationChains.Step`, `OAI.SimpleAmenable.ConfigurationChains.Step.base`, `OAI.SimpleAmenable.ConfigurationChains.Step.extend`, `OAI.SimpleAmenable.ConfigurationChains.Step.next`, `OAI.SimpleAmenable.ConfigurationChains.Step.nextGenerator`, `OAI.SimpleAmenable.ConfigurationChains.Step.nextVertex`, `OAI.SimpleAmenable.ConfigurationChains.Step.residual`, `OAI.SimpleAmenable.ConfigurationChains.bankBound`, `OAI.SimpleAmenable.ConfigurationChains.boundary`, `OAI.SimpleAmenable.ConfigurationChains.cone`, `OAI.SimpleAmenable.ConfigurationChains.degree`, `OAI.SimpleAmenable.ConfigurationChains.degreeBoundary`, `OAI.SimpleAmenable.ConfigurationChains.degreePush`, `OAI.SimpleAmenable.ConfigurationChains.faceSum`, `OAI.SimpleAmenable.ConfigurationChains.push`, `OAI.SimpleAmenable.ConfigurationChains.representation`, `OAI.SimpleAmenable.ConfigurationChains.simplexModuleEquiv`, `OAI.SimpleAmenable.ConfigurationChains.vertices`, `OAI.SimpleAmenable.ConsecutiveSubdivision`, `OAI.SimpleAmenable.ControlAlphabet`, `OAI.SimpleAmenable.FieldSignalData`, `OAI.SimpleAmenable.FieldSignalData.signal`, `OAI.SimpleAmenable.FiniteSupportReiter`, `OAI.SimpleAmenable.FiniteTestReiter`, `OAI.SimpleAmenable.FiveAlphabet`, `OAI.SimpleAmenable.FiveSubalphabet`, `OAI.SimpleAmenable.HasCentralLaw`, `OAI.SimpleAmenable.IntegralHomology.coefficientMap`, `OAI.SimpleAmenable.IntegralHomology.coefficients`, `OAI.SimpleAmenable.IntegralHomology.mapC2`, `OAI.SimpleAmenable.IntegralHomology.mapH2`, `OAI.SimpleAmenable.IntegralHomology.prism1`, `OAI.SimpleAmenable.IntegralHomology.prism2`, `OAI.SimpleAmenable.IntegralTransgression.Kernel` and 208 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `SimpleAmenable_Amenability_BarrierAlgorithm`, `SimpleAmenable_Amenability_BarrierCells`, `SimpleAmenable_Amenability_BarrierLineGeometry`, `SimpleAmenable_Amenability_BarrierSignalSystem`, `SimpleAmenable_Amenability_FiniteCoarea`, `SimpleAmenable_Amenability_SubgroupTestReiter`, `SimpleAmenable_Amenability_SuccessfulLawCovariance`, `SimpleAmenable_Arithmetic_DyadicArithmetic`, `SimpleAmenable_Arithmetic_LatticeCounting`, `SimpleAmenable_Arithmetic_PolygonArithmetic`, `SimpleAmenable_CentralCovers_AlphabetAlignedGeneration`, `SimpleAmenable_CentralCovers_AssignmentAtoms`, `SimpleAmenable_CentralCovers_AssignmentGeneration`, `SimpleAmenable_CentralCovers_AtomConjugation`, `SimpleAmenable_CentralCovers_BooleanCoordinateGeneration`, `SimpleAmenable_CentralCovers_CentralRangeReflection`, `SimpleAmenable_CentralCovers_ConditionalFamilyLaws`, `SimpleAmenable_CentralCovers_DirectFactors`, `SimpleAmenable_CentralCovers_FiniteCentralKernel`, `SimpleAmenable_CentralCovers_FormalCoordinates`, `SimpleAmenable_CentralCovers_FullAlphabetGeneration`, `SimpleAmenable_CentralCovers_FullSector`, `SimpleAmenable_CentralCovers_GrowthAxisUniform`, `SimpleAmenable_CentralCovers_InitialCoverSystem`, `SimpleAmenable_CentralCovers_LocalAtomComparison`, `SimpleAmenable_CentralCovers_PairControl`, `SimpleAmenable_CentralCovers_PairLawAssembly`, `SimpleAmenable_CentralCovers_PerfectCalculus`, `SimpleAmenable_CentralCovers_PerfectGeneratingFamilies`, `SimpleAmenable_CentralCovers_PrimitiveGeometricGeneration`, `SimpleAmenable_CentralCovers_PrimitiveTable`, `SimpleAmenable_CentralCovers_PrimitiveWords`, `SimpleAmenable_CentralCovers_SmallFamilyGlobal`, `SimpleAmenable_CentralCovers_SmallSectorGeneration`, `SimpleAmenable_CentralCovers_TemplateFormalRelators`, `SimpleAmenable_Configurations_DistinctSlotStars`, `SimpleAmenable_Configurations_EmptyStage`, `SimpleAmenable_Configurations_FiveTrackGeneration`, `SimpleAmenable_Configurations_PolygonGrid`, `SimpleAmenable_Configurations_PolygonTrackArea`, `SimpleAmenable_Configurations_RepeatedTrackRouting`, `SimpleAmenable_Configurations_ReserveAtom`, `SimpleAmenable_Configurations_SymmetricConfiguration`, `SimpleAmenable_Configurations_SymmetricFaces`, `SimpleAmenable_Configurations_SymmetricStabilizer`, `SimpleAmenable_Configurations_TrajectoryCoordinates`, `SimpleAmenable_Configurations_TrajectoryFaces`, `SimpleAmenable_Configurations_TrajectoryStages`, `SimpleAmenable_Configurations_TransitiveInduction`, `SimpleAmenable_Homology_Configuration`, `SimpleAmenable_Homology_ConfigurationEquivariance`, `SimpleAmenable_Homology_ConfigurationResolution`, `SimpleAmenable_Homology_FinitePrimitiveResolution`, `SimpleAmenable_Homology_FullGroupStability`, `SimpleAmenable_Homology_GroupoidComponentHomology`, `SimpleAmenable_Homology_HomologyAdditive`, `SimpleAmenable_Homology_IntegralHomologyFunctorial`, `SimpleAmenable_Homology_IntegralTransgressionFinite`, `SimpleAmenable_Homology_IntegralTransgressionHomology`, `SimpleAmenable_Homology_NoetherianTor`, `SimpleAmenable_Homology_PolygonCoefficientFinite`, `SimpleAmenable_Homology_RingGroupHomology`, `SimpleAmenable_Homology_TorusCoefficientFinite`, `SimpleAmenable_Homology_TransitiveCanonical`, `SimpleAmenable_Homology_VerticalStringResolution`, `SimpleAmenable_PolygonGeometry_AxisAnchorFamily`, `SimpleAmenable_PolygonGeometry_CanonicalSectors`, `SimpleAmenable_PolygonGeometry_ConcurrentAnchors`, `SimpleAmenable_PolygonGeometry_ConjugationTransport`, `SimpleAmenable_PolygonGeometry_CoordinateWindowTarget`, `SimpleAmenable_PolygonGeometry_EvaluationTable`, `SimpleAmenable_PolygonGeometry_FiniteArrangementGerms`, `SimpleAmenable_PolygonGeometry_FiniteSectorPartition`, `SimpleAmenable_PolygonGeometry_FlagGerms`, `SimpleAmenable_PolygonGeometry_FlagTentMass`, `SimpleAmenable_PolygonGeometry_FlagTranslation`, `SimpleAmenable_PolygonGeometry_FrameDisjointness`, `SimpleAmenable_PolygonGeometry_GoodRowSeparators`, `SimpleAmenable_PolygonGeometry_LiftedTranslationOrbits`, `SimpleAmenable_PolygonGeometry_LocalChartDecisions`, `SimpleAmenable_PolygonGeometry_MatrixInverseCalculus`, `SimpleAmenable_PolygonGeometry_NestedCutCalculus`, `SimpleAmenable_PolygonGeometry_ObservableDistance`, `SimpleAmenable_PolygonGeometry_PlaneCornerCoordinates`, `SimpleAmenable_PolygonGeometry_PlaneCornerInjectivity`, `SimpleAmenable_PolygonGeometry_PolygonArea`, `SimpleAmenable_PolygonGeometry_PolygonGridComparison`, `SimpleAmenable_PolygonGeometry_PrivateBankWord`, `SimpleAmenable_PolygonGeometry_RectangularBound`, `SimpleAmenable_PolygonGeometry_ResolvedBoolean`, `SimpleAmenable_PolygonGeometry_SectorControl`, `SimpleAmenable_PolygonGeometry_ShapeTranslationUnique`, `SimpleAmenable_PolygonGeometry_ShiftedSlots`, `SimpleAmenable_PolygonGeometry_SmallControlCalculus`, `SimpleAmenable_PolygonGeometry_SmallFamilyWords`, `SimpleAmenable_PolygonGeometry_Supported`, `SimpleAmenable_PolygonGeometry_TangentChartTemplates`, `SimpleAmenable_PolygonGeometry_TentMatrixPositivity`, `SimpleAmenable_PolygonGeometry_TupleChartDomain`, `SimpleAmenable_PolygonGeometry_VaryingCellClassification`, `SimpleAmenable_PolygonGeometry_WindowIntervals`, `SimpleAmenable_PolygonGeometry_WindowSubfamilies`, `SimpleAmenable_RandomFields_AffineDensityDerivative`, `SimpleAmenable_RandomFields_AffineGeneratorIntegrability`, `SimpleAmenable_RandomFields_AffineNoiseEnergy`, `SimpleAmenable_RandomFields_CompactSignalEnergy`, `SimpleAmenable_RandomFields_FieldHS`, `SimpleAmenable_RandomFields_FieldSignalData`, `SimpleAmenable_RandomFields_FiniteLawDistance`, `SimpleAmenable_RandomFields_FiniteOrthogonalEnergy`, `SimpleAmenable_RandomFields_FlagAveragingMatrices`, `SimpleAmenable_RandomFields_HellingerDistance`, `SimpleAmenable_RandomFields_MatrixDensityCalculus`, `SimpleAmenable_RandomFields_NoiseContinuity`, `SimpleAmenable_RandomFields_NoiseTensor`, `SimpleAmenable_RandomFields_PolygonApproxIdentity`, `SimpleAmenable_RandomFields_PolygonCovarianceEnergy`, `SimpleAmenable_RandomFields_PrimitiveCovariance`, `SimpleAmenable_RandomFields_SignalGoodRows`, `SimpleAmenable_RandomFields_SignalRemainder`, `SimpleAmenable_RandomFields_ThresholdField`, `SimpleAmenable_RandomFields_UniformThresholdCDF`, `SimpleAmenable_Simplicial_BitReindex`, `SimpleAmenable_Simplicial_FormalLawReindex`, `SimpleAmenable_Simplicial_LowerBarComposition`, `SimpleAmenable_Simplicial_StageNerveColimit`, `SimpleAmenable_Simplicial_StageSimplicialColimit`, `SimpleAmenable_Simplicial_TrajectoryReindexLabels`, `SimpleAmenable_Simplicial_TranslationNerve`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ65Sa005` and `OAIQ65Sa006`; the proof of `OAI_SimpleAmenable_affineNoiseRoot_square_distance`.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ065_SA.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_DirectFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section DirectFactors
variable {G : Type*} [Group G]

structure CommutingFactors (A B : Subgroup G) : Prop where
  commute : ∀ a ∈ A, ∀ b ∈ B, Commute a b
  cover : ∀ x : G, ∃ a ∈ A, ∃ b ∈ B, x = a * b

namespace CommutingFactors
variable {A B C D : Subgroup G}

theorem symm (h : CommutingFactors A B) : CommutingFactors B A where
  commute b hb a ha := (h.commute a ha b hb).symm
  cover x := by
    obtain ⟨a, ha, b, hb, rfl⟩ := h.cover x
    exact ⟨b, hb, a, ha, (h.commute a ha b hb).eq⟩

theorem mem_center_of_mem_inter (h : CommutingFactors A B) {x : G}
    (ha : x ∈ A) (hb : x ∈ B) : x ∈ Subgroup.center G := by
  apply Subgroup.mem_center_iff.mpr
  intro y
  obtain ⟨a, ha', b, hb', rfl⟩ := h.cover y
  exact ((h.commute a ha' x hb).mul_left (h.commute x ha b hb').symm).eq

theorem mem_left_of_commute_right (h : CommutingFactors A B)
    (hz : Subgroup.center G = ⊥) {x : G}
    (hx : ∀ b ∈ B, Commute x b) : x ∈ A := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.cover x
  have hbz : b ∈ Subgroup.center G := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨c, hc, d, hd, rfl⟩ := h.cover y
    have hbd : Commute b d := by
      have ht := (hx d hd).eq
      have ht' : a * (b * d) = a * (d * b) := by
        calc
          a * (b * d) = (a * b) * d := (mul_assoc _ _ _).symm
          _ = d * (a * b) := ht
          _ = (d * a) * b := (mul_assoc _ _ _).symm
          _ = (a * d) * b := by rw [(h.commute a ha d hd).eq]
          _ = a * (d * b) := mul_assoc _ _ _
      exact mul_left_cancel ht'
    exact ((h.commute c hc b hb).mul_left hbd.symm).eq
  have hb1 : b = 1 := by simpa [hz] using hbz
  simpa [hb1] using ha

def productHom (h : CommutingFactors A B) : A × B →* G where
  toFun x := x.1.1 * x.2.1
  map_one' := one_mul _
  map_mul' x y := by
    change (x.1.1 * y.1.1) * (x.2.1 * y.2.1) =
      (x.1.1 * x.2.1) * (y.1.1 * y.2.1)
    calc
      _ = x.1.1 * (y.1.1 * x.2.1) * y.2.1 := by group
      _ = x.1.1 * (x.2.1 * y.1.1) * y.2.1 := by
        rw [(h.commute _ y.1.2 _ x.2.2).eq]
      _ = _ := by group

@[simp] theorem productHom_apply (h : CommutingFactors A B) (x : A × B) :
    h.productHom x = x.1.1 * x.2.1 := rfl

theorem productHom_bijective (h : CommutingFactors A B)
    (hz : Subgroup.center G = ⊥) : Function.Bijective h.productHom := by
  constructor
  · apply (MonoidHom.ker_eq_bot_iff h.productHom).mp
    apply bot_unique
    rintro ⟨a, b⟩ hab
    change (a : G) * b = 1 at hab
    have hab' : (a : G) = (b : G)⁻¹ := eq_inv_of_mul_eq_one_left hab
    have haB : (a : G) ∈ B := hab' ▸ B.inv_mem b.property
    have ha1 : (a : G) = 1 := by
      simpa [hz] using h.mem_center_of_mem_inter a.property haB
    have hb1 : (b : G) = 1 := by simpa [ha1] using hab
    change (a, b) = 1
    exact Prod.ext (Subtype.ext ha1) (Subtype.ext hb1)
  · intro x
    obtain ⟨a, ha, b, hb, hab⟩ := h.cover x
    exact ⟨(⟨a,ha⟩,⟨b,hb⟩), hab.symm⟩

noncomputable def productEquiv (h : CommutingFactors A B)
    (hz : Subgroup.center G = ⊥) : A × B ≃* G :=
  MulEquiv.ofBijective h.productHom (h.productHom_bijective hz)

@[simp] theorem productEquiv_apply (h : CommutingFactors A B)
    (hz : Subgroup.center G = ⊥) (x : A × B) :
    h.productEquiv hz x = x.1.1 * x.2.1 := rfl

theorem left_component_commutes (h : CommutingFactors C D)
    (hz : Subgroup.center G = ⊥) {c y : G} (hc : c ∈ C) {d : G} (hd : d ∈ D)
    (hcy : Commute (c * d) y) : Commute c y := by
  obtain ⟨c', hc', d', hd', rfl⟩ := h.cover y
  let e := h.productEquiv hz
  have he : Commute ((⟨c,hc⟩,⟨d,hd⟩) : C × D)
      ((⟨c',hc'⟩,⟨d',hd'⟩) : C × D) := by
    apply e.injective
    simpa only [map_mul, e, productEquiv_apply] using hcy.eq
  have hcc' : Commute c c' := by
    exact congrArg (fun z : C × D => (z.1 : G)) he
  exact hcc'.mul_right (h.commute c hc d' hd')

end CommutingFactors
end DirectFactors

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PerfectCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
section PerfectCalculus

open scoped commutatorElement

variable {P H Q : Type*} [Group P] [Group H] [Group Q]

theorem perfect_center_quotient [Group.IsPerfect H] :
    Subgroup.center (H ⧸ Subgroup.center H) = ⊥ :=
  Group.IsPerfect.center_quotient_center_eq_bot H

end PerfectCalculus

open scoped commutatorElement

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FiniteCentralKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FiniteCentralKernel

open scoped commutatorElement

variable {G H Q : Type*} [Group G] [Group H] [Group Q]

theorem perfect_lift_range [Group.IsPerfect G] (l : G →* H) (q : H →* Q)
    (hq : Function.Surjective (q.comp l)) (hc : q.ker ≤ Subgroup.center H) :
    l.range = commutator H := by
  apply le_antisymm
  · have he : l.range = ⁅l.range,l.range⁆ := by
      rw [← map_commutator_eq,Group.IsPerfect.commutator_eq_top,← MonoidHom.range_eq_map]
    rw [he,commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  · rw [commutator_def]
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    obtain ⟨u,hu⟩ := hq (q x)
    obtain ⟨v,hv⟩ := hq (q y)
    change q (l u) = q x at hu
    change q (l v) = q y at hv
    have hx : (l u)⁻¹*x ∈ Subgroup.center H := hc (by
      change q ((l u)⁻¹*x) = 1
      simpa only [map_mul,map_inv,MonoidHom.comp_apply] using
        (show (q (l u))⁻¹*q x = 1 by rw [hu]; simp))
    have hy : (l v)⁻¹*y ∈ Subgroup.center H := hc (by
      change q ((l v)⁻¹*y) = 1
      simpa only [map_mul,map_inv,MonoidHom.comp_apply] using
        (show (q (l v))⁻¹*q y = 1 by rw [hv]; simp))
    have hex : x = l u*((l u)⁻¹*x) := by simp
    have hey : y = l v*((l v)⁻¹*y) := by simp
    have hz (a : H) : ⁅(l u)⁻¹*x,a⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr ((Subgroup.mem_center_iff.mp hx a).symm)
    have hw (a : H) : ⁅a,(l v)⁻¹*y⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hy a)
    have he : ⁅x,y⁆ = ⁅l u,l v⁆ := by
      conv_lhs => rw [hex,hey]
      rw [commutatorElement_mul_left_eq_conj_mul,hz]
      simp only [mul_one,mul_inv_cancel,one_mul]
      rw [commutatorElement_mul_right_eq_mul_conj,hw]
      simp only [mul_one,mul_inv_cancel_right]
    rw [he]
    exact ⟨⁅u,v⁆,map_commutatorElement l u v⟩

end FiniteCentralKernel

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_CanonicalSectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section CanonicalSectors
open scoped commutatorElement

variable {E H Q : Type*} [Group E] [Group H] [Group Q]

variable {Ω : Type*}

variable [Group.IsPerfect E]

def assignmentPullback {Ω' : Type*} (r : Ω' → Ω) : (Ω → E) →* (Ω' → E) where
  toFun f := f ∘ r
  map_one' := rfl
  map_mul' _ _ := rfl

end CanonicalSectors

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_AssignmentGeneration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section FiniteDirectRefinement
variable {G : Type*} [Group G]

namespace CommutingFactors
variable {A B C D : Subgroup G}

noncomputable def projectLeft (h : CommutingFactors A B)
    (hz : Subgroup.center G = ⊥) : G →* G :=
  A.subtype.comp ((MonoidHom.fst A B).comp (h.productEquiv hz).symm.toMonoidHom)

@[simp] theorem projectLeft_mem (h : CommutingFactors A B)
    (hz : Subgroup.center G = ⊥) (x : G) : h.projectLeft hz x ∈ A :=
  ((h.productEquiv hz).symm x).1.property

theorem projectLeft_factors (h : CommutingFactors A B)
    (hz : Subgroup.center G = ⊥) {a b : G} (ha : a ∈ A) (hb : b ∈ B) :
    h.projectLeft hz (a*b) = a := by
  change (((h.productEquiv hz).symm (a*b)).1 : G) = a
  have hh : (h.productEquiv hz).symm (a*b) = (⟨a,ha⟩,⟨b,hb⟩) := by
    apply (h.productEquiv hz).injective
    simp only [MulEquiv.apply_symm_apply, productEquiv_apply]
  rw [hh]

theorem projectLeft_split (h : CommutingFactors A B)
    (hz : Subgroup.center G = ⊥) (x : G) :
    x = h.projectLeft hz x * h.symm.projectLeft hz x := by
  obtain ⟨a,ha,b,hb,rfl⟩ := h.cover x
  rw [h.projectLeft_factors hz ha hb]
  rw [(h.commute a ha b hb).eq, h.symm.projectLeft_factors hz hb ha]
  exact (h.commute a ha b hb).eq.symm

theorem projectLeft_preserves (h : CommutingFactors A B) (k : CommutingFactors C D)
    (hz : Subgroup.center G = ⊥) {x : G} (hx : x ∈ C) : h.projectLeft hz x ∈ C := by
  apply k.mem_left_of_commute_right hz
  intro y hy
  apply h.left_component_commutes hz (h.projectLeft_mem hz x)
    (h.symm.projectLeft_mem hz x)
  rw [← h.projectLeft_split hz x]
  exact k.commute x hx y hy

end CommutingFactors

def assignmentFactor {ι : Type*} (A : ι → Subgroup G) (S : Finset ι) : Subgroup G :=
  ⨅ i ∈ S, A i

theorem projectLeft_mem_assignmentFactor {ι : Type*}
    (A B : ι → Subgroup G) (h : ∀ i, CommutingFactors (A i) (B i))
    {C D : Subgroup G} (k : CommutingFactors C D) (hz : Subgroup.center G = ⊥)
    (S : Finset ι) {x : G} (hx : x ∈ assignmentFactor A S) :
    k.projectLeft hz x ∈ assignmentFactor A S := by
  simp only [assignmentFactor, Subgroup.mem_iInf] at hx ⊢
  intro i hi
  exact k.projectLeft_preserves (h i) hz (hx i hi)

theorem split_assignmentFactor {ι : Type*}
    (A B : ι → Subgroup G) (h : ∀ i, CommutingFactors (A i) (B i))
    {C D : Subgroup G} (k : CommutingFactors C D) (hz : Subgroup.center G = ⊥)
    (S : Finset ι) {x : G} (hx : x ∈ assignmentFactor A S) :
    ∃ c ∈ assignmentFactor A S ⊓ C, ∃ d ∈ assignmentFactor A S ⊓ D, x = c*d := by
  refine ⟨k.projectLeft hz x, ⟨?_,k.projectLeft_mem hz x⟩,
    k.symm.projectLeft hz x, ⟨?_,k.symm.projectLeft_mem hz x⟩,k.projectLeft_split hz x⟩
  · exact projectLeft_mem_assignmentFactor A B h k hz S hx
  · exact projectLeft_mem_assignmentFactor A B h k.symm hz S hx

def refinedFactor {ι : Type*} (A B : ι → Subgroup G) (S : Finset ι)
    (σ : ι → Bool) : Subgroup G :=
  assignmentFactor (fun i => if σ i then A i else B i) S

theorem simultaneous_refinement {ι : Type*} (A B : ι → Subgroup G)
    (h : ∀ i, CommutingFactors (A i) (B i)) (hz : Subgroup.center G = ⊥)
    (S : Finset ι) : (⨆ σ : ι → Bool, refinedFactor A B S σ) = ⊤ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [refinedFactor, assignmentFactor]
  | @insert i S hi ih =>
    apply top_unique
    rw [← ih]
    apply iSup_le
    intro σ x hx
    have hp (j : ι) : CommutingFactors
        (if σ j then A j else B j) (if σ j then B j else A j) := by
      cases hs : σ j
      · simpa only [hs, Bool.false_eq_true, ↓reduceIte] using (h j).symm
      · simpa only [hs, ↓reduceIte] using h j
    obtain ⟨c,hc,d,hd,rfl⟩ := split_assignmentFactor
      (fun j => if σ j then A j else B j) (fun j => if σ j then B j else A j)
      hp (h i) hz S hx
    have hm (b : Bool) {z : G}
        (hS : z ∈ refinedFactor A B S σ) (hzi : z ∈ if b then A i else B i) :
        z ∈ refinedFactor A B (insert i S) (Function.update σ i b) := by
      simp only [refinedFactor, assignmentFactor, Subgroup.mem_iInf] at hS ⊢
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa only [Function.update_self] using hzi
      · have hji : j ≠ i := by
          intro heq
          subst j
          exact hi hj
        simpa only [Function.update_of_ne hji] using hS j hj
    apply Subgroup.mul_mem
    · exact Subgroup.mem_iSup_of_mem (Function.update σ i true) (hm true hc.1 hc.2)
    · exact Subgroup.mem_iSup_of_mem (Function.update σ i false) (hm false hd.1 hd.2)

theorem refinedFactor_commute {ι : Type*} [Fintype ι] (A B : ι → Subgroup G)
    (h : ∀ i, CommutingFactors (A i) (B i)) {σ τ : ι → Bool} (hστ : σ ≠ τ)
    {x y : G} (hx : x ∈ refinedFactor A B Finset.univ σ)
    (hy : y ∈ refinedFactor A B Finset.univ τ) : Commute x y := by
  classical
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hστ
  simp only [refinedFactor, assignmentFactor, Subgroup.mem_iInf, Finset.mem_univ,
    forall_const] at hx hy
  specialize hx i
  specialize hy i
  cases hs : σ i <;> cases ht : τ i <;> simp_all
  · exact ((h i).commute y hy x hx).symm
  · exact (h i).commute x hx y hy

theorem commuting_factors_independent {ι : Type*} (F : ι → Subgroup G)
    (hcomm : Pairwise fun i j => ∀ x y : G, x ∈ F i → y ∈ F j → Commute x y)
    (hgenerate : (⨆ i, F i) = ⊤) (hz : Subgroup.center G = ⊥) : iSupIndep F := by
  classical
  intro i
  rw [disjoint_iff_inf_le]
  intro x hx
  have hrest : (⨆ j, ⨆ (_ : j ≠ i), F j) ≤ Subgroup.centralizer (F i : Set G) := by
    apply iSup_le
    intro j
    apply iSup_le
    intro hji y hy
    exact Subgroup.mem_centralizer_iff.mpr fun z hz' => (hcomm hji y z hy hz').eq.symm
  have hself : x ∈ Subgroup.centralizer (F i : Set G) := hrest hx.2
  have hall : (⨆ j, F j) ≤ Subgroup.centralizer {x} := by
    apply iSup_le
    intro j y hy
    apply Subgroup.mem_centralizer_iff.mpr
    intro z hz'
    have hzx : z = x := Set.mem_singleton_iff.mp hz'
    subst z
    by_cases hji : j = i
    · subst j
      exact (Subgroup.mem_centralizer_iff.mp hself y hy).symm
    · exact (hcomm hji y x hy hx.1).eq.symm
  have hcenter : x ∈ Subgroup.center G := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    have hy := hall (hgenerate ▸ Subgroup.mem_top y)
    exact (Subgroup.mem_centralizer_iff.mp hy x (Set.mem_singleton x)).symm
  simpa only [hz, Subgroup.mem_bot] using hcenter

noncomputable def commutingFactorsEquiv {ι : Type*} [Fintype ι] (F : ι → Subgroup G)
    (hcomm : Pairwise fun i j => ∀ x y : G, x ∈ F i → y ∈ F j → Commute x y)
    (hgenerate : (⨆ i, F i) = ⊤) (hz : Subgroup.center G = ⊥) :
    (∀ i, F i) ≃* G :=
  MulEquiv.ofBijective (Subgroup.noncommPiCoprod hcomm)
    ⟨Subgroup.injective_noncommPiCoprod_of_iSupIndep
        (commuting_factors_independent F hcomm hgenerate hz),
      MonoidHom.range_eq_top.mp (by
        rw [Subgroup.noncommPiCoprod_range]
        exact hgenerate)⟩

@[simp] theorem commutingFactorsEquiv_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → Subgroup G)
    (hcomm : Pairwise fun i j => ∀ x y : G, x ∈ F i → y ∈ F j → Commute x y)
    (hgenerate : (⨆ i, F i) = ⊤) (hz : Subgroup.center G = ⊥)
    (i : ι) (x : F i) : commutingFactorsEquiv F hcomm hgenerate hz (Pi.mulSingle i x) = x := by
  exact Subgroup.noncommPiCoprod_mulSingle (hcomm := hcomm) i x

end FiniteDirectRefinement

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_NestedCutCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section NestedCutCalculus

variable {E H : Type*} [Group E] [Group H]

theorem commute_ratio_of_conjugation {u v x : H}
    (h : v*x*v⁻¹ = u*x*u⁻¹) : Commute x (u⁻¹*v) := by
  change x*(u⁻¹*v) = (u⁻¹*v)*x
  have ht := congrArg (fun z => u⁻¹*z*v) h
  simpa only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] using ht.symm

def differenceHom (l g : E →* H)
    (h : ∀ s t, Commute (l s) ((l t)⁻¹*g t)) : E →* H where
  toFun t := (l t)⁻¹*g t
  map_one' := by simp
  map_mul' s t := by
    simp only [map_mul, mul_inv_rev]
    calc
      (l t)⁻¹*(l s)⁻¹*(g s*g t) = (l t)⁻¹*((l s)⁻¹*g s)*g t := by group
      _ = ((l s)⁻¹*g s)*(l t)⁻¹*g t := by rw [(h t s).inv_left.eq]
      _ = ((l s)⁻¹*g s)*((l t)⁻¹*g t) := by group

@[simp] theorem differenceHom_apply (l g : E →* H)
    (h : ∀ s t, Commute (l s) ((l t)⁻¹*g t)) (t : E) :
    differenceHom l g h t = (l t)⁻¹*g t := rfl

theorem split_conjugation (l k : E →* H) (h : ∀ s t, Commute (l s) (k t))
    (s t : E) : (l t*k t)*l s*(l t*k t)⁻¹ = l t*l s*(l t)⁻¹ := by
  calc
    (l t*k t)*l s*(l t*k t)⁻¹ = l t*(k t*l s)*(k t)⁻¹*(l t)⁻¹ := by group
    _ = l t*(l s*k t)*(k t)⁻¹*(l t)⁻¹ := by rw [(h s t).symm.eq]
    _ = l t*l s*(l t)⁻¹ := by group

theorem nested_cut_commute_ratio (f l₁ h₁ l₂ h₂ : E →* H)
    (hf₁ : ∀ s, f s = l₁ s*h₁ s) (hf₂ : ∀ s, f s = l₂ s*h₂ s)
    (hc₁ : ∀ s t, Commute (l₁ s) (h₁ t))
    (hc₁₂ : ∀ s t, Commute (l₁ s) (h₂ t)) :
    ∀ s t, Commute (l₁ s) ((l₂ t)⁻¹*f t) ∧
      Commute (l₁ s) ((l₁ t)⁻¹*l₂ t) := by
  intro s t
  constructor
  · simpa [hf₂] using hc₁₂ s t
  · apply commute_ratio_of_conjugation
    calc
      l₂ t*l₁ s*(l₂ t)⁻¹ = f t*l₁ s*(f t)⁻¹ := by
        rw [hf₂]
        calc
          l₂ t*l₁ s*(l₂ t)⁻¹ = l₂ t*(l₁ s*h₂ t)*(h₂ t)⁻¹*(l₂ t)⁻¹ := by group
          _ = l₂ t*(h₂ t*l₁ s)*(h₂ t)⁻¹*(l₂ t)⁻¹ := by rw [(hc₁₂ s t).eq]
          _ = (l₂ t*h₂ t)*l₁ s*(l₂ t*h₂ t)⁻¹ := by group
      _ = l₁ t*l₁ s*(l₁ t)⁻¹ := by rw [hf₁]; exact split_conjugation l₁ h₁ hc₁ s t

end NestedCutCalculus

open scoped commutatorElement
section ConditionalControl
variable {E H : Type*} [Group E] [Group H]

def SameActionOn (f g : E → H) (P : Subgroup H) : Prop :=
  ∀ s, ∀ k ∈ P, f s*k*(f s)⁻¹ = g s*k*(g s)⁻¹

section NestedCuts
variable (f : E →* H) (l h : ℕ → E →* H)
    (hf : ∀ i s, f s = l i s*h i s)
    (hc : ∀ i j, i ≤ j → ∀ s t, Commute (l i s) (h j t))

def cutDifference (i : ℕ) : E →* H :=
  differenceHom (l i) (l (i+1)) (fun s t =>
    (nested_cut_commute_ratio f (l i) (h i) (l (i+1)) (h (i+1))
      (hf i) (hf (i+1)) (hc i i le_rfl) (hc i (i+1) (by omega)) s t).2)

end NestedCuts

end ConditionalControl

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_CentralRangeReflection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section FormalSectorSupport
variable {E E' H Ω ι : Type*} [Group E] [Group E'] [Group H]

def assignmentPost (ψ : E' →* E) : (Ω → E') →* (Ω → E) where
  toFun f ω := ψ (f ω)
  map_one' := by ext ω; exact map_one ψ
  map_mul' f g := by ext ω; exact map_mul ψ (f ω) (g ω)

end FormalSectorSupport

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Arithmetic_PolygonArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open scoped symmDiff

namespace SimpleAmenable

section PolygonArithmetic

theorem golden_coefficients_unique {p q : ℤ}
    (h : (p : ℝ) + (q : ℝ) * Real.goldenRatio = 0) : p = 0 ∧ q = 0 := by
  have hq : q = 0 := by
    by_contra hq
    have hir := (Real.goldenRatio_irrational.intCast_mul hq).intCast_add p
    exact hir.ne_int 0 (by simpa using h)
  exact ⟨by simpa [hq] using h, hq⟩

end PolygonArithmetic

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_TupleChartDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section PolygonFullGroup
attribute [local instance] Classical.propDecidable

def threeInFive : Fin 3 ↪ Fin 5 := ⟨![0,1,2], by decide⟩
def leftThreeInFive : Fin 3 ↪ Fin 5 := ⟨![0,1,3], by decide⟩
def rightThreeInFive : Fin 3 ↪ Fin 5 := ⟨![0,2,4], by decide⟩

theorem two_spare_tracks {m : ℕ} (hm : 5 ≤ m) (s : Fin 3 → Fin m) :
    ∃ k l : Fin m, k ≠ l ∧ (∀ i, s i ≠ k) ∧ (∀ i, s i ≠ l) := by
  classical
  let used := Finset.univ.image s
  have hc : used.card ≤ 3 := by
    exact Finset.card_image_le.trans (by simp)
  have hleft : 1 < usedᶜ.card := by
    rw [Finset.card_compl]
    simp only [Fintype.card_fin]
    omega
  obtain ⟨k,hk⟩ := Finset.card_pos.mp (by omega : 0 < usedᶜ.card)
  obtain ⟨l,hl,hlk⟩ := Finset.exists_mem_ne hleft k
  refine ⟨k,l,Ne.symm hlk,?_,?_⟩
  · intro i he
    have hi : k ∈ used := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he⟩
    exact Finset.mem_compl.mp hk hi
  · intro i he
    have hi : l ∈ used := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he⟩
    exact Finset.mem_compl.mp hl hi

end PolygonFullGroup
end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PerfectGeneratingFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PerfectGeneratingFamilies

variable {ι G H : Type*} [Group G] [Group H]

theorem perfect_iSup (F : ι → Subgroup G) [∀ i, Group.IsPerfect (F i)] :
    Group.IsPerfect ↥(⨆ i, F i) := by
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm (Subgroup.commutator_le_self _)
  apply iSup_le
  intro i
  rw [← Subgroup.commutator_eq_self (H := F i)]
  exact Subgroup.commutator_mono (le_iSup F i) (le_iSup F i)

theorem central_perfect_generating_ranges {E : ι → Type*} [∀ i, Group (E i)]
    [∀ i, Group.IsPerfect (E i)] [Group.IsPerfect H]
    (q : H →* G) (hc : q.ker ≤ Subgroup.center H)
    (f : ∀ i, E i →* H) (hf : (⨆ i, (q.comp (f i)).range) = ⊤) :
    (⨆ i, (f i).range) = ⊤ := by
  let S : Subgroup H := ⨆ i, (f i).range
  let (i : ι) : Group.IsPerfect (f i).range := Group.IsPerfect.range (f i)
  let : Group.IsPerfect S := perfect_iSup (fun i => (f i).range)
  have hm : S.map q = ⊤ := by
    simp only [S, Subgroup.map_iSup, ← MonoidHom.range_comp]
    exact hf
  have hs : Function.Surjective (q.comp S.subtype) := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hm
  have hr := perfect_lift_range S.subtype q hs hc
  simpa only [Subgroup.range_subtype, Group.IsPerfect.commutator_eq_top] using hr

end PerfectGeneratingFamilies

section FiniteTranslationCentralizers

variable {α β ι G : Type*} [Group G]

noncomputable def translationWordMap (β : Type*) :
    FreeGroup β →* Multiplicative (FreeAbelianGroup β) :=
  FreeGroup.lift (fun i => Multiplicative.ofAdd (FreeAbelianGroup.of i))

theorem translationWordMap_surjective : Function.Surjective (translationWordMap β) := by
  intro x
  change ∃ y, translationWordMap β y =
    Multiplicative.ofAdd (Multiplicative.toAdd x)
  induction Multiplicative.toAdd x using FreeAbelianGroup.induction_on with
  | zero => exact ⟨1,map_one _⟩
  | of i => exact ⟨FreeGroup.of i,FreeGroup.lift_apply_of⟩
  | neg i hi =>
      obtain ⟨w,hw⟩ := hi
      exact ⟨w⁻¹,by change translationWordMap β (w⁻¹) = _⁻¹; rw [map_inv,hw]; rfl⟩
  | add x y hx hy =>
      obtain ⟨w,hw⟩ := hx
      obtain ⟨v,hv⟩ := hy
      exact ⟨w*v,by change translationWordMap β (w*v) = _*_; rw [map_mul,hw,hv]; rfl⟩

end FiniteTranslationCentralizers

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_BooleanCoordinateGeneration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section BooleanCoordinateGeneration

theorem fract_sub_unit {x u : ℝ} (hx : 0 ≤ x ∧ x < 1)
    (hu : 0 ≤ u ∧ u < 1) :
    Int.fract (x-u) = if x < u then x-u+1 else x-u := by
  split_ifs with h
  · have hf : ⌊x-u⌋ = (-1 : ℤ) := Int.floor_eq_iff.mpr ⟨by norm_num; linarith,by norm_num; linarith⟩
    simp only [Int.fract,hf,Int.cast_neg,Int.cast_one]
    ring
  · exact Int.fract_eq_self.mpr ⟨by linarith,by linarith⟩

theorem fract_sum_unit {u v : ℝ} (hu : 0 ≤ u ∧ u < 1)
    (hv : 0 ≤ v ∧ v < 1) :
    Int.fract (u+v) = if u+v < 1 then u+v else u+v-1 := by
  split_ifs with h
  · exact Int.fract_eq_self.mpr ⟨by linarith,h⟩
  · have hf : ⌊u+v⌋ = (1 : ℤ) := Int.floor_eq_iff.mpr ⟨by norm_num; linarith,by norm_num; linarith⟩
    simp [Int.fract,hf]

theorem arc_add_test (x u v : ℝ) (hx : 0 ≤ x ∧ x < 1)
    (hu : 0 ≤ u ∧ u < 1) (hv : 0 ≤ v ∧ v < 1) :
    (x < Int.fract (u+v)) ↔
      if u+v < 1 then Xor (x < u) (Int.fract (x-u) < v)
      else ¬ Xor (x < u) (Int.fract (x-u) < v) := by
  rw [fract_sum_unit hu hv,fract_sub_unit hx hu]
  by_cases hs : u+v < 1 <;> by_cases hxu : x < u <;>
    simp only [hs,hxu,ite_true,ite_false,Xor,true_and,false_and,false_or,
      not_true_eq_false,not_false_eq_true,and_true,and_false,or_false,not_lt] <;>
    constructor <;> intro h <;> linarith

theorem fract_sub_fract (x y : ℝ) :
    Int.fract (x-Int.fract y) = Int.fract (x-y) := by
  change Int.fract (x-(y-(⌊y⌋ : ℝ))) = _
  rw [sub_sub_eq_add_sub,add_sub_right_comm,Int.fract_add_intCast]

theorem arc_neg_test (x u : ℝ) (hx : 0 ≤ x ∧ x < 1)
    (hu : 0 < u ∧ u < 1) :
    (x < 1-u) ↔ ¬ Int.fract (x+u) < u := by
  rw [fract_sum_unit hx ⟨hu.1.le,hu.2⟩]
  split_ifs <;> push Not <;> constructor <;> intro h <;> linarith

end BooleanCoordinateGeneration

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_FiveTrackGeneration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FiveTrackGeneration

noncomputable def fiveTrackHom {m : ℕ} (ι : Fin 5 ↪ Fin m) :
    alternatingGroup (Fin 5) →* Equiv.Perm (Fin m) :=
  (Equiv.Perm.viaEmbeddingHom ι).comp (alternatingGroup (Fin 5)).subtype

instance fiveTrackPerfect : Group.IsPerfect (alternatingGroup (Fin 5)) :=
  ⟨commutator_alternatingGroup_eq_top (by norm_num)⟩

theorem fiveTrack_sign {m : ℕ} (ι : Fin 5 ↪ Fin m)
    (g : alternatingGroup (Fin 5)) : fiveTrackHom ι g ∈ alternatingGroup (Fin m) := by
  classical
  change Equiv.Perm.sign (g.val.viaEmbedding ι) = 1
  rw [Equiv.Perm.viaEmbedding,Equiv.Perm.sign_extendDomain]
  exact g.property

theorem fiveTrack_support {m : ℕ} (ι : Fin 5 ↪ Fin m)
    (g : alternatingGroup (Fin 5)) : (fiveTrackHom ι g).support.card ≤ 5 := by
  classical
  have hsub : (fiveTrackHom ι g).support ⊆ Finset.univ.map ι := by
    intro i hi
    by_contra hn
    have hn' : i ∉ Set.range ι := by simpa using hn
    exact (Equiv.Perm.mem_support.mp hi) (Equiv.Perm.viaEmbedding_apply_of_notMem g.val ι i hn')
  simpa using Finset.card_le_card hsub

end FiveTrackGeneration

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_LiftedTranslationOrbits
attribute [-instance] _root_.OAI.SimpleAmenable.fiveTrackPerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section LiftedTranslationOrbits

variable {A G H : Type*} [CommGroup A] [Group G] [Group H]

theorem lifted_translation_orbit_independent (q : A →* G) (t : A →* H)
    (x : G) (y : H)
    (hc : ∀ k, Commute (q k) x → Commute (t k) y)
    (u v : A) (h : q u*x*(q u)⁻¹ = q v*x*(q v)⁻¹) :
    t u*y*(t u)⁻¹ = t v*y*(t v)⁻¹ := by
  have hc₀ : Commute (q (v⁻¹*u)) x := by
    simpa only [map_mul,map_inv] using (commute_ratio_of_conjugation h).symm
  have hc₁ : Commute (t v⁻¹*t u) y := by
    simpa only [map_mul,map_inv] using hc (v⁻¹*u) hc₀
  calc
    t u*y*(t u)⁻¹ = t v*((t v⁻¹*t u)*y)*(t u)⁻¹ := by rw [map_inv]; group
    _ = t v*(y*(t v⁻¹*t u))*(t u)⁻¹ := by rw [hc₁.eq]
    _ = t v*y*(t v)⁻¹ := by rw [map_inv]; group

end LiftedTranslationOrbits

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_Supported
attribute [-instance] _root_.OAI.SimpleAmenable.fiveTrackPerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section LocalDisplacement

def SupportedIn {α : Type*} (g : Equiv.Perm α) (U : Set α) : Prop :=
  ∀ p ∉ U, g p = p

theorem supported_conjugate {α : Type*} (n : Equiv.Perm α)
    {g : Equiv.Perm α} {U : Set α} (hg : SupportedIn g U) :
    SupportedIn (n * g * n⁻¹) (n '' U) := by
  intro p hp
  have hx : n.symm p ∉ U := by
    intro h
    exact hp ⟨n.symm p,h,n.apply_symm_apply p⟩
  change n (g (n.symm p)) = p
  rw [hg _ hx, n.apply_symm_apply]

end LocalDisplacement
end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PrimitiveGeometricGeneration
attribute [-instance] _root_.OAI.SimpleAmenable.fiveTrackPerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PrimitiveGeometricGeneration

theorem fract_small_lift {r x : ℝ} (hr : 0 < r ∧ r < 1/2)
    (hx : -r < x ∧ x < r) : ∃ k : Fin 2, Int.fract x = x + k.val := by
  by_cases hx0 : 0 ≤ x
  · refine ⟨0,?_⟩
    simp only [Fin.val_zero,Nat.cast_zero,add_zero]
    exact Int.fract_eq_self.mpr ⟨hx0,by linarith⟩
  · refine ⟨1,?_⟩
    have hf : ⌊x⌋ = (-1 : ℤ) := Int.floor_eq_iff.mpr (by constructor <;> norm_num <;> linarith)
    simp [Int.fract,hf]

theorem fract_small_lift_unique {r x : ℝ} (hr : 0 < r ∧ r < 1/2)
    (hx : -r < x ∧ x < r) (k : Fin 2)
    (hk : -r ≤ Int.fract x - k.val ∧ Int.fract x - k.val < r) :
    Int.fract x - k.val = x := by
  obtain ⟨j,hj⟩ := fract_small_lift hr hx
  fin_cases j <;> fin_cases k <;>
    simp only [Nat.cast_zero,Nat.cast_one,add_zero,sub_zero] at hj hk ⊢ <;>
    linarith

end PrimitiveGeometricGeneration

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ShiftedSlots
attribute [-instance] _root_.OAI.SimpleAmenable.fiveTrackPerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section LocalDisplacement

theorem supported_inv {α : Type*} {g : Equiv.Perm α} {U : Set α}
    (h : SupportedIn g U) : SupportedIn g⁻¹ U := by
  intro p hp
  apply g.injective
  change g (g.symm p) = g p
  rw [g.apply_symm_apply,h p hp]

theorem SupportedIn.mono {α : Type*} {g : Equiv.Perm α} {U V : Set α}
    (h : SupportedIn g U) (hUV : U ⊆ V) : SupportedIn g V :=
  fun p hp => h p (fun hu => hp (hUV hu))

end LocalDisplacement

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_InitialCoverSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section InitialCoverSystem

theorem alternating_hom_ext_small {I H : Type*} [Fintype I] [DecidableEq I]
    [Group H] (f g : alternatingGroup I →* H)
    (h : ∀ s : alternatingGroup I, s.val.support.card ≤ 5 → f s = g s) : f = g := by
  apply MonoidHom.eq_of_eqOn_dense alternatingGroup.closure_isThreeCycles_eq_top
  intro s hs
  exact h s (by rw [hs.card_support]; omega)

end InitialCoverSystem

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_AlphabetAlignedGeneration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section AlphabetAlignedGeneration

noncomputable def alphabetHom {n m : ℕ} (ι : Fin n ↪ Fin m) :
    alternatingGroup (Fin n) →* Equiv.Perm (Fin m) :=
  (Equiv.Perm.viaEmbeddingHom ι).comp (alternatingGroup (Fin n)).subtype

theorem alphabet_support_subset {n m : ℕ} (ι : Fin n ↪ Fin m)
    (g : alternatingGroup (Fin n)) :
    (alphabetHom ι g).support ⊆ Finset.univ.map ι := by
  classical
  intro i hi
  by_contra hn
  have hn' : i ∉ Set.range ι := by simpa using hn
  exact (Equiv.Perm.mem_support.mp hi)
    (Equiv.Perm.viaEmbedding_apply_of_notMem g.val ι i hn')

end AlphabetAlignedGeneration

section CentralLaws

variable {D M H : Type*} [Group D] [Group M] [Group H]

def HasCentralLaw (v : D →* M) (f : D →* H) : Prop :=
  v.ker ≤ ((QuotientGroup.mk' (Subgroup.center H)).comp f).ker

theorem hasCentralLaw_iff (v : D →* M) (f : D →* H) :
    HasCentralLaw v f ↔ ∀ w, v w = 1 → f w ∈ Subgroup.center H := by
  constructor
  · intro h w hw
    have hh : f w ∈ (QuotientGroup.mk' (Subgroup.center H)).ker := h hw
    rwa [QuotientGroup.ker_mk'] at hh
  · intro h w hw
    change f w ∈ (QuotientGroup.mk' (Subgroup.center H)).ker
    rw [QuotientGroup.ker_mk']
    exact h w hw

end CentralLaws

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_ConditionalFamilyLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ConditionalFamilyLaws

variable {ι E H Ω : Type*} [Group E] [Group H]

noncomputable def copyFamilyEval (F : ι → E →* H) : FreeGroup (ι × E) →* H :=
  FreeGroup.lift (fun p => F p.1 p.2)

@[simp] theorem copyFamilyEval_of (F : ι → E →* H) (i : ι) (x : E) :
    copyFamilyEval F (FreeGroup.of (i,x)) = F i x := FreeGroup.lift_apply_of

theorem copyFamilyEval_range (F : ι → E →* H) :
    (copyFamilyEval F).range = ⨆ i, (F i).range := by
  rw [copyFamilyEval,FreeGroup.range_lift_eq_closure]
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨⟨i,x⟩,rfl⟩
    exact (le_iSup (fun i => (F i).range) i) ⟨x,rfl⟩
  · apply iSup_le
    intro i x hx
    obtain ⟨x,rfl⟩ := hx
    exact Subgroup.subset_closure ⟨(i,x),rfl⟩

end ConditionalFamilyLaws

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ConjugationTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ConjugationTransport

variable {J M H T : Type*} [Group M] [Group H] [MulAction M T]

theorem word_conjugates_differences (p : J → M) (f : J → H) (Y : T → H)
    (R : T → T → Prop)
    (hR : ∀ (g : M) t u, R t u → R (g • t) (g • u))
    (hgen : ∀ j t u, R t u →
      f j * (Y t)⁻¹ * Y u * (f j)⁻¹ =
        (Y (p j • t))⁻¹ * Y (p j • u))
    (w : FreeGroup J) : ∀ t u, R t u →
      FreeGroup.lift f w * (Y t)⁻¹ * Y u * (FreeGroup.lift f w)⁻¹ =
        (Y (FreeGroup.lift p w • t))⁻¹ * Y (FreeGroup.lift p w • u) := by
  induction w using OAI.freeGroupInductionOn with
  | one =>
      intro t u _
      simp
  | of j =>
      simpa only [FreeGroup.lift_apply_of] using hgen j
  | inv_of j ih =>
      intro t u htu
      have h := ih ((p j)⁻¹ • t) ((p j)⁻¹ • u) (hR _ _ _ htu)
      simp only [FreeGroup.lift_apply_of, smul_inv_smul] at h
      simp only [map_inv, FreeGroup.lift_apply_of]
      calc
        (f j)⁻¹ * (Y t)⁻¹ * Y u * ((f j)⁻¹)⁻¹ =
            (f j)⁻¹ * (f j * (Y ((p j)⁻¹ • t))⁻¹ *
                Y ((p j)⁻¹ • u) * (f j)⁻¹) * f j := by rw [h]; group
        _ = _ := by group
  | mul x y ihx ihy =>
      intro t u htu
      simp only [map_mul, mul_smul]
      calc
        (FreeGroup.lift f x * FreeGroup.lift f y) * (Y t)⁻¹ * Y u *
            (FreeGroup.lift f x * FreeGroup.lift f y)⁻¹ =
            FreeGroup.lift f x *
              (FreeGroup.lift f y * (Y t)⁻¹ * Y u * (FreeGroup.lift f y)⁻¹) *
              (FreeGroup.lift f x)⁻¹ := by group
        _ = FreeGroup.lift f x *
              ((Y (FreeGroup.lift p y • t))⁻¹ * Y (FreeGroup.lift p y • u)) *
              (FreeGroup.lift f x)⁻¹ := by rw [ihy t u htu]
        _ = _ := by
          simpa only [mul_assoc] using
            ihx _ _ (hR (FreeGroup.lift p y) t u htu)

theorem centralLaw_of_difference_conjugations
    (p : J → M) (f : J → H) (Y : T → H) (R : T → T → Prop)
    (hR : ∀ (g : M) t u, R t u → R (g • t) (g • u))
    (hgen : ∀ j t u, R t u →
      f j * (Y t)⁻¹ * Y u * (f j)⁻¹ =
        (Y (p j • t))⁻¹ * Y (p j • u))
    (hgenerate : Subgroup.closure {h : H | ∃ t u, R t u ∧ h = (Y t)⁻¹ * Y u} = ⊤) :
    HasCentralLaw (FreeGroup.lift p) (FreeGroup.lift f) := by
  rw [hasCentralLaw_iff]
  intro w hw
  rw [← Subgroup.centralizer_univ, ← Subgroup.coe_top, ← hgenerate,
    Subgroup.centralizer_closure]
  apply Subgroup.mem_centralizer_iff.mpr
  rintro z ⟨t,u,htu,rfl⟩
  have h := word_conjugates_differences p f Y R hR hgen w t u htu
  rw [hw, one_smul, one_smul] at h
  have h' := congrArg (fun x => x * FreeGroup.lift f w) h
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using h'.symm

end ConjugationTransport

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_AtomConjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section AtomConjugation
variable {J M H T : Type*} [Group M] [Group H] [MulAction M T]

theorem difference_conjugation_of_atom (p : J → M) (f : J → H) (Y : T → H)
    (b : T → T) (R : T → T → Prop) (hb : ∀ t u, R t u → b t = b u)
    (hconj : ∀ j t, f j * Y t * (f j)⁻¹ =
      (Y (p j • b t))⁻¹ * Y (p j • t)) :
    ∀ j t u, R t u →
      f j * (Y t)⁻¹ * Y u * (f j)⁻¹ =
        (Y (p j • t))⁻¹ * Y (p j • u) := by
  intro j t u htu
  calc
    f j * (Y t)⁻¹ * Y u * (f j)⁻¹ =
        (f j * Y t * (f j)⁻¹)⁻¹ * (f j * Y u * (f j)⁻¹) := by group
    _ = ((Y (p j • b t))⁻¹ * Y (p j • t))⁻¹ *
        ((Y (p j • b u))⁻¹ * Y (p j • u)) := by rw [hconj, hconj]
    _ = _ := by rw [hb t u htu]; group

theorem centralLaw_of_atom_conjugations (p : J → M) (f : J → H) (Y : T → H)
    (b : T → T) (R : T → T → Prop) (hb : ∀ t u, R t u → b t = b u)
    (hRb : ∀ t, R (b t) t) (hYb : ∀ t, Y (b t) = 1)
    (hR : ∀ (g : M) t u, R t u → R (g • t) (g • u))
    (hconj : ∀ j t, f j * Y t * (f j)⁻¹ =
      (Y (p j • b t))⁻¹ * Y (p j • t))
    (hgen : Subgroup.closure (Set.range Y) = ⊤) :
    HasCentralLaw (FreeGroup.lift p) (FreeGroup.lift f) := by
  apply centralLaw_of_difference_conjugations p f Y R hR
    (difference_conjugation_of_atom p f Y b R hb hconj)
  apply top_unique
  rw [← hgen]
  apply Subgroup.closure_mono
  rintro _ ⟨t,rfl⟩
  exact ⟨b t,t,hRb t,by rw [hYb]; simp⟩

end AtomConjugation

section LocalSupportLaws

variable {I D M H : Type*} [DecidableEq I] [Group D] [Group M] [Group H]

def LocalCentralLaw (L : Finset I → Subgroup D) (v : D →* M) (f : D →* H)
    (S : Finset I) : Prop :=
  ∀ d ∈ L S, v d = 1 → ∀ e ∈ L S, Commute (f d) (f e)

theorem local_null_is_central (L : Finset I → Subgroup D) (hmono : Monotone L)
    (v : D →* M) (f : D →* H)
    (hgen : Subgroup.closure {h : H | ∃ T : Finset I, T.card ≤ 5 ∧
      ∃ e ∈ L T, h = f e} = ⊤)
    (hlaw : ∀ T : Finset I, T.card ≤ 15 → LocalCentralLaw L v f T)
    {S : Finset I} (hS : S.card ≤ 10) {d : D} (hd : d ∈ L S) (hv : v d = 1) :
    f d ∈ Subgroup.center H := by
  rw [← Subgroup.centralizer_univ, ← Subgroup.coe_top, ← hgen,
    Subgroup.centralizer_closure]
  apply Subgroup.mem_centralizer_iff.mpr
  rintro z ⟨T,hT,e,he,rfl⟩
  have hc : (S ∪ T).card ≤ 15 := (Finset.card_union_le S T).trans (by omega)
  exact (hlaw (S ∪ T) hc d (hmono Finset.subset_union_left hd) hv e
    (hmono Finset.subset_union_right he)).symm.eq

theorem local_equality_mod_center (L : Finset I → Subgroup D) (hmono : Monotone L)
    (v : D →* M) (f : D →* H)
    (hgen : Subgroup.closure {h : H | ∃ T : Finset I, T.card ≤ 5 ∧
      ∃ e ∈ L T, h = f e} = ⊤)
    (hlaw : ∀ T : Finset I, T.card ≤ 15 → LocalCentralLaw L v f T)
    {S : Finset I} (hS : S.card ≤ 10) {d e : D}
    (hd : d ∈ L S) (he : e ∈ L S) (hv : v d = v e) :
    QuotientGroup.mk' (Subgroup.center H) (f d) =
      QuotientGroup.mk' (Subgroup.center H) (f e) := by
  have hz := local_null_is_central L hmono v f hgen hlaw hS
    ((L S).mul_mem hd ((L S).inv_mem he)) (by simp [hv] : v (d * e⁻¹) = 1)
  have hh : f (d * e⁻¹) ∈ (QuotientGroup.mk' (Subgroup.center H)).ker := by
    rwa [QuotientGroup.ker_mk']
  have hh' : QuotientGroup.mk' (Subgroup.center H) (f (d * e⁻¹)) = 1 := hh
  simpa only [map_mul, map_inv, mul_inv_eq_one] using hh'

end LocalSupportLaws

section ReserveAtoms

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev SwapLabel (I : Type*) [DecidableEq I] :=
  {t : Equiv.Perm I // t.IsSwap}

noncomputable def reserveAtom (a t : SwapLabel I) : alternatingGroup I :=
  ⟨a.val * t.val, Equiv.Perm.mul_mem_alternatingGroup_of_isSwap a.property t.property⟩

omit [Fintype I] in
theorem swapLabel_inv (t : SwapLabel I) : t.val⁻¹ = t.val := by
  obtain ⟨i,j,_,h⟩ := t.property
  simp [h]

theorem reserveAtom_base (a : SwapLabel I) : reserveAtom a a = 1 := by
  apply Subtype.ext
  change a.val * a.val = 1
  nth_rw 1 [← swapLabel_inv a]
  exact inv_mul_cancel a.val

theorem reserveAtom_difference (a s t : SwapLabel I) :
    ((reserveAtom a s)⁻¹ * reserveAtom a t : alternatingGroup I).val = s.val * t.val := by
  change (a.val * s.val)⁻¹ * (a.val * t.val) = _
  calc
    _ = s.val⁻¹ * t.val := by group
    _ = _ := by rw [swapLabel_inv]

theorem reserveAtoms_generate (a : SwapLabel I) :
    Subgroup.closure (Set.range (reserveAtom a)) = ⊤ := by
  apply top_unique
  rw [← alternatingGroup.closure_isThreeCycles_eq_top]
  apply (Subgroup.closure_le _).mpr
  intro g hg
  obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0 < g.val.support.card by rw [hg.card_support]; omega)
  have hne : i ≠ g.val i := (Equiv.Perm.mem_support.mp hi).symm
  let s : SwapLabel I := ⟨Equiv.swap i (g.val i), i, g.val i, hne, rfl⟩
  let t : SwapLabel I := ⟨Equiv.swap (g.val i) (g.val (g.val i)),
    g.val i, g.val (g.val i), fun h => hne (g.val.injective h), rfl⟩
  have heq : g = (reserveAtom a s)⁻¹ * reserveAtom a t := by
    apply Subtype.ext
    rw [reserveAtom_difference]
    exact hg.eq_swap_mul_swap_iff_mem_support.mpr hi
  rw [heq]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨s,rfl⟩))
    (Subgroup.subset_closure ⟨t,rfl⟩)

def swapLabelConj (g : Equiv.Perm I) (t : SwapLabel I) : SwapLabel I := by
  refine ⟨g * t.val * g⁻¹, ?_⟩
  obtain ⟨i,j,hij,ht⟩ := t.property
  refine ⟨g i,g j,fun h => hij (g.injective h), ?_⟩
  rw [ht]
  rw [Equiv.mul_swap_eq_swap_mul, mul_inv_cancel_right]

end ReserveAtoms

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_ReserveAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ReserveAtomSupport

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def subtypeAlternatingHom (S : Finset I) :
    alternatingGroup S →* alternatingGroup I :=
  { toFun := fun g => ⟨Equiv.Perm.ofSubtype g.val, by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_ofSubtype]
      exact g.property⟩
    map_one' := Subtype.ext (map_one Equiv.Perm.ofSubtype)
    map_mul' := fun x y => Subtype.ext (map_mul Equiv.Perm.ofSubtype x.val y.val) }

theorem swapLabel_subtype (S : Finset I) (a : SwapLabel I) (ha : a.val.support ⊆ S) :
    ∃ b : SwapLabel S, Equiv.Perm.ofSubtype b.val = a.val := by
  obtain ⟨i,j,hij,heq⟩ := a.property
  have hi : i ∈ S := ha (by rw [heq, Equiv.Perm.support_swap hij]; simp)
  have hj : j ∈ S := ha (by rw [heq, Equiv.Perm.support_swap hij]; simp)
  let b : SwapLabel S := ⟨Equiv.swap ⟨i,hi⟩ ⟨j,hj⟩,
    ⟨i,hi⟩,⟨j,hj⟩,fun h => hij (congrArg Subtype.val h), rfl⟩
  exact ⟨b,by simp only [b, Equiv.Perm.ofSubtype_swap_eq,heq]⟩

theorem supported_reserveAtoms_generate (S : Finset I) (a : SwapLabel I)
    (ha : a.val.support ⊆ S) (g : alternatingGroup I) (hg : g.val.support ⊆ S) :
    g ∈ Subgroup.closure {h : alternatingGroup I | ∃ t : SwapLabel I,
      t.val.support ⊆ S ∧ h = reserveAtom a t} := by
  classical
  let K := Subgroup.closure {h : alternatingGroup I | ∃ t : SwapLabel I,
      t.val.support ⊆ S ∧ h = reserveAtom a t}
  obtain ⟨aS,haS⟩ := swapLabel_subtype S a ha
  obtain ⟨gS,hgS⟩ := Equiv.Perm.mem_range_ofSubtype_iff.mpr hg
  have hgS' : gS ∈ alternatingGroup S := by
    rw [Equiv.Perm.mem_alternatingGroup, ← Equiv.Perm.sign_ofSubtype, hgS]
    exact g.property
  have hle : Subgroup.closure (Set.range (reserveAtom aS)) ≤
      K.comap (subtypeAlternatingHom S) := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨t,rfl⟩
    let t' : SwapLabel I := ⟨Equiv.Perm.ofSubtype t.val,t.property.of_subtype_isSwap⟩
    apply Subgroup.subset_closure
    refine ⟨t',?_,?_⟩
    · exact Equiv.Perm.mem_range_ofSubtype_iff.mp ⟨t.val,rfl⟩
    · apply Subtype.ext
      change Equiv.Perm.ofSubtype (aS.val * t.val) = a.val * Equiv.Perm.ofSubtype t.val
      rw [map_mul,haS]
  have hm := hle (reserveAtoms_generate aS ▸
    Subgroup.mem_top (⟨gS,hgS'⟩ : alternatingGroup S))
  change subtypeAlternatingHom S ⟨gS,hgS'⟩ ∈ K at hm
  have heq : subtypeAlternatingHom S ⟨gS,hgS'⟩ = g := Subtype.ext hgS
  rwa [heq] at hm

end ReserveAtomSupport

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PrimitiveWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PrimitiveWords

abbrev SmallAlt (m : ℕ) := {s : alternatingGroup (Fin (m+1)) // s.val.support.card ≤ 5}

theorem smallAlt_free_surjective (m : ℕ) :
    Function.Surjective (FreeGroup.lift (fun s : SmallAlt m => s.val)) := by
  apply MonoidHom.range_eq_top.mp
  rw [FreeGroup.range_lift_eq_closure]
  apply top_unique
  rw [← alternatingGroup.closure_isThreeCycles_eq_top]
  apply Subgroup.closure_mono
  intro s hs
  exact ⟨⟨s,by rw [hs.card_support]; omega⟩,rfl⟩

noncomputable def smallAltWord {m : ℕ} (s : alternatingGroup (Fin (m+1))) :
    FreeGroup (SmallAlt m) := (smallAlt_free_surjective m s).choose

@[simp] theorem smallAltWord_eval {m : ℕ} (s : alternatingGroup (Fin (m+1))) :
    FreeGroup.lift (fun t : SmallAlt m => t.val) (smallAltWord s) = s :=
  (smallAlt_free_surjective m s).choose_spec

end PrimitiveWords

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_CoordinateWindowTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section CoordinateWindowTarget

def coordinateTestIndex (j : Fin 2) : Fin 5 := ⟨j.val+1,by omega⟩

end CoordinateWindowTarget

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_PrimitiveCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section FamilyCovariance

variable {ι E H Q : Type*} [Group E] [Group H] [Group Q]

theorem copyFamilyEval_comp (F : ι → E →* H) (f : H →* Q) :
    copyFamilyEval (fun i => f.comp (F i)) = f.comp (copyFamilyEval F) := by
  apply FreeGroup.ext_hom
  rintro ⟨i,s⟩
  simp

theorem copyFamilyEval_reindex_range {κ : Type*} (F : ι → E →* H) (v : κ → ι) :
    (copyFamilyEval (F ∘ v)).range ≤ (copyFamilyEval F).range := by
  rw [copyFamilyEval_range,copyFamilyEval_range]
  apply iSup_le
  intro i
  exact le_iSup (fun j => (F j).range) (v i)

end FamilyCovariance

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_AssignmentAtoms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section AssignmentAtoms

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [DecidableEq Ω]

noncomputable def assignmentAtom (a : SwapLabel I) (t : Ω × SwapLabel I) :
    Ω → alternatingGroup I := Pi.mulSingle (M := fun _ : Ω => alternatingGroup I) t.1 (reserveAtom a t.2)

theorem supported_assignmentAtoms_generate [Finite Ω] (S : Finset I) (a : SwapLabel I)
    (ha : a.val.support ⊆ S) (g : Ω → alternatingGroup I)
    (hg : ∀ ω, (g ω).val.support ⊆ S) :
    g ∈ Subgroup.closure (Set.range (fun t : {t : Ω × SwapLabel I // t.2.val.support ⊆ S} =>
      assignmentAtom a t.val)) := by
  let K := Subgroup.closure (Set.range
    (fun t : {t : Ω × SwapLabel I // t.2.val.support ⊆ S} => assignmentAtom a t.val))
  apply Subgroup.pi_mem_of_mulSingle_mem g
  intro ω
  have hle : Subgroup.closure {h : alternatingGroup I | ∃ t : SwapLabel I,
      t.val.support ⊆ S ∧ h = reserveAtom a t} ≤
      K.comap (MonoidHom.mulSingle (fun _ : Ω => alternatingGroup I) ω) := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨t,ht,rfl⟩
    exact Subgroup.subset_closure ⟨⟨(ω,t),ht⟩,rfl⟩
  exact hle (supported_reserveAtoms_generate S a ha (g ω) (hg ω))

theorem assignmentAtoms_generate [Finite Ω] (a : SwapLabel I) :
    Subgroup.closure (Set.range (assignmentAtom (Ω := Ω) a)) = ⊤ := by
  apply top_unique
  intro g _
  have h := supported_assignmentAtoms_generate Finset.univ a (Finset.subset_univ _) g
    (fun _ => Finset.subset_univ _)
  have hsub : Set.range (fun t : {t : Ω × SwapLabel I // t.2.val.support ⊆ Finset.univ} =>
      assignmentAtom a t.val) ⊆ Set.range (assignmentAtom a) := by
    rintro _ ⟨t,rfl⟩
    exact ⟨t.val,rfl⟩
  exact Subgroup.closure_mono hsub h

instance assignmentSwapMulAction : MulAction (Ω → alternatingGroup I) (Ω × SwapLabel I) where
  smul g t := (t.1, swapLabelConj (g t.1).val t.2)
  one_smul t := by
    apply Prod.ext rfl
    apply Subtype.ext
    change 1 * t.2.val * 1⁻¹ = t.2.val
    simp
  mul_smul g h t := by
    apply Prod.ext rfl
    apply Subtype.ext
    change (g t.1).val * (h t.1).val * t.2.val *
      ((g t.1).val * (h t.1).val)⁻¹ =
      (g t.1).val * ((h t.1).val * t.2.val * (h t.1).val⁻¹) * (g t.1).val⁻¹
    group

theorem assignmentSwap_base_atom (a : SwapLabel I) (ω : Ω) :
    assignmentAtom a (ω,a) = 1 := by
  simp [assignmentAtom,reserveAtom_base]

theorem assignmentAtom_conjugation (a : SwapLabel I) (g : Ω → alternatingGroup I)
    (t : Ω × SwapLabel I) :
    g * assignmentAtom a t * g⁻¹ =
      (assignmentAtom a (g • (t.1,a)))⁻¹ * assignmentAtom a (g • t) := by
  funext ω
  by_cases hω : ω = t.1
  · subst ω
    change g t.1 * Pi.mulSingle (M := fun _ : Ω => alternatingGroup I) t.1 (reserveAtom a t.2) t.1 * (g t.1)⁻¹ =
      (Pi.mulSingle (M := fun _ : Ω => alternatingGroup I) t.1 (reserveAtom a (swapLabelConj (g t.1).val a)) t.1)⁻¹ *
        Pi.mulSingle (M := fun _ : Ω => alternatingGroup I) t.1 (reserveAtom a (swapLabelConj (g t.1).val t.2)) t.1
    simp only [Pi.mulSingle_eq_same]
    apply Subtype.ext
    rw [reserveAtom_difference]
    change (g t.1).val * (a.val * t.2.val) * (g t.1).val⁻¹ =
      ((g t.1).val * a.val * (g t.1).val⁻¹) *
        ((g t.1).val * t.2.val * (g t.1).val⁻¹)
    group
  · change g ω * Pi.mulSingle (M := fun _ : Ω => alternatingGroup I) t.1 (reserveAtom a t.2) ω * (g ω)⁻¹ =
      (Pi.mulSingle (M := fun _ : Ω => alternatingGroup I) t.1 (reserveAtom a (swapLabelConj (g t.1).val a)) ω)⁻¹ *
        Pi.mulSingle (M := fun _ : Ω => alternatingGroup I) t.1 (reserveAtom a (swapLabelConj (g t.1).val t.2)) ω
    simp [Pi.mulSingle_eq_of_ne hω]

end AssignmentAtoms

section SupportedAtomWords

variable {J K D Q : Type*} [Group D] [Group Q]

theorem hom_comp_freeLift (q : D →* Q) (u : J → D) :
    q.comp (FreeGroup.lift u) = FreeGroup.lift (fun j => q (u j)) := by
  apply FreeGroup.ext_hom
  intro j
  simp

theorem freeLift_comp_map (u : J → D) (b : K → J) :
    (FreeGroup.lift u).comp (FreeGroup.map b) = FreeGroup.lift (fun k => u (b k)) := by
  apply FreeGroup.ext_hom
  intro k
  simp

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [DecidableEq Ω] [Finite Ω]

theorem supported_atom_word (L : Finset I → Subgroup D) (hmono : Monotone L)
    (E : Finset I) (a : SwapLabel I) (ha : a.val.support ⊆ E)
    (u : Ω × SwapLabel I → D)
    (hu : ∀ t, u t ∈ L (E ∪ t.2.val.support))
    (S : Finset I) (hES : E ⊆ S) (g : Ω → alternatingGroup I)
    (hg : ∀ ω, (g ω).val.support ⊆ S) :
    ∃ w : FreeGroup (Ω × SwapLabel I),
      FreeGroup.lift (assignmentAtom a) w = g ∧ FreeGroup.lift u w ∈ L S := by
  let T := {t : Ω × SwapLabel I // t.2.val.support ⊆ S}
  have hm : g ∈ (FreeGroup.lift (fun t : T => assignmentAtom a t.val)).range := by
    rw [FreeGroup.range_lift_eq_closure]
    exact supported_assignmentAtoms_generate S a (ha.trans hES) g hg
  obtain ⟨w,hw⟩ := hm
  have hle : (FreeGroup.lift (fun t : T => u t.val)).range ≤ L S := by
    rw [FreeGroup.range_lift_eq_closure]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨t,rfl⟩
    exact hmono (Finset.union_subset hES t.property) (hu t.val)
  refine ⟨FreeGroup.map (Subtype.val : T → Ω × SwapLabel I) w, ?_, ?_⟩
  · change ((FreeGroup.lift (assignmentAtom a)).comp (FreeGroup.map Subtype.val)) w = g
    rw [freeLift_comp_map]
    exact hw
  · change ((FreeGroup.lift u).comp (FreeGroup.map Subtype.val)) w ∈ L S
    rw [freeLift_comp_map]
    exact hle ⟨w,rfl⟩

end SupportedAtomWords

section AtomSupportBounds

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [DecidableEq Ω]

theorem swapLabel_card_support (t : SwapLabel I) : t.val.support.card = 2 :=
  Equiv.Perm.card_support_eq_two.mpr t.property

theorem swapLabelConj_support (g : Equiv.Perm I) (t : SwapLabel I) (S : Finset I)
    (hg : g.support ⊆ S) (ht : t.val.support ⊆ S) :
    (swapLabelConj g t).val.support ⊆ S := by
  change (g * t.val * g⁻¹).support ⊆ S
  apply (Equiv.Perm.support_mul_le _ _).trans
  apply Finset.union_subset
  · exact (Equiv.Perm.support_mul_le _ _).trans (Finset.union_subset hg ht)
  · simpa only [Equiv.Perm.support_inv] using hg

theorem assignmentAtom_support (a : SwapLabel I) (t : Ω × SwapLabel I) (ω : Ω) :
    ((assignmentAtom a t) ω).val.support ⊆ a.val.support ∪ t.2.val.support := by
  by_cases h : ω = t.1
  · subst ω
    change (Pi.mulSingle (M := fun _ : Ω => alternatingGroup I) t.1
      (reserveAtom a t.2) t.1).val.support ⊆ _
    rw [Pi.mulSingle_eq_same]
    exact Equiv.Perm.support_mul_le a.val t.2.val
  · simp only [assignmentAtom,Pi.mulSingle_eq_of_ne h,OneMemClass.coe_one,
      Equiv.Perm.support_one,Finset.empty_subset]

theorem atom_conjugation_support (E : Finset I) (a : SwapLabel I)
    (ha : a.val.support ⊆ E) (s t : Ω × SwapLabel I) :
    ((assignmentAtom a s • (t.1,a)).2).val.support ⊆
        E ∪ s.2.val.support ∪ t.2.val.support ∧
    ((assignmentAtom a s • t).2).val.support ⊆
        E ∪ s.2.val.support ∪ t.2.val.support := by
  have hgs : ((assignmentAtom a s) t.1).val.support ⊆
      E ∪ s.2.val.support ∪ t.2.val.support :=
    (assignmentAtom_support a s t.1).trans
      ((Finset.union_subset_union_left ha).trans Finset.subset_union_left)
  constructor
  · exact swapLabelConj_support _ _ _ hgs
      (ha.trans (Finset.subset_union_left.trans Finset.subset_union_left))
  · exact swapLabelConj_support _ _ _ hgs Finset.subset_union_right

variable {D : Type*} [Group D]

theorem exists_supported_atom_words (L : Finset I → Subgroup D)
    (v : D →* (Ω → alternatingGroup I)) (E : Finset I) (hE : E.card = 5)
    (a : SwapLabel I) (ha : a.val.support ⊆ E)
    (hcomplete : ∀ S : Finset I, 5 ≤ S.card → S.card ≤ 7 → ∀ g : Ω → alternatingGroup I,
      (∀ ω, (g ω).val.support ⊆ S) → ∃ d ∈ L S, v d = g) :
    ∃ u : Ω × SwapLabel I → D, ∀ t,
      u t ∈ L (E ∪ t.2.val.support) ∧ v (u t) = assignmentAtom a t := by
  classical
  have h (t : Ω × SwapLabel I) : ∃ d ∈ L (E ∪ t.2.val.support),
      v d = assignmentAtom a t := by
    apply hcomplete (E ∪ t.2.val.support)
    · rw [← hE]
      exact Finset.card_le_card Finset.subset_union_left
    · exact (Finset.card_union_le _ _).trans (by rw [hE,swapLabel_card_support])
    · intro ω
      exact (assignmentAtom_support a t ω).trans (Finset.union_subset_union_left ha)
  choose u hu hv using h
  exact ⟨u,fun t => ⟨hu t,hv t⟩⟩

end AtomSupportBounds

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_LocalAtomComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section LocalAtomComparison

variable {I Ω D H : Type*} [Fintype I] [DecidableEq I] [DecidableEq Ω] [Finite Ω]
    [Group D] [Group H]

theorem local_atom_comparison (L : Finset I → Subgroup D) (hmono : Monotone L)
    (v : D →* (Ω → alternatingGroup I)) (f : D →* H)
    (hgen : Subgroup.closure {h : H | ∃ T : Finset I, T.card ≤ 5 ∧
      ∃ e ∈ L T, h = f e} = ⊤)
    (hlaw : ∀ T : Finset I, T.card ≤ 15 → LocalCentralLaw L v f T)
    (E : Finset I) (hE : E.card = 5) (a : SwapLabel I) (ha : a.val.support ⊆ E)
    (u : Ω × SwapLabel I → D)
    (hu : ∀ t, u t ∈ L (E ∪ t.2.val.support))
    (huv : ∀ t, v (u t) = assignmentAtom a t)
    (S : Finset I) (hS : S.card ≤ 5) (d : D) (hd : d ∈ L S)
    (hvd : ∀ ω, ((v d) ω).val.support ⊆ S) :
    ∃ w : FreeGroup (Ω × SwapLabel I),
      FreeGroup.lift (assignmentAtom a) w = v d ∧
      QuotientGroup.mk' (Subgroup.center H) (f (FreeGroup.lift u w)) =
        QuotientGroup.mk' (Subgroup.center H) (f d) := by
  obtain ⟨w,hw,hwu⟩ := supported_atom_word L hmono E a ha u hu (E ∪ S)
    Finset.subset_union_left (v d) (fun ω => (hvd ω).trans Finset.subset_union_right)
  refine ⟨w,hw,?_⟩
  have hvw : v (FreeGroup.lift u w) = v d := by
    change (v.comp (FreeGroup.lift u)) w = v d
    rw [hom_comp_freeLift]
    simpa only [huv] using hw
  have hc : (E ∪ S).card ≤ 10 :=
    (Finset.card_union_le _ _).trans (by omega)
  exact local_equality_mod_center L hmono v f hgen hlaw hc hwu
    (hmono Finset.subset_union_right hd) hvw

theorem local_atoms_generate_center_quotient (L : Finset I → Subgroup D)
    (hmono : Monotone L) (v : D →* (Ω → alternatingGroup I)) (f : D →* H)
    (hgen : Subgroup.closure {h : H | ∃ T : Finset I, T.card ≤ 5 ∧
      ∃ e ∈ L T, h = f e} = ⊤)
    (hlaw : ∀ T : Finset I, T.card ≤ 15 → LocalCentralLaw L v f T)
    (hsupp : ∀ S : Finset I, ∀ d ∈ L S, ∀ ω, ((v d) ω).val.support ⊆ S)
    (E : Finset I) (hE : E.card = 5) (a : SwapLabel I) (ha : a.val.support ⊆ E)
    (u : Ω × SwapLabel I → D)
    (hu : ∀ t, u t ∈ L (E ∪ t.2.val.support))
    (huv : ∀ t, v (u t) = assignmentAtom a t) :
    Subgroup.closure (Set.range (fun t => QuotientGroup.mk' (Subgroup.center H) (f (u t)))) = ⊤ := by
  let q := QuotientGroup.mk' (Subgroup.center H)
  let Y := fun t => q (f (u t))
  rw [← FreeGroup.range_lift_eq_closure]
  apply top_unique
  have hle : (⊤ : Subgroup H) ≤ (FreeGroup.lift Y).range.comap q := by
    rw [← hgen]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨S,hS,d,hd,rfl⟩
    obtain ⟨w,_,hw⟩ := local_atom_comparison L hmono v f hgen hlaw E hE a ha u hu huv
      S hS d hd (hsupp S d hd)
    refine ⟨w,?_⟩
    have heq := DFunLike.congr_fun (hom_comp_freeLift (q.comp f) u) w
    exact heq.symm.trans hw
  intro z _
  obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center H) z
  exact hle (Subgroup.mem_top h)

end LocalAtomComparison

section LocalAtomConjugation

variable {I Ω D H : Type*} [Fintype I] [DecidableEq I] [DecidableEq Ω]
    [Group D] [Group H]

theorem local_atom_conjugation (L : Finset I → Subgroup D) (hmono : Monotone L)
    (v : D →* (Ω → alternatingGroup I)) (f : D →* H)
    (hgen : Subgroup.closure {h : H | ∃ T : Finset I, T.card ≤ 5 ∧
      ∃ e ∈ L T, h = f e} = ⊤)
    (hlaw : ∀ T : Finset I, T.card ≤ 15 → LocalCentralLaw L v f T)
    (E : Finset I) (hE : E.card = 5) (a : SwapLabel I) (ha : a.val.support ⊆ E)
    (u : Ω × SwapLabel I → D)
    (hu : ∀ t, u t ∈ L (E ∪ t.2.val.support))
    (huv : ∀ t, v (u t) = assignmentAtom a t) (s t : Ω × SwapLabel I) :
    let Y := fun t => QuotientGroup.mk' (Subgroup.center H) (f (u t))
    Y s * Y t * (Y s)⁻¹ =
      (Y (assignmentAtom a s • (t.1,a)))⁻¹ * Y (assignmentAtom a s • t) := by
  dsimp only
  let S := E ∪ s.2.val.support ∪ t.2.val.support
  have hES : E ⊆ S := Finset.subset_union_left.trans Finset.subset_union_left
  have hs : u s ∈ L S := hmono Finset.subset_union_left (hu s)
  have ht : u t ∈ L S := hmono
    (Finset.union_subset hES Finset.subset_union_right) (hu t)
  have hc := atom_conjugation_support E a ha s t
  have hb : u (assignmentAtom a s • (t.1,a)) ∈ L S :=
    hmono (Finset.union_subset hES hc.1) (hu _)
  have hd : u (assignmentAtom a s • t) ∈ L S :=
    hmono (Finset.union_subset hES hc.2) (hu _)
  have hcard : S.card ≤ 10 := by
    have h1 := Finset.card_union_le E s.2.val.support
    have h2 := Finset.card_union_le (E ∪ s.2.val.support) t.2.val.support
    rw [swapLabel_card_support] at h1 h2
    dsimp [S]
    omega
  have heq : v (u s * u t * (u s)⁻¹) =
      v ((u (assignmentAtom a s • (t.1,a)))⁻¹ * u (assignmentAtom a s • t)) := by
    simp only [map_mul,map_inv,huv]
    exact assignmentAtom_conjugation a (assignmentAtom a s) t
  have h := local_equality_mod_center L hmono v f hgen hlaw hcard
    ((L S).mul_mem ((L S).mul_mem hs ht) ((L S).inv_mem hs))
    ((L S).mul_mem ((L S).inv_mem hb) hd) heq
  simpa only [map_mul,map_inv] using h

theorem local_atom_base (L : Finset I → Subgroup D) (hmono : Monotone L)
    (v : D →* (Ω → alternatingGroup I)) (f : D →* H)
    (hgen : Subgroup.closure {h : H | ∃ T : Finset I, T.card ≤ 5 ∧
      ∃ e ∈ L T, h = f e} = ⊤)
    (hlaw : ∀ T : Finset I, T.card ≤ 15 → LocalCentralLaw L v f T)
    (E : Finset I) (hE : E.card = 5) (a : SwapLabel I)
    (u : Ω × SwapLabel I → D)
    (hu : ∀ t, u t ∈ L (E ∪ t.2.val.support))
    (huv : ∀ t, v (u t) = assignmentAtom a t) (ω : Ω) :
    QuotientGroup.mk' (Subgroup.center H) (f (u (ω,a))) = 1 := by
  have hc : (E ∪ a.val.support).card ≤ 10 :=
    (Finset.card_union_le _ _).trans (by rw [hE,swapLabel_card_support]; omega)
  have heq : v (u (ω,a)) = v 1 := by rw [huv,assignmentSwap_base_atom,map_one]
  simpa only [map_one] using local_equality_mod_center L hmono v f hgen hlaw hc
    (hu (ω,a)) (L (E ∪ a.val.support)).one_mem heq

end LocalAtomConjugation

section SmallSupportAssignment

variable {I Ω D H : Type*} [Fintype I] [DecidableEq I] [DecidableEq Ω] [Finite Ω]
    [Group D] [Group H] [Group.IsPerfect H]

theorem small_support_assignment_law_with_atoms
    (L : Finset I → Subgroup D) (hmono : Monotone L)
    (v : D →* (Ω → alternatingGroup I)) (f : D →* H) (hf : Function.Surjective f)
    (hDgen : Subgroup.closure {d : D | ∃ S : Finset I, S.card ≤ 5 ∧ d ∈ L S} = ⊤)
    (hsupp : ∀ S : Finset I, ∀ d ∈ L S, ∀ ω, ((v d) ω).val.support ⊆ S)
    (hlaw : ∀ T : Finset I, T.card ≤ 15 → LocalCentralLaw L v f T)
    (E : Finset I) (hE : E.card = 5) (a : SwapLabel I) (ha : a.val.support ⊆ E)
    (u : Ω × SwapLabel I → D)
    (hu : ∀ t, u t ∈ L (E ∪ t.2.val.support))
    (huv : ∀ t, v (u t) = assignmentAtom a t) : HasCentralLaw v f := by
  classical
  have hgen : Subgroup.closure {h : H | ∃ T : Finset I, T.card ≤ 5 ∧
      ∃ e ∈ L T, h = f e} = ⊤ := by
    have hi : f '' {d : D | ∃ S : Finset I, S.card ≤ 5 ∧ d ∈ L S} =
        {h : H | ∃ T : Finset I, T.card ≤ 5 ∧ ∃ e ∈ L T, h = f e} := by
      ext h
      constructor
      · rintro ⟨d,⟨S,hS,hd⟩,rfl⟩
        exact ⟨S,hS,d,hd,rfl⟩
      · rintro ⟨S,hS,d,hd,rfl⟩
        exact ⟨d,⟨S,hS,hd⟩,rfl⟩
    rw [← hi, ← MonoidHom.map_closure, hDgen, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hf]
  let Q := H ⧸ Subgroup.center H
  let q : H →* Q := QuotientGroup.mk' (Subgroup.center H)
  let P := FreeGroup.lift (assignmentAtom (Ω := Ω) a)
  let Y := fun t => q (f (u t))
  have hgenY : Subgroup.closure (Set.range Y) = ⊤ :=
    local_atoms_generate_center_quotient L hmono v f hgen hlaw hsupp E hE a ha u hu huv
  have hcentral : HasCentralLaw P (FreeGroup.lift Y) := by
    apply centralLaw_of_atom_conjugations (assignmentAtom a) Y Y (fun t => (t.1,a))
      (fun t s => t.1 = s.1)
    · intro t s hts
      exact Prod.ext hts rfl
    · intro t
      rfl
    · intro t
      exact local_atom_base L hmono v f hgen hlaw E hE a u hu huv t.1
    · intro g t s hts
      exact hts
    · intro s t
      exact local_atom_conjugation L hmono v f hgen hlaw E hE a ha u hu huv s t
    · exact hgenY
  have hker : P.ker ≤ (FreeGroup.lift Y).ker := by
    intro w hw
    have hz := (hasCentralLaw_iff P (FreeGroup.lift Y)).mp hcentral w hw
    change FreeGroup.lift Y w ∈ Subgroup.center (H ⧸ Subgroup.center H) at hz
    rw [perfect_center_quotient] at hz
    exact hz
  have hP : Function.Surjective P :=
    FreeGroup.lift_surjective_iff_closure_range_eq_top.mpr (assignmentAtoms_generate a)
  let φ : (Ω → alternatingGroup I) →* Q := P.liftOfSurjective hP ⟨_,hker⟩
  have hφ : φ.comp P = FreeGroup.lift Y := P.liftOfRightInverse_comp _ _ _
  have hmap : φ.comp v = q.comp f := by
    apply MonoidHom.eq_of_eqOn_dense hDgen
    rintro d ⟨S,hS,hd⟩
    obtain ⟨w,hw,hq⟩ := local_atom_comparison L hmono v f hgen hlaw E hE a ha u hu huv
      S hS d hd (hsupp S d hd)
    change φ (v d) = q (f d)
    have hwp : P w = v d := hw
    calc
      φ (v d) = φ (P w) := congrArg φ hwp.symm
      _ = FreeGroup.lift Y w := DFunLike.congr_fun hφ w
      _ = q (f (FreeGroup.lift u w)) :=
        (DFunLike.congr_fun (hom_comp_freeLift (q.comp f) u) w).symm
      _ = q (f d) := hq
  rw [hasCentralLaw_iff]
  intro d hd
  have he := DFunLike.congr_fun hmap d
  change φ (v d) = q (f d) at he
  rw [hd,map_one] at he
  have hk : f d ∈ (QuotientGroup.mk' (Subgroup.center H)).ker := he.symm
  rwa [QuotientGroup.ker_mk'] at hk

theorem small_support_assignment_law
    (L : Finset I → Subgroup D) (hmono : Monotone L)
    (v : D →* (Ω → alternatingGroup I)) (f : D →* H) (hf : Function.Surjective f)
    (hDgen : Subgroup.closure {d : D | ∃ S : Finset I, S.card ≤ 5 ∧ d ∈ L S} = ⊤)
    (hsupp : ∀ S : Finset I, ∀ d ∈ L S, ∀ ω, ((v d) ω).val.support ⊆ S)
    (hlaw : ∀ T : Finset I, T.card ≤ 15 → LocalCentralLaw L v f T)
    (E : Finset I) (hE : E.card = 5) (a : SwapLabel I) (ha : a.val.support ⊆ E)
    (hcomplete : ∀ S : Finset I, 5 ≤ S.card → S.card ≤ 7 → ∀ g : Ω → alternatingGroup I,
      (∀ ω, (g ω).val.support ⊆ S) → ∃ d ∈ L S, v d = g) : HasCentralLaw v f := by
  obtain ⟨u,hu⟩ := exists_supported_atom_words L v E hE a ha hcomplete
  exact small_support_assignment_law_with_atoms L hmono v f hf hDgen hsupp hlaw E hE a ha u
    (fun t => (hu t).1) (fun t => (hu t).2)

end SmallSupportAssignment

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PrimitiveTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ActualPrimitiveTable

variable {a m M : ℕ}
  {hm : 2 ≤ m}
  {ι : Type*}
  [Finite ι]

theorem subtypeAlternatingHom_injective {X : Type*} [Fintype X] [DecidableEq X]
    (I : Finset X) : Function.Injective (subtypeAlternatingHom I) := by
  intro s t h
  apply Subtype.ext
  exact Equiv.Perm.ofSubtype_injective (congrArg Subtype.val h)

noncomputable def tableAlphabetHom (I : Finset (Fin (m+1))) {Ω : Type*} :
    (Ω → alternatingGroup I) →* (Ω → alternatingGroup (Fin (m+1))) where
  toFun s ω := subtypeAlternatingHom I (s ω)
  map_one' := by funext ω; exact map_one _
  map_mul' s t := by funext ω; exact map_mul _ _ _

theorem tableAlphabetHom_injective (I : Finset (Fin (m+1))) {Ω : Type*} :
    Function.Injective (tableAlphabetHom (Ω := Ω) I) := by
  intro s t h
  funext ω
  exact subtypeAlternatingHom_injective I (congrFun h ω)

end ActualPrimitiveTable

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ResolvedBoolean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ResolvedBoolean

variable {X ι : Type*}

def ResolvedBy (U : ι → Set X) (V : Set X) : Prop :=
  ∀ x y, (∀ i, x ∈ U i ↔ y ∈ U i) → (x ∈ V ↔ y ∈ V)

def resolvedAlgebra (U : ι → Set X) : BooleanSubalgebra (Set X) where
  carrier := {V | ResolvedBy U V}
  supClosed' := by
    intro V hV W hW x y h
    exact or_congr (hV x y h) (hW x y h)
  infClosed' := by
    intro V hV W hW x y h
    exact and_congr (hV x y h) (hW x y h)
  compl_mem' := by
    intro V hV x y h
    exact not_congr (hV x y h)
  bot_mem' := by intro x y h; rfl

theorem resolved_test (U : ι → Set X) (i : ι) : U i ∈ resolvedAlgebra U := by
  intro x y h
  exact h i

end ResolvedBoolean

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SectorControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section AlphabetInclusion

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem subtypeAlternatingHom_mem_range (I : Finset α) (s : alternatingGroup α) :
    s ∈ (subtypeAlternatingHom I).range ↔ s.val.support ⊆ I := by
  constructor
  · rintro ⟨t,rfl⟩
    exact Equiv.Perm.mem_range_ofSubtype_iff.mp ⟨t.val,rfl⟩
  · intro hs
    obtain ⟨t,ht⟩ := Equiv.Perm.mem_range_ofSubtype_iff.mpr hs
    have hat : t ∈ alternatingGroup I := by
      rw [Equiv.Perm.mem_alternatingGroup,← Equiv.Perm.sign_ofSubtype,ht]
      exact s.property
    exact ⟨⟨t,hat⟩,Subtype.ext ht⟩

noncomputable def subalphabetHom {I J : Finset α} (hIJ : I ⊆ J) :
    alternatingGroup I →* alternatingGroup J :=
  (MonoidHom.ofInjective (subtypeAlternatingHom_injective J)).symm.toMonoidHom.comp
    ((subtypeAlternatingHom I).codRestrict (subtypeAlternatingHom J).range
      (fun s => (subtypeAlternatingHom_mem_range J _).mpr
        ((subtypeAlternatingHom_mem_range I _).mp ⟨s,rfl⟩ |>.trans hIJ)))

@[simp] theorem subtypeAlternatingHom_comp {I J : Finset α} (hIJ : I ⊆ J) :
    (subtypeAlternatingHom J).comp (subalphabetHom hIJ) = subtypeAlternatingHom I := by
  apply MonoidHom.ext
  intro s
  exact MonoidHom.apply_ofInjective_symm (subtypeAlternatingHom_injective J) _

end AlphabetInclusion

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_WindowIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section EnlargedControl

theorem alphabetPerfect {α : Type*} [Fintype α] [DecidableEq α]
    (J : Finset α) (hJ : 5 ≤ J.card) : Group.IsPerfect (alternatingGroup J) :=
  ⟨commutator_alternatingGroup_eq_top (by simpa using hJ)⟩

end EnlargedControl

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_SmallSectorGeneration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SmallSectorGeneration

variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev FiveSubalphabet (J : Finset α) := {I : Finset α // I ⊆ J ∧ I.card = 5}

instance fiveSubalphabet_perfect (J : Finset α) (I : FiveSubalphabet J) :
    Group.IsPerfect (alternatingGroup I.val) := alphabetPerfect I.val (by rw [I.property.2])

theorem subalphabet_five_generate (J : Finset α) (hJ : 5 ≤ J.card) :
    (⨆ I : FiveSubalphabet J, (subalphabetHom I.property.1).range) = ⊤ := by
  apply top_unique
  rw [← alternatingGroup.closure_isThreeCycles_eq_top]
  apply (Subgroup.closure_le _).mpr
  intro g hg
  let σ := subtypeAlternatingHom J g
  have hs : σ.val.support ⊆ J := (subtypeAlternatingHom_mem_range J σ).mp ⟨g,rfl⟩
  have hc : σ.val.support.card = 3 := by
    change (Equiv.Perm.ofSubtype g.val).support.card = 3
    have hF : (Subtype.fintype (fun x : α => x ∈ J)) = (inferInstance : Fintype J) := Subsingleton.elim _ _
    rw [Equiv.Perm.support_ofSubtype,Finset.card_map,hF,hg.card_support]
  obtain ⟨I,hSI,hIJ,hI⟩ := Finset.exists_subsuperset_card_eq hs (by omega : σ.val.support.card ≤ 5) hJ
  obtain ⟨t,ht⟩ := (subtypeAlternatingHom_mem_range I σ).mpr hSI
  apply le_iSup (fun I : FiveSubalphabet J => (subalphabetHom I.property.1).range) ⟨I,hIJ,hI⟩
  refine ⟨t,?_⟩
  apply subtypeAlternatingHom_injective J
  exact (DFunLike.congr_fun (subtypeAlternatingHom_comp hIJ) t).trans ht

end SmallSectorGeneration

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SmallFamilyWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SmallFamilyWords

variable {α ι Ω H : Type*} [Fintype α] [DecidableEq α] [Group H]

abbrev FiveAlphabet (α : Type*) [Fintype α] [DecidableEq α] :=
  FiveSubalphabet (Finset.univ : Finset α)

abbrev SmallFamilyLabel (α ι : Type*) [Fintype α] [DecidableEq α] :=
  Σ I : FiveAlphabet α, Option ι × alternatingGroup I.val

abbrev SmallFamilyWord (α ι : Type*) [Fintype α] [DecidableEq α] :=
  FreeGroup (SmallFamilyLabel α ι)

noncomputable def smallFamilyEval
    (F : (I : FiveAlphabet α) → Option ι → alternatingGroup I.val →* H) :
    SmallFamilyWord α ι →* H := FreeGroup.lift (fun l => F l.1 l.2.1 l.2.2)

@[simp] theorem smallFamilyEval_of
    (F : (I : FiveAlphabet α) → Option ι → alternatingGroup I.val →* H)
    (I : FiveAlphabet α) (i : Option ι) (s : alternatingGroup I.val) :
    smallFamilyEval F (FreeGroup.of ⟨I,i,s⟩) = F I i s := FreeGroup.lift_apply_of

theorem smallFamilyEval_range
    (F : (I : FiveAlphabet α) → Option ι → alternatingGroup I.val →* H) :
    (smallFamilyEval F).range = ⨆ I, ⨆ i, (F I i).range := by
  rw [smallFamilyEval,FreeGroup.range_lift_eq_closure]
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨⟨I,i,s⟩,rfl⟩
    exact (le_iSup (fun I => ⨆ i, (F I i).range) I)
      ((le_iSup (fun i => (F I i).range) i) ⟨s,rfl⟩)
  · apply iSup_le
    intro I
    apply iSup_le
    rintro i x ⟨s,rfl⟩
    exact Subgroup.subset_closure ⟨⟨I,i,s⟩,rfl⟩

theorem smallFamilyEval_perfect
    (F : (I : FiveAlphabet α) → Option ι → alternatingGroup I.val →* H) :
    Group.IsPerfect (smallFamilyEval F).range := by
  rw [smallFamilyEval_range]
  let (I : FiveAlphabet α) (i : Option ι) : Group.IsPerfect (F I i).range :=
    Group.IsPerfect.range (F I i)
  let (I : FiveAlphabet α) : Group.IsPerfect ↥(⨆ i, (F I i).range) :=
    perfect_iSup (fun i => (F I i).range)
  exact perfect_iSup (fun I => ⨆ i, (F I i).range)

noncomputable def smallFamilyLocal (S : Finset α) : Subgroup (SmallFamilyWord α ι) :=
  Subgroup.closure {w | ∃ l : SmallFamilyLabel α ι, l.1.val ⊆ S ∧ w = FreeGroup.of l}

theorem smallFamilyLocal_mono : Monotone (smallFamilyLocal (α := α) (ι := ι)) := by
  intro S T hST
  apply Subgroup.closure_mono
  rintro w ⟨l,hl,rfl⟩
  exact ⟨l,hl.trans hST,rfl⟩

theorem smallFamilyLocal_of (l : SmallFamilyLabel α ι) {S : Finset α} (h : l.1.val ⊆ S) :
    FreeGroup.of l ∈ smallFamilyLocal (ι := ι) S :=
  Subgroup.subset_closure ⟨l,h,rfl⟩

theorem smallFamilyLocal_generate :
    Subgroup.closure {w : SmallFamilyWord α ι | ∃ S : Finset α,
      S.card ≤ 5 ∧ w ∈ smallFamilyLocal S} = ⊤ := by
  apply top_unique
  rw [← FreeGroup.closure_range_of]
  apply Subgroup.closure_mono
  rintro w ⟨l,rfl⟩
  exact ⟨l.1.val,by rw [l.1.property.2],smallFamilyLocal_of l (Finset.Subset.refl _)⟩

noncomputable def alphabetAssignment (I : Finset α) :
    (Ω → alternatingGroup I) →* (Ω → alternatingGroup α) where
  toFun g ω := subtypeAlternatingHom I (g ω)
  map_one' := by funext ω; exact map_one _
  map_mul' g h := by funext ω; exact map_mul _ _ _

theorem alphabetAssignment_support (I : Finset α) (g : Ω → alternatingGroup I) (ω : Ω) :
    ((alphabetAssignment I g) ω).val.support ⊆ I :=
  (subtypeAlternatingHom_mem_range I _).mp ⟨g ω,rfl⟩

theorem alphabetAssignment_range (I : Finset α) (g : Ω → alternatingGroup α) :
    g ∈ (alphabetAssignment (Ω := Ω) I).range ↔ ∀ ω, (g ω).val.support ⊆ I := by
  constructor
  · rintro ⟨g,rfl⟩
    exact alphabetAssignment_support I g
  · intro h
    choose f hf using fun ω => (subtypeAlternatingHom_mem_range I (g ω)).mpr (h ω)
    exact ⟨f,funext hf⟩

end SmallFamilyWords

section SmallFamilyComplete
variable {α ι Ω H : Type*} [Fintype α] [DecidableEq α] [Group H]

theorem smallFamilyLocal_map_le
    (F : (I : FiveAlphabet α) → Option ι → alternatingGroup I.val →* H)
    (S : Finset α) (K : Subgroup H)
    (h : ∀ I, I.val ⊆ S → ∀ i, (F I i).range ≤ K) :
    (smallFamilyLocal S).map (smallFamilyEval F) ≤ K := by
  apply (Subgroup.map_le_iff_le_comap).mpr
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨l,hl,rfl⟩
  exact h l.1 hl l.2.1 ⟨l.2.2,(FreeGroup.lift_apply_of).symm⟩

end SmallFamilyComplete

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_SmallFamilyGlobal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section GlobalPrimitiveTable

theorem exists_alphabet_balance {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (hS : S.card < Fintype.card α) : ∃ b, b ∉ S := by
  classical
  by_contra h
  push Not at h
  have he : S = Finset.univ := Finset.eq_univ_iff_forall.mpr h
  rw [he,Finset.card_univ] at hS
  exact (lt_irrefl _ hS)

noncomputable def smallAlphabetBalance {m : ℕ} (hlarge : 15 < m+1)
    (S : Finset (Fin (m+1))) (hS : S.card ≤ 15) : Fin (m+1) :=
  (exists_alphabet_balance S (by simpa using lt_of_le_of_lt hS hlarge)).choose

theorem smallAlphabetBalance_notMem {m : ℕ} (hlarge : 15 < m+1)
    (S : Finset (Fin (m+1))) (hS : S.card ≤ 15) :
    smallAlphabetBalance hlarge S hS ∉ S :=
  (exists_alphabet_balance S (by simpa using lt_of_le_of_lt hS hlarge)).choose_spec

end GlobalPrimitiveTable

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_EvaluationTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section EvaluationTable
variable {D H Q T : Type*} [Group D] [Group H] [Group Q] [Group T]

noncomputable def evaluationModel (q : H →* Q) (e : D →* H)
    (v : D →* T) (ρ : T →* Q) (hρ : Function.Injective ρ)
    (he : q.comp e = ρ.comp v) : e.range →* T :=
  e.rangeRestrict.liftOfSurjective e.rangeRestrict_surjective
    ⟨v,by
      intro w hw
      apply hρ
      have hh := DFunLike.congr_fun he w
      change q (e w) = ρ (v w) at hh
      have hw' : e w = 1 := congrArg Subtype.val hw
      rw [hw',map_one] at hh
      simpa only [map_one] using hh.symm⟩

theorem evaluationModel_comp (q : H →* Q) (e : D →* H)
    (v : D →* T) (ρ : T →* Q) (hρ : Function.Injective ρ)
    (he : q.comp e = ρ.comp v) :
    (evaluationModel q e v ρ hρ he).comp e.rangeRestrict = v :=
  e.rangeRestrict.liftOfRightInverse_comp _ _ _

theorem evaluationModel_projection (q : H →* Q) (e : D →* H)
    (v : D →* T) (ρ : T →* Q) (hρ : Function.Injective ρ)
    (he : q.comp e = ρ.comp v) :
    q.comp e.range.subtype = ρ.comp (evaluationModel q e v ρ hρ he) := by
  apply MonoidHom.ext
  intro x
  obtain ⟨w,rfl⟩ := e.rangeRestrict_surjective x
  have hh := DFunLike.congr_fun (evaluationModel_comp q e v ρ hρ he) w
  change evaluationModel q e v ρ hρ he (e.rangeRestrict w) = v w at hh
  simp only [MonoidHom.comp_apply,hh]
  exact DFunLike.congr_fun he w

end EvaluationTable

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FullAlphabetGeneration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FullAlphabetGeneration
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem five_alphabet_generate (hα : 5 ≤ Fintype.card α) :
    (⨆ I : FiveAlphabet α, (subtypeAlternatingHom I.val).range) = ⊤ := by
  apply top_unique
  rw [← alternatingGroup.closure_isThreeCycles_eq_top]
  apply (Subgroup.closure_le _).mpr
  intro s hs
  obtain ⟨I,hSI,hIU,hI⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ s.val.support) (by rw [hs.card_support]; omega : s.val.support.card ≤ 5)
    (by simpa using hα : 5 ≤ (Finset.univ : Finset α).card)
  apply le_iSup (fun I : FiveAlphabet α => (subtypeAlternatingHom I.val).range) ⟨I,hIU,hI⟩
  exact (subtypeAlternatingHom_mem_range I s).mpr hSI

end FullAlphabetGeneration

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SmallControlCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SmallControlCalculus
variable {α H : Type*} [Fintype α] [DecidableEq α] [Group H]
    [Group.IsPerfect (alternatingGroup α)]

abbrev ControlAlphabet (α : Type*) [Fintype α] [DecidableEq α] :=
  {I : Finset α // 5 ≤ I.card ∧ I.card ≤ 10}

instance controlAlphabet_perfect (I : ControlAlphabet α) :
    Group.IsPerfect (alternatingGroup I.val) := alphabetPerfect I.val I.property.1

end SmallControlCalculus

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_WindowSubfamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section WindowSubfamilies

def coordinateWindowEmbedding (n k : ℕ) (q p : Fin 2 → ℤ)
    (hstart : ∀ j, q j ≤ p j) (hend : ∀ j, p j+(k:ℤ) ≤ q j+n) :
    Fin 2 × Fin (k-1) → Fin 2 × Fin (n-1) := fun i =>
  (i.1,⟨(p i.1-q i.1).toNat+i.2.val,by
    have hi := i.2.isLt
    have he : ((p i.1-q i.1).toNat:ℤ) = p i.1-q i.1 := Int.toNat_of_nonneg (by linarith [hstart i.1])
    have hn := hend i.1
    omega⟩)

end WindowSubfamilies

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FullSector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section AxisWindows

def axisWindowEmbedding (j : Fin 2) (n k : ℕ) (q : Fin 2 → ℤ) (p : ℤ)
    (hs : q j ≤ p) (he : p+(k:ℤ) ≤ q j+n) : Fin (k-1) → Fin 2 × Fin (n-1) :=
  fun i => (j,⟨(p-q j).toNat+i.val,by
    have hh : ((p-q j).toNat:ℤ) = p-q j := Int.toNat_of_nonneg (by omega)
    have hi := i.isLt
    omega⟩)

end AxisWindows

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Arithmetic_LatticeCounting
attribute [-instance] _root_.OAI.SimpleAmenable.fiveTrackPerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable

section QuantitativeArithmetic

lemma floor_error (x : ℝ) : |(⌊x⌋ : ℝ) - x| ≤ 1 := by
  rw [abs_of_nonpos (sub_nonpos.mpr (Int.floor_le x))]
  linarith [Int.lt_floor_add_one x]

end QuantitativeArithmetic

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_TangentChartTemplates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section TangentChartTemplates

def slopeDirection (d : Fin 2) : Fin 4 := ⟨d.val+2,by omega⟩
def slopeTestIndex (d : Fin 2) : Fin 5 := ⟨d.val+3,by omega⟩

end TangentChartTemplates

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FiniteSectorPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section AxisCellSplitting

def otherAxis (d : Fin 2) : Fin 2 := if d=0 then 1 else 0
@[simp] theorem otherAxis_ne (d : Fin 2) : otherAxis d ≠ d := by fin_cases d <;> decide

end AxisCellSplitting

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_AxisAnchorFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section GrowthAnchors

def growthOldLength (n : ℕ) := n*9/10

def growthNewLength (n : ℕ) := n*6/5

def growthAnchorLength (n : ℕ) := 2*growthOldLength n-growthNewLength n

def growthAnchorStart (n : ℕ) (p : ℤ) := p+(growthNewLength n:ℤ)-growthOldLength n

theorem growth_lengths {n : ℕ} (hn : 1005 ≤ n) :
    growthOldLength n ≤ n ∧ growthOldLength n ≤ growthNewLength n ∧
    growthNewLength n ≤ 2*growthOldLength n ∧ 201 ≤ growthAnchorLength n ∧
    growthAnchorLength n ≤ n ∧ n ≤ 2*growthAnchorLength n := by
  simp only [growthAnchorLength,growthOldLength,growthNewLength]
  omega

end GrowthAnchors

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PairLawAssembly
attribute [-instance] _root_.OAI.SimpleAmenable.fiveTrackPerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PairLawAssembly
variable {G E ι : Type*} [Group G] [Group E]

noncomputable def assignmentRestriction {Ω : Type*} (F : Ω → Type*) [∀ ω, Group (F ω)]
    (U : Set Ω) : (∀ ω, F ω) →* (∀ ω, F ω) := by
  classical
  exact { toFun := fun s ω => if ω ∈ U then s ω else 1
          map_one' := by ext ω; simp
          map_mul' := by intro s t; ext ω; by_cases hu : ω ∈ U <;> simp [hu] }

@[simp] theorem assignmentRestriction_single {Ω : Type*} [DecidableEq Ω]
    (F : Ω → Type*) [∀ ω, Group (F ω)] (U : Set Ω) [DecidablePred (· ∈ U)]
    (ω : Ω) (s : F ω) :
    assignmentRestriction F U (Pi.mulSingle ω s) =
      if ω ∈ U then Pi.mulSingle ω s else 1 := by
  classical
  ext ν
  by_cases heq : ν = ω
  · subst ν
    by_cases hu : ω ∈ U <;> simp [assignmentRestriction, hu]
  · by_cases huω : ω ∈ U <;> by_cases huν : ν ∈ U <;>
      simp [assignmentRestriction, heq, huω, huν]

variable [Fintype ι]
variable (A B : ι → Subgroup G) (h : ∀ i, CommutingFactors (A i) (B i))
    (hz : Subgroup.center G = ⊥)

noncomputable def refinementEquiv : (∀ σ : ι → Bool, refinedFactor A B Finset.univ σ) ≃* G := by
  classical
  exact commutingFactorsEquiv (fun σ => refinedFactor A B Finset.univ σ)
    (fun _ _ hστ _ _ hx hy => refinedFactor_commute A B h hστ hx hy)
    (simultaneous_refinement A B h hz Finset.univ) hz

@[simp] theorem refinementEquiv_single [DecidableEq (ι → Bool)] (σ : ι → Bool)
    (x : refinedFactor A B Finset.univ σ) :
    refinementEquiv A B h hz (Pi.mulSingle σ x) = x := by
  classical
  exact commutingFactorsEquiv_single _ _ _ _ _ _

noncomputable def refinementSource (c : E →* G) (σ : ι → Bool) :
    E →* refinedFactor A B Finset.univ σ :=
  (Pi.evalMonoidHom _ σ).comp ((refinementEquiv A B h hz).symm.toMonoidHom.comp c)

noncomputable def simultaneousAssignmentMap (c : E →* G) : ((ι → Bool) → E) →* G :=
  (refinementEquiv A B h hz).toMonoidHom.comp
    (MonoidHom.pi fun σ => (refinementSource A B h hz c σ).comp (Pi.evalMonoidHom _ σ))

end PairLawAssembly

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_GrowthAxisUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section SplitAssignment
variable {E S G ι κ : Type*} [Group E] [Group S] [Group G]

def splitFactorProduct (A B : Subgroup G)
    (h : ∀ x ∈ A, ∀ y ∈ B, Commute x y) : A × B →* G where
  toFun x := x.1.1*x.2.1
  map_one' := one_mul _
  map_mul' x y := by
    change (x.1.1*y.1.1)*(x.2.1*y.2.1) = (x.1.1*x.2.1)*(y.1.1*y.2.1)
    calc
      _ = x.1.1*(y.1.1*x.2.1)*y.2.1 := by group
      _ = x.1.1*(x.2.1*y.1.1)*y.2.1 := by rw [(h _ y.1.2 _ x.2.2).eq]
      _ = _ := by group

end SplitAssignment

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PairControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section AssignmentExclusions
variable {E S G K ι Ω : Type*} [Group E] [Group S] [Group G] [Group K]

noncomputable def copySourceMap (π : E →* S) : FreeGroup (Option ι × E) →* FreeGroup (Option ι × S) :=
  FreeGroup.map (fun p => (p.1,π p.2))

end AssignmentExclusions

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_TemplateFormalRelators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section TemplateFormalRelators
variable {E H Q Ω ι : Type*} [Group E] [Group H] [Group Q]

noncomputable def maskedAssignmentPullback (r : Ω → ι → Bool) (V : Set Ω) :
    ((ι → Bool) → E) →* (Ω → E) := by
  classical
  exact { toFun := fun f ω => if ω ∈ V then f (r ω) else 1
          map_one' := by ext ω; simp
          map_mul' := by intro f g; ext ω; by_cases h : ω ∈ V <;> simp [h] }

noncomputable def templateSides (U : ι → Set Ω) (V : Set Ω) : Option ι → Set Ω
  | none => V
  | some i => V ∩ U i

noncomputable def templateAssignment (U : ι → Set Ω) (ω : Ω) : ι → Bool := by
  classical
  exact fun i => decide (ω ∈ U i)

end TemplateFormalRelators

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FormalCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section StarFormalComponents
variable {E S G ι κ Ω : Type*}
  [Group E]
  [Group S]
  [Group G]
  [Finite ι]
  [DecidableEq (ι → Bool)]
  [Group.IsPerfect G]
  (π : E →* S)
  (c : S →* G)
  (F : Option ι → E →* G)
  (hc : F none = c.comp π)
  (φ : ((ι → Bool) → S) →* (G ⧸ Subgroup.center G))
  (hφ : Function.Surjective φ)

noncomputable def formalCoordinateSource (σ : ι → Bool) : S →* (G ⧸ Subgroup.center G) :=
  φ.comp (MonoidHom.mulSingle (fun _ : ι → Bool => S) σ)

end StarFormalComponents

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_RectangularBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section GlobalWindowCoherence

theorem finite_coordinate_windows_container {ι : Type*} [Fintype ι]
    (k : ι → ℕ) (p : ι → Fin 2 → ℤ) :
    ∃ n : ℕ, ∃ q : Fin 2 → ℤ, ∀ i j, q j ≤ p i j ∧ p i j+(k i:ℤ) ≤ q j+n := by
  let N := Finset.univ.sup (fun i => k i+(p i 0).natAbs+(p i 1).natAbs)
  have hb i : k i+(p i 0).natAbs+(p i 1).natAbs ≤ N := Finset.le_sup (f := fun i => k i+(p i 0).natAbs+(p i 1).natAbs) (Finset.mem_univ i)
  refine ⟨3*N+1,fun _ => -(N:ℤ),?_⟩
  intro i j
  have hk : k i ≤ N := by have := hb i; omega
  have hp : (p i j).natAbs ≤ N := by fin_cases j <;> dsimp <;> have := hb i <;> omega
  have hp₀ := (Int.le_natAbs : -p i j ≤ ((-p i j).natAbs : ℤ))
  simp only [Int.natAbs_neg] at hp₀
  have hp₁ := (Int.le_natAbs : p i j ≤ ((p i j).natAbs : ℤ))
  dsimp only
  constructor <;> omega

end GlobalWindowCoherence

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_LocalChartDecisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section LocalChartDecisions

noncomputable def realCoordinate (z : ℝ × ℝ) (j : Fin 2) : ℝ := ![z.1,z.2] j

end LocalChartDecisions

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ConcurrentAnchors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ConcurrentAnchors

abbrev VertexType (D : ℕ) := (Fin D × Fin D) × (Fin D × Fin D)

end ConcurrentAnchors

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_VaryingCellClassification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section VaryingCellClassification

def axisDirection (j : Fin 2) : Fin 4 := Fin.castLE (by omega) j

end VaryingCellClassification

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_FormalLawReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FormalLawReindex
variable {α ι κ H : Type*} [Fintype α] [DecidableEq α] [Group H]

noncomputable def smallFamilyReindex (v : κ → ι) : SmallFamilyWord α κ →* SmallFamilyWord α ι :=
  FreeGroup.map (fun l => ⟨l.1,l.2.1.map v,l.2.2⟩)

end FormalLawReindex

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FiniteArrangementGerms
attribute [-instance] _root_.OAI.SimpleAmenable.fiveTrackPerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FiniteArrangementGerms

theorem exists_interval_avoiding_countable (l r : ℝ) (hlr : l < r)
    (S : Set ℝ) (hS : S.Countable) : ∃ x ∈ Set.Ioo l r, x ∉ S := by
  apply Set.not_subset.mp
  intro h
  have := Cardinal.Real.Ioo_countable_iff.mp (hS.mono h)
  linarith

end FiniteArrangementGerms

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_FinitePrimitiveResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FinitePrimitiveResolution
variable {X ι : Type*}

theorem finite_resolving_subfamily (U : ι → Set X) {V : Set X}
    (hV : V ∈ BooleanSubalgebra.closure (Set.range U)) :
    ∃ S : Finset ι, ResolvedBy (fun i : S => U i.val) V := by
  classical
  induction hV using BooleanSubalgebra.closure_bot_sup_induction with
  | mem V h =>
    obtain ⟨i,rfl⟩ := h
    exact ⟨{i},fun x y he => he ⟨i,Finset.mem_singleton_self i⟩⟩
  | bot => exact ⟨∅,fun _ _ _ => Iff.rfl⟩
  | sup V W _ _ ihV ihW =>
    obtain ⟨S,hS⟩ := ihV
    obtain ⟨T,hT⟩ := ihW
    refine ⟨S ∪ T,fun x y he => or_congr (hS x y ?_) (hT x y ?_)⟩
    · intro i
      exact he ⟨i.val,Finset.mem_union_left _ i.property⟩
    · intro i
      exact he ⟨i.val,Finset.mem_union_right _ i.property⟩
  | compl V _ ih =>
    obtain ⟨S,hS⟩ := ih
    exact ⟨S,fun x y he => not_congr (hS x y he)⟩

end FinitePrimitiveResolution

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FrameDisjointness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement

theorem supported_fixer_commute {α : Type*} {f g : Equiv.Perm α} {U : Set α}
    (hf : ∀ p ∈ U, f p = p) (hg : SupportedIn g U) : Commute f g := by
  apply Equiv.Perm.Disjoint.commute
  intro p
  by_cases hp : p ∈ U
  · exact Or.inl (hf p hp)
  · exact Or.inr (hg p hp)

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_DistinctSlotStars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section DistinctSlotStars

noncomputable def fiveAlternatingHom {m : ℕ} (ι : Fin 5 ↪ Fin m) :
    alternatingGroup (Fin 5) →* alternatingGroup (Fin m) :=
  (fiveTrackHom ι).codRestrict _ (fiveTrack_sign ι)

noncomputable def orderedTrackAlphabet {m : ℕ} (ι : Fin 5 ↪ Fin m) : Finset (Fin m) :=
  Finset.univ.map ι

instance orderedTrackAlphabetPerfect {m : ℕ} (ι : Fin 5 ↪ Fin m) :
    Group.IsPerfect (alternatingGroup (orderedTrackAlphabet ι)) := by
  classical
  apply Group.IsPerfect.mk
  apply commutator_alternatingGroup_eq_top
  rw [Nat.card_eq_fintype_card,Fintype.card_coe,orderedTrackAlphabet,Finset.card_map,Finset.card_univ,Fintype.card_fin]

end DistinctSlotStars

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PrivateBankWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PrivateBankWord

theorem perm_list_prod_fix {α X : Type*} (l : List α) (f : α → Equiv.Perm X) (x : X)
    (h : ∀ i ∈ l, f i x=x) : (l.map f).prod x=x := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.map_cons,List.prod_cons,Equiv.Perm.mul_apply]
    rw [ih (fun j hj => h j (List.mem_cons_of_mem _ hj)),h i List.mem_cons_self]

theorem perm_list_prod_transport {α X : Type*} [DecidableEq α]
    (l : List α) (hl : l.Nodup) (f : α → Equiv.Perm X) (j : α) (hj : j ∈ l)
    (x y : X) (he : f j x=y)
    (hs : ∀ i ∈ l, i≠j → f i x=x ∧ f i y=y) : (l.map f).prod x=y := by
  induction l with
  | nil => simp at hj
  | cons i l ih =>
    have hn := (List.nodup_cons.mp hl).1
    have ht := (List.nodup_cons.mp hl).2
    by_cases hij : i=j
    · subst i
      simp only [List.map_cons,List.prod_cons,Equiv.Perm.mul_apply]
      rw [perm_list_prod_fix l f x (fun i hi => (hs i (List.mem_cons_of_mem _ hi)
        (fun he => hn (he ▸ hi))).1),he]
    · have hj' : j ∈ l := (List.mem_cons.mp hj).resolve_left (Ne.symm hij)
      simp only [List.map_cons,List.prod_cons,Equiv.Perm.mul_apply]
      rw [ih ht hj' (fun k hk => hs k (List.mem_cons_of_mem _ hk)),
        (hs i List.mem_cons_self hij).2]

def bankRow {m : ℕ} (e : (Fin 5 × Fin 5) ↪ Fin m) (j : Fin 5) : Fin 5 ↪ Fin m :=
  ⟨fun i => e (j,i),fun _ _ he => congrArg Prod.snd (e.injective he)⟩

def bankColumn {m : ℕ} (e : (Fin 5 × Fin 5) ↪ Fin m) (j : Fin 5) : Fin 5 ↪ Fin m :=
  ⟨fun i => e (i,j),fun _ _ he => congrArg Prod.fst (e.injective he)⟩

noncomputable def bankAlphabet {m : ℕ} (e : (Fin 5 × Fin 5) ↪ Fin m) : Finset (Fin m) :=
  Finset.univ.map e

def privateCycle : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2,by
    rw [Equiv.Perm.mem_alternatingGroup,map_mul]
    norm_num <;> decide⟩

@[simp] theorem privateCycle_apply_zero : privateCycle.val 0=1 := by
  decide

end PrivateBankWord

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_RepeatedTrackRouting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement

structure PrivateRoutingBank {m : ℕ} (i : Fin 5 → Fin m) where
  row : Fin 5 → Fin 5 ↪ Fin m
  source : ∀ j, row j 0=i j
  fresh : ∀ j k, k≠0 → ∀ l, row j k≠i l
  separate : ∀ j k j' k', k≠0 → k'≠0 → row j k=row j' k' → j=j' ∧ k=k'

namespace PrivateRoutingBank
variable {m : ℕ} {i : Fin 5 → Fin m} (P : PrivateRoutingBank i)

def target : Fin 5 ↪ Fin m :=
  ⟨fun j => P.row j 1,fun _ _ he => (P.separate _ _ _ _ (by decide) (by decide) he).1⟩

noncomputable def alphabet : Finset (Fin m) :=
  Finset.univ.image (fun p : Fin 5 × Fin 5 => P.row p.1 p.2)

theorem alphabet_card : P.alphabet.card ≤ 25 := by
  classical
  exact (Finset.card_image_le).trans (by simp)

end PrivateRoutingBank

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_BarrierCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section BarrierCells
open Classical Set

def squareInterior : Set (ℝ×ℝ) := Ioo 0 1 ×ˢ Ioo 0 1

def barrierRegion (B : Set (ℝ×ℝ)) : Set (ℝ×ℝ) := squareInterior \ B

end BarrierCells

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FlagGerms
attribute [-instance] _root_.OAI.SimpleAmenable.fiveTrackPerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FlagGerms
open Classical

def SquareBoundary (v z : ℝ × ℝ) : Prop :=
  z.1 ∈ Set.Icc (0:ℝ) 1 ∧ z.2 ∈ Set.Icc (0:ℝ) 1 ∧
  (z.1=0 → 0<v.1) ∧ (z.1=1 → v.1<0) ∧
  (z.2=0 → 0<v.2) ∧ (z.2=1 → v.2<0)

end FlagGerms

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FlagTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FlagTranslation
open Classical

noncomputable def flagFloor (x d : ℝ) : ℤ :=
  if d<0 then -1-⌊-x⌋ else ⌊x⌋

noncomputable def flagFract (x d : ℝ) : ℝ :=
  if d<0 then 1-Int.fract (-x) else Int.fract x

theorem flagFract_eq (x d : ℝ) : flagFract x d=x-(flagFloor x d:ℝ) := by
  unfold flagFract flagFloor
  split_ifs <;> simp only [Int.fract,Int.cast_sub,Int.cast_neg,Int.cast_one]
  ring

theorem flagFract_add_int (x d : ℝ) (n : ℤ) : flagFract (x+n) d=flagFract x d := by
  unfold flagFract
  split_ifs
  · rw [neg_add,← sub_eq_add_neg,Int.fract_sub_intCast]
  · rw [Int.fract_add_intCast]

theorem flagFract_sub_int (x d : ℝ) (n : ℤ) : flagFract (x-n) d=flagFract x d := by
  simpa [sub_eq_add_neg] using flagFract_add_int x d (-n)

theorem flagFract_flagFract_add (x y d : ℝ) :
    flagFract (flagFract x d+y) d=flagFract (x+y) d := by
  rw [flagFract_eq x d,sub_add_eq_add_sub,flagFract_sub_int]

theorem flagFract_boundary (x d : ℝ) (hd : d≠0) :
    flagFract x d∈Set.Icc (0:ℝ) 1 ∧
      (flagFract x d=0 → 0<d) ∧ (flagFract x d=1 → d<0) := by
  have h₀ := Int.fract_nonneg x
  have h₁ := Int.fract_lt_one x
  have h₀' := Int.fract_nonneg (-x)
  have h₁' := Int.fract_lt_one (-x)
  unfold flagFract
  split_ifs with ht
  · exact ⟨⟨by linarith,by linarith⟩,fun he => by linarith,fun _ => ht⟩
  · exact ⟨⟨h₀,le_of_lt h₁⟩,fun _ => lt_of_le_of_ne (le_of_not_gt ht) hd.symm,
      fun he => by linarith⟩

theorem flagFract_self {x d : ℝ} (hx : x∈Set.Icc (0:ℝ) 1)
    (h₀ : x=0 → 0<d) (h₁ : x=1 → d<0) : flagFract x d=x := by
  unfold flagFract
  split_ifs with ht
  · have hx₀ : 0<x := lt_of_le_of_ne hx.1 (by intro he; have := h₀ he.symm; linarith)
    have hf : Int.fract (-x)=1-x := Int.fract_eq_iff.mpr
      ⟨by linarith [hx.2],by linarith,⟨-1,by norm_num; ring⟩⟩
    rw [hf]; ring
  · exact Int.fract_eq_self.mpr ⟨hx.1,lt_of_le_of_ne hx.2 (fun he => ht (h₁ he))⟩

end FlagTranslation

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_BarrierLineGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section BarrierLineGeometry
open Classical Set

noncomputable def barrierLineParameter (j : Fin 4) (p : ℝ×ℝ) : ℝ :=
  ![p.2,p.1,p.1,p.2] j

end BarrierLineGeometry

section BarrierFlags
open Classical

noncomputable def barrierTangent (a : ℕ) (j : Fin 4) : ℝ×ℝ :=
  ![(0,1),(1,0),(1,Real.goldenRatio^a),(Real.goldenRatio^a,1)] j

end BarrierFlags

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_BarrierAlgorithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section BarrierAlgorithm
open Classical Set

def ConsecutiveSubdivision (E : Finset ℝ) (s t : ℝ) : Prop :=
  s∈E ∧ t∈E ∧ s<t ∧ ∀r∈E,s < r → t ≤ r

end BarrierAlgorithm

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Arithmetic_DyadicArithmetic
attribute [-instance] _root_.OAI.SimpleAmenable.fiveTrackPerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SourceDyadicArithmetic
open Classical Filter
open scoped Topology

noncomputable def sourceDyadicN (n : ℕ) : ℝ := (2:ℝ)^(4*n)
noncomputable def sourceDyadicWeight (n : ℕ) : ℝ := (Real.log (sourceDyadicN n))^(-3/4:ℝ)
def sourceDyadicIndices (n : ℕ) : Finset ℕ := Finset.Icc n (2*n)

theorem sourceDyadicN_pos (n : ℕ) : 0 < sourceDyadicN n := by unfold sourceDyadicN; positivity

end SourceDyadicArithmetic

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_TentMatrixPositivity
attribute [-instance] _root_.OAI.SimpleAmenable.fiveTrackPerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section TentMatrixPositivity
open Classical MeasureTheory

noncomputable def intervalMark (x t : ℝ) : ℝ :=
  (Set.Icc x (x+1)).indicator (fun _ => 1) t

end TentMatrixPositivity

section FlagSeparatorMatrices
open Classical MeasureTheory

noncomputable def thresholdLaw (s κ : ℝ) : Measure (Fin 4 → ℝ) :=
  Measure.pi fun _ => ProbabilityTheory.cond volume (Set.Icc (κ/s) (2*κ/s))

end FlagSeparatorMatrices

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_UniformThresholdCDF
attribute [-instance] _root_.OAI.SimpleAmenable.fiveTrackPerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section UniformThresholdCDF
open Classical MeasureTheory ProbabilityTheory

noncomputable def intervalCDF (lo hi d : ℝ) : ℝ := max (min hi d-lo) 0 / (hi-lo)

end UniformThresholdCDF

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_GoodRowSeparators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section NormalizedTentMass
open Classical MeasureTheory

noncomputable def unitTent (x : ℝ) : ℝ := max (1-|x|) 0

noncomputable def doubleUnitTent (x : Fin 2 → ℝ) : ℝ := ∏i,unitTent (x i)

noncomputable def pairedUnitTent (x : (Fin 2 → ℝ)×(Fin 2 → ℝ)) : ℝ :=
  doubleUnitTent x.1*doubleUnitTent x.2

end NormalizedTentMass

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_FlagAveragingMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FlagAveragingMatrices
open Classical MeasureTheory

noncomputable def planeTent (s : ℝ) (x y : ℝ×ℝ) : ℝ :=
  max (1-|(x.1-y.1)/s|) 0 * max (1-|(x.2-y.2)/s|) 0

@[simp] theorem planeTent_self (s : ℝ) (x : ℝ×ℝ) : planeTent s x x=1 := by
  simp [planeTent]

end FlagAveragingMatrices

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FlagTentMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FlagTentMass
open Classical

noncomputable def tentRowOffset (s t : ℝ) (x y : ℝ×ℝ) : (Fin 2 → ℝ)×(Fin 2 → ℝ) :=
  (![-x.1/s,-y.1/t],![-x.2/s,-y.2/t])

end FlagTentMass

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_SignalGoodRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section ApproximationEnergy
open Classical

noncomputable def flagVolumeConstant (m D : ℕ) (Q : ℝ) : ℝ := m*(2*(D:ℝ)^2*Q+2)^2
noncomputable def flagRowSumConstant (D : ℕ) : ℝ := (4*(D:ℝ)^2+2)^2/((D:ℝ)^4/5)+1

end ApproximationEnergy

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_PolygonApproxIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section FiniteResolvent
open Classical Matrix

noncomputable def finiteL2Norm {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  ‖WithLp.toLp 2 x‖

end FiniteResolvent

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_CompactSignalEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section SourceSignalScales
open Classical Filter
open scoped Topology

noncomputable def sourceDyadicMass (n : ℕ) : ℝ :=
  sourceDyadicWeight n*((sourceDyadicIndices n).card:ℝ)

end SourceSignalScales

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_PolygonCovarianceEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section PolygonDyadicRowEnergy
open Classical

noncomputable def flagRowConstant (D : ℕ) (ρ η : ℝ) : ℝ :=
  (4*(D:ℝ)^2*η+2)/(ρ*η^2)

end PolygonDyadicRowEnergy

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ObservableDistance
attribute [-instance] _root_.OAI.SimpleAmenable.fiveTrackPerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ObservableDistance
open Classical MeasureTheory Set

def ObservableClose {X : Type*} [MeasurableSpace X] (μ ν : Measure X) (ε : ℝ) : Prop :=
  ∀f : X → ℝ,Measurable f → (∀x,f x∈Icc (0:ℝ) 1) →
    |(∫x,f x ∂μ)-(∫x,f x ∂ν)| ≤ ε

end ObservableDistance

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_NoiseTensor
attribute [-instance] _root_.OAI.SimpleAmenable.fiveTrackPerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section NoiseTensor
open Classical MeasureTheory

noncomputable def noiseTensor {ι : Type*} [Fintype ι] (u : ι → ℝ → ℝ)
    (x : ι → ℝ) : ℝ := ∏i,u i (x i)

noncomputable def centeredNoiseTensor {ι : Type*} [Fintype ι] (f : ℝ → ℝ)
    (s : Finset ι) (u : ι → ℝ → ℝ) : (ι → ℝ) → ℝ :=
  noiseTensor (fun i => if i∈s then u i else f)

end NoiseTensor

section NoiseMoments
open Classical MeasureTheory

inductive NoiseFactor
  | base | score | position | diagonal
  deriving DecidableEq

noncomputable def noiseFactor (f : ℝ → ℝ) : NoiseFactor → ℝ → ℝ
  | .base => f
  | .score => deriv f
  | .position => fun x => x*f x
  | .diagonal => fun x => x*deriv f x+f x/2

end NoiseMoments

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_FiniteOrthogonalEnergy
attribute [-instance] _root_.OAI.SimpleAmenable.fiveTrackPerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section SmoothNoise
open Classical MeasureTheory
open scoped ContDiff

noncomputable def rawNoiseBump : ContDiffBump (0 : ℝ) :=
  ⟨1/2,1,by norm_num,by norm_num⟩

noncomputable def rawNoiseMass : ℝ := ∫x : ℝ,(rawNoiseBump x)^2

noncomputable def smoothNoiseRoot (x : ℝ) : ℝ := rawNoiseBump x/Real.sqrt rawNoiseMass

end SmoothNoise

section NoiseCenteredEnergy
open Classical MeasureTheory

noncomputable def noiseEnergy (f : ℝ → ℝ) (i : NoiseFactor) : ℝ :=
  ∫x : ℝ,noiseFactor f i x^2

noncomputable def singletonNoise {ι : Type*} [Fintype ι] (f : ℝ → ℝ)
    (q : NoiseFactor) (i : ι) : (ι → ℝ) → ℝ := centeredNoiseTensor f {i} (fun _ => noiseFactor f q)

def NoisePair (ι : Type*) := {p : ι×ι // p.1≠p.2}

instance instFintypeNoisePairOfDecidableEq {ι : Type*} [Fintype ι] [DecidableEq ι] : Fintype (NoisePair ι) :=
  inferInstanceAs (Fintype {p : ι×ι // p.1≠p.2})

def noisePairSwap {ι : Type*} (p : NoisePair ι) : NoisePair ι := ⟨(p.val.2,p.val.1),Ne.symm p.property⟩

noncomputable def pairNoise {ι : Type*} [Fintype ι] (f : ℝ → ℝ)
    (p : NoisePair ι) : (ι → ℝ) → ℝ := centeredNoiseTensor f {p.val.1,p.val.2}
      (fun i => noiseFactor f (if i=p.val.1 then .score else .position))

end NoiseCenteredEnergy

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_AffineNoiseEnergy
attribute [-instance] _root_.OAI.SimpleAmenable.fiveTrackPerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section AffineNoiseEnergy
open Classical MeasureTheory

noncomputable def affineNoiseGenerator {ι : Type*} [Fintype ι]
    (f : ℝ → ℝ) (L : Matrix ι ι ℝ) (v : ι → ℝ) (x : ι → ℝ) : ℝ :=
  (∑i,L i i*singletonNoise f .diagonal i x)+
  (∑i,v i*singletonNoise f .score i x)+
  ∑p : NoisePair ι,L p.val.1 p.val.2*pairNoise f p x

noncomputable def affineNoiseEnergyConstant (f : ℝ → ℝ) : ℝ :=
  3*(noiseEnergy f .diagonal+noiseEnergy f .score+2*(noiseEnergy f .score*noiseEnergy f .position))

end AffineNoiseEnergy

section ActualNoiseLaw
open Classical MeasureTheory ProbabilityTheory
open scoped ContDiff ENNReal

noncomputable def smoothNoiseDensity (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (smoothNoiseRoot x^2)

noncomputable def smoothNoiseLaw : Measure ℝ := volume.withDensity smoothNoiseDensity

noncomputable def independentSmoothNoiseLaw (ι : Type*) : Measure (ι → ℝ) :=
  Measure.infinitePi (fun _ : ι => smoothNoiseLaw)

end ActualNoiseLaw

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_MatrixDensityCalculus
attribute [-instance] _root_.OAI.SimpleAmenable.fiveTrackPerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section MatrixDensityCalculus
open Classical Matrix

noncomputable def determinantMultilinear {ι : Type*} [Fintype ι] :
    ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ where
  toMultilinearMap := Matrix.detRowAlternating.toMultilinearMap
  cont := continuous_id.matrix_det

end MatrixDensityCalculus

section AffineNoiseIdentity
open Classical Matrix

noncomputable def noiseGradientCoordinate {ι : Type*} [Fintype ι]
    (f : ℝ → ℝ) (i : ι) (x : ι → ℝ) : ℝ :=
  deriv f (x i)*∏j∈Finset.univ.erase i,f (x j)

end AffineNoiseIdentity

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_MatrixInverseCalculus
attribute [-instance] _root_.OAI.SimpleAmenable.fiveTrackPerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section AffineVolume
open Classical Matrix MeasureTheory
open scoped ENNReal

noncomputable def matrixAffineEquiv {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (a : ι → ℝ) (hA : IsUnit A.det) :
    (ι → ℝ) ≃ᵐ (ι → ℝ) :=
  ((Matrix.toLinearEquiv (Pi.basisFun ℝ ι) A hA).toContinuousLinearEquiv.toHomeomorph.trans
    (Homeomorph.addLeft a)).toMeasurableEquiv

end AffineVolume

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_AffineDensityDerivative
attribute [-instance] _root_.OAI.SimpleAmenable.fiveTrackPerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section AffineDensityDerivative
open Classical Matrix
open scoped Matrix.Norms.Elementwise

noncomputable def affineNoiseRoot {ι : Type*} [Fintype ι]
    (f : ℝ → ℝ) (A : Matrix ι ι ℝ) (a y : ι → ℝ) : ℝ :=
  noiseTensor (fun _ : ι => f) (A⁻¹*ᵥ(y-a))/Real.sqrt A.det

end AffineDensityDerivative

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_NoiseContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section NoiseContinuity
open Classical Matrix MeasureTheory

@[fun_prop] theorem noiseTensor_continuous {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : Continuous f) : Continuous (noiseTensor (fun _ : ι => f)) := by
  unfold noiseTensor
  fun_prop

@[fun_prop] theorem noiseGradientCoordinate_continuous {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (i : ι) : Continuous (noiseGradientCoordinate f i) := by
  have hd : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hc := hf.continuous
  unfold noiseGradientCoordinate
  fun_prop

@[fun_prop] theorem affineNoiseRoot_continuous {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : Continuous f) (A : Matrix ι ι ℝ) (a : ι → ℝ) :
    Continuous (affineNoiseRoot f A a) := by
  unfold affineNoiseRoot
  apply Continuous.div_const
  exact (noiseTensor_continuous hf).comp (by fun_prop)

local instance instMeasurableSpaceMatrixReal_solutions {ι : Type*} : MeasurableSpace (Matrix ι ι ℝ) :=
  inferInstanceAs (MeasurableSpace (ι → ι → ℝ))

end NoiseContinuity

section CovarianceResolvent
open Classical Matrix

noncomputable def matrixHSNorm {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) : ℝ :=
  Real.sqrt (∑i,∑j,A i j^2)

noncomputable def covarianceSegment {ι : Type*} [Fintype ι]
    (B C : Matrix ι ι ℝ) (t : ℝ) : Matrix ι ι ℝ := (1-t) • B+t • C

end CovarianceResolvent

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_AffineGeneratorIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section NoiseInterpolation
open Classical Matrix MeasureTheory Set
open scoped Matrix.Norms.Elementwise

noncomputable def noiseInterpolationRoot {ι : Type*} [Fintype ι]
    (f : ℝ → ℝ) (B C : Matrix ι ι ℝ) (a h : ι → ℝ) (t : ℝ) : (ι → ℝ) → ℝ :=
  affineNoiseRoot f (1+covarianceSegment B C t) (a+t • h)

noncomputable def noiseInterpolationDerivative {ι : Type*} [Fintype ι]
    (f : ℝ → ℝ) (B C : Matrix ι ι ℝ) (a h : ι → ℝ) (t : ℝ) (y : ι → ℝ) : ℝ :=
  let T := 1+covarianceSegment B C t;
  -affineNoiseGenerator f (T⁻¹*(C-B)) (T⁻¹*ᵥh) (T⁻¹*ᵥ(y-(a+t • h)))/Real.sqrt T.det

local instance instMeasurableSpaceMatrixReal_solutions_1 {ι : Type*} : MeasurableSpace (Matrix ι ι ℝ) :=
  inferInstanceAs (MeasurableSpace (ι → ι → ℝ))

end NoiseInterpolation

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_HellingerDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section FiniteAffineLaw
open Classical MeasureTheory Matrix Set
open scoped ENNReal

noncomputable def finiteAffineNoiseLaw {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (a : ι → ℝ) : Measure (ι → ℝ) :=
  (independentSmoothNoiseLaw ι).map (fun x => a+A*ᵥx)

end FiniteAffineLaw

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_FiniteLawDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FiniteLawDistance
open Classical Matrix MeasureTheory

noncomputable def smoothNoiseTransportError {ι : Type*} [Fintype ι]
    (B C : Matrix ι ι ℝ) (h : ι → ℝ) : ℝ :=
  2*Real.sqrt (affineNoiseEnergyConstant smoothNoiseRoot*(matrixHSNorm (C-B)^2+
    ((1+matrixHSNorm (C-B))*finiteL2Norm ((1+B)⁻¹*ᵥh))^2))

end FiniteLawDistance

section FiniteField
open Classical Matrix MeasureTheory

noncomputable def finiteCoefficientField {ι : Type*} (J : Finset ι)
    (a : ι → ℝ) (B : Matrix ι ι ℝ) (x : ι → ℝ) : ι → ℝ :=
  fun z => a z+x z+∑w∈J,B z w*x w

noncomputable def joinedNoiseField {ι : Type*} (J : Finset ι) (q : ℝ)
    (x : (J → ℝ) × ({z : ι // z∉J} → ℝ)) : ι → ℝ :=
  fun z => if hz : z∈J then x.1 ⟨z,hz⟩ else q+x.2 ⟨z,hz⟩

end FiniteField

section WholeFieldDistance
open Classical Matrix MeasureTheory

noncomputable def smoothNoiseTransportConstant : ℝ :=
  2*Real.sqrt (affineNoiseEnergyConstant smoothNoiseRoot)+1

end WholeFieldDistance

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_FieldHS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section FiniteFieldCovariance
open Classical Matrix MeasureTheory

noncomputable def fieldReindex {ι : Type*} (e : ι ≃ ι) (x : ι → ℝ) : ι → ℝ :=
  fun z => x (e.symm z)

end FiniteFieldCovariance

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_ThresholdField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ThresholdField
open Classical MeasureTheory Set

noncomputable def thresholdField {ι : Type*} (x : ι → ℝ) : ι → Bool :=
  fun z => if 0<x z then true else false

def signalSuccess {ι : Type*} (a : ι → ℝ) (b : ι → Bool) : Prop :=
  ∀z,(2≤a z → b z=true) ∧ (a z≤-2 → b z=false)

end ThresholdField

section SourceBitField
open Classical MeasureTheory Filter Set
open scoped Topology

noncomputable def extendFiniteBits {ι : Type*} (J : Finset ι) (b : J → Bool) : ι → Bool :=
  fun z => if hz : z∈J then b ⟨z,hz⟩ else false

end SourceBitField

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_FieldSignalData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FieldSignalData
open Classical Set
open scoped ContDiff

structure FieldSignalData where
  ψ : (ℝ×ℝ) → ℝ
  χ : (ℝ×ℝ) → ℝ
  smooth : ContDiff ℝ 2 ψ
  compact : HasCompactSupport ψ
  q : ℝ
  K : ℝ
  L : ℝ
  Λ : ℝ
  L_pos : 0<L
  gap : K+2≤L
  ψ_zero : ∀x,K≤‖x‖ → ψ x=0
  χ_range : ∀x,χ x∈Icc (0:ℝ) 1
  χ_one : ∀x,‖x‖≤K+2 → χ x=1
  χ_zero : ∀x,L≤‖x‖ → χ x=0
  Λ_nonneg : 0≤Λ
  χ_lipschitz : ∀x y,|χ x-χ y|≤Λ*(|x.1-y.1|+|x.2-y.2|)

namespace FieldSignalData
noncomputable def signal (S : FieldSignalData) (x : ℝ×ℝ) : ℝ := S.q+S.ψ x

end FieldSignalData
end FieldSignalData

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_BarrierSignalSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section SubdivisionCovariance
open Classical Set

def subdivisionBarrier (E : Finset ℝ) (b : ℝ → Bool) : Set ℝ :=
  {x | ∃s t,ConsecutiveSubdivision E s t ∧ b s=true ∧ x ∈ Icc s t}

end SubdivisionCovariance

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_FiniteCoarea
attribute [-instance] _root_.OAI.SimpleAmenable.fiveTrackPerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FiniteCoarea

variable {V E : Type*} [Fintype V] [Fintype E]

noncomputable def graphVariation (u v : E → V) (w : V → ℝ) : ℝ :=
  ∑ e, |w (u e) - w (v e)|

noncomputable def graphBoundary (u v : E → V) (A : Finset V) : ℝ := by
  classical
  exact graphVariation u v (fun x => if x ∈ A then 1 else 0)

end FiniteCoarea

section WeightedGroupCoarea

variable {G : Type*} [Group G] [DecidableEq G]

noncomputable def translationWindow (K S : Finset G) : Finset G := by
  classical
  exact S ∪ K.biUnion (fun k => S.image (fun x => k*x))

noncomputable def weightedVariation (K S : Finset G) (p : G → ℝ) : ℝ :=
  ∑ k ∈ K, ∑ x ∈ translationWindow K S, |p (k⁻¹*x) - p x|

end WeightedGroupCoarea

noncomputable def FiniteSupportReiter (G : Type*) [Group G] : Prop := by
  classical
  exact ∀ K : Finset G, ∀ ε : ℝ, 0 < ε →
      ∃ (S : Finset G) (p : G → ℝ), (∀ x, 0 ≤ p x) ∧
        (∀ x ∉ S, p x = 0) ∧ (∑ x ∈ S, p x) = 1 ∧
        weightedVariation K S p < ε

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_SignalRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SourceSignalRemainder
open Classical Filter
open scoped Topology

noncomputable def sourceSignalDelta (D : ℕ) (η : ℝ) (n : ℕ) : ℝ :=
  38880/((D:ℝ)*Real.sqrt ((2:ℝ)^n*η))

noncomputable def sourceSignalError (A B Cv Ca Cr η κ : ℝ) (D n : ℕ) : ℝ :=
  Real.sqrt A*(Cv*η*(1+sourceSignalDelta D η n)+Ca*sourceSignalDelta D η n)+
    Real.sqrt B*Real.sqrt (κ+(1/4:ℝ)^n)*(Cr*Ca)

end SourceSignalRemainder

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_BitReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section BitReindex
open Classical MeasureTheory

noncomputable def bitReindex {ι : Type*} (e : ι ≃ ι) (b : ι → Bool) : ι → Bool :=
  fun z => b (e.symm z)

end BitReindex

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ShapeTranslationUnique
attribute [-instance] _root_.OAI.SimpleAmenable.fiveTrackPerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ShapeTranslationUnique
open Classical Set

theorem real_sSup_translate {A : Set ℝ} (hne : A.Nonempty) (hb : BddAbove A) (u : ℝ) :
    sSup ((fun x => x+u) '' A)=sSup A+u := by
  have hi : ((fun x => x+u) '' A).Nonempty := hne.image _
  have hbi : BddAbove ((fun x => x+u) '' A) := by
    obtain ⟨M,hM⟩ := hb
    exact ⟨M+u,by rintro y ⟨x,hx,rfl⟩; dsimp; linarith [hM hx]⟩
  apply le_antisymm
  · apply csSup_le hi
    rintro y ⟨x,hx,rfl⟩
    dsimp; linarith [le_csSup hb hx]
  · have h : sSup A ≤ sSup ((fun x => x+u) '' A)-u := by
      apply csSup_le hne
      intro x hx
      have hh := le_csSup hbi (show x+u∈(fun x => x+u) '' A from ⟨x,hx,rfl⟩)
      linarith
    linarith

theorem bounded_coordinate_shift_unique {X Y : Type*} (A : Set X) (φ : X → ℝ) (ψ : Y → ℝ)
    (hne : A.Nonempty) (hb : BddAbove (φ '' A)) (f h : X → Y)
    (he : f '' A=h '' A) (u v : ℝ)
    (hu : ∀x∈A,ψ (f x)=φ x+u) (hv : ∀x∈A,ψ (h x)=φ x+v) : u=v := by
  have him (f : X → Y) (u : ℝ) (hf : ∀x∈A,ψ (f x)=φ x+u) :
      ψ '' (f '' A)=(fun x => x+u) '' (φ '' A) := by
    rw [Set.image_image,Set.image_image]
    apply Set.image_congr
    intro x hx
    exact hf x hx
  have hx := congrArg (fun T : Set Y => sSup (ψ '' T)) he
  rw [him f u hu,him h v hv,real_sSup_translate (hne.image φ) hb,
    real_sSup_translate (hne.image φ) hb] at hx
  linarith

end ShapeTranslationUnique

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_SuccessfulLawCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section FiniteMixtureWeights
open Classical

noncomputable def finiteUniformWeight {G : Type*} (U : Finset G) (x : G) : ℝ :=
  if x∈U then (1:ℝ)/U.card else 0

end FiniteMixtureWeights

section FiniteTestReiter
open Classical Set

def FiniteTestReiter (G : Type*) [Group G] : Prop :=
  ∀K : Finset G,∀δ : ℝ,0 < δ → ∃(S : Finset G) (p : G → ℝ),
    (∀x,0 ≤ p x) ∧ (∀x∉S,p x=0) ∧ (∑x∈S,p x)=1 ∧
    ∀k∈K,∀f : G → ℝ,(∀x,f x∈Icc (0:ℝ) 1) →
      |(∑x∈S,p x*f x)-(∑x∈S,p x*f (k*x))| ≤ δ

end FiniteTestReiter

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_SubgroupTestReiter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SubgroupTestReiter
open Classical Set

noncomputable def subgroupOrbitSetoid {G : Type*} [Group G] (H : Subgroup G) : Setoid G where
  r x y := ∃h : H,(h:G)*x=y
  iseqv := ⟨fun x => ⟨1,by simp⟩,by
    rintro x y ⟨h,hh⟩
    refine ⟨h⁻¹,?_⟩
    rw [←hh]
    simp,by
    rintro x y z ⟨h,hh⟩ ⟨k,hk⟩
    refine ⟨k*h,?_⟩
    change (k:G)*(h:G)*x=z
    rw [mul_assoc,hh,hk]⟩

noncomputable def subgroupOrbitBase {G : Type*} [Group G] (H : Subgroup G) (x : G) : G :=
  (Quotient.mk (subgroupOrbitSetoid H) x).out

theorem subgroupOrbitBase_spec {G : Type*} [Group G] (H : Subgroup G) (x : G) :
    ∃h : H,(h:G)*subgroupOrbitBase H x=x :=
  Quotient.exact (Quotient.out_eq (Quotient.mk (subgroupOrbitSetoid H) x))

noncomputable def subgroupCoordinate {G : Type*} [Group G] (H : Subgroup G) (x : G) : H :=
  (subgroupOrbitBase_spec H x).choose

end SubgroupTestReiter

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_VerticalStringResolution
attribute [-instance] _root_.OAI.SimpleAmenable.fiveTrackPerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section IntegralTransgression
open Classical

namespace IntegralTransgression
variable {H E : Type*} [Group H] [Group E]

def Kernel (q : H →* E) (_hc : q.ker ≤ Subgroup.center H) : Type _ := q.ker

instance kernelCommGroup (q : H →* E) (hc : q.ker ≤ Subgroup.center H) :
    CommGroup (Kernel q hc) := by
  change CommGroup q.ker
  exact { (inferInstance : Group q.ker) with
    mul_comm := fun x y => Subtype.ext (Subgroup.mem_center_iff.mp (hc x.property) y.val).symm }

noncomputable def inclusion (q : H →* E) (hc : q.ker ≤ Subgroup.center H) : Kernel q hc →* H :=
  q.ker.subtype

variable (q : H →* E) (hq : Function.Surjective q) (hc : q.ker ≤ Subgroup.center H)

noncomputable def sectionMap (x : E) : H := if x=1 then 1 else Classical.choose (hq x)

@[simp] theorem section_one : sectionMap q hq 1 = 1 := by simp [sectionMap]
@[simp] theorem section_projection (x : E) : q (sectionMap q hq x)=x := by
  by_cases hx : x=1
  · simp [sectionMap,hx]
  · simpa [sectionMap,hx] using Classical.choose_spec (hq x)

noncomputable def factor (x y : E) : Kernel q hc :=
  ⟨sectionMap q hq x * sectionMap q hq y * (sectionMap q hq (x*y))⁻¹,by
    change q (sectionMap q hq x * sectionMap q hq y * (sectionMap q hq (x*y))⁻¹) = 1
    simp⟩

noncomputable def remainder (h : H) : Kernel q hc :=
  ⟨h * (sectionMap q hq (q h))⁻¹,by
    change q (h * (sectionMap q hq (q h))⁻¹) = 1
    simp⟩

@[simp] theorem factor_one_left (x : E) : factor q hq hc 1 x=1 := by
  apply Subtype.ext; simp only [factor,section_one,one_mul,mul_inv_cancel]; rfl
@[simp] theorem factor_one_right (x : E) : factor q hq hc x 1=1 := by
  apply Subtype.ext; simp only [factor,section_one,mul_one,mul_inv_cancel]; rfl
@[simp] theorem remainder_one : remainder q hq hc 1=1 := by
  apply Subtype.ext; simp only [remainder,map_one,section_one,inv_one,mul_one]; rfl
@[simp] theorem remainder_inclusion (k : Kernel q hc) :
    remainder q hq hc (inclusion q hc k)=k := by
  apply Subtype.ext
  change k.val * (sectionMap q hq (q k.val))⁻¹=k.val
  have hk : q k.val=1 := k.property
  simp [hk]

theorem factor_cocycle (x y z : E) :
    factor q hq hc x y * factor q hq hc (x*y) z =
    factor q hq hc y z * factor q hq hc x (y*z) := by
  apply Subtype.ext
  change (sectionMap q hq x * sectionMap q hq y * (sectionMap q hq (x*y))⁻¹) *
      (sectionMap q hq (x*y) * sectionMap q hq z * (sectionMap q hq (x*y*z))⁻¹) =
    (factor q hq hc y z).val *
      (sectionMap q hq x * sectionMap q hq (y*z) * (sectionMap q hq (x*(y*z)))⁻¹)
  have hcomm := Subgroup.mem_center_iff.mp (hc (factor q hq hc y z).property)
    (sectionMap q hq x)
  simp only [mul_assoc x y z]
  calc
    _ = sectionMap q hq x * sectionMap q hq y * sectionMap q hq z *
        (sectionMap q hq (x*(y*z)))⁻¹ := by group
    _ = sectionMap q hq x * (factor q hq hc y z).val *
        sectionMap q hq (y*z) * (sectionMap q hq (x*(y*z)))⁻¹ := by
      dsimp [factor]; group
    _ = _ := by rw [hcomm]; group

end IntegralTransgression
end IntegralTransgression

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_IntegralTransgressionHomology
attribute [-instance] _root_.OAI.SimpleAmenable.fiveTrackPerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section IntegralTransgressionHomology
open Classical
open scoped TensorProduct
namespace IntegralTransgression
open groupHomology
variable {H E : Type} [Group H] [Group E]

abbrev coefficients (E : Type) [Group E] := Rep.trivial ℤ E ℤ

variable (q : H →* E) (hq : Function.Surjective q) (hc : q.ker ≤ Subgroup.center H)

noncomputable def onChains : (E × E →₀ ℤ) →ₗ[ℤ] Additive (Kernel q hc) :=
  Finsupp.linearCombination ℤ (fun xy : E×E => Additive.ofMul (factor q hq hc xy.1 xy.2))

@[simp] theorem onChains_single (x y : E) (n : ℤ) :
    onChains q hq hc (Finsupp.single (x,y) n)= n • Additive.ofMul (factor q hq hc x y) := by
  simp only [onChains,Finsupp.linearCombination_single]

theorem additive_cocycle (x y z : E) :
    Additive.ofMul (factor q hq hc y z) - Additive.ofMul (factor q hq hc (x*y) z) +
      Additive.ofMul (factor q hq hc x (y*z)) - Additive.ofMul (factor q hq hc x y)=0 := by
  have he : Additive.ofMul (factor q hq hc x y) + Additive.ofMul (factor q hq hc (x*y) z) =
      Additive.ofMul (factor q hq hc y z) + Additive.ofMul (factor q hq hc x (y*z)) :=
    congrArg Additive.ofMul (factor_cocycle q hq hc x y z)
  calc
    _ = (Additive.ofMul (factor q hq hc y z) + Additive.ofMul (factor q hq hc x (y*z))) -
        (Additive.ofMul (factor q hq hc x y) + Additive.ofMul (factor q hq hc (x*y) z)) := by abel
    _ = 0 := sub_eq_zero.mpr he.symm

theorem onChains_d3 :
    (onChains q hq hc).comp (d₃₂ (coefficients E)).hom = 0 := by
  apply Finsupp.lhom_ext
  intro xyz n
  rcases xyz with ⟨x,y,z⟩
  change onChains q hq hc (d₃₂ (coefficients E) (Finsupp.single (x,y,z) n)) = 0
  rw [d₃₂_single (A := coefficients E) (x,y,z) n]
  change onChains q hq hc ((Finsupp.single (y,z) n - Finsupp.single (x*y,z) n) +
    Finsupp.single (x,y*z) n - Finsupp.single (x,y) n)=0
  rw [(onChains q hq hc).map_sub, (onChains q hq hc).map_add,
    (onChains q hq hc).map_sub]
  simp only [onChains_single]
  simpa only [zsmul_sub,zsmul_add,zsmul_zero] using
    congrArg (fun v : Additive (Kernel q hc) => (n : ℤ) • v) (additive_cocycle q hq hc x y z)

noncomputable def onCycles : cycles₂ (coefficients E) →ₗ[ℤ] Additive (Kernel q hc) :=
  (onChains q hq hc).comp (cycles₂ (coefficients E)).subtype

end IntegralTransgression
end IntegralTransgressionHomology

section IntegralTransgressionSurjective
open Classical
namespace IntegralTransgression
open groupHomology

noncomputable def factorThrough {R : Type*} [CommRing R] {M N P : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P] (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (g : M →ₗ[R] P) (hg : f.ker ≤ g.ker) : N →ₗ[R] P :=
  (f.ker.liftQ g hg).comp (f.quotKerEquivOfSurjective hf).symm.toLinearMap

@[simp] theorem factorThrough_apply {R : Type*} [CommRing R] {M N P : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P] (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (g : M →ₗ[R] P) (hg : f.ker ≤ g.ker) (x : M) :
    factorThrough f hf g hg (f x)=g x := by
  simp [factorThrough]

end IntegralTransgression
end IntegralTransgressionSurjective

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_IntegralTransgressionFinite
attribute [-instance] _root_.OAI.SimpleAmenable.fiveTrackPerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section IntegralTransgressionFinite
open Classical
namespace IntegralTransgression
open groupHomology _root_.CategoryTheory
variable {H E : Type} [Group H] [Group E]
variable (q : H →* E) (hq : Function.Surjective q) (hc : q.ker ≤ Subgroup.center H)

 theorem onCycles_kills_homology_kernel :
    (H2π (coefficients E)).hom.ker ≤ (onCycles q hq hc).ker := by
  intro x hx
  have hb := (H2π_eq_zero_iff x).mp hx
  obtain ⟨y,hy⟩ := hb
  change onChains q hq hc x.val=0
  rw [←hy]
  exact LinearMap.congr_fun (onChains_d3 q hq hc) y

theorem cycles_to_h2_surjective : Function.Surjective (H2π (coefficients E)) := by
  intro x
  induction x using H2_induction_on with
  | h x => exact ⟨x,rfl⟩

noncomputable def transgression : H2 (coefficients E) →ₗ[ℤ] Additive (Kernel q hc) :=
by
  let f : cycles₂ (coefficients E) →ₗ[ℤ] H2 (coefficients E) := (H2π (coefficients E)).hom
  have hf : Function.Surjective f := cycles_to_h2_surjective
  have hk : f.ker ≤ (onCycles q hq hc).ker := onCycles_kills_homology_kernel q hq hc
  exact factorThrough f hf (onCycles q hq hc) hk

@[simp] theorem transgression_cycle (x : cycles₂ (coefficients E)) :
    transgression q hq hc (H2π (coefficients E) x)=onCycles q hq hc x :=
  factorThrough_apply _ _ _ _ x

end IntegralTransgression
end IntegralTransgressionFinite

section IntegralHomologyConjugation
open Classical _root_.CategoryTheory Finsupp groupHomology
namespace IntegralHomology

abbrev coefficients (E : Type) [Group E] := IntegralTransgression.coefficients E

variable {E F : Type} [Group E] [Group F]

noncomputable def coefficientMap (f : E →* F) : coefficients E ⟶ Rep.res f (coefficients F) :=
  Rep.ofHom ⟨LinearMap.id,fun _ => rfl⟩

noncomputable def mapH2 (f : E →* F) : H2 (coefficients E) →ₗ[ℤ] H2 (coefficients F) :=
  (groupHomology.map f (coefficientMap f) 2).hom

noncomputable def mapC2 (f : E →* F) : (E×E →₀ ℤ) →ₗ[ℤ] (F×F →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (Prod.map f f)

@[simp] theorem mapC2_single (f : E →* F) (x y : E) (n : ℤ) :
    mapC2 f (single (x,y) n)=single (f x,f y) n := by
  simp [mapC2]

noncomputable def prism1 (c : E) : (E →₀ ℤ) →ₗ[ℤ] (E×E →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => single (c,x) 1 - single (MulAut.conj c x,c) 1)

noncomputable def prism2 (c : E) : (E×E →₀ ℤ) →ₗ[ℤ] (E×E×E →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun xy =>
    single (c,xy.1,xy.2) 1 - single (MulAut.conj c xy.1,c,xy.2) 1 +
      single (MulAut.conj c xy.1,MulAut.conj c xy.2,c) 1)

@[simp] theorem prism1_single (c x : E) (n : ℤ) :
    prism1 c (single x n)=single (c,x) n-single (MulAut.conj c x,c) n := by
  simp [prism1,smul_sub,Finsupp.smul_single]

@[simp] theorem prism2_single (c x y : E) (n : ℤ) :
    prism2 c (single (x,y) n)=single (c,x,y) n-single (MulAut.conj c x,c,y) n+
      single (MulAut.conj c x,MulAut.conj c y,c) n := by
  simp [prism2,smul_sub,smul_add,Finsupp.smul_single]

end IntegralHomology
end IntegralHomologyConjugation

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_IntegralHomologyFunctorial
attribute [-instance] _root_.OAI.SimpleAmenable.fiveTrackPerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section IntegralHomologyFunctorial
open Classical _root_.CategoryTheory Finsupp groupHomology
namespace IntegralHomology
variable {E F G : Type} [Group E] [Group F] [Group G]

@[simp] theorem mapH2_id : mapH2 (MonoidHom.id E)=LinearMap.id := by
  have he : coefficientMap (MonoidHom.id E)=𝟙 (coefficients E) := rfl
  unfold mapH2
  rw [he,groupHomology.map_id]
  rfl

end IntegralHomology
end IntegralHomologyFunctorial

section ConfigurationChains
open Classical Finsupp
namespace ConfigurationChains
variable {V : Type*}
abbrev Chain (V : Type*) := List V →₀ ℤ

noncomputable def cone (v : V) : Chain V →ₗ[ℤ] Chain V :=
  Finsupp.lmapDomain ℤ ℤ (List.cons v)

@[simp] theorem cone_single (v : V) (l : List V) (n : ℤ) :
    cone v (single l n)=single (v::l) n := by
  simp [cone]

noncomputable def faceSum : List V → Chain V
  | [] => 0
  | v::l => single l 1-cone v (faceSum l)

noncomputable def boundary : Chain V →ₗ[ℤ] Chain V :=
  Finsupp.linearCombination ℤ faceSum

@[simp] theorem boundary_single (l : List V) (n : ℤ) :
    boundary (single l n)=n • faceSum l := by
  simp [boundary]

theorem boundary_cone (v : V) (c : Chain V) :
    boundary (cone v c)=c-cone v (boundary c) := by
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l n c hl hn ih =>
    simp only [map_add,cone_single,boundary_single,faceSum,smul_sub,map_smul,ih]
    rw [Finsupp.smul_single,smul_eq_mul,mul_one]
    abel

@[simp] theorem boundary_faceSum (l : List V) : boundary (faceSum l)=0 := by
  induction l with
  | nil => simp [faceSum]
  | cons v l ih => simp [faceSum,boundary_cone,ih]

@[simp] theorem boundary_boundary (c : Chain V) : boundary (boundary c)=0 := by
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l n c hl hn ih => simp [ih]

noncomputable def vertices (c : Chain V) : Finset V := c.support.biUnion List.toFinset

@[simp] theorem vertices_zero : vertices (0 : Chain V)=∅ := by simp [vertices]

theorem mem_vertices {c : Chain V} {v : V} : v∈vertices c ↔ ∃l∈c.support,v∈l := by
  simp [vertices]

theorem vertices_single_subset (l : List V) (n : ℤ) :
    vertices (single l n)⊆l.toFinset := by
  intro v hv
  obtain ⟨s,hs,hv⟩ := mem_vertices.mp hv
  have he : s=l := Finset.mem_singleton.mp (Finsupp.support_single_subset hs)
  simpa [he] using hv

theorem vertices_add_subset (c d : Chain V) : vertices (c+d)⊆vertices c∪vertices d := by
  intro v hv
  obtain ⟨l,hl,hv⟩ := mem_vertices.mp hv
  rcases Finset.mem_union.mp (Finsupp.support_add hl) with hl|hl
  · exact Finset.mem_union.mpr (Or.inl (mem_vertices.mpr ⟨l,hl,hv⟩))
  · exact Finset.mem_union.mpr (Or.inr (mem_vertices.mpr ⟨l,hl,hv⟩))

@[simp] theorem vertices_neg (c : Chain V) : vertices (-c)=vertices c := by
  simp [vertices]

theorem vertices_sub_subset (c d : Chain V) : vertices (c-d)⊆vertices c∪vertices d := by
  simpa [sub_eq_add_neg] using vertices_add_subset c (-d)

theorem cone_support_subset (v : V) (c : Chain V) :
    (cone v c).support⊆c.support.image (List.cons v) := by
  exact Finsupp.mapDomain_support

theorem vertices_cone_subset (v : V) (c : Chain V) :
    vertices (cone v c)⊆insert v (vertices c) := by
  intro x hx
  obtain ⟨l,hl,hx⟩ := mem_vertices.mp hx
  obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp (cone_support_subset v c hl)
  rcases List.mem_cons.mp hx with rfl|hx
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (mem_vertices.mpr ⟨s,hs,hx⟩)

theorem faceSum_support {l s : List V} (hs : s∈(faceSum l).support) :
    s.Sublist l ∧ s.length+1=l.length := by
  induction l generalizing s with
  | nil => simp [faceSum] at hs
  | cons v l ih =>
    have hu := Finsupp.support_sub hs
    rcases Finset.mem_union.mp hu with hs|hs
    · have he : s=l := Finset.mem_singleton.mp (Finsupp.support_single_subset hs)
      subst s
      exact ⟨List.sublist_cons_self _ _,by simp⟩
    · obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp (cone_support_subset v _ hs)
      obtain ⟨hts,htl⟩ := ih ht
      exact ⟨hts.cons_cons _,by simp; omega⟩

theorem faceSum_support_card (l : List V) : (faceSum l).support.card≤l.length := by
  induction l with
  | nil => simp [faceSum]
  | cons v l ih =>
    calc
      (faceSum (v::l)).support.card ≤
          ((single l (1:ℤ)).support∪(cone v (faceSum l)).support).card :=
        Finset.card_le_card Finsupp.support_sub
      _ ≤ (single l (1:ℤ)).support.card+(cone v (faceSum l)).support.card := Finset.card_union_le _ _
      _ ≤ 1+(faceSum l).support.card := by
        have hc := Finset.card_le_card (cone_support_subset v (faceSum l))
        have hi := Finset.card_image_le (s:=(faceSum l).support) (f:=List.cons v)
        simp only [Finsupp.support_single _ (by decide : (1:ℤ)≠0),Finset.card_singleton]
        omega
      _ ≤ (v::l).length := by simp; omega

end ConfigurationChains
end ConfigurationChains

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_Configuration
attribute [-instance] _root_.OAI.SimpleAmenable.fiveTrackPerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ConfigurationSupport
open Classical Finsupp
namespace ConfigurationChains
variable {V : Type*}

theorem linear_expansion (f : Chain V →ₗ[ℤ] Chain V) (c : Chain V) :
    f c=c.sum (fun l n => n • f (single l 1)) := by
  conv_lhs => rw [← Finsupp.sum_single c]
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro l hl
  rw [←map_smul,Finsupp.smul_single,smul_eq_mul,mul_one]

theorem linear_support_subset (f : Chain V →ₗ[ℤ] Chain V) (c : Chain V) :
    (f c).support⊆c.support.biUnion (fun l => (f (single l 1)).support) := by
  rw [linear_expansion f c]
  intro s hs
  obtain ⟨l,hl,hs⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hs)
  exact Finset.mem_biUnion.mpr ⟨l,hl,Finsupp.support_smul hs⟩

theorem vertices_linear_subset (f : Chain V →ₗ[ℤ] Chain V) (c : Chain V) :
    vertices (f c)⊆c.support.biUnion (fun l => vertices (f (single l 1))) := by
  intro v hv
  obtain ⟨s,hs,hv⟩ := mem_vertices.mp hv
  obtain ⟨l,hl,hs⟩ := Finset.mem_biUnion.mp (linear_support_subset f c hs)
  exact Finset.mem_biUnion.mpr ⟨l,hl,mem_vertices.mpr ⟨s,hs,hv⟩⟩

theorem vertices_linear_card (f : Chain V →ₗ[ℤ] Chain V) (c : Chain V)
    (b : ℕ) (hb : ∀l∈c.support,(vertices (f (single l 1))).card≤b) :
    (vertices (f c)).card ≤ c.support.card*b := by
  calc
    _ ≤ (c.support.biUnion (fun l => vertices (f (single l 1)))).card :=
      Finset.card_le_card (vertices_linear_subset f c)
    _ ≤ ∑l∈c.support,(vertices (f (single l 1))).card := Finset.card_biUnion_le
    _ ≤ ∑l∈c.support,b := Finset.sum_le_sum hb
    _ = _ := by simp

def Admissible (R : V → V → Prop) (n : ℕ) (c : Chain V) : Prop :=
  ∀l∈c.support,List.Pairwise R l ∧ l.length=n

@[simp] theorem admissible_zero (R : V → V → Prop) (n : ℕ) :
    Admissible R n (0 : Chain V) := by simp [Admissible]

theorem admissible_single {R : V → V → Prop} {n : ℕ} {l : List V}
    (hl : List.Pairwise R l) (hn : l.length=n) (k : ℤ) :
    Admissible R n (single l k) := by
  intro s hs
  have he : s=l := Finset.mem_singleton.mp (Finsupp.support_single_subset hs)
  subst s
  exact ⟨hl,hn⟩

theorem admissible_sub {R : V → V → Prop} {n : ℕ} {c d : Chain V}
    (hc : Admissible R n c) (hd : Admissible R n d) : Admissible R n (c-d) := by
  intro l hl
  rcases Finset.mem_union.mp (Finsupp.support_sub hl) with hl|hl
  · exact hc l hl
  · exact hd l hl

theorem admissible_linear {R : V → V → Prop} {n k : ℕ} {c : Chain V}
    (f : Chain V →ₗ[ℤ] Chain V) (hc : Admissible R n c)
    (hf : ∀l,List.Pairwise R l → l.length=n → Admissible R k (f (single l 1))) :
    Admissible R k (f c) := by
  intro s hs
  obtain ⟨l,hl,hs⟩ := Finset.mem_biUnion.mp (linear_support_subset f c hs)
  exact hf l (hc l hl).1 (hc l hl).2 s hs

theorem admissible_faceSum {R : V → V → Prop} {n : ℕ} {l : List V}
    (hl : List.Pairwise R l) (hn : l.length=n+1) : Admissible R n (faceSum l) := by
  intro s hs
  obtain ⟨hsub,hlen⟩ := faceSum_support hs
  exact ⟨hl.sublist hsub,by omega⟩

theorem admissible_boundary {R : V → V → Prop} {n : ℕ} {c : Chain V}
    (hc : Admissible R (n+1) c) : Admissible R n (boundary c) := by
  apply admissible_linear boundary hc
  intro l hl hn
  simpa using admissible_faceSum hl hn

theorem admissible_cone {R : V → V → Prop} {n : ℕ} {c : Chain V}
    (hc : Admissible R n c) (v : V) (hv : ∀w∈vertices c,R v w) :
    Admissible R (n+1) (cone v c) := by
  intro l hl
  obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp (cone_support_subset v c hl)
  have h := hc s hs
  refine ⟨List.pairwise_cons.mpr ⟨?_,h.1⟩,by simp [h.2]⟩
  intro w hw
  exact hv w (mem_vertices.mpr ⟨s,hs,hw⟩)

theorem linear_eq_on_admissible {R : V → V → Prop} {n : ℕ}
    (f g : Chain V →ₗ[ℤ] Chain V)
    (h : ∀l,List.Pairwise R l → l.length=n → f (single l 1)=g (single l 1))
    {c : Chain V} (hc : Admissible R n c) : f c=g c := by
  rw [linear_expansion f c,linear_expansion g c]
  apply Finsupp.sum_congr
  intro l hl
  rw [h l (hc l hl).1 (hc l hl).2]

end ConfigurationChains
end ConfigurationSupport

section BoundedConfigurationContraction
open Classical Finsupp
namespace ConfigurationChains
variable {V : Type*} {R : V → V → Prop}

structure Step (R : V → V → Prop) (n b : ℕ) where
  previous : Chain V →ₗ[ℤ] Chain V
  current : Chain V →ₗ[ℤ] Chain V
  equation : ∀c,Admissible R n c → boundary (current c)+previous (boundary c)=c
  admissible : ∀l,List.Pairwise R l → l.length=n →
    Admissible R (n+1) (current (single l 1))
  bounded : ∀l,List.Pairwise R l → l.length=n →
    (vertices (current (single l 1))).card≤b

namespace Step
variable {n b : ℕ} (D : Step R n b)

noncomputable def base (v : V) : Step R 0 1 where
  previous := 0
  current := cone v
  equation c hc := by
    have he : boundary c=0 := by
      have hz : ∀l,List.Pairwise R l → l.length=0 → boundary (single l 1)=(0 : Chain V) := by
        intro l hl hn
        have : l=[] := List.length_eq_zero_iff.mp hn
        simp [this,faceSum]
      exact linear_eq_on_admissible boundary 0 hz hc
    simp [boundary_cone,he]
  admissible l hl hn := by
    have : l=[] := List.length_eq_zero_iff.mp hn
    simp only [this,cone_single]
    exact admissible_single (by simp) (by simp) _
  bounded l hl hn := by
    have : l=[] := List.length_eq_zero_iff.mp hn
    simp only [this,cone_single]
    exact (Finset.card_le_card (vertices_single_subset [v] (1:ℤ))).trans (by simp)

noncomputable def residual (l : List V) : Chain V := single l 1-D.current (faceSum l)

theorem residual_admissible {l : List V} (hl : List.Pairwise R l) (hn : l.length=n+1) :
    Admissible R (n+1) (D.residual l) := by
  apply admissible_sub (admissible_single hl hn 1)
  exact admissible_linear D.current (admissible_faceSum hl hn) D.admissible

theorem residual_cycle {l : List V} (hl : List.Pairwise R l) (hn : l.length=n+1) :
    boundary (D.residual l)=0 := by
  have he := D.equation (faceSum l) (admissible_faceSum hl hn)
  simp only [boundary_faceSum,map_zero,add_zero] at he
  simp [residual,he]

theorem residual_bound {l : List V} (hl : List.Pairwise R l) (hn : l.length=n+1) :
    (vertices (D.residual l)).card≤(n+1)+(n+1)*b := by
  have hb : (vertices (D.current (faceSum l))).card≤(n+1)*b := by
    apply (vertices_linear_card D.current (faceSum l) b ?_).trans
      (Nat.mul_le_mul_right b ((faceSum_support_card l).trans hn.le))
    intro s hs
    have had := admissible_faceSum hl hn s hs
    exact D.bounded s had.1 had.2
  calc
    _ ≤ (vertices (single l 1)∪vertices (D.current (faceSum l))).card :=
      Finset.card_le_card (vertices_sub_subset _ _)
    _ ≤ (vertices (single l 1)).card+(vertices (D.current (faceSum l))).card := Finset.card_union_le _ _
    _ ≤ l.toFinset.card+(n+1)*b := Nat.add_le_add
      (Finset.card_le_card (vertices_single_subset _ _)) hb
    _ ≤ (n+1)+(n+1)*b := Nat.add_le_add_right ((List.toFinset_card_le l).trans hn.le) _

variable (hc : ∀S : Finset V,S.card≤(n+1)+(n+1)*b → ∃v,∀w∈S,R v w)

noncomputable def nextVertex (l : List V) (hl : List.Pairwise R l ∧ l.length=n+1) : V :=
  (hc (vertices (D.residual l)) (D.residual_bound hl.1 hl.2)).choose

theorem nextVertex_rel (l : List V) (hl : List.Pairwise R l ∧ l.length=n+1) :
    ∀w∈vertices (D.residual l),R (D.nextVertex hc l hl) w :=
  (hc _ (D.residual_bound hl.1 hl.2)).choose_spec

noncomputable def nextGenerator (l : List V) : Chain V :=
  if hl : List.Pairwise R l ∧ l.length=n+1 then
    cone (D.nextVertex hc l hl) (D.residual l) else 0

noncomputable def next : Chain V →ₗ[ℤ] Chain V :=
  Finsupp.linearCombination ℤ (D.nextGenerator hc)

@[simp] theorem next_single (l : List V) :
    D.next hc (single l 1)=D.nextGenerator hc l := by simp [next]

theorem next_contraction {l : List V} (hl : List.Pairwise R l) (hn : l.length=n+1) :
    boundary (D.next hc (single l 1))+D.current (boundary (single l 1))=single l 1 := by
  rw [next_single,nextGenerator,dite_eq_left ⟨hl,hn⟩,boundary_cone,D.residual_cycle hl hn]
  simp [residual]

theorem next_admissible {l : List V} (hl : List.Pairwise R l) (hn : l.length=n+1) :
    Admissible R (n+1+1) (D.next hc (single l 1)) := by
  rw [next_single,nextGenerator,dite_eq_left ⟨hl,hn⟩]
  exact admissible_cone (D.residual_admissible hl hn) _ (D.nextVertex_rel hc l ⟨hl,hn⟩)

theorem next_bounded {l : List V} (hl : List.Pairwise R l) (hn : l.length=n+1) :
    (vertices (D.next hc (single l 1))).card≤1+(n+1)+(n+1)*b := by
  rw [next_single,nextGenerator,dite_eq_left ⟨hl,hn⟩]
  have hi := Finset.card_le_card (vertices_cone_subset (D.nextVertex hc l ⟨hl,hn⟩) (D.residual l))
  have hj := Finset.card_insert_le (D.nextVertex hc l ⟨hl,hn⟩) (vertices (D.residual l))
  have hb := D.residual_bound hl hn
  omega

noncomputable def extend : Step R (n+1) (1+(n+1)+(n+1)*b) where
  previous := D.current
  current := D.next hc
  equation c h := by
    have he : (boundary.comp (D.next hc)+D.current.comp boundary) c=LinearMap.id c :=
      linear_eq_on_admissible _ _ (fun _ hl hn => D.next_contraction hc hl hn) h
    exact he
  admissible _ := D.next_admissible hc
  bounded _ := D.next_bounded hc

include D in

theorem fills {c : Chain V} (hc : Admissible R n c) (hz : boundary c=0) :
    ∃d,Admissible R (n+1) d ∧ boundary d=c := by
  refine ⟨D.current c,admissible_linear D.current hc D.admissible,?_⟩
  have he := D.equation c hc
  simpa [hz] using he

end Step

def bankBound : ℕ → ℕ
  | 0 => 1
  | n+1 => 1+(n+1)+(n+1)*bankBound n

theorem bankBound_mono : Monotone bankBound := by
  apply monotone_nat_of_le_succ
  intro n
  rw [bankBound]
  have hh : bankBound n≤(n+1)*bankBound n := by nlinarith
  omega

theorem exists_step (N : ℕ)
    (hc : ∀S : Finset V,S.card≤bankBound N → ∃v,∀w∈S,R v w) :
    ∀n≤N,Nonempty (Step R n (bankBound n)) := by
  intro n hn
  induction n with
  | zero =>
    obtain ⟨v,hv⟩ := hc ∅ (by simp)
    exact ⟨Step.base v⟩
  | succ n ih =>
    obtain ⟨D⟩ := ih (by omega)
    refine ⟨D.extend (fun S hS => hc S ?_)⟩
    apply hS.trans
    apply le_trans (by simp only [bankBound]; omega) (bankBound_mono hn)

theorem low_degree_filling
    (hc : ∀S : Finset V,S.card≤31 → ∃v,∀w∈S,R v w)
    {n : ℕ} (hn : n≤3) {c : Chain V} (had : Admissible R n c) (hz : boundary c=0) :
    ∃d,Admissible R (n+1) d ∧ boundary d=c := by
  obtain ⟨D⟩ := exists_step (R:=R) 3 (by simpa [bankBound] using hc) n hn
  exact D.fills had hz

end ConfigurationChains
end BoundedConfigurationContraction

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ConfigurationEquivariance
attribute [-instance] _root_.OAI.SimpleAmenable.fiveTrackPerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ConfigurationEquivariance
open Classical Finsupp
namespace ConfigurationChains
variable {V W Z : Type*}

noncomputable def push (f : V → W) : Chain V →ₗ[ℤ] Chain W :=
  Finsupp.lmapDomain ℤ ℤ (List.map f)

@[simp] theorem push_single (f : V → W) (l : List V) (n : ℤ) :
    push f (single l n)=single (l.map f) n := by simp [push]

@[simp] theorem push_id (c : Chain V) : push id c=c := by
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l n c hl hn ih => simp [ih]

@[simp] theorem push_comp (g : W → Z) (f : V → W) (c : Chain V) :
    push g (push f c)=push (g ∘ f) c := by
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l n c hl hn ih => simp [ih, List.map_map]

theorem push_cone (f : V → W) (v : V) (c : Chain V) :
    push f (cone v c)=cone (f v) (push f c) := by
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l n c hl hn ih => simp [ih]

theorem push_faceSum (f : V → W) (l : List V) :
    push f (faceSum l)=faceSum (l.map f) := by
  induction l with
  | nil => simp [faceSum]
  | cons v l ih => simp [faceSum,push_cone,ih]

theorem push_boundary (f : V → W) (c : Chain V) :
    push f (boundary c)=boundary (push f c) := by
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l n c hl hn ih => simp [push_faceSum,ih]

theorem push_admissible {R : V → V → Prop} {S : W → W → Prop}
    (f : V → W) (hf : ∀v w,R v w → S (f v) (f w)) {n : ℕ} {c : Chain V}
    (hc : Admissible R n c) : Admissible S n (push f c) := by
  intro l hl
  obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hl)
  exact ⟨List.pairwise_map.mpr ((hc k hk).1.imp (fun h => hf _ _ h)),
    by simpa only [List.length_map] using (hc k hk).2⟩

noncomputable def degree (R : V → V → Prop) (n : ℕ) : Submodule ℤ (Chain V) where
  carrier := {c | Admissible R n c}
  zero_mem' := admissible_zero R n
  add_mem' := by
    intro c d hc hd l hl
    rcases Finset.mem_union.mp (Finsupp.support_add hl) with hl|hl
    · exact hc l hl
    · exact hd l hl
  smul_mem' := by
    intro k c hc l hl
    exact hc l (Finsupp.support_smul hl)

@[simp] theorem mem_degree {R : V → V → Prop} {n : ℕ} {c : Chain V} :
    c∈degree R n ↔ Admissible R n c := Iff.rfl

noncomputable def degreeBoundary (R : V → V → Prop) (n : ℕ) :
    degree R (n+1) →ₗ[ℤ] degree R n :=
  boundary.restrict (fun _ h => admissible_boundary h)

@[simp] theorem degreeBoundary_val {R : V → V → Prop} {n : ℕ}
    (c : degree R (n+1)) : (degreeBoundary R n c).val=boundary c.val := rfl

@[simp] theorem degreeBoundary_square (R : V → V → Prop) (n : ℕ)
    (c : degree R (n+2)) : degreeBoundary R n (degreeBoundary R (n+1) c)=0 := by
  apply Subtype.ext
  exact boundary_boundary c.val

noncomputable def degreePush {R : V → V → Prop} {S : W → W → Prop}
    (f : V → W) (hf : ∀v w,R v w → S (f v) (f w)) (n : ℕ) :
    degree R n →ₗ[ℤ] degree S n :=
  (push f).restrict (fun _ h => push_admissible f hf h)

@[simp] theorem degreePush_val {R : V → V → Prop} {S : W → W → Prop}
    (f : V → W) (hf : ∀v w,R v w → S (f v) (f w)) (n : ℕ)
    (c : degree R n) : (degreePush f hf n c).val=push f c.val := rfl

theorem degreePush_boundary {R : V → V → Prop} {S : W → W → Prop}
    (f : V → W) (hf : ∀v w,R v w → S (f v) (f w)) (n : ℕ)
    (c : degree R (n+1)) :
    degreePush f hf n (degreeBoundary R n c)=
      degreeBoundary S n (degreePush f hf (n+1) c) := by
  apply Subtype.ext
  exact push_boundary f c.val

end ConfigurationChains
end ConfigurationEquivariance

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ConfigurationResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ConfigurationResolution
open Classical _root_.CategoryTheory Finsupp
namespace ConfigurationChains
variable {V : Type*} {R : V → V → Prop}

noncomputable def representation {G : Type*} [Monoid G] [MulAction G V]
    (hR : ∀g : G,∀v w,R v w → R (g • v) (g • w)) (n : ℕ) :
    Representation ℤ G (degree R n) where
  toFun g := degreePush (fun v => g • v) (hR g) n
  map_one' := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    change push (fun v : V => (1:G) • v) c.val=c.val
    have he : (fun v : V => (1:G) • v)=id := funext (fun v => one_smul G v)
    rw [he]
    exact push_id c.val
  map_mul' g h := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    change push (fun v : V => (g*h) • v) c.val=push (fun v => g • v) (push (fun v => h • v) c.val)
    rw [push_comp]
    simp only [Function.comp_def, mul_smul]

@[simp] theorem representation_boundary {G : Type*} [Monoid G] [MulAction G V]
    (hR : ∀g : G,∀v w,R v w → R (g • v) (g • w)) (g : G) (n : ℕ)
    (c : degree R (n+1)) :
    representation hR n g (degreeBoundary R n c)=
      degreeBoundary R n (representation hR (n+1) g c) :=
  degreePush_boundary _ (hR g) n c

noncomputable def simplexModuleEquiv (R : V → V → Prop) (n : ℕ) :
    degree R n ≃ₗ[ℤ] ({l : List V // l.Pairwise R ∧ l.length=n} →₀ ℤ) := by
  have he : degree R n=Finsupp.supported ℤ ℤ {l : List V | l.Pairwise R ∧ l.length=n} := by
    ext c
    rw [Finsupp.mem_supported]
    rfl
  exact (LinearEquiv.ofEq _ _ he).trans (Finsupp.supportedEquivFinsupp _)

theorem lowDegree_exact
    (hc : ∀S : Finset V,S.card≤31 → ∃v,∀w∈S,R v w)
    {n : ℕ} (hn : n≤2) :
    Function.Exact (degreeBoundary R (n+1)) (degreeBoundary R n) := by
  intro c
  constructor
  · intro hz
    have hz' : boundary c.val=0 := congrArg Subtype.val hz
    obtain ⟨d,hd,he⟩ := low_degree_filling hc (by omega : n+1≤3) c.property hz'
    exact ⟨⟨d,hd⟩,Subtype.ext he⟩
  · rintro ⟨d,rfl⟩
    exact degreeBoundary_square R n d

end ConfigurationChains

end ConfigurationResolution

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PolygonArea
attribute [-instance] _root_.OAI.SimpleAmenable.fiveTrackPerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section PolygonJordan
open Classical Set MeasureTheory
namespace PolygonArea

noncomputable def square : Set (ℝ×ℝ) := Ico (0:ℝ) 1 ×ˢ Ico (0:ℝ) 1

theorem null_frontier_inter {S T : Set (ℝ×ℝ)}
    (hS : volume (frontier S)=0) (hT : volume (frontier T)=0) :
    volume (frontier (S∩T))=0 := by
  apply measure_mono_null (subset_trans (frontier_inter_subset S T) ?_)
    (measure_union_null hS hT)
  exact Set.union_subset_union Set.inter_subset_left Set.inter_subset_right

theorem null_frontier_union {S T : Set (ℝ×ℝ)}
    (hS : volume (frontier S)=0) (hT : volume (frontier T)=0) :
    volume (frontier (S∪T))=0 := by
  apply measure_mono_null (subset_trans (frontier_union_subset S T) ?_)
    (measure_union_null hS hT)
  exact Set.union_subset_union Set.inter_subset_left Set.inter_subset_right

theorem null_frontier_diff {S T : Set (ℝ×ℝ)}
    (hS : volume (frontier S)=0) (hT : volume (frontier T)=0) :
    volume (frontier (S\T))=0 := by
  change volume (frontier (S ∩ Tᶜ))=0
  exact null_frontier_inter hS (by simpa only [frontier_compl] using hT)

theorem closure_ae_eq {S : Set (ℝ×ℝ)} (hS : volume (frontier S)=0) : closure S=ᵐ[volume] S := by
  have hn : ∀ᵐp : ℝ×ℝ,p∉frontier S := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hS
  filter_upwards [hn] with p hp
  apply propext
  constructor
  · intro hx
    exact interior_subset (show p∈interior S from by
      by_contra hn
      exact hp ⟨hx,hn⟩)
  · intro hx
    exact subset_closure hx

theorem interior_ae_eq {S : Set (ℝ×ℝ)} (hS : volume (frontier S)=0) : interior S=ᵐ[volume] S := by
  have hn : ∀ᵐp : ℝ×ℝ,p∉frontier S := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hS
  filter_upwards [hn] with p hp
  apply propext
  constructor
  · intro hx
    exact interior_subset hx
  · intro hx
    by_contra hn
    exact hp ⟨subset_closure hx,hn⟩

end PolygonArea
end PolygonJordan

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonGrid
attribute [-instance] _root_.OAI.SimpleAmenable.fiveTrackPerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonGrid
open Classical Set MeasureTheory Metric
namespace PolygonGrid

abbrev PlaneTracks := ℕ × ℝ × ℝ
abbrev Index (m N : ℕ) := Fin m × Fin N × Fin N
noncomputable def μ : Measure PlaneTracks := Measure.count.prod ((volume : Measure ℝ).prod volume)
noncomputable def interval (ε : ℝ) (i : ℕ) : Set ℝ := Ico (ε*i) (ε*(i+1))
noncomputable def cell {m N : ℕ} (ε : ℝ) (i : Index m N) : Set PlaneTracks :=
  {i.1.val} ×ˢ interval ε i.2.1.val ×ˢ interval ε i.2.2.val
noncomputable def region (m : ℕ) : Set PlaneTracks :=
  {i : ℕ | i < m} ×ˢ Ico (0:ℝ) 1 ×ˢ Ico (0:ℝ) 1

@[simp] theorem measurable_cell {m N : ℕ} (ε : ℝ) (i : Index m N) : MeasurableSet (cell ε i) :=
  (measurableSet_singleton _).prod (measurableSet_Ico.prod measurableSet_Ico)

@[simp] theorem volume_cell {m N : ℕ} (ε : ℝ) (i : Index m N) :
    μ (cell ε i)=ENNReal.ofReal ε * ENNReal.ofReal ε := by
  simp only [μ,cell,interval,Measure.prod_prod,Measure.count_singleton,one_mul,Real.volume_Ico]
  congr 2 <;> ring

theorem cells_disjoint {m N : ℕ} {ε : ℝ} (hε : 0 < ε) :
    Pairwise (fun i j : Index m N => Disjoint (cell ε i) (cell ε j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro p hi hj
  have ht : i.1=j.1 := Fin.ext (hi.1.symm.trans hj.1)
  have coord {i j : ℕ} {x : ℝ} (hi : x∈interval ε i) (hj : x∈interval ε j) : i=j := by
    rcases lt_trichotomy i j with h|h|h
    · have h' : (i:ℝ)+1 ≤ j := by exact_mod_cast h
      have := mul_le_mul_of_nonneg_left h' hε.le
      change ε*i ≤ x ∧ x < ε*(i+1) at hi
      change ε*j ≤ x ∧ x < ε*(j+1) at hj
      linarith
    · exact h
    · have h' : (j:ℝ)+1 ≤ i := by exact_mod_cast h
      have := mul_le_mul_of_nonneg_left h' hε.le
      change ε*i ≤ x ∧ x < ε*(i+1) at hi
      change ε*j ≤ x ∧ x < ε*(j+1) at hj
      linarith
  exact hij (Prod.ext ht (Prod.ext (Fin.ext (coord hi.2.1 hj.2.1)) (Fin.ext (coord hi.2.2 hj.2.2))))

theorem cell_dist {m N : ℕ} {ε : ℝ} (hε : 0 < ε) {i : Index m N} {p q : PlaneTracks}
    (hp : p∈cell ε i) (hq : q∈cell ε i) : dist p q < ε := by
  have coord {i : ℕ} {x y : ℝ} (hx : x∈interval ε i) (hy : y∈interval ε i) : dist x y < ε := by
    rw [Real.dist_eq,abs_lt]
    change ε*i ≤ x ∧ x < ε*(i+1) at hx
    change ε*i ≤ y ∧ y < ε*(i+1) at hy
    constructor <;> nlinarith
  have ht : p.1=q.1 := hp.1.trans hq.1.symm
  rw [Prod.dist_eq,Prod.dist_eq,ht,dist_self,max_lt_iff,max_lt_iff]
  exact ⟨hε,coord hp.2.1 hq.2.1,coord hp.2.2 hq.2.2⟩

theorem region_covered {m N : ℕ} {ε : ℝ} (hε : 0 < ε) (hN : 1/ε < (N:ℝ)) :
    region m⊆⋃i : Index m N,cell ε i := by
  rintro ⟨t,x,y⟩ ⟨ht,hx,hy⟩
  have coord {x : ℝ} (hx : x∈Ico (0:ℝ) 1) : ∃i : Fin N,x∈interval ε i.val := by
    have hnon : 0 ≤ x/ε := div_nonneg hx.1 hε.le
    have hlt : x/ε < (N:ℝ) := (div_lt_div_of_pos_right hx.2 hε).trans hN
    have hi : ⌊x/ε⌋₊ < N := by
      exact_mod_cast lt_of_le_of_lt (Nat.floor_le hnon) hlt
    refine ⟨⟨⌊x/ε⌋₊,hi⟩,?_,?_⟩
    · have h := (le_div_iff₀ hε).mp (Nat.floor_le hnon)
      nlinarith
    · have h := (div_lt_iff₀ hε).mp (Nat.lt_floor_add_one (x/ε))
      nlinarith
  obtain ⟨i,hi⟩ := coord hx
  obtain ⟨j,hj⟩ := coord hy
  exact Set.mem_iUnion.mpr ⟨(⟨t,ht⟩,i,j),rfl,hi,hj⟩

theorem volume_cells {m N : ℕ} {ε : ℝ} (hε : 0 < ε) (I : Finset (Index m N)) :
    μ (⋃i∈I,cell ε i)=I.card*(ENNReal.ofReal ε * ENNReal.ofReal ε) := by
  rw [measure_biUnion_finset (fun i hi j hj hij => cells_disjoint hε hij)
    (fun i _ => measurable_cell ε i)]
  simp only [volume_cell,Finset.sum_const, nsmul_eq_mul]

theorem matching_of_volume {m N : ℕ} {ε : ℝ} (hε : 0 < ε)
    (I J : Finset (Index m N))
    (hμ : μ (⋃i∈I,cell ε i) < μ (⋃j∈J,cell ε j)) : Nonempty (I ↪ J) := by
  have hc : I.card ≤ J.card := by
    by_contra hn
    have hnat : J.card ≤ I.card := by omega
    have hcast : (J.card : ENNReal) ≤ I.card := by exact_mod_cast hnat
    rw [volume_cells hε,volume_cells hε] at hμ
    exact not_lt_of_ge (mul_le_mul hcast le_rfl (by positivity) (by positivity)) hμ
  have hf : Fintype.card I ≤ Fintype.card J := by simpa using hc
  exact Function.Embedding.nonempty_of_card_le hf

end PolygonGrid
end PolygonGrid

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PolygonGridComparison
attribute [-instance] _root_.OAI.SimpleAmenable.fiveTrackPerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonGridComparison
open Classical Set MeasureTheory Metric
namespace PolygonGrid

instance instIsLocallyFiniteMeasureNatCount_solutions : IsLocallyFiniteMeasure (Measure.count : Measure ℕ) where
  finiteAtNhds n := ⟨{n}, (isOpen_discrete _).mem_nhds rfl, by simp⟩

instance instIsLocallyFiniteMeasurePlaneTracksμ : IsLocallyFiniteMeasure μ := by
  unfold μ
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance instOuterRegularPlaneTracksμ : Measure.OuterRegular μ := by
  unfold μ
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance instInnerRegularCompactLTTopPlaneTracksμ : Measure.InnerRegularCompactLTTop μ := by
  unfold μ
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

@[simp] theorem volume_region (m : ℕ) : μ (region m)=m := by
  have he : {i : ℕ | i < m}=(Finset.range m : Set ℕ) := by ext i; simp
  simp only [μ,region,Measure.prod_prod,he,Measure.count_apply_finset,Finset.card_range]
  simp

theorem compact_closure {m : ℕ} {S : Set PlaneTracks} (hS : S⊆region m) : IsCompact (closure S) := by
  let K : Set PlaneTracks := (Finset.range m : Set ℕ) ×ˢ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1
  have hK : IsCompact K := (Finset.finite_toSet _).isCompact.prod (isCompact_Icc.prod isCompact_Icc)
  apply hK.of_isClosed_subset isClosed_closure
  apply hK.isClosed.closure_subset_iff.mpr
  intro p hp
  have h := hS hp
  exact ⟨by simpa using h.1,⟨h.2.1.1,h.2.1.2.le⟩,⟨h.2.2.1,h.2.2.2.le⟩⟩

theorem strict_grid_comparison {m : ℕ} {S T : Set PlaneTracks}
    (hS : S⊆region m) (hT : T⊆region m)
    (hμ : μ (closure S) < μ (interior T)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ε : ℝ, 0 < ε → ε < δ →
      ∃ (N : ℕ) (I J : Finset (Index m N)), Nonempty (I ↪ J) ∧
        S⊆⋃i∈I,cell ε i ∧ ∀j∈J,cell ε j⊆T := by
  obtain ⟨r,hrS,hrT⟩ := exists_between hμ
  obtain ⟨O,hSO,hO,hOr⟩ := (closure S).exists_isOpen_lt_of_lt r hrS
  have hfinite : μ (interior T)≠⊤ := by
    apply ne_top_of_le_ne_top (by simp : μ (region m)≠⊤)
    exact measure_mono (Set.Subset.trans interior_subset hT)
  obtain ⟨K,hKT,hK,hrK⟩ := isOpen_interior.measurableSet.exists_lt_isCompact_of_ne_top hfinite hrT
  obtain ⟨δS,hδS,hOS⟩ := (compact_closure hS).exists_thickening_subset_open hO hSO
  obtain ⟨δK,hδK,hTK⟩ := hK.exists_thickening_subset_open isOpen_interior hKT
  refine ⟨min δS δK,lt_min hδS hδK,fun ε hε hδ => ?_⟩
  let N : ℕ := ⌈1/ε⌉₊+1
  have hN : 1/ε < (N:ℝ) := by
    have h := Nat.le_ceil (1/ε)
    dsimp [N]
    simp only [Nat.cast_add,Nat.cast_one]
    linarith
  let hits (A : Set PlaneTracks) : Finset (Index m N) := Finset.univ.filter (fun i => (cell ε i∩A).Nonempty)
  have cover (A : Set PlaneTracks) (hA : A⊆region m) : A⊆⋃i∈hits A,cell ε i := by
    intro p hp
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (region_covered hε hN (hA hp))
    exact Set.mem_iUnion₂.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,hi,hp⟩,hi⟩
  have inO : (⋃i∈hits S,cell ε i)⊆O := by
    intro p hp
    obtain ⟨i,hi,hp⟩ := Set.mem_iUnion₂.mp hp
    obtain ⟨q,hq,hqS⟩ := (Finset.mem_filter.mp hi).2
    apply hOS
    rw [mem_thickening_iff]
    exact ⟨q,subset_closure hqS,(cell_dist hε hp hq).trans (hδ.trans_le (min_le_left _ _))⟩
  have inT : ∀j∈hits K,cell ε j⊆T := by
    intro j hj p hp
    obtain ⟨q,hq,hqK⟩ := (Finset.mem_filter.mp hj).2
    apply interior_subset
    apply hTK
    rw [mem_thickening_iff]
    exact ⟨q,hqK,(cell_dist hε hp hq).trans (hδ.trans_le (min_le_right _ _))⟩
  have hKregion : K⊆region m := Set.Subset.trans hKT (Set.Subset.trans interior_subset hT)
  have hmass : μ (⋃i∈hits S,cell ε i) < μ (⋃j∈hits K,cell ε j) :=
    lt_of_le_of_lt (measure_mono inO) ((hOr.trans hrK).trans_le (measure_mono (cover K hKregion)))
  exact ⟨N,hits S,hits K,matching_of_volume hε _ _ hmass,cover S hS,inT⟩

end PolygonGrid
end PolygonGridComparison

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonTrackArea
attribute [-instance] _root_.OAI.SimpleAmenable.fiveTrackPerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonTrackArea
open Classical Set MeasureTheory
namespace PolygonGrid

noncomputable def trackUnion {m : ℕ} (S : Fin m → Set (ℝ×ℝ)) : Set PlaneTracks :=
  ⋃i, {i.val} ×ˢ S i

@[simp] theorem mem_trackUnion {m : ℕ} (S : Fin m → Set (ℝ×ℝ)) (i : Fin m) (x : ℝ×ℝ) :
    (i.val,x)∈trackUnion S ↔ x∈S i := by
  constructor
  · intro h
    obtain ⟨j,hj,hx⟩ := Set.mem_iUnion.mp h
    have he : i=j := Fin.ext hj
    simpa only [←he] using hx
  · intro hx
    exact Set.mem_iUnion.mpr ⟨i,rfl,hx⟩

theorem trackUnion_mono {m : ℕ} {S T : Fin m → Set (ℝ×ℝ)} (h : ∀i,S i⊆T i) :
    trackUnion S⊆trackUnion T := by
  intro p hp
  obtain ⟨i,hi,hp⟩ := Set.mem_iUnion.mp hp
  exact Set.mem_iUnion.mpr ⟨i,hi,h i hp⟩

theorem trackUnion_region {m : ℕ} {S : Fin m → Set (ℝ×ℝ)}
    (h : ∀i,S i⊆PolygonArea.square) : trackUnion S⊆region m := by
  intro p hp
  obtain ⟨i,hi,hp⟩ := Set.mem_iUnion.mp hp
  exact ⟨hi ▸ i.isLt,h i hp⟩

@[simp] theorem volume_trackUnion {m : ℕ} (S : Fin m → Set (ℝ×ℝ))
    (hS : ∀i,MeasurableSet (S i)) : μ (trackUnion S)=∑i,volume (S i) := by
  have hdis : Pairwise (fun i j : Fin m => Disjoint ({i.val}×ˢ S i) ({j.val}×ˢ S j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro p ⟨hi,-⟩ ⟨hj,-⟩
    exact hij (Fin.ext (hi.symm.trans hj))
  rw [trackUnion,measure_iUnion hdis (fun i => (measurableSet_singleton _).prod (hS i))]
  simp only [μ,Measure.prod_prod,Measure.count_singleton,one_mul,tsum_fintype]
  rfl

end PolygonGrid
end PolygonTrackArea

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_TransitiveInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section TransitiveInduction

open Classical _root_.CategoryTheory Representation Finsupp
namespace TransitiveInduction
variable {G X : Type} [Group G] [MulAction G X] (x : X)

lemma mk_same {g h : G} (he : g⁻¹ • x=h⁻¹ • x) (z : ℤ) :
    IndV.mk (MulAction.stabilizer G x).subtype
      (Representation.trivial ℤ (MulAction.stabilizer G x) ℤ) g z=
    IndV.mk (MulAction.stabilizer G x).subtype
      (Representation.trivial ℤ (MulAction.stabilizer G x) ℤ) h z := by
  have hs : h*g⁻¹∈MulAction.stabilizer G x := by
    change (h*g⁻¹) • x=x
    rw [mul_smul,he,smul_inv_smul]
  have hh := Coinvariants.mk_self_apply
    (Representation.tprod ((Representation.leftRegular ℤ G).comp (MulAction.stabilizer G x).subtype)
      (Representation.trivial ℤ (MulAction.stabilizer G x) ℤ))
    (⟨h*g⁻¹,hs⟩ : MulAction.stabilizer G x)
    (TensorProduct.tmul ℤ (MonoidAlgebra.single g (1:ℤ)) z)
  simpa [IndV.mk,Representation.tprod_apply,mul_assoc] using hh.symm

noncomputable def transport (ht : ∀y : X,∃g : G,g • x=y) (y : X) : G := (ht y).choose
@[simp] theorem transport_spec (ht : ∀y : X,∃g : G,g • x=y) (y : X) :
    transport x ht y • x=y := (ht y).choose_spec

noncomputable def fromPermutation (ht : ∀y : X,∃g : G,g • x=y) :
    (X →₀ ℤ) →ₗ[ℤ] Representation.IndV (MulAction.stabilizer G x).subtype
      (Representation.trivial ℤ (MulAction.stabilizer G x) ℤ) :=
  Finsupp.lsum ℤ (fun y => IndV.mk _ _ (transport x ht y)⁻¹)

@[simp] theorem fromPermutation_single (ht : ∀y : X,∃g : G,g • x=y) (y : X) (z : ℤ) :
    fromPermutation x ht (Finsupp.single y z)=IndV.mk _ _ (transport x ht y)⁻¹ z := by
  exact Finsupp.lsum_single ℤ _ y z

end TransitiveInduction
end TransitiveInduction

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_TransitiveCanonical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable.TransitiveInduction
variable {G X Y : Type} [Group G] [MulAction G X] [MulAction G Y]

def stabilizerMap (f : X → Y) (hf : ∀g : G,∀x,f (g • x)=g • f x) (x : X) :
    MulAction.stabilizer G x →* MulAction.stabilizer G (f x) :=
  (MulAction.stabilizer G x).inclusion (by
    intro g hg
    change g • f x=f x
    rw [← hf, hg])

noncomputable def trivialMap {K L : Type} [Group K] [Group L] (f : K →* L) :
    Rep.trivial ℤ K ℤ ⟶ Rep.res f (Rep.trivial ℤ L ℤ) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

lemma isIso_map_trivial_H0 {K L : Type} [Group K] [Group L] (f : K →* L) :
    IsIso (groupHomology.map f (trivialMap f) 0) := by
  have he : (groupHomology.H0IsoOfIsTrivial (Rep.trivial ℤ K ℤ)).inv ≫
      groupHomology.map f (trivialMap f) 0 =
      (groupHomology.H0IsoOfIsTrivial (Rep.trivial ℤ L ℤ)).inv := by
    rw [groupHomology.H0IsoOfIsTrivial_inv_eq_π,
      groupHomology.H0π_comp_map, groupHomology.H0IsoOfIsTrivial_inv_eq_π]
    change 𝟙 _ ≫ _ = _
    exact Category.id_comp _
  exact IsIso.of_isIso_fac_left he

end SimpleAmenable.TransitiveInduction

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_HomologyAdditive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable

namespace PolygonPlacement.Configuration
attribute [local instance 1200] Rep.hV2
variable {a m p : ℕ}

noncomputable def facePermutation (i j : Fin (p+1)) : Equiv.Perm (Fin (p+1)) :=
  (finSuccEquiv' i).trans (finSuccEquiv' j).symm

@[simp] lemma facePermutation_apply (i j : Fin (p+1)) (k : Fin p) :
    facePermutation i j (i.succAbove k)=j.succAbove k := by
  simp [facePermutation]

end PolygonPlacement.Configuration
end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_FullGroupStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable

attribute [local instance 1200] Rep.hV2

namespace TrivialHomology
variable {G H K : Type} [Group G] [Group H] [Group K]
noncomputable abbrev map (f : G →* H) (q : ℕ) :=
  groupHomology.map f (TransitiveInduction.trivialMap f) q

@[simp] lemma map_id (q : ℕ) : map (MonoidHom.id G) q=𝟙 _ := by
  exact groupHomology.map_id (A:=Rep.trivial ℤ G ℤ) (n:=q)

lemma map_comp (f : G →* H) (g : H →* K) (q : ℕ) :
    map (g.comp f) q = map f q ≫ map g q := by
  exact groupHomology.map_comp f g (TransitiveInduction.trivialMap f)
    (TransitiveInduction.trivialMap g) q

lemma isIso_equiv (e : G ≃* H) (q : ℕ) : IsIso (map e.toMonoidHom q) := by
  refine ⟨⟨map e.symm.toMonoidHom q,?_,?_⟩⟩
  · rw [← map_comp]
    have he : e.symm.toMonoidHom.comp e.toMonoidHom=MonoidHom.id G := by ext; simp
    rw [he, map_id]
  · rw [← map_comp]
    have he : e.toMonoidHom.comp e.symm.toMonoidHom=MonoidHom.id H := by ext; simp
    rw [he, map_id]
end TrivialHomology

end SimpleAmenable

end

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable.TrivialHomology

attribute [local instance 1200] Rep.hV2
variable {G H : Type} [Group G] [Group H]

noncomputable def abelianizationEquiv (G : Type) [Group G] :
    groupHomology.H1 (Rep.trivial ℤ G ℤ) ≃+ Additive (Abelianization G) :=
  (groupHomology.H1AddEquivOfIsTrivial (Rep.trivial ℤ G ℤ)).trans
    (TensorProduct.rid ℤ (Additive (Abelianization G))).toAddEquiv

noncomputable def cycle (g : G) : groupHomology.H1 (Rep.trivial ℤ G ℤ) :=
  groupHomology.H1π _ ((groupHomology.cycles₁IsoOfIsTrivial _).inv (single g (1:ℤ)))

@[simp] lemma abelianizationEquiv_cycle (g : G) :
    abelianizationEquiv G (cycle g)=Additive.ofMul (Abelianization.of g) := by
  change (TensorProduct.rid ℤ (Additive (Abelianization G)))
    ((groupHomology.H1AddEquivOfIsTrivial (Rep.trivial ℤ G ℤ))
      (groupHomology.H1π _ ((groupHomology.cycles₁IsoOfIsTrivial _).inv (single g (1:ℤ))))) = _
  rw [groupHomology.H1AddEquivOfIsTrivial_single, TensorProduct.rid_tmul]
  simp

lemma cycle_map (f : G →* H) (g : G) : map f 1 (cycle g)=cycle (f g) := by
  unfold cycle
  rw [groupHomology.H1π_comp_map_apply]
  congr 1
  apply Subtype.ext
  change groupHomology.chainsMap₁ f (TransitiveInduction.trivialMap f) (single g (1:ℤ))=
    single (f g) (1:ℤ)
  simp [groupHomology.chainsMap₁, TransitiveInduction.trivialMap]

lemma cycle_eq_zero_iff (g : G) : cycle g=0 ↔ g∈_root_.commutator G := by
  rw [← (abelianizationEquiv G).map_eq_zero_iff, abelianizationEquiv_cycle]
  change Abelianization.of g=1 ↔ _
  change g∈(Abelianization.of : G →* Abelianization G).ker ↔ _
  rw [Abelianization.ker_of]

lemma commutator_comap_of_mono (f : G →* H) [Mono (map f 1)] :
    (_root_.commutator H).comap f=_root_.commutator G := by
  ext g
  change f g∈_root_.commutator H ↔ g∈_root_.commutator G
  rw [← cycle_eq_zero_iff, ← cycle_eq_zero_iff, ← cycle_map]
  exact (ModuleCat.mono_iff_injective (map f 1)).mp inferInstance |>.eq_iff' (map_zero _)

end SimpleAmenable.TrivialHomology

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_TrajectoryStages
attribute [-instance] _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory Classical Set
namespace SimpleAmenable.PolygonObject

structure FiniteSetGroupoid where
  size : ℕ
namespace FiniteSetGroupoid
instance instGroupoid : Groupoid FiniteSetGroupoid where
  Hom U V := Fin U.size ≃ Fin V.size
  id object := Equiv.refl (Fin object.size)
  comp f g := f.trans g
  inv f := f.symm
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
  inv_comp f := Equiv.symm_trans_self f
  comp_inv f := Equiv.self_trans_symm f
end FiniteSetGroupoid

end SimpleAmenable.PolygonObject

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_EmptyStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory MonoidalCategory
namespace SimpleAmenable.PolygonObject.FiniteSetGroupoid
abbrev Terminal := Discrete PUnit
instance terminalSymmetric : SymmetricCategory Terminal where
  braiding X Y := eqToIso (Subsingleton.elim _ _)
  braiding_naturality_left := by intros; exact Subsingleton.elim _ _
  braiding_naturality_right := by intros; exact Subsingleton.elim _ _
  hexagon_forward := by intros; exact Subsingleton.elim _ _
  hexagon_reverse := by intros; exact Subsingleton.elim _ _
  symmetry := by intros; exact Subsingleton.elim _ _
noncomputable def terminal {C:Type} [Category.{0} C] : C ⥤ Terminal :=
  (Functor.const C).obj ⟨PUnit.unit⟩
noncomputable instance terminalMonoidal {C:Type} [Category.{0} C] [MonoidalCategory C] :
    (terminal (C:=C)).Monoidal := Functor.CoreMonoidal.toMonoidal {
  εIso := Iso.refl _
  μIso _ _ := Iso.refl _
  μIso_hom_natural_left := by intros; exact Subsingleton.elim _ _
  μIso_hom_natural_right := by intros; exact Subsingleton.elim _ _
  associativity := by intros; exact Subsingleton.elim _ _
  left_unitality := by intros; exact Subsingleton.elim _ _
  right_unitality := by intros; exact Subsingleton.elim _ _ }
noncomputable instance terminalBraided {C:Type} [Category.{0} C] [MonoidalCategory C] [BraidedCategory C] :
    (terminal (C:=C)).Braided where
  braided _ _ := Subsingleton.elim _ _
end SimpleAmenable.PolygonObject.FiniteSetGroupoid

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_SymmetricConfiguration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable.SymmetricConfiguration

attribute [local instance 1200] Rep.hV2
abbrev G (m:ℕ) := Equiv.Perm (Fin m)
def Configuration (m p:ℕ) := {f:Fin p → Fin m // Function.Injective f}
variable {m p:ℕ}
instance instCoeFunConfigurationForallFin : CoeFun (Configuration m p) (fun _=>Fin p → Fin m) := ⟨Subtype.val⟩
@[ext] theorem ext {f g:Configuration m p} (h:∀i,f i=g i) : f=g := Subtype.ext (funext h)
noncomputable instance instMulActionGConfiguration : MulAction (G m) (Configuration m p) where
  smul g f := ⟨fun i=>g (f i), g.injective.comp f.property⟩
  one_smul f := by apply ext; intro i; rfl
  mul_smul g h f := by apply ext; intro i; rfl
@[simp] theorem smul_apply (g:G m) (f:Configuration m p) (i:Fin p) : (g • f) i=g (f i) := rfl
noncomputable def standard (p n:ℕ) : Configuration (p+n) p := ⟨Fin.castAdd n,Fin.castAdd_injective p n⟩
noncomputable def standardLE (m p:ℕ) (hp:p ≤ m) : Configuration m p := ⟨Fin.castLE hp,Fin.castLE_injective hp⟩
lemma ne_smul (g:G m) (v w:Fin m) (h:v ≠ w) : g • v ≠ g • w := fun hh=>h (g.injective hh)
noncomputable def listEquiv (m p : ℕ) : Configuration m p ≃
    {l : List (Fin m) // l.Pairwise Ne ∧ l.length=p} where
  toFun f := ⟨List.ofFn f.val,List.pairwise_ofFn.mpr (fun _ _ h => fun hh => (ne_of_lt h) (f.property hh)),List.length_ofFn⟩
  invFun l := ⟨fun i => l.val.get ⟨i.val,by rw [l.property.2];exact i.isLt⟩,by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with h|h
    · exact l.property.1.rel_get_of_lt h hij
    · exact l.property.1.rel_get_of_lt h hij.symm⟩
  left_inv f := by apply ext; intro i; simp
  right_inv l := by
    apply Subtype.ext
    apply List.ext_getElem
    · simp [l.property.2]
    · intro i hi hj
      simp

@[simp] theorem listEquiv_apply_val (f : Configuration m p) :
    (listEquiv m p f).val=List.ofFn f.val := rfl

end SimpleAmenable.SymmetricConfiguration

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_SymmetricFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable.SymmetricConfiguration

section

attribute [local instance 1200] Rep.hV2
variable {m p:ℕ}
noncomputable def facePermutation (i j : Fin (p+1)) : Equiv.Perm (Fin (p+1)) :=
  (finSuccEquiv' i).trans (finSuccEquiv' j).symm
@[simp] lemma facePermutation_apply (i j : Fin (p+1)) (k : Fin p) :
    facePermutation i j (i.succAbove k)=j.succAbove k := by simp [facePermutation]

end

attribute [local instance 1200] Rep.hV2

end SimpleAmenable.SymmetricConfiguration

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_SymmetricStabilizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable.SymmetricConfiguration

attribute [local instance 1200] Rep.hV2
noncomputable def tailEquiv (p n:ℕ) : Fin n ≃ {x:Fin (p+n) // p≤x.val} where
  toFun i := ⟨Fin.natAdd p i,by simp⟩
  invFun x := ⟨x.val.val-p,by omega⟩
  left_inv _ := by apply Fin.ext; simp
  right_inv _ := by apply Subtype.ext; apply Fin.ext; dsimp; omega
end SimpleAmenable.SymmetricConfiguration

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_TrajectoryReindexLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory MonoidalCategory
namespace SimpleAmenable.PolygonObject.Labelled

section
variable {a n m:ℕ} (u:Fin (m+1) ⥤ Fin (n+1))
lemma comp_inv_last {D : Type*} [Category D] {A B X Y : D}
    (a : A ⟶ B) (f : B ⟶ X) (g : X ⟶ Y) [IsIso g] :
    (a ≫ f ≫ g) ≫ inv g = a ≫ f := by
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

lemma cancel_two_inverses {D : Type*} [Category D] {A B X Y : D}
    (a : A ⟶ B) (f : A ⟶ X) (g : X ⟶ Y) [IsIso a] [IsIso g] :
    a ≫ (inv a ≫ f ≫ g) ≫ inv g = f := by
  simp only [Category.assoc, IsIso.hom_inv_id_assoc, IsIso.hom_inv_id, Category.comp_id]

end

end SimpleAmenable.PolygonObject.Labelled

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_TrajectoryFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory
namespace SimpleAmenable.PolygonObject.Labelled

variable {n : ℕ}
abbrev faceFunctor (i : Fin (n+2)) : Fin (n+1) ⥤ Fin (n+2) :=
  (SimplexCategory.δ i).toOrderHom.toFunctor
lemma faceFunctor_obj (i : Fin (n+2)) (k : Fin (n+1)) :
    (faceFunctor i).obj k = i.succAbove k := rfl
end SimpleAmenable.PolygonObject.Labelled

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PlaneCornerInjectivity
attribute [-instance] _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PlaneCornerInjectivity
open Classical

noncomputable def planeHeight (p : ℝ × ℝ) : ℝ := p.1+p.2

end PlaneCornerInjectivity

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PlaneCornerCoordinates
attribute [-instance] _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PlaneCornerCoordinates
open Classical

abbrev PlaneSectorIndex := Fin 4 → Bool

end PlaneCornerCoordinates

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_PolygonCoefficientFinite
attribute [-instance] _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section NoetherianResolution
open _root_.CategoryTheory CategoryTheory.Limits
universe nr

namespace NoetherianResolution
variable {R : Type nr} [CommRing R] [IsNoetherianRing R]

theorem fg_projective_of_free (M : FGModuleCat.{nr} R) [Module.Free R M] :
    Projective M := by
  refine ⟨fun {E X} f e he => ?_⟩
  let F := forget₂ (FGModuleCat.{nr} R) (ModuleCat.{nr} R)
  have hi : Epi (F.map e) := inferInstance
  have hp : Projective (F.obj M) := ModuleCat.projective_of_free (Module.Free.chooseBasis R M)
  obtain ⟨g,hg⟩ := Projective.factors (F.map f) (F.map e)
  refine ⟨FGModuleCat.ofHom g.hom, ?_⟩
  apply F.map_injective
  exact hg

theorem finitePresentation (M : FGModuleCat.{nr} R) : Nonempty (ProjectivePresentation M) := by
  obtain ⟨n,f,hf⟩ := Module.Finite.exists_fin' R M
  have hp : Projective (FGModuleCat.of R (Fin n → R)) := fg_projective_of_free _
  have he : Epi (FGModuleCat.ofHom f) := by
    apply ConcreteCategory.epi_of_surjective
    exact hf
  exact ⟨⟨FGModuleCat.of R (Fin n → R),FGModuleCat.ofHom f⟩⟩

noncomputable local instance instEnoughProjectivesFGModuleCat_solutions : EnoughProjectives (FGModuleCat.{nr} R) where
  presentation := finitePresentation

omit [IsNoetherianRing R] in
theorem forget_projective (M : FGModuleCat.{nr} R) [Projective M] : Projective M.obj := by
  obtain ⟨n,f,hf⟩ := Module.Finite.exists_fin' R M
  let q : FGModuleCat.of R (Fin n → R) ⟶ M := FGModuleCat.ofHom f
  have he : Epi q := ConcreteCategory.epi_of_surjective q hf
  obtain ⟨s,hs⟩ := Projective.factors (𝟙 M) q
  have hlin : f.comp s.hom.hom = LinearMap.id := by
    exact congrArg (fun g => g.hom.hom) hs
  have hp : Module.Projective R M :=
    Module.Projective.of_split s.hom.hom f hlin
  exact ModuleCat.projective_of_categoryTheory_projective M.obj

noncomputable local instance instPreservesProjectiveObjectsFGModuleCatModuleCatForget₂LinearMapIdCarrierObjIsFG_solutions :
    (forget₂ (FGModuleCat.{nr} R) (ModuleCat.{nr} R)).PreservesProjectiveObjects where
  projective_obj {X} h := by
    let := h
    exact forget_projective X

noncomputable def resolution (M : FGModuleCat.{nr} R) : ProjectiveResolution M.obj :=
  (forget₂ (FGModuleCat.{nr} R) (ModuleCat.{nr} R)).mapProjectiveResolution
    (ProjectiveResolution.of M)

instance finite_resolution (M : FGModuleCat.{nr} R) (n : ℕ) :
    Module.Finite R ((resolution M).complex.X n) :=
  inferInstanceAs (Module.Finite R ((ProjectiveResolution.of M).complex.X n))

end NoetherianResolution
end NoetherianResolution

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_NoetherianTor
attribute [-instance] _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section NoetherianTor
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe nt

namespace NoetherianResolution
variable {R : Type nt} [CommRing R]

noncomputable def annihilatorHomotopy {M : ModuleCat.{nt} R}
    (P : ProjectiveResolution M) (r : R) (hr : ∀ x : M, r • x = 0) :
    Homotopy (r • 𝟙 P.complex) 0 := by
  apply ProjectiveResolution.liftHomotopyZero
  apply HomologicalComplex.to_single_hom_ext
  ext x
  change (P.π.f 0).hom (r • x) = 0
  rw [map_smul]
  exact hr (P.π.f 0 x)

end NoetherianResolution

end NoetherianTor

section AugmentationTor
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace NoetherianResolution
variable {R : Type} [CommRing R] [IsNoetherianRing R]

noncomputable abbrev augmentationModule (ε : R →+* ℤ) : ModuleCat R :=
  (ModuleCat.restrictScalars ε).obj (ModuleCat.of ℤ ℤ)

instance finite_augmentationModule (ε : R →+* ℤ) :
    Module.Finite R (augmentationModule ε) := by
  have : Module.Finite ℤ (augmentationModule ε) := inferInstanceAs (Module.Finite ℤ ℤ)
  exact Module.Finite.of_restrictScalars_finite ℤ R (augmentationModule ε)

noncomputable def augmentationResolution (ε : R →+* ℤ) :
    ProjectiveResolution (augmentationModule ε) :=
  resolution (FGModuleCat.of R (augmentationModule ε))

noncomputable def augmentationComplex (ε : R →+* ℤ) (L : FGModuleCat R) :
    ChainComplex (ModuleCat R) ℕ :=
  ((((tensoringLeft (ModuleCat R)).obj L.obj).mapHomologicalComplex _).obj
    (augmentationResolution ε).complex)

end NoetherianResolution
end AugmentationTor

section RingCoinvariants

open _root_.CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct
attribute [local instance 1200] Rep.hV2
namespace RingCoinvariants
variable {G : Type} [CommGroup G]
local notation "R" => MonoidAlgebra ℤ G

noncomputable abbrev inverseRep (M : ModuleCat R) : Rep ℤ G :=
  Rep.of ((Representation.ofModule' (k := ℤ) (G := G) M).comp (invMonoidHom : G →* G))

noncomputable abbrev moduleRep (M : ModuleCat R) : Rep ℤ G :=
  Rep.of (Representation.ofModule' (k := ℤ) (G := G) M)

@[simp] theorem inverseRep_apply (M : ModuleCat R) (g : G) (x : M) :
    (inverseRep M).ρ g x = (MonoidAlgebra.single g⁻¹ 1 : R) • x := rfl

@[simp] theorem moduleRep_apply (M : ModuleCat R) (g : G) (x : M) :
    (moduleRep M).ρ g x = (MonoidAlgebra.single g 1 : R) • x := rfl

noncomputable def forwardTensor (L M : ModuleCat R) :
    (↑(inverseRep L) ⊗[ℤ] ↑(moduleRep M)) →ₗ[ℤ] (L ⊗[R] M) :=
  TensorProduct.lift ((TensorProduct.mk R L M).restrictScalars₁₂ ℤ ℤ)

theorem forwardTensor_invariant (L M : ModuleCat R) (g : G) :
    (forwardTensor L M).comp ((inverseRep L).ρ.tprod (moduleRep M).ρ g) =
      forwardTensor L M := by
  apply TensorProduct.ext
  ext x y
  change ((MonoidAlgebra.single g⁻¹ 1 : R) • x) ⊗ₜ[R]
    ((MonoidAlgebra.single g 1 : R) • y) = x ⊗ₜ[R] y
  rw [TensorProduct.smul_tmul, ← smul_assoc]
  simp [MonoidAlgebra.single_mul_single, ← MonoidAlgebra.one_def]

noncomputable def forward (L M : ModuleCat R) :
    ((Rep.coinvariantsTensor ℤ G).obj (inverseRep L)).obj (moduleRep M) →ₗ[ℤ]
      (L ⊗[R] M) :=
  Representation.Coinvariants.lift _ (forwardTensor L M)
    (forwardTensor_invariant L M)

@[simp] theorem forward_mk (L M : ModuleCat R) (x : L) (y : M) :
    forward L M (Rep.coinvariantsTensorMk (inverseRep L) (moduleRep M) x y) =
      x ⊗ₜ[R] y := rfl

theorem mk_act_left {k H : Type} [CommRing k] [Group H] (A B : Rep k H)
    (g : H) (x : A) (y : B) :
    Rep.coinvariantsTensorMk A B (A.ρ g⁻¹ x) y =
      Rep.coinvariantsTensorMk A B x (B.ρ g y) := by
  have h := Representation.Coinvariants.mk_self_apply (A.ρ.tprod B.ρ) g
    ((A.ρ g⁻¹ x) ⊗ₜ[k] y)
  change Representation.Coinvariants.mk _
    ((A.ρ g (A.ρ g⁻¹ x)) ⊗ₜ[k] (B.ρ g y)) = _ at h
  have hx : A.ρ g (A.ρ g⁻¹ x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [hx] at h
  exact h.symm

theorem mk_balanced_group (L M : ModuleCat R) (g : G) (x : L) (y : M) :
    Rep.coinvariantsTensorMk (inverseRep L) (moduleRep M)
      ((MonoidAlgebra.single g 1 : R) • x) y =
    Rep.coinvariantsTensorMk (inverseRep L) (moduleRep M)
      x ((MonoidAlgebra.single g 1 : R) • y) := by
  have h := mk_act_left (inverseRep L) (moduleRep M) g x y
  change Rep.coinvariantsTensorMk (inverseRep L) (moduleRep M)
    ((MonoidAlgebra.single (g⁻¹)⁻¹ 1 : R) • x) y =
    Rep.coinvariantsTensorMk (inverseRep L) (moduleRep M)
    x ((MonoidAlgebra.single g 1 : R) • y) at h
  simpa only [inv_inv] using h

noncomputable def backward (L M : ModuleCat R) :
    (L ⊗[R] M) →ₗ[ℤ]
      ((Rep.coinvariantsTensor ℤ G).obj (inverseRep L)).obj (moduleRep M) :=
  (TensorProduct.liftAddHom
    (LinearMap.toAddMonoidHom'.comp
      (Rep.coinvariantsTensorMk (inverseRep L) (moduleRep M)).toAddMonoidHom)
    (by
      intro r x y
      induction r using MonoidAlgebra.induction_on with
      | of g => exact mk_balanced_group L M g x y
      | add r s hr hs => simpa only [add_smul, map_add, LinearMap.add_apply, AddMonoidHom.add_apply] using congrArg₂ (· + ·) hr hs
      | smul n r hr =>
        simpa only [smul_assoc, map_zsmul, AddMonoidHom.zsmul_apply] using congrArg (n • ·) hr
    )).toIntLinearMap

@[simp] theorem backward_mk (L M : ModuleCat R) (x : L) (y : M) :
    backward L M (x ⊗ₜ[R] y) =
      Rep.coinvariantsTensorMk (inverseRep L) (moduleRep M) x y := rfl

noncomputable def equiv (L M : ModuleCat R) :
    ((Rep.coinvariantsTensor ℤ G).obj (inverseRep L)).obj (moduleRep M) ≃ₗ[ℤ]
      (L ⊗[R] M) := by
  refine LinearEquiv.ofLinearMap (forward L M) (backward L M) ?_ ?_
  · apply LinearMap.ext
    intro z
    induction z using OAI.tensorInductionOn with
    | tmul x y => rfl
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  · apply Representation.Coinvariants.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl

@[simp] theorem equiv_mk (L M : ModuleCat R) (x : L) (y : M) :
    equiv L M (Rep.coinvariantsTensorMk (inverseRep L) (moduleRep M) x y) =
      x ⊗ₜ[R] y := rfl

noncomputable def moduleRepIso (M : ModuleCat R) :
    moduleRep M ≅ Rep.ofModuleMonoidAlgebra.obj M :=
  @Rep.mkIso ℤ G _ _ (moduleRep M) (Rep.ofModuleMonoidAlgebra.obj M) _ _
    (moduleRep M).hV2 (Rep.ofModuleMonoidAlgebra.obj M).hV2 _ _ {
    toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun n x => by
      change n • x = (algebraMap ℤ R n) • x
      exact (IsScalarTower.algebraMap_smul R n x).symm
    isIntertwining' := fun g => rfl }

noncomputable def intRestrictionIso {S : Type} [Ring S] (M : ModuleCat S) :
    ModuleCat.of ℤ M ≅ (ModuleCat.restrictScalars (Int.castRingHom S)).obj M := by
  let A := ModuleCat.of ℤ M
  let B := (ModuleCat.restrictScalars (Int.castRingHom S)).obj M
  let e : A ≃ₗ[ℤ] B := {
    toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun integer element => by
      change integer • element = (integer : S) • (show M from element)
      exact (Int.cast_smul_eq_zsmul S integer (show M from element)).symm }
  exact e.toModuleIso

noncomputable def functorIso (L : ModuleCat R) :
    Rep.ofModuleMonoidAlgebra ⋙ (Rep.coinvariantsTensor ℤ G).obj (inverseRep L) ≅
      (tensoringLeft (ModuleCat R)).obj L ⋙
        ModuleCat.restrictScalars (Int.castRingHom R) :=
  NatIso.ofComponents (fun M =>
    (((Rep.coinvariantsTensor ℤ G).obj (inverseRep L)).mapIso (moduleRepIso M)).symm ≪≫
      (equiv L M).toModuleIso ≪≫ intRestrictionIso (ModuleCat.of R (L ⊗[R] M))) (by
    intro M N f
    apply Rep.coinvariantsTensor_hom_ext
    apply DFunLike.ext
    intro x
    apply DFunLike.ext
    intro y
    rfl)
end RingCoinvariants
end RingCoinvariants

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_RingGroupHomology
attribute [-instance] _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section RingGroupHomology

open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
attribute [local instance 1200] Rep.hV2
namespace RingCoinvariants
variable {G : Type} [CommGroup G]
local notation "R" => MonoidAlgebra ℤ G

noncomputable def augmentation : R →+* ℤ :=
  (MonoidAlgebra.lift ℤ ℤ G (1 : G →* ℤ)).toRingHom

@[simp] theorem augmentation_of (g : G) :
    augmentation (MonoidAlgebra.of ℤ G g) = 1 :=
  MonoidAlgebra.lift_of _ _

noncomputable def augmentationTrivialIso :
    Rep.ofModuleMonoidAlgebra.obj (NoetherianResolution.augmentationModule
      (augmentation (G := G))) ≅ Rep.trivial ℤ G ℤ := by
  refine (moduleRepIso _).symm ≪≫ Rep.mkIso ?_
  refine { (LinearEquiv.refl ℤ ℤ) with isIntertwining' := ?_ }
  intro g
  apply LinearMap.ext
  intro x
  change augmentation (MonoidAlgebra.of ℤ G g) • x = x
  rw [augmentation_of, one_smul]

instance instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions : (Rep.ofModuleMonoidAlgebra (k := ℤ) (G := G)).Additive where
  map_add := by intros; rfl

variable [IsNoetherianRing (MonoidAlgebra ℤ G)]

noncomputable def groupResolution : ProjectiveResolution (Rep.trivial ℤ G ℤ) := by
  let Q := Rep.ofModuleMonoidAlgebra.mapProjectiveResolution
    (NoetherianResolution.augmentationResolution (augmentation (G := G)))
  exact {
    complex := Q.complex
    projective := Q.projective
    π := Q.π ≫ (ChainComplex.single₀ (Rep ℤ G)).map augmentationTrivialIso.hom }

noncomputable def complexIso (L : FGModuleCat R) :
    (groupResolution (G := G)).complex.coinvariantsTensorObj (inverseRep L.obj) ≅
      ((ModuleCat.restrictScalars (Int.castRingHom R)).mapHomologicalComplex _).obj
        (NoetherianResolution.augmentationComplex augmentation L) :=
  (CategoryTheory.Functor.mapHomologicalComplexCompIso (functorIso L.obj)
    (ComplexShape.down ℕ)).app
      (NoetherianResolution.augmentationResolution (augmentation (G := G))).complex

end RingCoinvariants
end RingGroupHomology

section FiniteAbelianHomology

open _root_.CategoryTheory
attribute [local instance 1200] Rep.hV2
namespace RingCoinvariants
variable {G : Type} [CommGroup G] [IsNoetherianRing (MonoidAlgebra ℤ G)]

noncomputable def inverseHomologyIso (A : Rep ℤ G) (n : ℕ) :
    groupHomology (inverseRep (ModuleCat.of (MonoidAlgebra ℤ G) A.ρ.asModule)) n ≅
      groupHomology A n := by
  let e : (inverseRep (ModuleCat.of (MonoidAlgebra ℤ G) A.ρ.asModule)) ≃+ A := {
    toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl }
  refine groupHomology.mapIso
    (A := inverseRep (ModuleCat.of (MonoidAlgebra ℤ G) A.ρ.asModule)) (B := A)
    (MulEquiv.inv G) (e.toIntLinearEquiv) ?_ n
  intro g
  apply DFunLike.ext
  intro x
  change A.ρ.asAlgebraHom (MonoidAlgebra.single g⁻¹ 1) x = A.ρ g⁻¹ x
  rw [Representation.asAlgebraHom_single_one]

end RingCoinvariants
end FiniteAbelianHomology

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_TorusCoefficientFinite
attribute [-instance] _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section TorusCoefficientFinite

open Classical
namespace SquareStep

abbrev OrbitGroupRing := MonoidAlgebra ℤ (Multiplicative (ℤ×ℤ))

instance instIsNoetherianRingOrbitGroupRing : IsNoetherianRing OrbitGroupRing := by
  let : Algebra.FiniteType ℤ OrbitGroupRing :=
    MonoidAlgebra.finiteType_iff_group_fg.mpr inferInstance
  exact Algebra.FiniteType.isNoetherianRing ℤ OrbitGroupRing

end SquareStep
end TorusCoefficientFinite

section TensorCoefficientFinite

open scoped TensorProduct
attribute [local instance 1200] Representation.instModuleAsModule TensorProduct.instModule
attribute [local instance 1300] TensorProduct.leftModule
namespace RingCoinvariants

variable {G M K : Type} [CommGroup G] [AddCommGroup M] [Module ℤ M]
  [AddCommGroup K] [Module ℤ K]
local notation "R" => MonoidAlgebra ℤ G

noncomputable def trivialTensorEquiv (ρ : Representation ℤ G M) :
    (ρ.asModule ⊗[ℤ] K) ≃ₗ[ℤ] (ρ.tprod (Representation.trivial ℤ G K)).asModule :=
  (TensorProduct.congr ρ.asModuleEquiv (LinearEquiv.refl ℤ K)).trans
    (ρ.tprod (Representation.trivial ℤ G K)).asModuleEquiv.symm

noncomputable def trivialTensorMap (ρ : Representation ℤ G M) :
    (ρ.asModule ⊗[ℤ] K) →ₗ[R] (ρ.tprod (Representation.trivial ℤ G K)).asModule :=
  MonoidAlgebra.equivariantOfLinearOfComm (trivialTensorEquiv ρ).toLinearMap (by
    intro g x
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [smul_add,map_add,hx,hy]
    | tmul x y =>
      apply (ρ.tprod (Representation.trivial ℤ G K)).asModuleEquiv.injective
      simp [trivialTensorEquiv,TensorProduct.smul_tmul']
      rfl)

end RingCoinvariants
end TensorCoefficientFinite

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_StageNerveColimit
attribute [-instance] _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory CategoryTheory.Limits Opposite
namespace StageNerveColimit

universe u v w
lemma comp_injective {C : Type u} {D : Type v} {K : Type w}
    [Category C] [Category D] [Category K] (F : C ⥤ D) [F.Faithful]
    (hF : Function.Injective F.obj) : Function.Injective (fun G : K ⥤ C => G ⋙ F) := by
  intro G H h
  refine CategoryTheory.Functor.ext (fun X => hF (Functor.congr_obj h X)) ?_
  intro X Y f
  apply F.map_injective
  simpa only [Functor.comp_map,Functor.comp_obj,Functor.map_comp,eqToHom_map] using Functor.congr_hom h f
end StageNerveColimit

end

open _root_.CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_StageSimplicialColimit
attribute [-instance] _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory Limits Simplicial Opposite
namespace SimplicialDiagonal

variable {J : Type} [Category.{0} J] [IsFiltered J]
omit [IsFiltered J] in
lemma isIso_of_colimit_fac {A : Type*} [Category A] {F : J ⥤ A}
    {s t : Cocone F} (hs : IsColimit s) (ht : IsColimit t) (u : s.pt ⟶ t.pt)
    (hu : ∀ j,s.ι.app j ≫ u=t.ι.app j) : IsIso u := by
  have he : u=(hs.coconePointUniqueUpToIso ht).hom := by
    apply hs.hom_ext
    intro j
    rw [hu]
    exact (hs.fac t j).symm
  rw [he]
  infer_instance
end SimplicialDiagonal

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_TrajectoryCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory
open scoped TensorProduct
namespace SimpleAmenable.PolygonObject.LabelledStage
open Labelled

variable {a n : ℕ} {K : Type} [AddCommGroup K]
abbrev RankTwo := Multiplicative (ℤ×ℤ)
end SimpleAmenable.PolygonObject.LabelledStage

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_GroupoidComponentHomology
attribute [-instance] _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory
namespace TranslationFiltered

variable (P:Type) [CommMonoid P]
instance regular_filtered : IsFiltered (ActionCategory P P) where
  cocone_objs x y := ⟨(x.back*y.back:P),⟨y.back, by change y.back*x.back=x.back*y.back; exact mul_comm _ _⟩,⟨x.back,rfl⟩,trivial⟩
  cocone_maps {x y} f g := by
    refine ⟨(x.back*y.back:P),⟨x.back,rfl⟩,?_⟩
    apply Subtype.ext
    change x.back*f.val=x.back*g.val
    have h:f.val*x.back=g.val*x.back:=f.property.trans g.property.symm
    simpa only [mul_comm] using h
  nonempty := inferInstance
abbrev Q := Algebra.GrothendieckGroup P
noncomputable instance completed_action : MulAction P (Q P) :=
  MulAction.compHom (Q P) Algebra.GrothendieckGroup.of
lemma common_target (x y:Q P) : ∃ r s:P,
    Algebra.GrothendieckGroup.of r*x=Algebra.GrothendieckGroup.of s*y := by
  let f:=Localization.monoidOf (⊤:Submonoid P)
  let t:=f.sec (x*y⁻¹)
  refine ⟨t.2.val,t.1,?_⟩
  calc
    _ = ((x*y⁻¹)*f t.2)*y := by change f t.2*x=_; simp [mul_assoc,mul_comm,mul_left_comm]
    _ = _ := congrArg (fun q:Q P => q*y) (f.sec_spec (x*y⁻¹))
noncomputable instance completed_filtered : IsFiltered (ActionCategory P (Q P)) where
  cocone_objs x y := by
    obtain ⟨r,s,h⟩:=common_target P x.back y.back
    exact ⟨(Algebra.GrothendieckGroup.of r*x.back:Q P),⟨r,rfl⟩,⟨s,h.symm⟩,trivial⟩
  cocone_maps {x y} f g := by
    have he : Algebra.GrothendieckGroup.of f.val=Algebra.GrothendieckGroup.of g.val := by
      apply mul_right_cancel (b:=x.back)
      exact f.property.trans g.property.symm
    obtain ⟨c,hc⟩ := (Localization.monoidOf (⊤:Submonoid P)).exists_of_eq he
    refine ⟨(Algebra.GrothendieckGroup.of c.val*y.back:Q P),⟨c.val,rfl⟩,?_⟩
    exact Subtype.ext hc
  nonempty := inferInstance
end TranslationFiltered

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_LowerBarComposition
attribute [-instance] _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory Limits HomologicalComplex SimplicialObject Simplicial Opposite AlgebraicTopology
namespace SimplicialFirstFinite

attribute [local instance 1200] Submodule.module
universe u
variable {R:Type u} [CommRing R]
variable (T:SimplicialObject (ModuleCat.{u} R))
noncomputable def outer : T.obj (op ⦋2⦌) →ₗ[R] (T.obj (op ⦋1⦌) × T.obj (op ⦋1⦌)) :=
  (T.δ (0:Fin 3)).hom.prod (T.δ (2:Fin 3)).hom
noncomputable def sec : (T.obj (op ⦋1⦌) × T.obj (op ⦋1⦌)) →ₗ[R] T.obj (op ⦋2⦌) :=
  (T.σ (0:Fin 2)).hom.comp (LinearMap.fst R _ _) +
  (T.σ (1:Fin 2)).hom.comp (LinearMap.snd R _ _)
end SimplicialFirstFinite

end

open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite AlgebraicTopology

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_TranslationNerve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory Simplicial Opposite
namespace TranslationNerve
open TranslationFiltered

variable (P:Type) [CommMonoid P]
abbrev C := ActionCategory P (Q P)
abbrev B (n:ℕ) := ComposableArrows (SingleObj P) n
lemma eqToHom_val {x y:C P} (h:x=y) : (eqToHom h).val=(1:P) := by subst y; rfl
noncomputable def lift (n:ℕ) (q:Q P) (s:B P n) : ComposableArrows (C P) n where
  obj i := (Algebra.GrothendieckGroup.of (M:=P) (s.map (homOfLE (Fin.zero_le i))) * q : Q P)
  map {i j} f := ⟨s.map f, by
    change Algebra.GrothendieckGroup.of (M:=P) (s.map f) * (Algebra.GrothendieckGroup.of (M:=P)
      (s.map (homOfLE (Fin.zero_le i))) * q) = Algebra.GrothendieckGroup.of (M:=P) (s.map (homOfLE (Fin.zero_le j))) * q
    rw [←mul_assoc,←map_mul (Algebra.GrothendieckGroup.of (M:=P))]
    have h:=s.map_comp (homOfLE (Fin.zero_le i)) f
    change s.map (homOfLE (Fin.zero_le i) ≫ f)=s.map f*s.map (homOfLE (Fin.zero_le i)) at h
    rw [←h]
    rfl⟩
  map_id i := by apply Subtype.ext; exact s.map_id i
  map_comp f g := by apply Subtype.ext; exact s.map_comp f g
lemma lift_left (n:ℕ) (q:Q P) (s:B P n) : (lift P n q s).left.back=q := by
  change Algebra.GrothendieckGroup.of (s.map (homOfLE (Fin.zero_le (0:Fin (n+1))))) * q=q
  rw [show homOfLE (Fin.zero_le (0:Fin (n+1))) = 𝟙 _ from rfl,s.map_id]
  change Algebra.GrothendieckGroup.of (M:=P) (1:P)*q=q
  rw [map_one,one_mul]
noncomputable def translate (q:Q P) : C P ⥤ C P where
  obj x := (q*x.back:Q P)
  map f := ⟨f.val,by
    change Algebra.GrothendieckGroup.of f.val * (q * _) = _
    rw [mul_left_comm]
    exact congrArg (q*·) f.property⟩
  map_id _ := rfl
  map_comp _ _ := rfl
lemma translate_one : translate P 1=𝟭 _ := by
  apply CategoryTheory.Functor.ext
  · intro x y f; apply Subtype.ext
    erw [CategoryOfElements.comp_val,CategoryOfElements.comp_val]
    simp only [SingleObj.comp_as_mul,eqToHom_val,one_mul,mul_one]
    rfl
  · intro x; apply (ActionCategory.objEquiv P (Q P)).symm.injective; exact one_mul _
lemma translate_mul (q r:Q P) : translate P (q*r)=translate P r ⋙ translate P q := by
  apply CategoryTheory.Functor.ext
  · intro x y f; apply Subtype.ext
    erw [CategoryOfElements.comp_val,CategoryOfElements.comp_val]
    simp only [SingleObj.comp_as_mul,eqToHom_val,one_mul,mul_one]
    rfl
  · intro x; apply (ActionCategory.objEquiv P (Q P)).symm.injective; exact mul_assoc _ _ _
noncomputable instance action (n:ℕ) : MulAction (Q P) (ComposableArrows (C P) n) where
  smul q s := s ⋙ translate P q
  one_smul s := by change s ⋙ translate P 1=s; rw [translate_one]; rfl
  mul_smul q r s := by change s ⋙ translate P (q*r)=(s ⋙ translate P r) ⋙ translate P q; rw [translate_mul]; rfl
end TranslationNerve

end

end OAI
end


