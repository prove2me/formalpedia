-- Prove2me | Definitions.Def_OAIQ068A011
-- name    : OAIQ068A011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T07:40:48.410534+00:00
-- url     : https://prove2.me/theorems/da02c1a1-a637-459e-93a6-e83d87168fbe
-- title:
--   Definitions bundle OAIQ068A011 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 96 declarations of OpenAI's Lean: 47 definitions, 11 instances and 38 theorems. The definitions and types are `OAI.PiExponent.GeometrySupport.CechH1Transfer.schemeUnit`, `OAI.PiExponent.GeometrySupport.CechOneConverse.schemeUnit`, `OAI.PiExponent.GeometrySupport.ProjectiveCoordinateAcyclicity.schemeUnit`, `OAI.PiExponent.GeometrySupport.SerreAssembly.schemeUnit`, `OAI.PiExponent.ProjectiveO1.schemeUnit`, `OAI.PiExponent.ProjectiveTwistAcyclicity.schemeUnit`, `OAI.PiExponentJets.W29.boundedCoefficientMap`, `OAI.PiExponentJets.W29.generatorPiece`, `OAI.PiExponentJets.W32.exponentBall`, `OAI.PiExponentJets.W32.polynomialGrowth`, `OAI.PiExponentJets.W32.scaledPolynomialGrowth`, `OAI.PiExponentJets.W64.degreeAt`, `OAI.PiExponentJets.W64.degreePolynomial`, `OAI.PiExponentJets.W64.hilbertMultiplicity`, `OAI.PiExponentJets.W64.rationalDegreePolynomial`, `OAI.PiExponentJets.W64.regularSequenceHilbertPolynomial`, `OAI.PiExponentJets.W64.shiftHilbertPolynomial`, `OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.LocallyAnnihilated`, `OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.quotientModule`, `OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.quotientModuleRestrictIso`, `OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.specPushforwardSectionsIso`, `OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.specPushforwardTildeIso`, `OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.specSurjectiveDescent`, `OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.specSurjectiveDescentPushforwardIso`, `OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.surjectiveModule`, `OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.surjectiveModuleRestrictIso`, `OAI.PiExponentSeshadri.ClosedImmersionModules.additiveFullyFaithful`, `OAI.PiExponentSeshadri.ClosedImmersionModules.additivePreimage`, `OAI.PiExponentSeshadri.ClosedImmersionModules.modulePreimage`, `OAI.PiExponentSeshadri.ClosedImmersionModules.pushforwardFullyFaithful`, `OAI.PiExponentSeshadri.Geometry.presentationOfIso`, `OAI.PiExponentSeshadri.Projective.reindexCoordinateCover`, `OAI.PiExponentSiegel.W08.coefficientAdjoinRootQuotientEquiv`, `OAI.PiExponentSiegel.W08.coordinateCoefficientSplit`, `OAI.PiExponentSiegel.W08.coordinateMinpolyIdeal`, `OAI.PiExponentSiegel.W08.coordinateMinpolyQuotientEquiv`, `OAI.PiExponentSiegel.W10.TriangularLocalParameters.firstCoordinateContraction`, `OAI.PiExponentSiegel.W10.TriangularLocalParameters.firstCoordinatePolynomial`, `OAI.PiExponentSiegel.W10.TriangularLocalParameters.principalModuleQuotientEquiv`, `OAI.PiExponentSiegel.W17.ConeLocalLength.laurentPrime` and 7 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Analysis_RegularSequenceSeries`, `PiExponent_Approximation_AffineClosedAnnihilatedDescent`, `PiExponent_Approximation_ClosedAnnihilatedDescent`, `PiExponent_Approximation_ClosedImmersionModules`, `PiExponent_Approximation_ClosedPowerSectionLifting`, `PiExponent_Approximation_ClosedThickeningSections`, `PiExponent_Approximation_GlobalClosedAnnihilatedDescent`, `PiExponent_Approximation_ModulePullbackCoherent`, `PiExponent_Approximation_SerreAssembly`, `PiExponent_Cohomology_CechH1Transfer`, `PiExponent_Cohomology_CechOneConverse`, `PiExponent_Cohomology_IdealPowerCohomology`, `PiExponent_Cohomology_ProjectiveCoordinateAcyclicity`, `PiExponent_Cohomology_ProjectiveTwistAcyclicity`, `PiExponent_Geometry_FiniteNormalizationGrowth`, `PiExponent_Geometry_ProjectiveSectionReindex`, `PiExponent_Geometry_ProjectiveSpaceSerre`, `PiExponent_Jets_KoszulTopDifferential`, `PiExponent_LocalAlgebra_CompleteIntersectionHilbert`, `PiExponent_LocalAlgebra_ConeLocalLength`, `PiExponent_LocalAlgebra_ConeQuotientAugmentation`, `PiExponent_LocalAlgebra_FiniteFreeResolutionExt`, `PiExponent_LocalAlgebra_IdealPowerRestriction`, `PiExponent_LocalAlgebra_KoszulDualBottom`, `PiExponent_LocalAlgebra_KoszulDualCone`, `PiExponent_LocalAlgebra_PositiveDimensionalHilbert`, `PiExponent_LocalAlgebra_RegularSequenceResolution`, `PiExponent_LocalAlgebra_TriangularLocalParameters`, `PiExponent_Polynomials_ColonHilbertPolynomial`, `PiExponent_Polynomials_PolynomialCoordinateMinpolyQuotient`, `PiExponent_Polynomials_PolynomialGrowthRanks`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ068A019`; the statements `OAI_PiExponentJets_W22_homogeneous_local_regular_bezout`, `OAI.PiExponentJets.W22.homogeneous_local_regular_bezout_q68`, `OAI_PiExponentSeshadri_Geometry_eventual_twist_ext_zero_of_closed_pushforward`, `OAI.PiExponentSeshadri.Geometry.eventual_twist_ext_zero_of_closed_pushforward_q68`, `OAI_PiExponentSiegelAux_W30_iterateScalarCones_dual_low_exact`, `OAI.PiExponentSiegelAux.W30.iterateScalarCones_dual_low_exact_q68`, `OAI_PiExponent_BlowupJetSurjectivity_eventual_blowup_jetRestriction_surjective` and `OAI_PiExponent_GlobalReesRecoveryComparison_eventually_ordinaryMap_app_bijective`; the proofs of `OAI_PiExponentJets_W22_actualMultiplicityCycle_zero_degree`, `OAI.PiExponentJets.W22.actualMultiplicityCycle_zero_degree_q68`, `OAI_PiExponentJets_W22_component_multiplicity_sum_bound`, `OAI.PiExponentJets.W22.component_multiplicity_sum_bound_q68`, `OAI_PiExponentJets_W22_homogeneous_prefix_hilbert_degree`, `OAI.PiExponentJets.W22.homogeneous_prefix_hilbert_degree_q68` and `OAI_PiExponent_CurveFieldRigidity_logarithmic_coordinate_eq_one`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Lean.Elab.Tactic.Omega

section
-- module Solutions.OAIQ068_PI.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_RegularSequenceSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Finite σ]

noncomputable def degreeAt {m : ℕ} (degrees : Fin m → ℕ) (i : ℕ) : ℕ :=
  if hi : i < m then degrees ⟨i, hi⟩ else 0

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ClosedAnnihilatedDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.ClosedAnnihilatedDescent
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {R S : CommRingCat.{0}}

def specPushforwardSectionsIso (φ : R ⟶ S) (N : (Spec S).Modules) :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (Spec.map φ)).obj N) ≅
      (ModuleCat.restrictScalars φ.hom).obj (moduleSpecΓFunctor.obj N) := by
  let E : TopCat.Sheaf (ModuleCat R) (Spec R) ⥤ ModuleCat R :=
    TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (op ⊤)
  exact E.mapIso ((pushforwardCompModulesSpecToSheafIso φ).app N)

def specPushforwardTildeIso (φ : R ⟶ S) (N : ModuleCat S) :
    (Scheme.Modules.pushforward (Spec.map φ)).obj (tilde N) ≅
      tilde ((ModuleCat.restrictScalars φ.hom).obj N) := by
  let P := (Scheme.Modules.pushforward (Spec.map φ)).obj (tilde N)
  let : IsIso P.fromTildeΓ := isIso_fromTildeΓ_pushforward φ (tilde N)
  exact (asIso P.fromTildeΓ).symm ≪≫ (tilde.functor R).mapIso
    (specPushforwardSectionsIso φ (tilde N) ≪≫
      (ModuleCat.restrictScalars φ.hom).mapIso (tilde.isoTop N).symm)

def quotientModule (I : Ideal R) (M : ModuleCat R)
    (h : I ≤ Module.annihilator R M) : ModuleCat (CommRingCat.of (R ⧸ I)) := by
  let ht : Module.IsTorsionBySet R M I := fun {x} {a} =>
    Module.mem_annihilator.mp (h a.property) x
  letI := ht.module
  exact ModuleCat.of _ M

def quotientModuleRestrictIso (I : Ideal R) (M : ModuleCat R)
    (h : I ≤ Module.annihilator R M) :
    (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj (quotientModule I M h) ≅ M :=
  Iso.refl M

instance quotientModule_finite (I : Ideal R) (M : ModuleCat R) [Module.Finite R M]
    (h : I ≤ Module.annihilator R M) :
    Module.Finite (CommRingCat.of (R ⧸ I)) (quotientModule I M h) := by
  let ht : Module.IsTorsionBySet R M I := fun {x} {a} =>
    Module.mem_annihilator.mp (h a.property) x
  let := ht.module
  let : IsScalarTower R (R ⧸ I) M := ht.isScalarTower
  change Module.Finite (R ⧸ I) M
  exact Module.Finite.of_restrictScalars_finite R (R ⧸ I) M

end
end PiExponentSeshadri.ClosedAnnihilatedDescent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_AffineClosedAnnihilatedDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.ClosedAnnihilatedDescent
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
variable {R S : CommRingCat.{0}}

def surjectiveModule (φ : R ⟶ S) (hφ : Function.Surjective φ) (M : ModuleCat R)
    (h : RingHom.ker φ.hom ≤ Module.annihilator R M) : ModuleCat S :=
  (ModuleCat.restrictScalars (φ.hom.quotientKerEquivOfSurjective hφ).symm.toRingHom).obj
    (quotientModule (RingHom.ker φ.hom) M h)

def surjectiveModuleRestrictIso (φ : R ⟶ S) (hφ : Function.Surjective φ)
    (M : ModuleCat R) (h : RingHom.ker φ.hom ≤ Module.annihilator R M) :
    (ModuleCat.restrictScalars φ.hom).obj (surjectiveModule φ hφ M h) ≅ M :=
  (ModuleCat.restrictScalarsComp'App φ.hom
    (φ.hom.quotientKerEquivOfSurjective hφ).symm.toRingHom
    (Ideal.Quotient.mk (RingHom.ker φ.hom))
    (RingHom.quotientKerEquivOfSurjective_symm_comp hφ).symm
    (quotientModule (RingHom.ker φ.hom) M h)).symm ≪≫ quotientModuleRestrictIso _ M h

def specSurjectiveDescent (φ : R ⟶ S) (hφ : Function.Surjective φ)
    (M : (Spec R).Modules)
    (h : RingHom.ker φ.hom ≤ Module.annihilator R (moduleSpecΓFunctor.obj M)) :
    (Spec S).Modules := tilde (surjectiveModule φ hφ (moduleSpecΓFunctor.obj M) h)

def specSurjectiveDescentPushforwardIso (φ : R ⟶ S) (hφ : Function.Surjective φ)
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (h : RingHom.ker φ.hom ≤ Module.annihilator R (moduleSpecΓFunctor.obj M)) :
    (Scheme.Modules.pushforward (Spec.map φ)).obj (specSurjectiveDescent φ hφ M h) ≅ M :=
  specPushforwardTildeIso _ _ ≪≫
    (tilde.functor R).mapIso (surjectiveModuleRestrictIso φ hφ (moduleSpecΓFunctor.obj M) h) ≪≫
      @asIso _ _ _ _ M.fromTildeΓ
        (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M)

end
end PiExponentSeshadri.ClosedAnnihilatedDescent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ClosedImmersionModules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.ClosedImmersionModules
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {X Y : Scheme.{0}} (f : Y ⟶ X)

def additiveFullyFaithful [IsClosedImmersion f] :
    ((Functor.whiskeringLeft _ _ AddCommGrpCat).obj (Opens.map f.base).op).FullyFaithful := by
  let h := f.isClosedEmbedding.isEmbedding.isInducing
  let adj := h.adjunction
  have hc (V : Y.Opens) : IsIso (adj.counit.app V) := by
    have he : adj.counit.app V = eqToHom (h.map_functorObj V) := Subsingleton.elim _ _
    exact he.symm ▸ (eqToIso (h.map_functorObj V)).isIso_hom
  let : IsIso adj.counit := NatIso.isIso_of_isIso_app _
  let := adj.fullyFaithfulROfIsIsoCounit.full
  let := adj.fullyFaithfulROfIsIsoCounit.faithful
  let W := (MorphismProperty.isomorphisms Y.Opens).inverseImage (Opens.map f.base)
  let : (Opens.map f.base).IsLocalization W := adj.isLocalization
  let : (Opens.map f.base).op.IsLocalization W.op :=
    (Functor.IsLocalization.op_iff (Opens.map f.base) W).mpr inferInstance
  exact Localization.fullyFaithfulWhiskeringLeft (Opens.map f.base).op W.op AddCommGrpCat

lemma preimage_surjective [IsClosedImmersion f] :
    Function.Surjective (fun U : X.Opens => f ⁻¹ᵁ U) := by
  intro V
  let h := f.isClosedEmbedding.isEmbedding.isInducing
  exact ⟨h.functorObj V, h.map_functorObj V⟩

def additivePreimage [IsClosedImmersion f] {M N : Y.Modules}
    (a : (Scheme.Modules.pushforward f).obj M ⟶ (Scheme.Modules.pushforward f).obj N) :
    M.presheaf ⟶ N.presheaf :=
  (additiveFullyFaithful f).preimage a.mapPresheaf

lemma additivePreimage_app [IsClosedImmersion f] {M N : Y.Modules}
    (a : (Scheme.Modules.pushforward f).obj M ⟶ (Scheme.Modules.pushforward f).obj N)
    (U : X.Opens) : (additivePreimage f a).app (op (f ⁻¹ᵁ U)) = a.app U := by
  exact congrArg (fun b : (Opens.map f.base).op ⋙ M.presheaf ⟶
      (Opens.map f.base).op ⋙ N.presheaf => b.app (op U))
    ((additiveFullyFaithful f).map_preimage (X := M.presheaf) (Y := N.presheaf) a.mapPresheaf)

lemma additivePreimage_smul [IsClosedImmersion f]
    {M N : Y.Modules}
    (a : (Scheme.Modules.pushforward f).obj M ⟶ (Scheme.Modules.pushforward f).obj N)
    (V : Y.Opens) (r : Γ(Y,V)) (m : Γ(M,V)) :
    (additivePreimage f a).app (op V) (r • m) =
      r • (additivePreimage f a).app (op V) m := by
  obtain ⟨U, rfl⟩ := preimage_surjective f V
  apply N.isSheaf.section_ext
  intro y hy
  obtain ⟨W, hW, hyW, hWU⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := f y) (U := U) hy
  let j : W ⟶ U := homOfLE hWU
  let k : f ⁻¹ᵁ W ⟶ f ⁻¹ᵁ U := (Opens.map f.base).map j
  refine ⟨f ⁻¹ᵁ W, leOfHom k, hyW, ?_⟩
  have hn (z : Γ(M,f ⁻¹ᵁ U)) :
      (additivePreimage f a).app (op (f ⁻¹ᵁ W)) (M.presheaf.map k.op z) =
        N.presheaf.map k.op ((additivePreimage f a).app (op (f ⁻¹ᵁ U)) z) :=
    CategoryTheory.congr_fun ((additivePreimage f a).naturality k.op) z
  have hs : N.presheaf.map k.op (r • (additivePreimage f a).app (op (f ⁻¹ᵁ U)) m) =
      Y.presheaf.map k.op r • N.presheaf.map k.op ((additivePreimage f a).app (op (f ⁻¹ᵁ U)) m) :=
    N.val.map_smul k.op r ((additivePreimage f a).app (op (f ⁻¹ᵁ U)) m)
  change N.presheaf.map k.op ((additivePreimage f a).app (op (f ⁻¹ᵁ U)) (r • m)) =
    N.presheaf.map k.op (r • (additivePreimage f a).app (op (f ⁻¹ᵁ U)) m)
  rw [← hn, hs, ← hn, additivePreimage_app]
  obtain ⟨c, hc⟩ := f.app_surjective W hW (Y.presheaf.map k.op r)
  have hm := M.val.map_smul k.op r m
  change M.presheaf.map k.op (r • m) = Y.presheaf.map k.op r • M.presheaf.map k.op m at hm
  rw [hm, ← hc]
  exact a.app_smul (r := c) (x := M.presheaf.map k.op m)

def modulePreimage [IsClosedImmersion f] {M N : Y.Modules}
    (a : (Scheme.Modules.pushforward f).obj M ⟶ (Scheme.Modules.pushforward f).obj N) :
    M ⟶ N where
  val.app V := ModuleCat.ofHom (X := M.val.obj V) (Y := N.val.obj V)
    { toAddHom := ((additivePreimage f a).app V).hom.toAddHom
      map_smul' := fun r m => additivePreimage_smul f a V.unop r m }
  val.naturality {V W} j := by
    ext m
    exact CategoryTheory.congr_fun ((additivePreimage f a).naturality j) m

def pushforwardFullyFaithful [IsClosedImmersion f] :
    (Scheme.Modules.pushforward f).FullyFaithful where
  preimage a := modulePreimage f a
  map_preimage a := by
    ext U m
    exact CategoryTheory.congr_fun (additivePreimage_app f a U) m
  preimage_map a := by
    apply Scheme.Modules.hom_ext
    intro V
    obtain ⟨U, rfl⟩ := preimage_surjective f V
    exact additivePreimage_app f ((Scheme.Modules.pushforward f).map a) U

theorem counit_isIso [IsClosedImmersion f]  :
    IsIso (Scheme.Modules.pullbackPushforwardAdjunction f).counit := by
  let := (pushforwardFullyFaithful f).full
  let := (pushforwardFullyFaithful f).faithful
  exact (Scheme.Modules.pullbackPushforwardAdjunction f).counit_isIso_of_R_fully_faithful

theorem unit_isIso_of_pushforward [IsClosedImmersion f]
    {M : X.Modules} {N : Y.Modules}
    (e : M ≅ (Scheme.Modules.pushforward f).obj N) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) := by
  let : IsIso (Scheme.Modules.pullbackPushforwardAdjunction f).counit := counit_isIso f
  let := (Scheme.Modules.pullbackPushforwardAdjunction f).fullyFaithfulROfIsIsoCounit.full
  let := (Scheme.Modules.pullbackPushforwardAdjunction f).fullyFaithfulROfIsIsoCounit.faithful
  exact (Scheme.Modules.pullbackPushforwardAdjunction f).isIso_unit_app_of_iso e

end
end PiExponentSeshadri.ClosedImmersionModules

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ClosedThickeningSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite
variable {X Y : Scheme.{0}}
local instance instHasExtModules_solutions (Z : Scheme.{0}) : HasExt.{1} Z.Modules := HasExt.standard _

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ClosedPowerSectionLifting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
variable {X Y : Scheme.{0}}
local instance instHasExtModules_solutions_1 : HasExt.{1} X.Modules := HasExt.standard _

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ModulePullbackCoherent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

def presentationOfIso (X : Scheme.{0})
    {M N : SheafOfModules X.ringCatSheaf} (e : M ≅ N)
    (P : M.Presentation) : N.Presentation := by
  let : IsIso e.hom := e.isIso_hom
  exact P.ofIsIso e.hom

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_GlobalClosedAnnihilatedDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.ClosedAnnihilatedDescent
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
variable {X Y : Scheme.{0}} (f : Y ⟶ X)

def LocallyAnnihilated (M : X.Modules) : Prop :=
  ∀ U : X.affineOpens,
    RingHom.ker (f ∣_ U.1).appTop.hom ≤
      Module.annihilator Γ(U.1.toScheme,⊤) Γ(M.restrict U.1.ι,⊤)

end
end PiExponentSeshadri.ClosedAnnihilatedDescent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_SerreAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.SerreAssembly

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open PiExponentSeshadri.Geometry

abbrev schemeUnit (X : Scheme.{0}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

end
end PiExponent.GeometrySupport.SerreAssembly

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CechOneConverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.GeometrySupport.CechOneConverse

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry
universe u
variable {Y : Scheme.{u}} {J : Type u} (U : J → Y.Opens) (M : Y.Modules)

abbrev schemeUnit : Y.Modules := SheafOfModules.unit Y.ringCatSheaf

end PiExponent.GeometrySupport.CechOneConverse

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CechH1Transfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.CechH1Transfer
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace

universe u
variable {X Y : Scheme.{u}} {J : Type u}

abbrev schemeUnit (Z : Scheme.{u}) : Z.Modules :=
  SheafOfModules.unit Z.ringCatSheaf

end
end PiExponent.GeometrySupport.CechH1Transfer

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_IdealPowerCohomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}
local instance instHasExtModules_solutions : HasExt.{1} X.Modules := HasExt.standard _

end
end PiExponentSeshadri.IdealModule

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ProjectiveTwistAcyclicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveTwistAcyclicity

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Abelian

universe u
variable {X : Scheme.{u}} {ι K : Type u} [Fintype ι] [AddCommGroup K]

abbrev schemeUnit : X.Modules := SheafOfModules.unit X.ringCatSheaf

end
end PiExponent.ProjectiveTwistAcyclicity

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ProjectiveCoordinateAcyclicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.ProjectiveCoordinateAcyclicity
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K] [Fintype σ]
variable (M : X.Modules)
  (k : K →+* Γ(X,⊤))

abbrev schemeUnit : X.Modules := SheafOfModules.unit X.ringCatSheaf

end
end PiExponent.GeometrySupport.ProjectiveCoordinateAcyclicity

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_FiniteNormalizationGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W29

open MvPolynomial Submodule
open scoped BigOperators

section CoefficientPieces

variable {k R τ : Type*} [Field k] [CommRing R] [Algebra k R]
  [Fintype τ] {m : ℕ}

noncomputable def boundedCoefficientMap (g : MvPolynomial τ k →ₐ[k] R)
    (e : Fin m → R) (n : ℕ) :
    (Fin m → restrictTotalDegree τ k n) →ₗ[k] R where
  toFun p := ∑ j, g (p j) * e j
  map_add' p q := by simp [map_add, add_mul, Finset.sum_add_distrib]
  map_smul' c p := by simp [map_smul, Finset.smul_sum]

noncomputable def generatorPiece (g : MvPolynomial τ k →ₐ[k] R)
    (e : Fin m → R) (n : ℕ) : Submodule k R :=
  LinearMap.range (boundedCoefficientMap g e n)

noncomputable instance generatorPiece_finite (g : MvPolynomial τ k →ₐ[k] R)
    (e : Fin m → R) (n : ℕ) : Module.Finite k (generatorPiece g e n) := by
  unfold generatorPiece
  infer_instance

end CoefficientPieces

end PiExponentJets.W29

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveSectionReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u

namespace PiExponentSeshadri.Projective

section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type u} [CommRing K]

lemma reindex_polynomial_irrelevant_le :
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule σ K)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X (R := K) : σ → MvPolynomial σ K)) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn p hp
  change p ∈ idealOfVars σ K
  rw [← pow_one (idealOfVars σ K), mem_pow_idealOfVars_iff]
  intro d hd
  change 1 ≤ d.sum fun _ v => v
  rw [Finsupp.sum, ← hp.degree_eq_sum_deg_support hd]
  exact hn

def reindexCoordinateCover : (Proj (homogeneousSubmodule σ K)).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan _ (X (R := K))
    (m := fun _ => 1) (fun i => isHomogeneous_X K i) (fun _ => by decide)
    reindex_polynomial_irrelevant_le

end

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

end PiExponentSeshadri.Projective

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveSpaceSerre
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveO1
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open PiExponentSeshadri.Geometry

abbrev schemeUnit (X : Scheme.{0}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

end
end PiExponent.ProjectiveO1

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RegularSequenceResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSiegelAux.W30

variable {R X Y Z W Q : Type*} [CommRing R]
variable [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
variable [AddCommGroup W] [AddCommGroup Q]
variable [Module R X] [Module R Y] [Module R Z] [Module R W] [Module R Q]

lemma comp_zero_of_range_eq_ker (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (h : LinearMap.range f = LinearMap.ker g) : g.comp f = 0 := by
  apply LinearMap.ext
  intro x
  change g (f x) = 0
  apply LinearMap.mem_ker.mp
  rw [← h]
  exact LinearMap.mem_range_self f x

end PiExponentSiegelAux.W30

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_KoszulDualCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSiegelAux.W30
open Module

variable {R X Y Z W : Type*} [CommRing R]
variable [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] [AddCommGroup W]
variable [Module R X] [Module R Y] [Module R Z] [Module R W]

def dualConeDifferential (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (r : R) :
    (Dual R Y × Dual R Z) →ₗ[R] (Dual R X × Dual R Y) :=
  (f.dualMap.comp (LinearMap.fst R _ _)).prod
    (r • LinearMap.fst R _ _ - g.dualMap.comp (LinearMap.snd R _ _))

@[simp] theorem dualConeDifferential_apply (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (r : R) (α : Dual R Y) (β : Dual R Z) :
    dualConeDifferential f g r (α, β) = (α.comp f, r • α - β.comp g) := rfl

end PiExponentSiegelAux.W30

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_KoszulTopDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
universe u
namespace PiExponentSiegelAux.W31
open Module
variable {R : Type u} [CommRing R]

def topDualCoordinate {T : Type u} [AddCommGroup T] [Module R T]
    (e : T ≃ₗ[R] R) : Module.Dual R T ≃ₗ[R] R :=
  e.dualMap.symm.trans (LinearMap.ringLmapEquivSelf R R R)

@[simp] theorem topDualCoordinate_apply {T : Type u} [AddCommGroup T] [Module R T]
    (e : T ≃ₗ[R] R) (φ : Module.Dual R T) :
    topDualCoordinate e φ = φ (e.symm 1) := rfl

end PiExponentSiegelAux.W31

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_CompleteIntersectionHilbert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def degreePolynomial (D : ℕ → ℕ) (m : ℕ) : Polynomial ℤ :=
  ∏ i ∈ Finset.range m, ∑ j ∈ Finset.range (D i), (Polynomial.X : Polynomial ℤ) ^ j

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_ConeLocalLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSiegel.W17.ConeLocalLength

attribute [local instance] Localization.AtPrime.algebraOfLiesOver

section PolynomialExtension

variable (A : Type*) [CommRing A] (P : Ideal A) [P.IsPrime]

abbrev polynomialPrime : Ideal (Polynomial A) := P.map Polynomial.C

omit [P.IsPrime] in
theorem polynomialPrime_comap :
    (polynomialPrime A P).comap (algebraMap A (Polynomial A)) = P := by
  ext a
  change Polynomial.C a ∈ P.map Polynomial.C ↔ a ∈ P
  rw [Ideal.mem_map_C_iff]
  constructor
  · intro h
    simpa using h 0
  · intro ha n
    by_cases hn : n = 0
    · subst n
      simpa using ha
    · simp [Polynomial.coeff_C, hn]

instance polynomialPrime_liesOver : (polynomialPrime A P).LiesOver P :=
  (Ideal.liesOver_iff _ _).mpr (polynomialPrime_comap A P).symm

end PolynomialExtension

section LaurentExtension

variable (A : Type*) [CommRing A] (P : Ideal A) [P.IsPrime]

abbrev laurentPrime : Ideal (LaurentPolynomial A) := P.map LaurentPolynomial.C

instance laurent_polynomial_tower : IsScalarTower A (Polynomial A) (LaurentPolynomial A) :=
  IsScalarTower.of_algebraMap_eq (fun a => by
    simp [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.algebraMap_eq,
      ← LaurentPolynomial.C_eq_algebraMap])

theorem polynomialPrime_disjoint_powers_X :
    Disjoint (Submonoid.powers (Polynomial.X : Polynomial A) : Set (Polynomial A))
      (polynomialPrime A P : Set (Polynomial A)) := by
  apply Set.disjoint_left.mpr
  rintro f ⟨n, rfl⟩ hf
  have hc := (Ideal.mem_map_C_iff.mp hf) n
  exact P.one_notMem (by simpa using hc)

omit [P.IsPrime] in
theorem laurentPrime_eq_map_polynomialPrime :
    laurentPrime A P = (polynomialPrime A P).map
      (algebraMap (Polynomial A) (LaurentPolynomial A)) := by
  have hc : (algebraMap (Polynomial A) (LaurentPolynomial A)).comp
      (Polynomial.C : A →+* Polynomial A) = LaurentPolynomial.C := by
    apply RingHom.ext
    intro a
    exact Polynomial.toLaurent_C a
  change P.map LaurentPolynomial.C =
    (P.map Polynomial.C).map (algebraMap (Polynomial A) (LaurentPolynomial A))
  rw [Ideal.map_map, hc]

instance laurentPrime_isPrime : (laurentPrime A P).IsPrime := by
  rw [laurentPrime_eq_map_polynomialPrime]
  exact IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers (Polynomial.X : Polynomial A)) (LaurentPolynomial A)
    (polynomialPrime A P) inferInstance (polynomialPrime_disjoint_powers_X A P)

theorem laurentPrime_comap :
    (laurentPrime A P).comap (algebraMap A (LaurentPolynomial A)) = P := by
  rw [IsScalarTower.algebraMap_eq A (Polynomial A) (LaurentPolynomial A),
    ← Ideal.comap_comap, laurentPrime_eq_map_polynomialPrime,
    show Ideal.comap (algebraMap (Polynomial A) (LaurentPolynomial A))
        ((polynomialPrime A P).map (algebraMap (Polynomial A) (LaurentPolynomial A))) =
        polynomialPrime A P from
      IsLocalization.under_map_of_isPrime_disjoint
        (Submonoid.powers (Polynomial.X : Polynomial A)) (LaurentPolynomial A)
        (show (polynomialPrime A P).IsPrime from inferInstance)
        (polynomialPrime_disjoint_powers_X A P)]
  exact polynomialPrime_comap A P

instance laurentPrime_liesOver : (laurentPrime A P).LiesOver P :=
  (Ideal.liesOver_iff _ _).mpr (laurentPrime_comap A P).symm

instance laurent_flat : Module.Flat A (LaurentPolynomial A) := by
  let : Module.Flat (Polynomial A) (LaurentPolynomial A) :=
    IsLocalization.flat (LaurentPolynomial A) (Submonoid.powers (Polynomial.X : Polynomial A))
  exact Module.Flat.trans A (Polynomial A) (LaurentPolynomial A)

end LaurentExtension

end PiExponentSiegel.W17.ConeLocalLength

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_ConeQuotientAugmentation
attribute [-instance] _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSiegelAux.W30
open scoped Pointwise
variable {R Y Z Q : Type*} [CommRing R] [AddCommGroup Y] [AddCommGroup Z]
  [AddCommGroup Q] [Module R Y] [Module R Z] [Module R Q]

def coneQuotientAugmentation (π : Z →ₗ[R] Q) (r : R) : Z →ₗ[R] QuotSMulTop r Q :=
  (r • (⊤ : Submodule R Q)).mkQ.comp π

theorem coneQuotientAugmentation_surjective (π : Z →ₗ[R] Q) (r : R)
    (hπ : Function.Surjective π) : Function.Surjective (coneQuotientAugmentation π r) :=
  (Submodule.mkQ_surjective _).comp hπ

end PiExponentSiegelAux.W30

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_FiniteFreeResolutionExt
attribute [-instance] _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
universe w v u

namespace PiExponentSiegelAux.W31
open Module
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open HomologicalComplex

section General
variable {C : Type u} [Category.{v} C] [Abelian C]

def projectiveResolutionOfExact (P : ChainComplex C ℕ) (M : C)
    (ε : P.X 0 ⟶ M) (hε : P.d 1 0 ≫ ε = 0)
    (hzero : (ShortComplex.mk (P.d 1 0) ε hε).Exact)
    (hepi : Epi ε) (hexact : ∀ n : ℕ, P.ExactAt (n + 1))
    (hproj : ∀ n : ℕ, CategoryTheory.Projective (P.X n)) :
    CategoryTheory.ProjectiveResolution M where
  complex := P
  projective := hproj
  π := (ChainComplex.toSingle₀Equiv P M).symm ⟨ε, hε⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,
        ShortComplex.quasiIso_iff_of_zeros' _ (by simp; rfl) (by simp; rfl)
          (by simp; rfl)]
      simpa [ChainComplex.toSingle₀Equiv] using! And.intro hzero hepi
    | succ n =>
      rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..)]
      exact hexact n⟩

end General

variable {R : Type u} [CommRing R]

theorem module_exactAt_succ_of_range_eq_ker (P : ChainComplex (ModuleCat.{u} R) ℕ)
    (n : ℕ)
    (h : LinearMap.range (P.d (n + 2) (n + 1)).hom =
      LinearMap.ker (P.d (n + 1) n).hom) : P.ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact h

def moduleFreeResolutionOfExact (P : ChainComplex (ModuleCat.{u} R) ℕ)
    (M : ModuleCat.{u} R) (ε : P.X 0 ⟶ M) (hε : P.d 1 0 ≫ ε = 0)
    (hzero : LinearMap.range (P.d 1 0).hom = LinearMap.ker ε.hom)
    (hepi : Function.Surjective ε.hom)
    (hexact : ∀ n : ℕ, LinearMap.range (P.d (n + 2) (n + 1)).hom =
      LinearMap.ker (P.d (n + 1) n).hom)
    (hfree : ∀ n : ℕ, Module.Free R (P.X n)) : ProjectiveResolution M :=
  projectiveResolutionOfExact P M ε hε
    ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr hzero)
    ((ModuleCat.epi_iff_surjective ε).mpr hepi)
    (fun n => module_exactAt_succ_of_range_eq_ker P n (hexact n))
    (fun n => by
      let := hfree n
      exact ModuleCat.projective_of_free (Module.Free.chooseBasis R (P.X n)))

end PiExponentSiegelAux.W31

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_IdealPowerRestriction
attribute [-instance] _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}}

theorem ker_subscheme_morphismRestrict (I : Y.IdealSheafData) (U : Y.Opens) :
    (I.subschemeι ∣_ U).ker = I.comap U.ι := by
  apply Scheme.IdealSheafData.ext
  funext V
  rw [Scheme.ker_ideal_of_isPullback_of_isOpenImmersion I.subschemeι
    (I.subschemeι ∣_ U) (I.subschemeι ⁻¹ᵁ U).ι U.ι
    (isPullback_morphismRestrict I.subschemeι U), I.ker_subschemeι,
    I.ideal_comap_of_isOpenImmersion]

theorem ker_appTop_subscheme_morphismRestrict (I : Y.IdealSheafData) (U : Y.affineOpens) :
    RingHom.ker (I.subschemeι ∣_ U.1).appTop.hom =
      RingHom.ker (I.comap U.1.ι).subschemeι.appTop.hom := by
  let : IsAffine U.1.toScheme := U.2
  exact (Scheme.Hom.ker_apply (I.subschemeι ∣_ U.1) ⟨⊤,isAffineOpen_top _⟩).symm.trans
    ((congrArg (fun J : U.1.toScheme.IdealSheafData => J.ideal ⟨⊤,isAffineOpen_top _⟩)
      (ker_subscheme_morphismRestrict I U.1)).trans
      ((I.comap U.1.ι).ker_subschemeι_app ⟨⊤,isAffineOpen_top _⟩).symm)

end
end PiExponentSeshadri.IdealModule

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_KoszulDualBottom
attribute [-instance] _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSiegelAux.W30
open Module

variable {R X Y Z : Type*} [CommRing R]
variable [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
variable [Module R X] [Module R Y] [Module R Z]

def dualConeBottom (g : Y →ₗ[R] Z) (r : R) :
    Dual R Z →ₗ[R] (Dual R Y × Dual R Z) :=
  g.dualMap.prod (r • LinearMap.id)

@[simp] theorem dualConeBottom_apply (g : Y →ₗ[R] Z) (r : R) (α : Dual R Z) :
    dualConeBottom g r α = (α.comp g, r • α) := rfl

universe u

end PiExponentSiegelAux.W30

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_PositiveDimensionalHilbert
attribute [-instance] _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Fintype σ]

noncomputable def rationalDegreePolynomial (D : ℕ → ℕ) (m : ℕ) : Polynomial ℚ :=
  (degreePolynomial D m).map (Int.castRingHom ℚ)

noncomputable def regularSequenceHilbertPolynomial
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ) : Polynomial ℚ :=
  Polynomial.hilbertPoly (rationalDegreePolynomial (degreeAt degrees) rs.length)
    (Fintype.card σ - rs.length)

noncomputable def hilbertMultiplicity (p : Polynomial ℚ) (ringDimension : ℕ) : ℚ :=
  p.coeff (ringDimension-1) * ((ringDimension-1).factorial : ℚ)

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PolynomialCoordinateMinpolyQuotient
attribute [-instance] _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSiegel.W08

open Polynomial

variable {K : Type*} [Field K]

noncomputable def coordinateCoefficientSplit (n : ℕ) :
    MvPolynomial (Fin (n + 1)) K ≃ₐ[K] MvPolynomial (Fin n) K[X] :=
  (MvPolynomial.renameEquiv K (_root_.finSuccEquiv n)).trans
    (MvPolynomial.optionEquivRight K (Fin n))

@[simp] theorem coordinateCoefficientSplit_X_zero (n : ℕ) :
    coordinateCoefficientSplit (K := K) n (MvPolynomial.X 0) = MvPolynomial.C Polynomial.X := by
  simp [coordinateCoefficientSplit]

@[simp] theorem coordinateCoefficientSplit_X_succ (n : ℕ) (i : Fin n) :
    coordinateCoefficientSplit (K := K) n (MvPolynomial.X i.succ) = MvPolynomial.X i := by
  simp [coordinateCoefficientSplit]

@[simp] theorem coordinateCoefficientSplit_C (n : ℕ) (a : K) :
    coordinateCoefficientSplit n (MvPolynomial.C a) = MvPolynomial.C (Polynomial.C a) := by
  simp [coordinateCoefficientSplit]

theorem coordinateCoefficientSplit_aeval (n : ℕ) (f : K[X]) :
    coordinateCoefficientSplit n (Polynomial.aeval (MvPolynomial.X (0 : Fin (n+1))) f) =
      MvPolynomial.C f := by
  have h : (coordinateCoefficientSplit (K := K) n).toAlgHom.comp
      (Polynomial.aeval (MvPolynomial.X (0 : Fin (n+1)))) =
      IsScalarTower.toAlgHom K K[X] (MvPolynomial (Fin n) K[X]) := by
    apply Polynomial.algHom_ext
    change coordinateCoefficientSplit n
      (Polynomial.aeval (MvPolynomial.X (0 : Fin (n+1))) Polynomial.X) =
      MvPolynomial.C Polynomial.X
    rw [Polynomial.aeval_X, coordinateCoefficientSplit_X_zero]
  exact AlgHom.congr_fun h f

noncomputable def coordinateMinpolyIdeal (n : ℕ) (f : K[X]) :
    Ideal (MvPolynomial (Fin (n + 1)) K) :=
  Ideal.span {Polynomial.aeval (MvPolynomial.X (0 : Fin (n+1))) f}

theorem coordinateMinpolyIdeal_map (n : ℕ) (f : K[X]) :
    (coordinateMinpolyIdeal n f).map (coordinateCoefficientSplit n).toRingEquiv.toRingHom =
      (Ideal.span {f}).map (MvPolynomial.C : K[X] →+* MvPolynomial (Fin n) K[X]) := by
  simp only [coordinateMinpolyIdeal, Ideal.map_span, Set.image_singleton]
  congr 1
  exact congrArg Set.singleton (coordinateCoefficientSplit_aeval n f)

noncomputable def coefficientAdjoinRootQuotientEquiv (n : ℕ) (f : K[X]) :
    (MvPolynomial (Fin n) K[X] ⧸
      (Ideal.span {f}).map (MvPolynomial.C : K[X] →+* MvPolynomial (Fin n) K[X])) ≃ₐ[K]
      MvPolynomial (Fin n) (AdjoinRoot f) :=
  ((MvPolynomial.quotientEquivQuotientMvPolynomial
    (σ := Fin n) (Ideal.span {f} : Ideal K[X])).symm).restrictScalars K

@[simp] theorem coefficientAdjoinRootQuotientEquiv_mk (n : ℕ) (f : K[X])
    (p : MvPolynomial (Fin n) K[X]) :
    coefficientAdjoinRootQuotientEquiv n f (Ideal.Quotient.mk _ p) =
      MvPolynomial.map (AdjoinRoot.mk f) p := by
  rw [MvPolynomial.map_eq_eval₂Hom_C_comp]
  rfl

noncomputable def coordinateMinpolyQuotientEquiv (n : ℕ) (f : K[X]) :
    (MvPolynomial (Fin (n + 1)) K ⧸ coordinateMinpolyIdeal n f) ≃ₐ[K]
      MvPolynomial (Fin n) (AdjoinRoot f) :=
  (Ideal.quotientEquivAlg (coordinateMinpolyIdeal n f) _
    (coordinateCoefficientSplit n) (coordinateMinpolyIdeal_map n f).symm).trans
      (coefficientAdjoinRootQuotientEquiv n f)

end PiExponentSiegel.W08

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_TriangularLocalParameters
attribute [-instance] _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentSiegel.W10.TriangularLocalParameters

open RingTheory.Sequence
open scoped Pointwise

variable {R S : Type*} [CommRing R] [CommRing S]

theorem scalar_top_eq_principal (r : R) :
    r • (⊤ : Ideal R) = Ideal.span {r} := by
  rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]

def principalModuleQuotientEquiv (π : R →+* S) (hπ : Function.Surjective π)
    (r : R) (hker : RingHom.ker π = Ideal.span {r}) : QuotSMulTop r R ≃+* S :=
  (Ideal.quotEquivOfEq ((scalar_top_eq_principal r).trans hker.symm)).trans
    (RingHom.quotientKerEquivOfSurjective hπ)

@[simp] theorem principalModuleQuotientEquiv_mk (π : R →+* S)
    (hπ : Function.Surjective π) (r : R) (hker : RingHom.ker π = Ideal.span {r}) (x : R) :
    principalModuleQuotientEquiv π hπ r hker (Submodule.Quotient.mk x) = π x := by
  change (RingHom.quotientKerEquivOfSurjective hπ)
    ((Ideal.quotEquivOfEq ((scalar_top_eq_principal r).trans hker.symm))
      (Ideal.Quotient.mk (r • (⊤ : Ideal R)) x)) = π x
  rw [Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

variable (K : Type*) [Field K] (n : ℕ)
    (m : Ideal (MvPolynomial (Fin (n + 1)) K)) [m.IsMaximal]

def firstCoordinateContraction : Ideal (Polynomial K) :=
  m.comap (Polynomial.aeval (MvPolynomial.X (0 : Fin (n + 1)))).toRingHom

def firstCoordinatePolynomial : Polynomial K :=
  Submodule.IsPrincipal.generator (firstCoordinateContraction K n m)

end PiExponentSiegel.W10.TriangularLocalParameters

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_ColonHilbertPolynomial
attribute [-instance] _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k] [Finite σ]

noncomputable def shiftHilbertPolynomial (p : Polynomial ℚ) (d : ℕ) : Polynomial ℚ :=
  p.comp (Polynomial.X - Polynomial.C (d : ℚ))

@[simp] theorem shiftHilbertPolynomial_eval (p : Polynomial ℚ) (d n : ℕ)
    (hdn : d ≤ n) :
    (shiftHilbertPolynomial p d).eval (n : ℚ) = p.eval ((n-d : ℕ) : ℚ) := by
  simp [shiftHilbertPolynomial, Polynomial.eval_comp, Nat.cast_sub hdn]

@[simp] theorem shiftHilbertPolynomial_natDegree (p : Polynomial ℚ) (d : ℕ) :
    (shiftHilbertPolynomial p d).natDegree = p.natDegree := by
  rw [shiftHilbertPolynomial, Polynomial.natDegree_comp,
    Polynomial.natDegree_X_sub_C, mul_one]

@[simp] theorem shiftHilbertPolynomial_leadingCoeff (p : Polynomial ℚ) (d : ℕ) :
    (shiftHilbertPolynomial p d).leadingCoeff = p.leadingCoeff := by
  rw [shiftHilbertPolynomial, Polynomial.leadingCoeff_comp]
  · rw [Polynomial.leadingCoeff_X_sub_C, one_pow, mul_one]
  · rw [Polynomial.natDegree_X_sub_C]
    exact one_ne_zero

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PolynomialGrowthRanks
attribute [-instance] _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace PiExponentJets.W32

def exponentBall (d n : ℕ) : Finset (Fin d →₀ ℕ) :=
  (Finset.range (n + 1)).biUnion fun m => (Finset.univ : Finset (Fin d)).finsuppAntidiag m

@[simp] theorem mem_exponentBall (d n : ℕ) (a : Fin d →₀ ℕ) :
    a ∈ exponentBall d n ↔ a.sum (fun _ e => e) ≤ n := by
  simp only [exponentBall, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_finsuppAntidiag', Finset.subset_univ, and_true]
  constructor
  · rintro ⟨m, hm, hsum⟩
    omega
  · intro h
    exact ⟨a.sum (fun _ e => e), by omega, rfl⟩

noncomputable def polynomialGrowth (d : ℕ) : Polynomial ℚ :=
  Polynomial.preHilbertPoly ℚ d 0

@[simp] theorem polynomialGrowth_eval (d n : ℕ) :
    (polynomialGrowth d).eval (n : ℚ) = ((n + d).choose d : ℚ) := by
  simpa [polynomialGrowth] using
    Polynomial.preHilbertPoly_eq_choose_sub_add ℚ d (k := 0) (n := n) (Nat.zero_le n)

@[simp] theorem polynomialGrowth_natDegree (d : ℕ) :
    (polynomialGrowth d).natDegree = d :=
  Polynomial.natDegree_preHilbertPoly ℚ d 0

noncomputable def scaledPolynomialGrowth (c d : ℕ) : Polynomial ℚ :=
  Polynomial.C (c : ℚ) * polynomialGrowth d

end PiExponentJets.W32

end OAI
end


