-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_IntervalRankInvariant_BarcodeUniqueness20261026_Defs
-- name    : LPCA_Solutions_LPCA_IntervalRankInvariant_BarcodeUniqueness20261026_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-26T05:41:59.64548+00:00
-- url     : https://prove2.me/theorems/d2249e2f-e342-4d62-8673-1e80f84e3d9b
-- title:
--   Interval Rank Invariant — finite barcode uniqueness dependencies
-- statement:
--   Selected constructions and proved compatibility results for interval rank invariant, used in finite real-interval barcode uniqueness for the original homogeneous Ext persistence. The formal declarations retain their exact objects, hypotheses and structure maps.
--
--   Naturality identifies the actual map ranges under an isomorphism.
--
--   The same independent real interval modules, in a concrete finite sum.
--
--   The actual map rank counts scalar summands present at both endpoints.
--
--   The range of a block diagonal product is the product of the ranges.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Theorem3.10, uniqueness of its finite interval decomposition, with formalization dependencies. Certified Lean source: Solutions/LPCA_IntervalRankInvariant.lean, selected declarations in lines 15–149; source SHA-256 8e1786e754a954b2c30c33bac49b1f1dd3de07c02ab17e31d8697391c9f47067; exact-source certificate Sapelo2 job 49315795.

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Homology.Embedding.Restriction
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Order.UpperLower.CompleteLattice
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_redRestrictLin_dLin_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_signed_complex_d_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_signed_dLin_idxCongr_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_signed_restrictLin_dLin_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_dd_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_mul_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_exists_insert_of_inc_ne_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_hc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_eq_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_sdiff_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_erase_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_gt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_lt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_sdiff_add_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_convex_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_mono_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_of_subset_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientCechComplex_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientFieldScalars_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientLocalizationTelescope_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechComplex_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechComplex_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechGradedInclusions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechGradingColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechSquareZero_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTermGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CohomologyGradingInclusions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulAugmentation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulExt_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulHom_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulResolution_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszul_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinatePowerCofinality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CriticalIntervalDecomposition_IntervalExistence20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_DiagramSplitKernel_IntervalExistence20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomologyLegs_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCech_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionKoszulCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionLocalizations_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FilteredColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FilteredHomologyNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiltrationFiniteLevels_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiltrationFunctor_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiniteCochainHomology_CriticalModel20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiniteCriticalSkeleton_CriticalModel20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiniteIntervalDecomposition_IntervalExistence20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiniteIntervalSummand_IntervalExistence20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedFaceRestrictionCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedSupportRestriction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedSupportRestriction_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterActualComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterCochainComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterCohomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterIncidence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterLinkTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterNonfaceVanishing_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterSigns_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HomLocalizationColumns_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HomLocalizationDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_IntervalContainmentTests_BarcodeUniqueness20261026_Defs
import Definitions.Def_LPCA_Solutions_LPCA_IntervalPersistence_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulAugmentationNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulExactness_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulHomDiagram_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulHomTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulModuleNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulMultidegree_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LaurentFaceEvaluation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LegacyExtModuleNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LegacyExtNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LinkIdentities_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyCechComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyKoszulComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyModuleNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationTelescope_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDegreeSeparation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedGradingSpan_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ModuleDirectSumColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_NatRestrictionHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_OrderedIntervalSplitting_IntervalExistence20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_PersistenceIntervalExistence_IntervalExistence20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceCochains_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceCochains_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexDegreeContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCohomologyPieces_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VariableMultiplication_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_MinusOne20261025_Defs

set_option autoImplicit false

namespace LPCA

open CategoryTheory

universe u v

variable (k : Type u) [Field k]

theorem finiteDimensional_intervalScalarSpace (P : Prop) :
    FiniteDimensional k (intervalScalarSpace k P) := by
  classical
  letI : Fintype (PLift P) := Fintype.ofFinite _
  exact inferInstance

theorem finrank_intervalScalarMap (P Q : Prop) [Decidable P] [Decidable Q] :
    Module.finrank k (LinearMap.range (intervalScalarMap k P Q)) =
      if P ∧ Q then 1 else 0 := by
  classical
  by_cases hp : P
  · by_cases hq : Q
    · have hsur : Function.Surjective (intervalScalarMap k P Q) := by
        intro y
        refine ⟨fun _ => y ⟨hq⟩, ?_⟩
        funext z
        simp [intervalScalarMap, hp]
      rw [LinearMap.range_eq_top.mpr hsur, finrank_top]
      simpa [hp, hq] using (intervalScalarEquivOfTrue k Q hq).symm.finrank_eq
    · have hz : intervalScalarMap k P Q = 0 := by
        ext x z
        exact (hq z.down).elim
      simp [hz, hq]
  · have hz : intervalScalarMap k P Q = 0 := by
      ext x z
      simp [intervalScalarMap, hp]
    simp [hz, hp]

variable {k} {ι : Type v} [Category ι]

/-- Naturality identifies the actual map ranges under an isomorphism. -/
noncomputable def natIsoMapRangeEquiv {F G : ι ⥤ ModuleCat.{u} k}
    (e : F ≅ G) {s t : ι} (h : s ⟶ t) :
    LinearMap.range (F.map h).hom ≃ₗ[k] LinearMap.range (G.map h).hom where
  toFun y := ⟨(e.hom.app t) y, by
    obtain ⟨x, hx⟩ := y.property
    refine ⟨(e.hom.app s) x, ?_⟩
    rw [← diagramNaturality_apply e.hom h x, hx]⟩
  invFun y := ⟨(e.inv.app t) y, by
    obtain ⟨x, hx⟩ := y.property
    refine ⟨(e.inv.app s) x, ?_⟩
    rw [← diagramNaturality_apply e.inv h x, hx]⟩
  left_inv y := by
    apply Subtype.ext
    exact congrArg (fun α : F ⟶ F => (α.app t) y) e.hom_inv_id
  right_inv y := by
    apply Subtype.ext
    exact congrArg (fun α : G ⟶ G => (α.app t) y) e.inv_hom_id
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _
  map_smul' c x := by apply Subtype.ext; exact map_smul _ _ _

theorem natIso_map_finrank_eq {F G : ι ⥤ ModuleCat.{u} k}
    (e : F ≅ G) {s t : ι} (h : s ⟶ t) :
    Module.finrank k (LinearMap.range (F.map h).hom) =
      Module.finrank k (LinearMap.range (G.map h).hom) :=
  (natIsoMapRangeEquiv e h).finrank_eq

/-- The range of a block diagonal product is the product of the ranges. -/
noncomputable def prodMapRangeEquiv {M N P Q : ModuleCat.{u} k}
    (f : M ⟶ N) (g : P ⟶ Q) :
    LinearMap.range (f.hom.prodMap g.hom) ≃ₗ[k]
      (LinearMap.range f.hom × LinearMap.range g.hom) where
  toFun y := ⟨⟨y.1.1, by
      obtain ⟨x, hx⟩ := y.property
      exact ⟨x.1, congrArg Prod.fst hx⟩⟩,
    ⟨y.1.2, by
      obtain ⟨x, hx⟩ := y.property
      exact ⟨x.2, congrArg Prod.snd hx⟩⟩⟩
  invFun y := ⟨(y.1.1, y.2.1), by
    obtain ⟨x, hx⟩ := y.1.property
    obtain ⟨z, hz⟩ := y.2.property
    exact ⟨(x, z), Prod.ext hx hz⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_prodMap {M N P Q : ModuleCat.{u} k}
    [FiniteDimensional k N] [FiniteDimensional k Q]
    (f : M ⟶ N) (g : P ⟶ Q) :
    Module.finrank k (LinearMap.range (f.hom.prodMap g.hom)) =
      Module.finrank k (LinearMap.range f.hom) + Module.finrank k (LinearMap.range g.hom) :=
  (prodMapRangeEquiv f g).finrank_eq.trans Module.finrank_prod

/-- The same independent real interval modules, in a concrete finite sum. -/
noncomputable def nonemptyRealIntervalSum (k : Type u) [Field k] :
    List NonemptyRealInterval → (OrderDual ℝ ⥤ ModuleCat.{u} k)
  | [] => emptyIntervalSum
  | J :: js => diagramProd (intervalPersistence k J.1 J.2.1) (nonemptyRealIntervalSum k js)

theorem finiteDimensional_nonemptyRealIntervalSum (js : List NonemptyRealInterval)
    (t : OrderDual ℝ) : FiniteDimensional k ((nonemptyRealIntervalSum k js).obj t) := by
  induction js with
  | nil => change FiniteDimensional k (Fin 0 → k); exact inferInstance
  | cons J js ih =>
    change FiniteDimensional k (intervalScalarSpace k (OrderDual.ofDual t ∈ J.1) ×
      (nonemptyRealIntervalSum k js).obj t)
    letI := finiteDimensional_intervalScalarSpace k (OrderDual.ofDual t ∈ J.1)
    letI := ih
    exact inferInstance

noncomputable def realIntervalCoverage (a b : ℝ) (js : List NonemptyRealInterval) : ℕ := by
  classical
  exact js.countP (fun J => decide (a ∈ J.1 ∧ b ∈ J.1))

/-- The actual map rank counts scalar summands present at both endpoints. -/
theorem nonemptyRealIntervalSum_map_rank (js : List NonemptyRealInterval)
    (a b : ℝ) (hab : a ≤ b) :
    Module.finrank k (LinearMap.range
      ((nonemptyRealIntervalSum k js).map (homOfLE
        (show OrderDual.toDual b ≤ OrderDual.toDual a from hab))).hom) =
      realIntervalCoverage a b js := by
  classical
  induction js with
  | nil =>
    change Module.finrank k (LinearMap.range
      (LinearMap.id : (Fin 0 → k) →ₗ[k] (Fin 0 → k))) = 0
    simp
  | cons J js ih =>
    letI := finiteDimensional_intervalScalarSpace k (a ∈ J.1)
    letI := finiteDimensional_nonemptyRealIntervalSum (k := k) js (OrderDual.toDual a)
    change Module.finrank k (LinearMap.range
      ((intervalScalarMap k (b ∈ J.1) (a ∈ J.1)).prodMap
        ((nonemptyRealIntervalSum k js).map (homOfLE
          (show OrderDual.toDual b ≤ OrderDual.toDual a from hab))).hom)) = _
    calc
      _ = Module.finrank k (LinearMap.range (intervalScalarMap k (b ∈ J.1) (a ∈ J.1))) +
          Module.finrank k (LinearMap.range ((nonemptyRealIntervalSum k js).map
            (homOfLE (show OrderDual.toDual b ≤ OrderDual.toDual a from hab))).hom) :=
        finrank_prodMap (ModuleCat.ofHom (intervalScalarMap k (b ∈ J.1) (a ∈ J.1)))
          ((nonemptyRealIntervalSum k js).map
            (homOfLE (show OrderDual.toDual b ≤ OrderDual.toDual a from hab)))
      _ = _ := by
        rw [finrank_intervalScalarMap, ih]
        simp [realIntervalCoverage, List.countP_cons, and_comm, Nat.add_comm]

end LPCA


