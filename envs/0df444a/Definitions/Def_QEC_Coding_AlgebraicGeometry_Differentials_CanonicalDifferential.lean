-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_CanonicalDifferential
-- name    : QEC_Coding_AlgebraicGeometry_Differentials_CanonicalDifferential
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:21:25.693217+00:00
-- url     : https://prove2.me/theorems/9edb8cf7-ba09-49d4-b2b0-f966c139a84f
-- title:
--   Canonical Differential
-- statement:
--   Definitions and structural lemmas for Canonical Differential, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/CanonicalDifferential.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_GlobalPrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_residue_eq_zero_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_differential_mem_localDifferentialLattice
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_mem_support_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differential_eq_functionFieldDerivation_smul_generator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialCoordinate_differential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferential_eq_coordinate_smul_generator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_exists_heightOne_valuationSubringAtPrime_eq
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_exists_infinityFibreGlobalPlace_of_inverseCoordinate_lt_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_maximalIdeal_eq_span_uniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_inv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_mul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_principalDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_mem_valuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_order_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residue_eq_zero_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuation_uniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_rationalInvolution_X
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
namespace FunctionFieldDifferential
open scoped RatFunc
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
noncomputable def localDerivativeLattice (P : GlobalPlace k F) :
    Submodule P.valuationRing F :=
  Submodule.span P.valuationRing
    (Set.range fun f : P.valuationRing =>
      functionFieldDerivation (k := k) (F := F) (f : F))
theorem localDerivativeLattice_eq_coordinate_map (P : GlobalPlace k F) :
    localDerivativeLattice (k := k) (F := F) P =
      (Differential.localDifferentialLattice P).map
        ((functionFieldDifferentialCoordinate (k := k) (F := F)).restrictScalars
          P.valuationRing) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, rfl⟩
    refine ⟨differential k F (f : F),
      Differential.differential_mem_localDifferentialLattice P f, ?_⟩
    simpa only [LinearMap.restrictScalars_apply] using
      (functionFieldDifferentialCoordinate_differential (k := k) (F := F) (f : F))
  · rw [Differential.localDifferentialLattice]
    refine Submodule.map_le_iff_le_comap.mpr (Submodule.span_le.mpr ?_)
    rintro _ ⟨f, rfl⟩
    change functionFieldDifferentialCoordinate (k := k) (F := F)
      (differential k F (f : F)) ∈ localDerivativeLattice (k := k) (F := F) P
    rw [functionFieldDifferentialCoordinate_differential]
    exact Submodule.subset_span ⟨f, rfl⟩
theorem localDifferentialLattice_eq_generatorMap_localDerivativeLattice
    (P : GlobalPlace k F) :
    Differential.localDifferentialLattice P =
      (localDerivativeLattice (k := k) (F := F) P).map
        ((functionFieldDifferentialGeneratorMap (k := k) (F := F)).restrictScalars
          P.valuationRing) := by
  apply le_antisymm
  · rw [Differential.localDifferentialLattice]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, rfl⟩
    refine ⟨functionFieldDerivation (k := k) (F := F) (f : F),
      Submodule.subset_span ⟨f, rfl⟩, ?_⟩
    simpa only [LinearMap.restrictScalars_apply,
      functionFieldDifferentialGeneratorMap, LinearMap.smulRight_apply,
      LinearMap.id_apply] using
      (differential_eq_functionFieldDerivation_smul_generator (k := k) (F := F) (f : F)).symm
  · refine Submodule.map_le_iff_le_comap.mpr (Submodule.span_le.mpr ?_)
    rintro _ ⟨f, rfl⟩
    change functionFieldDerivation (k := k) (F := F) (f : F) •
      functionFieldDifferentialGenerator (k := k) (F := F) ∈
        Differential.localDifferentialLattice P
    rw [← differential_eq_functionFieldDerivation_smul_generator]
    exact Differential.differential_mem_localDifferentialLattice P f
theorem mem_localDifferentialLattice_iff_coordinate_mem_localDerivativeLattice
    (P : GlobalPlace k F) (omega : Differential k F) :
    omega ∈ Differential.localDifferentialLattice P ↔
      functionFieldDifferentialCoordinate (k := k) (F := F) omega ∈
        localDerivativeLattice (k := k) (F := F) P := by
  constructor
  · rw [localDerivativeLattice_eq_coordinate_map (k := k) (F := F) P]
    exact fun homega => ⟨omega, homega, rfl⟩
  · rw [localDifferentialLattice_eq_generatorMap_localDerivativeLattice
      (k := k) (F := F) P]
    intro hcoordinate
    refine ⟨functionFieldDifferentialCoordinate (k := k) (F := F) omega,
      hcoordinate, ?_⟩
    simpa only [LinearMap.restrictScalars_apply,
      functionFieldDifferentialGeneratorMap, LinearMap.smulRight_apply,
      LinearMap.id_apply] using
      (functionFieldDifferential_eq_coordinate_smul_generator (k := k) (F := F) omega).symm
theorem directChart_localDerivativeLattice_ne_bot (P : GlobalPlace k F)
    (hX : P.valuation (algebraMap (RatFunc k) F RatFunc.X) ≤ 1) :
    localDerivativeLattice (k := k) (F := F) P ≠ ⊥ := by
  let x : P.valuationRing := ⟨algebraMap (RatFunc k) F RatFunc.X,
    (GlobalPlace.mem_valuationRing_iff P _).mpr hX⟩
  have hmem : (1 : F) ∈ localDerivativeLattice (k := k) (F := F) P := by
    have hDX : functionFieldDerivation (k := k) (F := F) (x : F) = 1 := by
      change functionFieldDerivation (k := k) (F := F)
        (algebraMap (RatFunc k) F RatFunc.X) = 1
      exact functionFieldDerivation_apply_X (k := k) (F := F)
    rw [← hDX]
    exact Submodule.subset_span ⟨x, rfl⟩
  intro hbot
  rw [hbot, Submodule.mem_bot] at hmem
  exact one_ne_zero hmem
theorem derivation_span_eq_liftKaehler_range
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (D : Derivation R S M) :
    Submodule.span S (Set.range D) = D.liftKaehlerDifferential.range := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨KaehlerDifferential.D R S x, D.liftKaehlerDifferential_comp_D x⟩
  · rintro y ⟨omega, rfl⟩
    have homega : omega ∈ Submodule.span S
        (Set.range (KaehlerDifferential.D R S)) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ homega
    · rintro _ ⟨x, rfl⟩
      rw [D.liftKaehlerDifferential_comp_D]
      exact Submodule.subset_span (show D x ∈ Set.range D from ⟨x, rfl⟩)
    · exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    · intro a x _ hx
      rw [map_smul]
      exact Submodule.smul_mem _ a hx
omit [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F] in
/-- A valuation-ring span of actual derivation values is finitely generated
once the valuation ring is known, by equality, to be an essentially
finite-type localization.  The equality is consumed by dependent
substitution, so no transported algebra instance is exported. -/
theorem derivationValueSpan_fg_of_valuationSubring_eq
    (P : GlobalPlace k F) (O : ValuationSubring F)
    [Algebra k O] [IsScalarTower k O F] [Algebra.EssFiniteType k O]
    (D : Derivation k F F) (hO : O = P.valuationRing) :
    (Submodule.span P.valuationRing
      (Set.range fun f : P.valuationRing => D (f : F))).FG := by
  subst O
  let D' : Derivation k P.valuationRing F := D.compAlgebraMap P.valuationRing
  change (Submodule.span P.valuationRing (Set.range D')).FG
  rw [derivation_span_eq_liftKaehler_range D']
  exact Submodule.fg_range _
theorem directChart_localDerivativeLattice_fg (P : GlobalPlace k F)
    (hX : P.valuation (algebraMap (RatFunc k) F RatFunc.X) ≤ 1) :
    (localDerivativeLattice (k := k) (F := F) P).FG := by
  letI : Algebra (Polynomial k) F :=
    ((algebraMap (RatFunc k) F).comp
      (algebraMap (Polynomial k) (RatFunc k))).toAlgebra
  letI : IsScalarTower (Polynomial k) (RatFunc k) F :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let B : Type _ := _root_.FunctionField.ringOfIntegers k F
  letI : Algebra k B :=
    ((algebraMap (Polynomial k) B).comp Polynomial.C).toAlgebra
  letI : IsScalarTower k (Polynomial k) B :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Module.Finite (Polynomial k) B := AffinePlace.finite_ringOfIntegers k F
  letI : Algebra.EssFiniteType (Polynomial k) B := inferInstance
  letI : Algebra.EssFiniteType k B :=
    Algebra.EssFiniteType.comp k (Polynomial k) B
  have hX' : P.valuation (((algebraMap B F).comp
      (algebraMap (Polynomial k) B)) Polynomial.X) ≤ 1 := by
    exact hX
  obtain ⟨C, hC⟩ := GlobalPlace.exists_heightOne_valuationSubringAtPrime_eq P hX'
  letI : Algebra k (C.valuationSubringAtPrime F) :=
    ((algebraMap B (C.valuationSubringAtPrime F)).comp
      (algebraMap k B)).toAlgebra
  letI : IsScalarTower k B (C.valuationSubringAtPrime F) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower k (C.valuationSubringAtPrime F) F :=
    IsScalarTower.of_algebraMap_eq fun c => by
      calc
        algebraMap k F c = algebraMap (RatFunc k) F (algebraMap k (RatFunc k) c) :=
          IsScalarTower.algebraMap_apply k (RatFunc k) F c
        _ = algebraMap (Polynomial k) F (Polynomial.C c) := by
          change algebraMap (RatFunc k) F
            (algebraMap (Polynomial k) (RatFunc k) (Polynomial.C c)) =
              algebraMap (Polynomial k) F (Polynomial.C c)
          exact (IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) F _).symm
        _ = algebraMap B F (algebraMap k B c) := by
          change algebraMap (Polynomial k) F (Polynomial.C c) =
            algebraMap B F (algebraMap (Polynomial k) B (Polynomial.C c))
          exact IsScalarTower.algebraMap_apply (Polynomial k) B F _
        _ = algebraMap (C.valuationSubringAtPrime F) F
            (algebraMap B (C.valuationSubringAtPrime F) (algebraMap k B c)) :=
          IsScalarTower.algebraMap_apply B (C.valuationSubringAtPrime F) F _
        _ = algebraMap (C.valuationSubringAtPrime F) F
            (algebraMap k (C.valuationSubringAtPrime F) c) := rfl
  letI : Algebra.EssFiniteType B (C.valuationSubringAtPrime F) :=
    Algebra.EssFiniteType.of_isLocalization (C.valuationSubringAtPrime F)
      C.asIdeal.primeCompl
  letI : Algebra.EssFiniteType k (C.valuationSubringAtPrime F) :=
    Algebra.EssFiniteType.comp k B (C.valuationSubringAtPrime F)
  exact derivationValueSpan_fg_of_valuationSubring_eq (k := k) (F := F) P
    (C.valuationSubringAtPrime F) (functionFieldDerivation (k := k) (F := F)) hC
theorem functionFieldDerivation_apply_inverseCoordinate :
    functionFieldDerivation (k := k) (F := F)
      (algebraMap (RatFunc k) F RatFunc.X)⁻¹ =
        -(algebraMap (RatFunc k) F RatFunc.X)⁻¹ ^ 2 := by
  rw [Derivation.leibniz_inv, functionFieldDerivation_apply_X]
  simp only [smul_eq_mul, mul_one]
theorem inverseChart_localDerivativeLattice_ne_bot (P : GlobalPlace k F)
    (hY : P.valuation (algebraMap (RatFunc k) F RatFunc.X)⁻¹ ≤ 1) :
    localDerivativeLattice (k := k) (F := F) P ≠ ⊥ := by
  let y : P.valuationRing := ⟨(algebraMap (RatFunc k) F RatFunc.X)⁻¹,
    (GlobalPlace.mem_valuationRing_iff P _).mpr hY⟩
  have hXne : algebraMap (RatFunc k) F RatFunc.X ≠ 0 :=
    (map_ne_zero_iff (algebraMap (RatFunc k) F)
      (algebraMap (RatFunc k) F).injective).mpr RatFunc.X_ne_zero
  have hDne : functionFieldDerivation (k := k) (F := F) (y : F) ≠ 0 := by
    change functionFieldDerivation (k := k) (F := F)
      (algebraMap (RatFunc k) F RatFunc.X)⁻¹ ≠ 0
    rw [functionFieldDerivation_apply_inverseCoordinate]
    exact (neg_ne_zero).mpr (pow_ne_zero _ (inv_ne_zero hXne))
  intro hbot
  apply hDne
  have hmem : functionFieldDerivation (k := k) (F := F) (y : F) ∈
      localDerivativeLattice (k := k) (F := F) P :=
    Submodule.subset_span ⟨y, rfl⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact hmem
theorem inverseChart_localDerivativeLattice_fg (P : GlobalPlace k F)
    (hY : P.valuation (algebraMap (RatFunc k) F RatFunc.X)⁻¹ ≤ 1) :
    (localDerivativeLattice (k := k) (F := F) P).FG := by
  let D₀ : Derivation k F F := functionFieldDerivation (k := k) (F := F)
  change (Submodule.span P.valuationRing
    (Set.range fun f : P.valuationRing => D₀ (f : F))).FG
  let oldRationalAlgebra : Algebra (RatFunc k) F := inferInstance
  let oldFunctionField : _root_.FunctionField k F := inferInstance
  let oldSeparable : Algebra.IsSeparable (RatFunc k) F := inferInstance
  have htransportConstants (c : k) :
      algebraMap k F c =
        InverseAffinePlace.transportedRationalMap
          (oldRationalAlgebra := oldRationalAlgebra) k F
            (algebraMap k (RatFunc k) c) := by
    change algebraMap k F c = algebraMap (RatFunc k) F
      (InverseAffinePlace.rationalInvolution k (algebraMap k (RatFunc k) c))
    rw [AlgEquiv.commutes]
    exact IsScalarTower.algebraMap_apply k (RatFunc k) F c
  have htransportX :
      InverseAffinePlace.transportedRationalMap
        (oldRationalAlgebra := oldRationalAlgebra) k F RatFunc.X =
          (algebraMap (RatFunc k) F RatFunc.X)⁻¹ := by
    change algebraMap (RatFunc k) F
      (InverseAffinePlace.rationalInvolution k RatFunc.X) =
        (algebraMap (RatFunc k) F RatFunc.X)⁻¹
    rw [InverseAffinePlace.rationalInvolution_X, map_inv₀]
  letI : Algebra (RatFunc k) F :=
    InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : Algebra (Polynomial k) F :=
    InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : IsScalarTower (Polynomial k) (RatFunc k) F :=
    InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : _root_.FunctionField k F :=
    InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := oldRationalAlgebra)
      (oldFunctionField := oldFunctionField) k F
  letI : Algebra.IsSeparable (RatFunc k) F :=
    InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) k F
  let B : Type _ := _root_.FunctionField.ringOfIntegers k F
  letI : Algebra k B :=
    ((algebraMap (Polynomial k) B).comp Polynomial.C).toAlgebra
  letI : IsScalarTower k (Polynomial k) B :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Module.Finite (Polynomial k) B := AffinePlace.finite_ringOfIntegers k F
  letI : Algebra.EssFiniteType (Polynomial k) B := inferInstance
  letI : Algebra.EssFiniteType k B :=
    Algebra.EssFiniteType.comp k (Polynomial k) B
  have hY' : P.valuation (((algebraMap B F).comp
      (algebraMap (Polynomial k) B)) Polynomial.X) ≤ 1 := by
    change P.valuation (InverseAffinePlace.transportedRationalMap
      (oldRationalAlgebra := oldRationalAlgebra) k F RatFunc.X) ≤ 1
    rw [htransportX]
    exact hY
  obtain ⟨C, hC⟩ := GlobalPlace.exists_heightOne_valuationSubringAtPrime_eq P hY'
  letI : Algebra k (C.valuationSubringAtPrime F) :=
    ((algebraMap B (C.valuationSubringAtPrime F)).comp
      (algebraMap k B)).toAlgebra
  letI : IsScalarTower k B (C.valuationSubringAtPrime F) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower k (C.valuationSubringAtPrime F) F :=
    IsScalarTower.of_algebraMap_eq fun c => by
      calc
        algebraMap k F c =
            InverseAffinePlace.transportedRationalMap
              (oldRationalAlgebra := oldRationalAlgebra) k F
                (algebraMap k (RatFunc k) c) := htransportConstants c
        _ = algebraMap (RatFunc k) F (algebraMap k (RatFunc k) c) := rfl
        _ = algebraMap (Polynomial k) F (Polynomial.C c) := by
          change algebraMap (RatFunc k) F
            (algebraMap (Polynomial k) (RatFunc k) (Polynomial.C c)) =
              algebraMap (Polynomial k) F (Polynomial.C c)
          exact (IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) F _).symm
        _ = algebraMap B F (algebraMap k B c) := by
          change algebraMap (Polynomial k) F (Polynomial.C c) =
            algebraMap B F (algebraMap (Polynomial k) B (Polynomial.C c))
          exact IsScalarTower.algebraMap_apply (Polynomial k) B F _
        _ = algebraMap (C.valuationSubringAtPrime F) F
            (algebraMap B (C.valuationSubringAtPrime F) (algebraMap k B c)) :=
          IsScalarTower.algebraMap_apply B (C.valuationSubringAtPrime F) F _
        _ = algebraMap (C.valuationSubringAtPrime F) F
            (algebraMap k (C.valuationSubringAtPrime F) c) := rfl
  letI : Algebra.EssFiniteType B (C.valuationSubringAtPrime F) :=
    Algebra.EssFiniteType.of_isLocalization (C.valuationSubringAtPrime F)
      C.asIdeal.primeCompl
  letI : Algebra.EssFiniteType k (C.valuationSubringAtPrime F) :=
    Algebra.EssFiniteType.comp k B (C.valuationSubringAtPrime F)
  exact derivationValueSpan_fg_of_valuationSubring_eq (k := k) (F := F) P
    (C.valuationSubringAtPrime F) D₀ hC
theorem exists_principal_cutoff_of_fg_ne_bot (P : GlobalPlace k F)
    (L : Submodule P.valuationRing F) (hfg : L.FG) (hne : L ≠ ⊥) :
    ∃ a : F, a ≠ 0 ∧
      L = Submodule.span P.valuationRing ({a} : Set F) ∧
        ∀ x : F, x ∈ L ↔ x = 0 ∨ P.order a ≤ P.order x := by
  classical
  obtain ⟨S, hS⟩ := hfg
  have hS_nonempty : (S.erase 0).Nonempty := by
    by_contra h
    have hS_zero : ∀ s ∈ S, s = 0 := by
      intro s hs
      by_contra hs0
      exact h ⟨s, Finset.mem_erase.mpr ⟨hs0, hs⟩⟩
    apply hne
    rw [← hS]
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      intro s hs
      rw [hS_zero s hs]
      exact Submodule.zero_mem _
    · exact bot_le
  let T : Finset ℤ := (S.erase 0).image P.order
  have hT_nonempty : T.Nonempty := by
    rcases hS_nonempty with ⟨s, hs⟩
    exact ⟨P.order s, Finset.mem_image.mpr ⟨s, hs, rfl⟩⟩
  obtain ⟨a, haS, haorder⟩ :=
    Finset.mem_image.mp (Finset.min'_mem T hT_nonempty)
  have ha_ne : a ≠ 0 := (Finset.mem_erase.mp haS).1
  have hmin (s : F) (hs : s ∈ S) (hs0 : s ≠ 0) :
      P.order a ≤ P.order s := by
    rw [haorder]
    apply Finset.min'_le
    exact Finset.mem_image.mpr ⟨s, Finset.mem_erase.mpr ⟨hs0, hs⟩, rfl⟩
  have ha_mem : a ∈ L := by
    rw [← hS]
    exact Submodule.subset_span (Finset.mem_erase.mp haS).2
  have hL_span : L = Submodule.span P.valuationRing ({a} : Set F) := by
    apply le_antisymm
    · rw [← hS]
      refine Submodule.span_le.mpr ?_
      intro s hs
      by_cases hs0 : s = 0
      · rw [hs0]
        exact Submodule.zero_mem _
      · refine Submodule.mem_span_singleton.mpr ⟨⟨s * a⁻¹, ?_⟩, ?_⟩
        · apply (GlobalPlace.regularAt_iff_mem_valuationRing P _).mp
          apply (GlobalPlace.regularAt_iff_order_nonnegative P
            (mul_ne_zero hs0 (inv_ne_zero ha_ne))).mpr
          rw [GlobalPlace.order_mul P hs0 (inv_ne_zero ha_ne),
            GlobalPlace.order_inv]
          have hmin_s := hmin s hs hs0
          omega
        · change (s * a⁻¹) * a = s
          rw [mul_assoc, inv_mul_cancel₀ ha_ne, mul_one]
    · refine Submodule.span_le.mpr ?_
      exact Set.singleton_subset_iff.mpr ha_mem
  refine ⟨a, ha_ne, hL_span, ?_⟩
  intro x
  constructor
  · intro hx
    rw [hL_span] at hx
    rcases Submodule.mem_span_singleton.mp hx with ⟨r, hr⟩
    by_cases hr0 : (r : F) = 0
    · left
      rw [← hr]
      change (r : F) * a = 0
      rw [hr0, zero_mul]
    · right
      have hr_regular : P.RegularAt (r : F) :=
        (GlobalPlace.regularAt_iff_mem_valuationRing P _).mpr r.property
      have hr_order : 0 ≤ P.order (r : F) :=
        (GlobalPlace.regularAt_iff_order_nonnegative P hr0).mp hr_regular
      have hx_order : P.order x = P.order (r : F) + P.order a := by
        rw [← hr]
        change P.order ((r : F) * a) = P.order (r : F) + P.order a
        rw [GlobalPlace.order_mul P hr0 ha_ne]
      omega
  · rintro (rfl | hx_order)
    · exact Submodule.zero_mem _
    · by_cases hx0 : x = 0
      · rw [hx0]
        exact Submodule.zero_mem _
      · rw [hL_span]
        refine Submodule.mem_span_singleton.mpr ⟨⟨x * a⁻¹, ?_⟩, ?_⟩
        · apply (GlobalPlace.regularAt_iff_mem_valuationRing P _).mp
          apply (GlobalPlace.regularAt_iff_order_nonnegative P
            (mul_ne_zero hx0 (inv_ne_zero ha_ne))).mpr
          rw [GlobalPlace.order_mul P hx0 (inv_ne_zero ha_ne),
            GlobalPlace.order_inv]
          omega
        · change (x * a⁻¹) * a = x
          rw [mul_assoc, inv_mul_cancel₀ ha_ne, mul_one]
theorem directChart_exists_localDerivativeLattice_principal_cutoff
    (P : GlobalPlace k F)
    (hX : P.valuation (algebraMap (RatFunc k) F RatFunc.X) ≤ 1) :
    ∃ a : F, a ≠ 0 ∧
      localDerivativeLattice (k := k) (F := F) P =
        Submodule.span P.valuationRing ({a} : Set F) ∧
        ∀ x : F, x ∈ localDerivativeLattice (k := k) (F := F) P ↔
          x = 0 ∨ P.order a ≤ P.order x :=
  exists_principal_cutoff_of_fg_ne_bot (k := k) (F := F) P
    (localDerivativeLattice (k := k) (F := F) P)
    (directChart_localDerivativeLattice_fg (k := k) (F := F) P hX)
    (directChart_localDerivativeLattice_ne_bot (k := k) (F := F) P hX)
theorem inverseChart_exists_localDerivativeLattice_principal_cutoff
    (P : GlobalPlace k F)
    (hY : P.valuation (algebraMap (RatFunc k) F RatFunc.X)⁻¹ ≤ 1) :
    ∃ a : F, a ≠ 0 ∧
      localDerivativeLattice (k := k) (F := F) P =
        Submodule.span P.valuationRing ({a} : Set F) ∧
        ∀ x : F, x ∈ localDerivativeLattice (k := k) (F := F) P ↔
          x = 0 ∨ P.order a ≤ P.order x :=
  exists_principal_cutoff_of_fg_ne_bot (k := k) (F := F) P
    (localDerivativeLattice (k := k) (F := F) P)
    (inverseChart_localDerivativeLattice_fg (k := k) (F := F) P hY)
    (inverseChart_localDerivativeLattice_ne_bot (k := k) (F := F) P hY)
theorem exists_localDerivativeLattice_principal_cutoff (P : GlobalPlace k F) :
    ∃ a : F, a ≠ 0 ∧
      localDerivativeLattice (k := k) (F := F) P =
        Submodule.span P.valuationRing ({a} : Set F) ∧
        ∀ x : F, x ∈ localDerivativeLattice (k := k) (F := F) P ↔
          x = 0 ∨ P.order a ≤ P.order x := by
  rcases Valuation.val_le_one_or_val_inv_le_one P.valuation
    (algebraMap (RatFunc k) F RatFunc.X) with hX | hY
  · exact directChart_exists_localDerivativeLattice_principal_cutoff
      (k := k) (F := F) P hX
  · exact inverseChart_exists_localDerivativeLattice_principal_cutoff
      (k := k) (F := F) P hY
def IsLocalDerivativeLatticePrincipalCutoff (P : GlobalPlace k F) (a : F) : Prop :=
  a ≠ 0 ∧
    localDerivativeLattice (k := k) (F := F) P =
      Submodule.span P.valuationRing ({a} : Set F) ∧
    ∀ x : F, x ∈ localDerivativeLattice (k := k) (F := F) P ↔
      x = 0 ∨ P.order a ≤ P.order x
theorem exists_localDerivativeLatticePrincipalCutoff (P : GlobalPlace k F) :
    ∃ a : F, IsLocalDerivativeLatticePrincipalCutoff (k := k) (F := F) P a := by
  simpa only [IsLocalDerivativeLatticePrincipalCutoff] using
    (exists_localDerivativeLattice_principal_cutoff (k := k) (F := F) P)
theorem localDerivativeLatticePrincipalCutoff_order_eq (P : GlobalPlace k F)
    {a b : F}
    (ha : IsLocalDerivativeLatticePrincipalCutoff (k := k) (F := F) P a)
    (hb : IsLocalDerivativeLatticePrincipalCutoff (k := k) (F := F) P b) :
    P.order a = P.order b := by
  rcases ha with ⟨ha_ne, ha_span, ha_cutoff⟩
  rcases hb with ⟨hb_ne, hb_span, hb_cutoff⟩
  apply le_antisymm
  · have hb_mem : b ∈ localDerivativeLattice (k := k) (F := F) P := by
      rw [hb_span]
      exact Submodule.subset_span (Set.mem_singleton b)
    rcases (ha_cutoff b).mp hb_mem with hb_zero | hab
    · exact (hb_ne hb_zero).elim
    · exact hab
  · have ha_mem : a ∈ localDerivativeLattice (k := k) (F := F) P := by
      rw [ha_span]
      exact Submodule.subset_span (Set.mem_singleton a)
    rcases (hb_cutoff a).mp ha_mem with ha_zero | hba
    · exact (ha_ne ha_zero).elim
    · exact hba
theorem chosenLocalDerivativeLatticePrincipalCutoff (P : GlobalPlace k F) :
    IsLocalDerivativeLatticePrincipalCutoff (k := k) (F := F) P
      (Classical.choose
        (exists_localDerivativeLatticePrincipalCutoff (k := k) (F := F) P)) :=
  Classical.choose_spec
    (exists_localDerivativeLatticePrincipalCutoff (k := k) (F := F) P)
noncomputable def localDerivativeLatticeGeneratorOrder (P : GlobalPlace k F) : ℤ :=
  P.order (Classical.choose
    (exists_localDerivativeLatticePrincipalCutoff (k := k) (F := F) P))
theorem localDerivativeLatticeGeneratorOrder_eq_order (P : GlobalPlace k F)
    {a : F}
    (ha : IsLocalDerivativeLatticePrincipalCutoff (k := k) (F := F) P a) :
    localDerivativeLatticeGeneratorOrder (k := k) (F := F) P = P.order a := by
  unfold localDerivativeLatticeGeneratorOrder
  exact localDerivativeLatticePrincipalCutoff_order_eq (k := k) (F := F) P
    (chosenLocalDerivativeLatticePrincipalCutoff (k := k) (F := F) P) ha
theorem functionFieldDifferentialCoordinate_ne_zero_iff (omega : Differential k F) :
    functionFieldDifferentialCoordinate (k := k) (F := F) omega ≠ 0 ↔ omega ≠ 0 := by
  constructor
  · intro hcoordinate homega
    apply hcoordinate
    rw [homega, map_zero]
  · intro homega hcoordinate
    apply homega
    rw [functionFieldDifferential_eq_coordinate_smul_generator (k := k) (F := F) omega,
      hcoordinate, zero_smul]
noncomputable def differentialOrder (P : GlobalPlace k F) (omega : Differential k F)
    (homega : omega ≠ 0) : ℤ := by
  have _hcoordinate : functionFieldDifferentialCoordinate (k := k) (F := F) omega ≠ 0 :=
    (functionFieldDifferentialCoordinate_ne_zero_iff (k := k) (F := F) omega).mpr homega
  exact P.order (functionFieldDifferentialCoordinate (k := k) (F := F) omega) -
    localDerivativeLatticeGeneratorOrder (k := k) (F := F) P
theorem functionFieldDerivation_apply_directPolynomial (p : Polynomial k) :
    functionFieldDerivation (k := k) (F := F)
      (Polynomial.aeval (algebraMap (RatFunc k) F RatFunc.X) p) =
        Polynomial.aeval (algebraMap (RatFunc k) F RatFunc.X) p.derivative := by
  rw [Derivation.map_aeval, functionFieldDerivation_apply_X]
  simp only [smul_eq_mul, mul_one]
theorem derivation_mem_valuationRing_of_finite_generators
    (P : GlobalPlace k F) {B : Type*} [CommRing B]
    [Algebra (Polynomial k) B] [Algebra B F] [Algebra (Polynomial k) F]
    [IsScalarTower (Polynomial k) B F]
    (D : Derivation k F F)
    (hpoly : ∀ p : Polynomial k,
      D (algebraMap (Polynomial k) F p) = algebraMap (Polynomial k) F p.derivative)
    (hBval : ∀ q : B, algebraMap B F q ∈ P.valuationRing)
    {n : ℕ} (b : Fin n → B)
    (hspan : Submodule.span (Polynomial k) (Set.range b) = ⊤)
    (hDb : ∀ i : Fin n, D (algebraMap B F (b i)) ∈ P.valuationRing) :
    ∀ q : B, D (algebraMap B F q) ∈ P.valuationRing := by
  intro q
  have hq : q ∈ Submodule.span (Polynomial k) (Set.range b) := by
    rw [hspan]
    trivial
  refine Submodule.span_induction
    (p := fun q _ => D (algebraMap B F q) ∈ P.valuationRing) ?_ ?_ ?_ ?_ hq
  · rintro q ⟨i, rfl⟩
    exact hDb i
  · simpa only [map_zero] using P.valuationRing.zero_mem
  · intro x y _ _ hx hy
    simpa only [map_add] using P.valuationRing.add_mem _ _ hx hy
  · intro p x _ hx
    have hp : algebraMap (Polynomial k) F p ∈ P.valuationRing := by
      rw [IsScalarTower.algebraMap_apply (Polynomial k) B F p]
      exact hBval (algebraMap (Polynomial k) B p)
    have hp' : algebraMap (Polynomial k) F p.derivative ∈ P.valuationRing := by
      rw [IsScalarTower.algebraMap_apply (Polynomial k) B F p.derivative]
      exact hBval (algebraMap (Polynomial k) B p.derivative)
    change D (algebraMap B F (p • x)) ∈ P.valuationRing
    simp only [Algebra.smul_def, map_mul, Derivation.leibniz, smul_eq_mul,
      ← IsScalarTower.algebraMap_apply (Polynomial k) B F, hpoly]
    exact P.valuationRing.add_mem _ _ (P.valuationRing.mul_mem _ _ hp hx)
      (P.valuationRing.mul_mem _ _ (hBval x) hp')
theorem derivation_mem_heightOneLocalization
    {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B F]
    [IsFractionRing B F]
    (C : IsDedekindDomain.HeightOneSpectrum B)
    (D : Derivation k F F)
    (hD : ∀ q : B, D (algebraMap B F q) ∈ C.valuationSubringAtPrime F) :
    ∀ z : C.valuationSubringAtPrime F,
      D (z : F) ∈ C.valuationSubringAtPrime F := by
  intro z
  obtain ⟨⟨q, s⟩, hzs⟩ := IsLocalization.surj C.asIdeal.primeCompl z
  have hzsF : (z : F) * algebraMap B F (s : B) = algebraMap B F q := by
    have h := congrArg (algebraMap (C.valuationSubringAtPrime F) F) hzs
    simp only [map_mul,
      ← IsScalarTower.algebraMap_apply B (C.valuationSubringAtPrime F) F] at h
    exact h
  have hs_unit : IsUnit (algebraMap B (C.valuationSubringAtPrime F) (s : B)) :=
    IsLocalization.map_units (C.valuationSubringAtPrime F) s
  have hs_nonzero : algebraMap B F (s : B) ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply B (C.valuationSubringAtPrime F) F]
    exact (IsUnit.map (algebraMap (C.valuationSubringAtPrime F) F) hs_unit).ne_zero
  have hs_inv_mem : (algebraMap B F (s : B))⁻¹ ∈ C.valuationSubringAtPrime F := by
    rw [IsScalarTower.algebraMap_apply B (C.valuationSubringAtPrime F) F,
      ← hs_unit.unit_spec,
      ← map_units_inv (algebraMap (C.valuationSubringAtPrime F) F) hs_unit.unit]
    exact (↑(hs_unit.unit⁻¹) : C.valuationSubringAtPrime F).property
  have hDzs : (z : F) * D (algebraMap B F (s : B)) +
      algebraMap B F (s : B) * D (z : F) = D (algebraMap B F q) := by
    have h := congrArg D hzsF
    rw [Derivation.leibniz] at h
    simpa only [smul_eq_mul] using h
  have hsub_mem : D (algebraMap B F q) -
      (z : F) * D (algebraMap B F (s : B)) ∈ C.valuationSubringAtPrime F :=
    (C.valuationSubringAtPrime F).sub_mem (hD q)
      ((C.valuationSubringAtPrime F).mul_mem _ _ z.property (hD (s : B)))
  have hsolve : D (z : F) = (algebraMap B F (s : B))⁻¹ *
      (D (algebraMap B F q) - (z : F) * D (algebraMap B F (s : B))) := by
    apply (eq_inv_mul_iff_mul_eq₀ hs_nonzero).mpr
    show algebraMap B F (s : B) * D (z : F) =
      D (algebraMap B F q) - (z : F) * D (algebraMap B F (s : B))
    rw [← hDzs]
    ring
  rw [hsolve]
  exact (C.valuationSubringAtPrime F).mul_mem _ _ hs_inv_mem hsub_mem
theorem localDerivativeLatticeGeneratorOrder_eq_zero_of_one_mem
    (P : GlobalPlace k F)
    (hone : (1 : F) ∈ localDerivativeLattice (k := k) (F := F) P)
    (hregular : ∀ x : F, x ∈ localDerivativeLattice (k := k) (F := F) P →
      P.RegularAt x) :
    localDerivativeLatticeGeneratorOrder (k := k) (F := F) P = 0 := by
  obtain ⟨a, ha_ne, ha_span, ha_cutoff⟩ :=
    exists_localDerivativeLattice_principal_cutoff (k := k) (F := F) P
  have ha_mem : a ∈ localDerivativeLattice (k := k) (F := F) P := by
    rw [ha_span]
    exact Submodule.subset_span (Set.mem_singleton a)
  have ha_order : 0 ≤ P.order a :=
    (GlobalPlace.regularAt_iff_order_nonnegative P ha_ne).mp (hregular a ha_mem)
  rw [ha_span] at hone
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hone
  have hr_eq : (r : F) * a = 1 := by
    exact hr
  have hr_ne : (r : F) ≠ 0 := by
    intro hr_zero
    rw [hr_zero, zero_mul] at hr_eq
    exact zero_ne_one hr_eq
  have hr_order : 0 ≤ P.order (r : F) :=
    (GlobalPlace.regularAt_iff_order_nonnegative P hr_ne).mp
      ((GlobalPlace.regularAt_iff_mem_valuationRing P _).mpr r.property)
  have hone_order : P.order (1 : F) = 0 := by
    unfold GlobalPlace.order
    rw [P.valuation.map_one]
    simp
  have hsum : 0 = P.order (r : F) + P.order a := by
    calc
      0 = P.order (1 : F) := hone_order.symm
      _ = P.order ((r : F) * a) := by rw [hr_eq]
      _ = P.order (r : F) + P.order a := GlobalPlace.order_mul P hr_ne ha_ne
  calc
    localDerivativeLatticeGeneratorOrder (k := k) (F := F) P = P.order a :=
      localDerivativeLatticeGeneratorOrder_eq_order (k := k) (F := F) P
        ⟨ha_ne, ha_span, ha_cutoff⟩
    _ = 0 := by omega
theorem exists_directChartGeneratorOrderExceptionalFinset :
    ∃ E : Finset (GlobalPlace k F),
      ∀ P : GlobalPlace k F,
        P.valuation (algebraMap (RatFunc k) F RatFunc.X) ≤ 1 →
        P ∉ E →
        localDerivativeLatticeGeneratorOrder (k := k) (F := F) P = 0 := by
  classical
  letI : Algebra (Polynomial k) F :=
    ((algebraMap (RatFunc k) F).comp
      (algebraMap (Polynomial k) (RatFunc k))).toAlgebra
  letI : IsScalarTower (Polynomial k) (RatFunc k) F :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let B : Type _ := _root_.FunctionField.ringOfIntegers k F
  letI : Algebra k B :=
    ((algebraMap (Polynomial k) B).comp Polynomial.C).toAlgebra
  letI : IsScalarTower k (Polynomial k) B :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower (Polynomial k) B F :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Module.Finite (Polynomial k) B := AffinePlace.finite_ringOfIntegers k F
  obtain ⟨n, b, hspan⟩ := Module.Finite.exists_fin (R := Polynomial k) (M := B)
  let E : Finset (GlobalPlace k F) :=
    Finset.univ.biUnion fun i =>
      if hDi : functionFieldDerivation (k := k) (F := F)
          (algebraMap B F (b i)) = 0 then ∅ else
        (GlobalPlace.principalDivisor (k := k) (F := F)
          (Units.mk0 (functionFieldDerivation (k := k) (F := F)
            (algebraMap B F (b i))) hDi)).support
  refine ⟨E, ?_⟩
  intro P hX hPE
  have hX' : P.valuation (((algebraMap B F).comp
      (algebraMap (Polynomial k) B)) Polynomial.X) ≤ 1 := by
    exact hX
  obtain ⟨C, hC⟩ :=
    GlobalPlace.exists_heightOne_valuationSubringAtPrime_eq P hX'
  have hBval : ∀ q : B, algebraMap B F q ∈ P.valuationRing := by
    intro q
    rw [← hC]
    exact (algebraMap B (C.valuationSubringAtPrime F) q).property
  have hDb : ∀ i : Fin n,
      functionFieldDerivation (k := k) (F := F) (algebraMap B F (b i)) ∈
        P.valuationRing := by
    intro i
    by_cases hDi : functionFieldDerivation (k := k) (F := F)
        (algebraMap B F (b i)) = 0
    · rw [hDi]
      exact P.valuationRing.zero_mem
    · have hPnot : P ∉ (GlobalPlace.principalDivisor (k := k) (F := F)
          (Units.mk0 (functionFieldDerivation (k := k) (F := F)
            (algebraMap B F (b i))) hDi)).support := by
        intro hsupport
        apply hPE
        simp only [E, Finset.mem_biUnion, Finset.mem_univ, true_and]
        refine ⟨i, ?_⟩
        simpa only [dif_neg hDi] using hsupport
      have hcoefficient : GlobalPlace.principalDivisor (k := k) (F := F)
          (Units.mk0 (functionFieldDerivation (k := k) (F := F)
            (algebraMap B F (b i))) hDi) P = 0 := by
        by_contra hnonzero
        exact hPnot (Finsupp.mem_support_iff.mpr hnonzero)
      have horder : P.order (functionFieldDerivation (k := k) (F := F)
          (algebraMap B F (b i))) = 0 := by
        simpa only [GlobalPlace.principalDivisor_apply, Units.val_mk0] using hcoefficient
      exact (GlobalPlace.regularAt_iff_mem_valuationRing P _).mp
        ((GlobalPlace.regularAt_iff_order_nonnegative P hDi).mpr (by omega))
  have hpoly : ∀ p : Polynomial k,
      functionFieldDerivation (k := k) (F := F) (algebraMap (Polynomial k) F p) =
        algebraMap (Polynomial k) F p.derivative := by
    intro p
    have h_aeval (q : Polynomial k) :
        Polynomial.aeval (algebraMap (RatFunc k) F RatFunc.X) q =
          algebraMap (RatFunc k) F (Polynomial.aeval RatFunc.X q) := by
      simpa only [IsScalarTower.toAlgHom_apply] using
        (Polynomial.aeval_algHom_apply
          (IsScalarTower.toAlgHom k (RatFunc k) F) RatFunc.X q)
    change functionFieldDerivation (k := k) (F := F)
      (algebraMap (RatFunc k) F
        (algebraMap (Polynomial k) (RatFunc k) p)) =
      algebraMap (RatFunc k) F
        (algebraMap (Polynomial k) (RatFunc k) p.derivative)
    calc
      functionFieldDerivation (k := k) (F := F)
          (algebraMap (RatFunc k) F
            (algebraMap (Polynomial k) (RatFunc k) p)) =
          functionFieldDerivation (k := k) (F := F)
            (algebraMap (RatFunc k) F (Polynomial.aeval RatFunc.X p)) := by
              rw [RatFunc.aeval_X_left_eq_algebraMap]
      _ = functionFieldDerivation (k := k) (F := F)
            (Polynomial.aeval (algebraMap (RatFunc k) F RatFunc.X) p) := by
              rw [h_aeval]
      _ = Polynomial.aeval (algebraMap (RatFunc k) F RatFunc.X) p.derivative :=
            functionFieldDerivation_apply_directPolynomial (k := k) (F := F) p
      _ = algebraMap (RatFunc k) F (Polynomial.aeval RatFunc.X p.derivative) := by
            exact h_aeval p.derivative
      _ = algebraMap (RatFunc k) F
            (algebraMap (Polynomial k) (RatFunc k) p.derivative) := by
            rw [RatFunc.aeval_X_left_eq_algebraMap]
  have hB : ∀ q : B,
      functionFieldDerivation (k := k) (F := F) (algebraMap B F q) ∈
        P.valuationRing :=
    derivation_mem_valuationRing_of_finite_generators (k := k) (F := F) P
      (functionFieldDerivation (k := k) (F := F)) hpoly hBval b hspan hDb
  have hBC : ∀ q : B,
      functionFieldDerivation (k := k) (F := F) (algebraMap B F q) ∈
        C.valuationSubringAtPrime F := by
    intro q
    rw [hC]
    exact hB q
  have hlocalC : ∀ z : C.valuationSubringAtPrime F,
      functionFieldDerivation (k := k) (F := F) (z : F) ∈
        C.valuationSubringAtPrime F :=
    derivation_mem_heightOneLocalization (k := k) (F := F) C
      (functionFieldDerivation (k := k) (F := F)) hBC
  have hlocal : ∀ z : P.valuationRing,
      functionFieldDerivation (k := k) (F := F) (z : F) ∈ P.valuationRing := by
    intro z
    let zC : C.valuationSubringAtPrime F := ⟨(z : F), by
      change (z : F) ∈ C.valuationSubringAtPrime F
      rw [hC]
      exact z.property⟩
    have hzC := hlocalC zC
    change functionFieldDerivation (k := k) (F := F) (zC : F) ∈
      C.valuationSubringAtPrime F at hzC
    have hzP : functionFieldDerivation (k := k) (F := F) (zC : F) ∈
        P.valuationRing := by
      rw [← hC]
      exact hzC
    simpa only [zC] using hzP
  have hregular : ∀ x : F, x ∈ localDerivativeLattice (k := k) (F := F) P →
      P.RegularAt x := by
    intro x hx
    apply (GlobalPlace.regularAt_iff_mem_valuationRing P _).mpr
    rw [localDerivativeLattice] at hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨z, rfl⟩
      exact hlocal z
    · exact P.valuationRing.zero_mem
    · intro x y _ _ hx hy
      exact P.valuationRing.add_mem _ _ hx hy
    · intro r x _ hx
      change (r : F) * x ∈ P.valuationRing
      exact P.valuationRing.mul_mem _ _ r.property hx
  have hone : (1 : F) ∈ localDerivativeLattice (k := k) (F := F) P := by
    let x : P.valuationRing := ⟨algebraMap (RatFunc k) F RatFunc.X,
      (GlobalPlace.mem_valuationRing_iff P _).mpr hX⟩
    have hDX : functionFieldDerivation (k := k) (F := F) (x : F) = 1 := by
      change functionFieldDerivation (k := k) (F := F)
        (algebraMap (RatFunc k) F RatFunc.X) = 1
      exact functionFieldDerivation_apply_X (k := k) (F := F)
    rw [← hDX]
    exact Submodule.subset_span ⟨x, rfl⟩
  exact localDerivativeLatticeGeneratorOrder_eq_zero_of_one_mem (k := k) (F := F) P
    hone hregular
theorem exists_localDerivativeLatticeGeneratorOrderExceptionalFinset :
    ∃ E : Finset (GlobalPlace k F),
      ∀ P : GlobalPlace k F, P ∉ E →
        localDerivativeLatticeGeneratorOrder (k := k) (F := F) P = 0 := by
  classical
  obtain ⟨E_direct, h_direct⟩ :=
    exists_directChartGeneratorOrderExceptionalFinset (k := k) (F := F)
  let oldRationalAlgebra : Algebra (RatFunc k) F := inferInstance
  let oldFunctionField : _root_.FunctionField k F := inferInstance
  let oldSeparable : Algebra.IsSeparable (RatFunc k) F := inferInstance
  let oldConstantAlgebra : Algebra k F := inferInstance
  letI : Algebra (Polynomial k) F :=
    (oldRationalAlgebra.algebraMap.comp
      (algebraMap (Polynomial k) (RatFunc k))).toAlgebra
  let oldPolynomialAlgebra : Algebra (Polynomial k) F := inferInstance
  letI : IsScalarTower (Polynomial k) (RatFunc k) F :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let oldScalarTower : IsScalarTower (Polynomial k) (RatFunc k) F := inferInstance
  letI : Fintype (InverseAffinePlace.infinityFibre
      (oldRationalAlgebra := oldRationalAlgebra) k F) :=
    InverseAffinePlace.infinityFibreFintype
      (oldRationalAlgebra := oldRationalAlgebra) k F
  let E_infty : Finset (GlobalPlace k F) :=
    (Finset.univ : Finset (InverseAffinePlace.infinityFibre
      (oldRationalAlgebra := oldRationalAlgebra) k F)).image fun D =>
      InverseAffinePlace.infinityFibreGlobalPlace
        (π := oldPolynomialAlgebra) (ρ := oldRationalAlgebra)
        (τ := oldScalarTower) (φ := oldFunctionField) (σ := oldSeparable)
        (κ := oldConstantAlgebra) D
  refine ⟨E_direct ∪ E_infty, ?_⟩
  intro P hP
  rcases Valuation.val_le_one_or_val_inv_lt_one P.valuation
    (algebraMap (RatFunc k) F RatFunc.X) with hX | hY
  · exact h_direct P hX fun hPdirect =>
      hP (Finset.mem_union_left E_infty hPdirect)
  · obtain ⟨D, hPD⟩ :=
      GlobalPlace.exists_infinityFibreGlobalPlace_of_inverseCoordinate_lt_one
        (π := oldPolynomialAlgebra) (ρ := oldRationalAlgebra)
        (τ := oldScalarTower) (φ := oldFunctionField) (σ := oldSeparable)
        (κ := oldConstantAlgebra) P hY
    apply False.elim
    apply hP
    rw [hPD]
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨D, Finset.mem_univ _, rfl⟩
theorem differentialOrder_support_finite
    (omega : Differential k F) (homega : omega ≠ 0) :
    (Function.support fun P : GlobalPlace k F =>
      differentialOrder (k := k) (F := F) P omega homega).Finite := by
  classical
  letI : Algebra (Polynomial k) F :=
    ((algebraMap (RatFunc k) F).comp
      (algebraMap (Polynomial k) (RatFunc k))).toAlgebra
  letI : IsScalarTower (Polynomial k) (RatFunc k) F :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let c : Fˣ := Units.mk0
    (functionFieldDifferentialCoordinate (k := k) (F := F) omega)
    ((functionFieldDifferentialCoordinate_ne_zero_iff (k := k) (F := F) omega).mpr
      homega)
  obtain ⟨E, hE⟩ :=
    exists_localDerivativeLatticeGeneratorOrderExceptionalFinset (k := k) (F := F)
  let E' : Finset (GlobalPlace k F) :=
    E ∪ (GlobalPlace.principalDivisor (k := k) (F := F) c).support
  refine E'.finite_toSet.subset ?_
  intro P hP
  simp only [Function.mem_support, ne_eq] at hP
  by_contra hPnot
  apply hP
  have hPE : P ∉ E := by
    intro hPE
    apply hPnot
    change P ∈ E ∪ (GlobalPlace.principalDivisor (k := k) (F := F) c).support
    exact Finset.mem_union_left _ hPE
  have hPc : P ∉ (GlobalPlace.principalDivisor (k := k) (F := F) c).support := by
    intro hPc
    apply hPnot
    change P ∈ E ∪ (GlobalPlace.principalDivisor (k := k) (F := F) c).support
    exact Finset.mem_union_right _ hPc
  have hgenerator :
      localDerivativeLatticeGeneratorOrder (k := k) (F := F) P = 0 :=
    hE P hPE
  have hcoefficient :
      GlobalPlace.principalDivisor (k := k) (F := F) c P = 0 := by
    by_contra hcoefficient
    exact hPc (Finsupp.mem_support_iff.mpr hcoefficient)
  have hcoordinate :
      P.order (functionFieldDifferentialCoordinate (k := k) (F := F) omega) = 0 := by
    rw [GlobalPlace.principalDivisor_apply] at hcoefficient
    exact hcoefficient
  simp only [differentialOrder, hcoordinate, hgenerator, sub_zero]
noncomputable def differentialDivisor
    (omega : Differential k F) (homega : omega ≠ 0) :
    Divisor (GlobalPlace k F) :=
  Finsupp.ofSupportFinite
    (fun P => differentialOrder (k := k) (F := F) P omega homega)
    (differentialOrder_support_finite (k := k) (F := F) omega homega)
def IsCanonicalDivisor (K : Divisor (GlobalPlace k F)) : Prop :=
  ∃ (omega : Differential k F) (homega : omega ≠ 0),
    K = differentialDivisor (k := k) (F := F) omega homega
noncomputable def principalCutoffResidueCoefficient
    (P : GlobalPlace k F) (a : F)
    (ha : IsLocalDerivativeLatticePrincipalCutoff (k := k) (F := F) P a) :
    Differential.simplePoleDifferentialLattice P →ₗ[P.valuationRing] P.valuationRing := by
  classical
  let π : P.valuationRing := P.uniformizerInValuationRing
  let C : Differential k F →ₗ[F] F :=
    functionFieldDifferentialCoordinate (k := k) (F := F)
  refine
    { toFun := fun x => ?_
      map_add' := ?_
      map_smul' := ?_ }
  · have hx := x.property
    change π • (x : Differential k F) ∈ Differential.localDifferentialLattice P at hx
    have hx_coordinate :
        (π : F) * C (x : Differential k F) ∈
          localDerivativeLattice (k := k) (F := F) P := by
      have h := (mem_localDifferentialLattice_iff_coordinate_mem_localDerivativeLattice
        (k := k) (F := F) P (π • (x : Differential k F))).mp hx
      rw [LinearMap.map_smul_of_tower] at h
      exact h
    rw [ha.2.1] at hx_coordinate
    let r : P.valuationRing :=
      Classical.choose (Submodule.mem_span_singleton.mp hx_coordinate)
    have hr : r • a = (π : F) * C (x : Differential k F) :=
      Classical.choose_spec (Submodule.mem_span_singleton.mp hx_coordinate)
    change (r : F) * a = (π : F) * C (x : Differential k F) at hr
    refine ⟨(π : F) * C (x : Differential k F) * a⁻¹, ?_⟩
    have hvalue :
        (π : F) * C (x : Differential k F) * a⁻¹ = (r : F) := by
      calc
        (π : F) * C (x : Differential k F) * a⁻¹ =
            ((r : F) * a) * a⁻¹ := by rw [← hr]
        _ = (r : F) := by field_simp [ha.1] <;> ring
    rw [hvalue]
    exact r.property
  · intro x y
    apply Subtype.ext
    change (π : F) * C ((x : Differential k F) + (y : Differential k F)) * a⁻¹ =
      (π : F) * C (x : Differential k F) * a⁻¹ +
        (π : F) * C (y : Differential k F) * a⁻¹
    rw [map_add]
    ring
  · intro r x
    apply Subtype.ext
    change (π : F) * C ((r : F) • (x : Differential k F)) * a⁻¹ =
      (r : F) * ((π : F) * C (x : Differential k F) * a⁻¹)
    rw [map_smul]
    simp only [smul_eq_mul]
    ring
theorem principalCutoffResidueCoefficient_apply
    (P : GlobalPlace k F) (a : F)
    (ha : IsLocalDerivativeLatticePrincipalCutoff (k := k) (F := F) P a)
    (x : Differential.simplePoleDifferentialLattice P) :
    ((principalCutoffResidueCoefficient (k := k) (F := F) P a ha x :
      P.valuationRing) : F) =
      (P.uniformizerInValuationRing : F) *
        functionFieldDifferentialCoordinate (k := k) (F := F) (x : Differential k F) * a⁻¹ := rfl
noncomputable def principalCutoffResidueReduction
    (P : GlobalPlace k F) (a : F)
    (ha : IsLocalDerivativeLatticePrincipalCutoff (k := k) (F := F) P a) :
    Differential.simplePoleDifferentialLattice P →ₗ[P.valuationRing]
      GlobalPlace.residueField P :=
  (Algebra.linearMap P.valuationRing (GlobalPlace.residueField P)).comp
    (principalCutoffResidueCoefficient (k := k) (F := F) P a ha)
theorem regularDifferentialSubmoduleOfSimplePole_eq_principalCutoffResidueKernel
    (P : GlobalPlace k F) (a : F)
    (ha : IsLocalDerivativeLatticePrincipalCutoff (k := k) (F := F) P a) :
    Differential.regularDifferentialSubmoduleOfSimplePole P =
      LinearMap.ker (principalCutoffResidueReduction (k := k) (F := F) P a ha) := by
  classical
  let π : P.valuationRing := P.uniformizerInValuationRing
  let C : Differential k F →ₗ[F] F :=
    functionFieldDifferentialCoordinate (k := k) (F := F)
  have hπ_ne : (π : F) ≠ 0 := by
    change P.uniformizer ≠ 0
    apply P.valuation.ne_zero_iff.mp
    rw [P.valuation_uniformizer]
    exact WithZero.exp_ne_zero
  ext x
  constructor
  · intro hx
    change (x : Differential k F) ∈ Differential.localDifferentialLattice P at hx
    change P.residue
      (principalCutoffResidueCoefficient (k := k) (F := F) P a ha x) = 0
    have hx_coordinate :
        C (x : Differential k F) ∈ localDerivativeLattice (k := k) (F := F) P :=
      (mem_localDifferentialLattice_iff_coordinate_mem_localDerivativeLattice
        (k := k) (F := F) P (x : Differential k F)).mp hx
    rw [ha.2.1] at hx_coordinate
    rcases Submodule.mem_span_singleton.mp hx_coordinate with ⟨r, hr⟩
    change (r : F) * a = C (x : Differential k F) at hr
    have hcoefficient :
        principalCutoffResidueCoefficient (k := k) (F := F) P a ha x = π * r := by
      apply Subtype.ext
      rw [principalCutoffResidueCoefficient_apply]
      change (π : F) * C (x : Differential k F) * a⁻¹ =
        (π : F) * (r : F)
      calc
        (π : F) * C (x : Differential k F) * a⁻¹ =
            (π : F) * ((r : F) * a) * a⁻¹ := by rw [← hr]
        _ = (π : F) * (r : F) := by field_simp [ha.1] <;> ring
    rw [GlobalPlace.residue_eq_zero_iff, hcoefficient,
      P.maximalIdeal_eq_span_uniformizer, Ideal.mem_span_singleton]
    exact ⟨r, rfl⟩
  · intro hx
    change P.residue
      (principalCutoffResidueCoefficient (k := k) (F := F) P a ha x) = 0 at hx
    have hx_maximal :
        principalCutoffResidueCoefficient (k := k) (F := F) P a ha x ∈
          IsLocalRing.maximalIdeal P.valuationRing :=
      (GlobalPlace.residue_eq_zero_iff P _).mp hx
    rw [P.maximalIdeal_eq_span_uniformizer, Ideal.mem_span_singleton] at hx_maximal
    rcases hx_maximal with ⟨r, hr⟩
    have hcoefficient :
        (π : F) * C (x : Differential k F) * a⁻¹ =
          (π : F) * (r : F) := by
      have hcoefficient' := congrArg (fun z : P.valuationRing => (z : F)) hr
      change
        ((principalCutoffResidueCoefficient (k := k) (F := F) P a ha x :
          P.valuationRing) : F) =
          (π : F) * (r : F) at hcoefficient'
      rw [principalCutoffResidueCoefficient_apply] at hcoefficient'
      exact hcoefficient'
    have hcoordinate : C (x : Differential k F) = (r : F) * a := by
      apply mul_left_cancel₀ hπ_ne
      calc
        (π : F) * C (x : Differential k F) =
            ((π : F) * C (x : Differential k F) * a⁻¹) * a := by
              field_simp [ha.1] <;> ring
        _ = ((π : F) * (r : F)) * a := by rw [hcoefficient]
        _ = (π : F) * ((r : F) * a) := by ring
    change (x : Differential k F) ∈ Differential.localDifferentialLattice P
    apply (mem_localDifferentialLattice_iff_coordinate_mem_localDerivativeLattice
      (k := k) (F := F) P (x : Differential k F)).mpr
    rw [ha.2.1]
    exact Submodule.mem_span_singleton.mpr ⟨r, hcoordinate.symm⟩
noncomputable def localResidueLineEquivResidueField_ofPrincipalCutoff
    (P : GlobalPlace k F) (a : F)
    (ha : IsLocalDerivativeLatticePrincipalCutoff (k := k) (F := F) P a) :
    Differential.localResidueLine P ≃ₗ[P.valuationRing]
      GlobalPlace.residueField P := by
  classical
  let π : P.valuationRing := P.uniformizerInValuationRing
  let C : Differential k F →ₗ[F] F :=
    functionFieldDifferentialCoordinate (k := k) (F := F)
  let reduction := principalCutoffResidueReduction (k := k) (F := F) P a ha
  have hkernel : Differential.regularDifferentialSubmoduleOfSimplePole P =
      LinearMap.ker reduction :=
    regularDifferentialSubmoduleOfSimplePole_eq_principalCutoffResidueKernel
      (k := k) (F := F) P a ha
  have hπ_ne : (π : F) ≠ 0 := by
    change P.uniformizer ≠ 0
    apply P.valuation.ne_zero_iff.mp
    rw [P.valuation_uniformizer]
    exact WithZero.exp_ne_zero
  refine LinearEquiv.ofBijective
    ((Differential.regularDifferentialSubmoduleOfSimplePole P).liftQ reduction
      (le_of_eq hkernel)) ⟨?_, ?_⟩
  · exact LinearMap.ker_eq_bot.mp
      (Submodule.ker_liftQ_eq_bot'
        (Differential.regularDifferentialSubmoduleOfSimplePole P) reduction hkernel)
  · intro y
    obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective y
    let omega : Differential k F :=
      functionFieldDifferentialGeneratorMap (k := k) (F := F)
        ((r : F) * a * (π : F)⁻¹)
    have homega_coordinate : C omega = (r : F) * a * (π : F)⁻¹ := by
      have h := LinearMap.congr_fun
        (functionFieldDifferentialCoordinate_comp_generatorMap (k := k) (F := F))
        ((r : F) * a * (π : F)⁻¹)
      simpa only [omega, LinearMap.comp_apply, LinearMap.id_apply] using h
    have homega_simple : omega ∈ Differential.simplePoleDifferentialLattice P := by
      change π • omega ∈ Differential.localDifferentialLattice P
      apply (mem_localDifferentialLattice_iff_coordinate_mem_localDerivativeLattice
        (k := k) (F := F) P (π • omega)).mpr
      rw [ha.2.1]
      refine Submodule.mem_span_singleton.mpr ⟨r, ?_⟩
      change (r : F) * a = C (π • omega)
      rw [C.map_smul_of_tower, homega_coordinate]
      change (r : F) * a = (π : F) * ((r : F) * a * (π : F)⁻¹)
      field_simp [hπ_ne] <;> ring
    let x : Differential.simplePoleDifferentialLattice P := ⟨omega, homega_simple⟩
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    change P.residue
      (principalCutoffResidueCoefficient (k := k) (F := F) P a ha x) = y
    have hcoefficient :
        principalCutoffResidueCoefficient (k := k) (F := F) P a ha x = r := by
      apply Subtype.ext
      rw [principalCutoffResidueCoefficient_apply]
      change (π : F) * C omega * a⁻¹ = (r : F)
      rw [homega_coordinate]
      field_simp [hπ_ne, ha.1] <;> ring
    rw [hcoefficient]
    exact hr
end FunctionFieldDifferential
end QEC.Coding.AlgebraicGeometry


