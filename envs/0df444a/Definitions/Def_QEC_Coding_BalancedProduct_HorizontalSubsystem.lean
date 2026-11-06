-- Prove2me | Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
-- name    : QEC_Coding_BalancedProduct_HorizontalSubsystem
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:09:51.643071+00:00
-- url     : https://prove2.me/theorems/79601b31-97f1-47ae-8d5c-f59b7c97e0bb
-- title:
--   Horizontal Subsystem
-- statement:
--   Definitions and structural lemmas for Horizontal Subsystem, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/HorizontalSubsystem.lean

import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_CSS_Subsystem
import Mathlib.LinearAlgebra.Finsupp.LSum
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_finCyclicEquiv_apply_eq_generator_pow
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_finCyclicInvEquiv_apply_eq_invGenerator_pow
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_liftedProductData_A
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_liftedProductData_B_apply
import Theorems.Thm_QEC_Coding_ChainComplexData_length_sub_firstCoboundaryCheckCode_sub_middleBoundaryCode_eq_finrank_middleHomology
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LinearCode_dual_dimension_eq_length_sub_dimension
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.BalancedProduct.Cyclic.finCyclicEquiv_apply_eq_generator_pow
attribute [local simp] QEC.Coding.BalancedProduct.Cyclic.finCyclicInvEquiv_apply_eq_invGenerator_pow
attribute [local simp] QEC.Coding.BalancedProduct.Cyclic.liftedProductData_A
attribute [local simp] QEC.Coding.BalancedProduct.Cyclic.liftedProductData_B_apply
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_secondZeroExtension
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
namespace QEC.Coding.BalancedProduct.HorizontalSubsystem
open Cyclic
universe u v
noncomputable def augmentation
    {G : Type u} [Fintype G] :
    MonoidAlgebra (ZMod 2) G →ₗ[ZMod 2] ZMod 2 :=
  (Finsupp.lsum (ZMod 2) (fun _ : G => LinearMap.id)).comp
    (MonoidAlgebra.coeffLinearEquiv (ZMod 2)).toLinearMap
@[simp]
theorem augmentation_apply
    {G : Type u} [Fintype G] (a : MonoidAlgebra (ZMod 2) G) :
    augmentation a = ∑ g : G, a.coeff g := by
  calc
    augmentation a = a.coeff.sum (fun _ c => c) := by
      exact Finsupp.lsum_apply (ZMod 2)
        (fun _ : G => LinearMap.id) a.coeff
    _ = ∑ g : G, a.coeff g := by
      apply Finsupp.sum_fintype
      intro g
      rfl
@[simp]
theorem augmentation_single
    {G : Type u} [Fintype G] [DecidableEq G] (g : G) (c : ZMod 2) :
    augmentation (MonoidAlgebra.single g c) = c := by
  exact Finsupp.lsum_single (ZMod 2) (fun _ : G => LinearMap.id) g c
@[simp]
theorem augmentation_cyclicBoundaryElement
    {G : Type u} [Group G] [Fintype G] [DecidableEq G] (x : G) :
    augmentation (cyclicBoundaryElement x) = 0 := by
  rw [cyclicBoundaryElement, map_add, augmentation_single,
    augmentation_single]
  change (2 : ZMod 2) = 0
  exact ZMod.natCast_self 2
theorem sum_leftRegularMatrix_column
    {G : Type u} [Group G] [Fintype G]
    (a : MonoidAlgebra (ZMod 2) G) (j : G) :
    (∑ i : G, LiftedProduct.leftRegularMatrix a i j) = augmentation a := by
  change (∑ i : G, a.coeff (i * j⁻¹)) = augmentation a
  rw [augmentation_apply]
  exact Equiv.sum_comp (Equiv.mulRight j⁻¹) a.coeff
theorem sum_rightRegularMatrix_column
    {G : Type u} [Group G] [Fintype G]
    (a : MonoidAlgebra (ZMod 2) G) (j : G) :
    (∑ i : G, LiftedProduct.rightRegularMatrix a i j) = augmentation a := by
  change (∑ i : G, a.coeff (j⁻¹ * i)) = augmentation a
  rw [augmentation_apply]
  exact Equiv.sum_comp (Equiv.mulLeft j⁻¹) a.coeff
theorem sum_rightRegularMatrix_row
    {G : Type u} [Group G] [Fintype G]
    (a : MonoidAlgebra (ZMod 2) G) (i : G) :
    (∑ j : G, LiftedProduct.rightRegularMatrix a i j) = augmentation a := by
  change (∑ j : G, a.coeff (j⁻¹ * i)) = augmentation a
  rw [augmentation_apply]
  exact Equiv.sum_comp ((Equiv.inv G).trans (Equiv.mulRight i)) a.coeff
theorem sum_rightRegularMatrix_mul
    {G : Type u} [Group G] [Fintype G]
    (a : MonoidAlgebra (ZMod 2) G) (z : G → ZMod 2) :
    (∑ go : G, ∑ gi : G,
        LiftedProduct.rightRegularMatrix a go gi * z gi) =
      augmentation a * ∑ gi : G, z gi := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  simp_rw [sum_rightRegularMatrix_column]
  exact (Finset.mul_sum Finset.univ z (augmentation a)).symm
theorem sum_rightRegularMatrix_row_mul
    {G : Type u} [Group G] [Fintype G]
    (a : MonoidAlgebra (ZMod 2) G) (go : G) (c : ZMod 2) :
    (∑ gi : G, LiftedProduct.rightRegularMatrix a go gi * c) =
      augmentation a * c := by
  rw [← Finset.sum_mul, sum_rightRegularMatrix_row]
theorem sum_leftRegularMatrix_mul
    {G : Type u} [Group G] [Fintype G]
    (a : MonoidAlgebra (ZMod 2) G) (z : G → ZMod 2) :
    (∑ go : G, ∑ gi : G,
        LiftedProduct.leftRegularMatrix a go gi * z gi) =
      augmentation a * ∑ gi : G, z gi := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  simp_rw [sum_leftRegularMatrix_column]
  exact (Finset.mul_sum Finset.univ z (augmentation a)).symm
noncomputable def quotientBoundaryMatrix
    {G aRow aCol : Type} [Fintype G]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) :
    Matrix aRow aCol (ZMod 2) :=
  fun r c => augmentation (A r c)
noncomputable def quotientBoundary
    {G aRow aCol : Type} [Fintype G]
    [Fintype aRow] [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) :
    Word (ZMod 2) aCol →ₗ[ZMod 2] Word (ZMod 2) aRow :=
  Matrix.toLin' (quotientBoundaryMatrix A)
noncomputable def quotientTannerComplex
    {G aRow aCol : Type} [Fintype G]
    [Fintype aRow] [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) :
    ChainComplexData (ZMod 2)
      (Word (ZMod 2) aRow) (Word (ZMod 2) aCol)
      (Word (ZMod 2) Empty) where
  boundary1 := quotientBoundary A
  boundary2 := 0
  boundary_squared := by simp
@[simp]
theorem quotientTannerComplex_boundary1
    {G aRow aCol : Type} [Fintype G]
    [Fintype aRow] [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) :
    (quotientTannerComplex A).boundary1 = quotientBoundary A := rfl
@[simp]
theorem quotientTannerComplex_boundary2
    {G aRow aCol : Type} [Fintype G]
    [Fintype aRow] [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) :
    (quotientTannerComplex A).boundary2 = 0 := rfl
noncomputable def fibreAugmentation
    {I : Type v} {G : Type u} [Fintype G] :
    Word (ZMod 2) (I × Unit × G) →ₗ[ZMod 2] Word (ZMod 2) I where
  toFun z i := ∑ g : G, z (i, (), g)
  map_add' z w := by
    ext i
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c z := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rfl
@[simp]
theorem fibreAugmentation_apply
    {I : Type v} {G : Type u} [Fintype G]
    (z : Word (ZMod 2) (I × Unit × G)) (i : I) :
    fibreAugmentation z i = ∑ g : G, z (i, (), g) := rfl
def constantFibre
    {I : Type v} {G : Type u} :
    Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) (I × Unit × G) where
  toFun z p := z p.1
  map_add' z w := by ext p; rfl
  map_smul' c z := by ext p; rfl
@[simp]
theorem constantFibre_apply
    {I : Type v} {G : Type u} (z : Word (ZMod 2) I)
    (i : I) (u : Unit) (g : G) :
    constantFibre z (i, u, g) = z i := rfl
noncomputable def horizontalAugmentation
    {aRow aCol : Type u} {G : Type v} [Fintype G] :
    Word (ZMod 2) (LiftedProduct.QubitIndex aRow aCol Unit Unit G) →ₗ[ZMod 2]
      Word (ZMod 2) aCol where
  toFun z c := ∑ g : G, z (Sum.inl (c, (), g))
  map_add' z w := by
    ext c
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' coefficient z := by
    ext c
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rfl
@[simp]
theorem horizontalAugmentation_apply
    {aRow aCol : Type u} {G : Type v} [Fintype G]
    (z : Word (ZMod 2) (LiftedProduct.QubitIndex aRow aCol Unit Unit G))
    (c : aCol) :
    horizontalAugmentation z c =
      ∑ g : G, z (Sum.inl (c, (), g)) := rfl
def horizontalConstant
    {aRow aCol : Type u} {G : Type v} :
    Word (ZMod 2) aCol →ₗ[ZMod 2]
      Word (ZMod 2) (LiftedProduct.QubitIndex aRow aCol Unit Unit G) where
  toFun z q :=
    match q with
    | Sum.inl (c, _, _) => z c
    | Sum.inr _ => 0
  map_add' z w := by
    ext q
    cases q <;> rfl
  map_smul' coefficient z := by
    ext q
    cases q <;> rfl
@[simp]
theorem horizontalConstant_inl
    {aRow aCol : Type u} {G : Type v} (z : Word (ZMod 2) aCol)
    (c : aCol) (r : Unit) (g : G) :
    horizontalConstant (aRow := aRow) (G := G) z (Sum.inl (c, r, g)) = z c :=
  rfl
@[simp]
theorem horizontalConstant_inr
    {aRow aCol : Type u} {G : Type v} (z : Word (ZMod 2) aCol)
    (r : aRow) (c : Unit) (g : G) :
    horizontalConstant (aRow := aRow) (G := G) z (Sum.inr (r, c, g)) = 0 :=
  rfl
theorem quotientBoundary_comp_horizontalAugmentation
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G) :
    (quotientBoundary A).comp
        (horizontalAugmentation (aRow := aRow) (G := G)) =
      (fibreAugmentation (I := aRow) (G := G)).comp
        (LiftedProduct.boundary1 (Cyclic.liftedProductData A x)) := by
  apply LinearMap.ext
  intro z
  funext ar
  simp only [LinearMap.comp_apply, quotientBoundary, Matrix.toLin'_apply,
    Matrix.mulVec, dotProduct, quotientBoundaryMatrix,
    horizontalAugmentation, fibreAugmentation_apply,
    LiftedProduct.boundary1, Fintype.sum_sum_type,
    Fintype.sum_prod_type, LiftedProduct.boundary1Matrix_inl_apply,
    LiftedProduct.boundary1Matrix_inr_apply_zmod2,
    Cyclic.liftedProductData_A, Cyclic.liftedProductData_B_apply]
  simp only [if_true, Fintype.sum_unique]
  simp only [ite_mul, zero_mul]
  simp_rw [Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero]
  simp only [Fintype.sum_ite_eq]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  simp_rw [sum_rightRegularMatrix_mul]
  rw [sum_leftRegularMatrix_mul, augmentation_cyclicBoundaryElement,
    zero_mul, add_zero]
  rfl
theorem horizontalAugmentation_comp_boundary2
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G) :
    (horizontalAugmentation (aRow := aRow) (G := G)).comp
        (LiftedProduct.boundary2 (Cyclic.liftedProductData A x)) = 0 := by
  apply LinearMap.ext
  intro z
  funext ac
  simp only [LinearMap.comp_apply, LiftedProduct.boundary2,
    Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    horizontalAugmentation_apply, Fintype.sum_prod_type,
    LiftedProduct.boundary2Matrix_inl_apply,
    Cyclic.liftedProductData_B_apply, LinearMap.zero_apply, Pi.zero_apply]
  simp only [ite_mul, zero_mul, Fintype.sum_unique]
  simp_rw [Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero, Fintype.sum_ite_eq]
  rw [sum_leftRegularMatrix_mul, augmentation_cyclicBoundaryElement, zero_mul]
noncomputable def augmentationChainMap
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G) :
    ThreeTermChainMap
      (LiftedProduct.chainComplex (Cyclic.liftedProductData A x))
      (quotientTannerComplex A) where
  map0 := fibreAugmentation
  map1 := horizontalAugmentation
  map2 := 0
  commutes_boundary1 := quotientBoundary_comp_horizontalAugmentation A x
  commutes_boundary2 := by
    rw [quotientTannerComplex_boundary2, LinearMap.zero_comp,
      LiftedProduct.chainComplex_boundary2,
      horizontalAugmentation_comp_boundary2 A x]
theorem boundary1_comp_horizontalConstant
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G) :
    (LiftedProduct.boundary1 (Cyclic.liftedProductData A x)).comp
        (horizontalConstant (aRow := aRow) (G := G)) =
      (constantFibre (G := G)).comp (quotientBoundary A) := by
  apply LinearMap.ext
  intro z
  funext p
  rcases p with ⟨ar, u, go⟩
  cases u
  simp only [LinearMap.comp_apply, LiftedProduct.boundary1,
    Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Fintype.sum_prod_type,
    LiftedProduct.boundary1Matrix_inl_apply,
    LiftedProduct.boundary1Matrix_inr_apply_zmod2,
    Cyclic.liftedProductData_A, Cyclic.liftedProductData_B_apply,
    constantFibre_apply, quotientBoundary,
    quotientBoundaryMatrix]
  simp only [if_true, Fintype.sum_unique, horizontalConstant_inl,
    horizontalConstant_inr, mul_zero, Finset.sum_const_zero, add_zero]
  simp_rw [sum_rightRegularMatrix_row_mul]
noncomputable def constantChainMap
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G) :
    ThreeTermChainMap
      (quotientTannerComplex A)
      (LiftedProduct.chainComplex (Cyclic.liftedProductData A x)) where
  map0 := constantFibre
  map1 := horizontalConstant
  map2 := 0
  commutes_boundary1 := by
    rw [LiftedProduct.chainComplex_boundary1,
      quotientTannerComplex_boundary1]
    exact boundary1_comp_horizontalConstant A x
  commutes_boundary2 := by
    rw [LinearMap.comp_zero, quotientTannerComplex_boundary2,
      LinearMap.comp_zero]
theorem horizontalAugmentation_comp_horizontalConstant_of_odd
    {aRow aCol G : Type} [Fintype G]
    (hOdd : Odd (Fintype.card G)) :
    (horizontalAugmentation (aRow := aRow) (aCol := aCol) (G := G)).comp
        (horizontalConstant (aRow := aRow) (aCol := aCol) (G := G)) =
      (LinearMap.id : Word (ZMod 2) aCol →ₗ[ZMod 2]
        Word (ZMod 2) aCol) := by
  apply LinearMap.ext
  intro z
  funext c
  simp only [LinearMap.comp_apply, horizontalAugmentation_apply,
    horizontalConstant_inl, LinearMap.id_apply]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    hOdd.natCast_zmod_two, one_mul]
theorem finrank_middleCohomology_eq_middleHomology
    {i0 i1 i2 : Type u} [Fintype i0] [Fintype i1] [Fintype i2]
    (K : ChainComplexData (ZMod 2)
      (Word (ZMod 2) i0) (Word (ZMod 2) i1) (Word (ZMod 2) i2)) :
    Module.finrank (ZMod 2) K.middleCohomology =
      Module.finrank (ZMod 2) K.middleHomology := by
  have hQuotient :=
    K.middleCoboundaryInCocycles.finrank_quotient_add_finrank
  have hDenominator :
      Module.finrank (ZMod 2) K.middleCoboundaryInCocycles =
        Dimension K.firstCoboundaryCheckCode := by
    rw [Dimension_eq_finrank_carrier]
    exact K.middleCoboundaryInCocyclesEquiv.finrank_eq
  have hCocycle :
      Module.finrank (ZMod 2) K.middleCocycleCode.carrier =
        Length (ZMod 2) i1 - Dimension K.middleBoundaryCode := by
    calc
      Module.finrank (ZMod 2) K.middleCocycleCode.carrier =
          Dimension K.middleBoundaryCode.dual := by
        rw [Dimension_eq_finrank_carrier]
        rw [K.middleBoundaryCode_dual_carrier_eq_middleCocycleCode]
      _ = Length (ZMod 2) i1 - Dimension K.middleBoundaryCode :=
        K.middleBoundaryCode.dual_dimension_eq_length_sub_dimension
  have hHomology :=
    K.length_sub_firstCoboundaryCheckCode_sub_middleBoundaryCode_eq_finrank_middleHomology
  rw [hDenominator, hCocycle] at hQuotient
  have hCohomology := Nat.eq_sub_of_add_eq hQuotient
  calc
    Module.finrank (ZMod 2) K.middleCohomology =
        (Length (ZMod 2) i1 - Dimension K.middleBoundaryCode) -
          Dimension K.firstCoboundaryCheckCode := hCohomology
    _ = Length (ZMod 2) i1 -
        (Dimension K.middleBoundaryCode +
          Dimension K.firstCoboundaryCheckCode) := by
      rw [Nat.sub_sub]
    _ = Length (ZMod 2) i1 -
        (Dimension K.firstCoboundaryCheckCode +
          Dimension K.middleBoundaryCode) := by
      rw [Nat.add_comm]
    _ = (Length (ZMod 2) i1 -
          Dimension K.firstCoboundaryCheckCode) -
        Dimension K.middleBoundaryCode := by
      rw [Nat.sub_sub]
    _ = Module.finrank (ZMod 2) K.middleHomology := hHomology
noncomputable def horizontalHomologyProjection
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G) :
    (LiftedProduct.chainComplex
        (Cyclic.liftedProductData A x)).middleHomology →ₗ[ZMod 2]
      (quotientTannerComplex A).middleHomology :=
  (augmentationChainMap A x).inducedMiddleHomology
noncomputable def horizontalCohomologyProjection
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G) :
    (LiftedProduct.chainComplex
        (Cyclic.liftedProductData A x)).middleCohomology →ₗ[ZMod 2]
      (quotientTannerComplex A).middleCohomology :=
  (constantChainMap A x).inducedMiddleCohomology
theorem horizontalHomologyProjection_surjective
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    (hOdd : Odd (Fintype.card G)) :
    Function.Surjective (horizontalHomologyProjection A x) := by
  intro y
  let f := augmentationChainMap A x
  let s := constantChainMap A x
  refine ⟨s.inducedMiddleHomology y, ?_⟩
  have hComposition := ThreeTermChainMap.inducedMiddleHomology_comp f s
  change f.inducedMiddleHomology (s.inducedMiddleHomology y) = y
  rw [← LinearMap.comp_apply, ← hComposition]
  obtain ⟨representative, rfl⟩ :=
    (quotientTannerComplex A).middleBoundaryInCycles.mkQ_surjective y
  rw [ThreeTermChainMap.inducedMiddleHomology_mk]
  congr 1
  apply Subtype.ext
  exact LinearMap.congr_fun
    (horizontalAugmentation_comp_horizontalConstant_of_odd
      (aRow := aRow) hOdd) representative.1
theorem horizontalCohomologyProjection_surjective
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    (hOdd : Odd (Fintype.card G)) :
    Function.Surjective (horizontalCohomologyProjection A x) := by
  intro y
  let f := augmentationChainMap A x
  let s := constantChainMap A x
  refine ⟨f.inducedMiddleCohomology y, ?_⟩
  have hComposition := ThreeTermChainMap.inducedMiddleCohomology_comp f s
  change s.inducedMiddleCohomology (f.inducedMiddleCohomology y) = y
  rw [← LinearMap.comp_apply, ← hComposition]
  obtain ⟨representative, rfl⟩ :=
    (quotientTannerComplex A).middleCoboundaryInCocycles.mkQ_surjective y
  rw [ThreeTermChainMap.inducedMiddleCohomology_mk]
  congr 1
  apply Subtype.ext
  change wordLinearMapTranspose ((f.comp s).map1) representative.1 =
    representative.1
  rw [ThreeTermChainMap.comp_map1]
  have hMap1 : f.map1.comp s.map1 =
      (LinearMap.id : Word (ZMod 2) aCol →ₗ[ZMod 2]
        Word (ZMod 2) aCol) := by
    dsimp [f, s, augmentationChainMap, constantChainMap]
    exact horizontalAugmentation_comp_horizontalConstant_of_odd
      (aRow := aRow) hOdd
  rw [hMap1, wordLinearMapTranspose_id]
  rfl
noncomputable def horizontalSubsystem
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    (hOdd : Odd (Fintype.card G)) :
    SubsystemCSSData
      (LiftedProduct.C0Index aRow Unit G)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit G)
      (LiftedProduct.C2Index aCol Unit G)
      (quotientTannerComplex A).middleHomology
      (quotientTannerComplex A).middleCohomology where
  complex := LiftedProduct.chainComplex (Cyclic.liftedProductData A x)
  homologyProjection := horizontalHomologyProjection A x
  cohomologyProjection := horizontalCohomologyProjection A x
  homologyProjection_surjective :=
    horizontalHomologyProjection_surjective A x hOdd
  cohomologyProjection_surjective :=
    horizontalCohomologyProjection_surjective A x hOdd
  logical_finrank_eq :=
    (finrank_middleCohomology_eq_middleHomology
      (quotientTannerComplex A)).symm
end QEC.Coding.BalancedProduct.HorizontalSubsystem


