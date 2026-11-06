-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialResidue
-- name    : QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialResidue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:37:25.782935+00:00
-- url     : https://prove2.me/theorems/b548b473-5de5-4b2c-9963-1ad7892681a9
-- title:
--   Adele Differential Residue
-- statement:
--   Definitions and structural lemmas for Adele Differential Residue, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleDifferentialResidue.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_FunctionFieldGlobalResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleWeilDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_localDifferentialLattice_le_simplePoleDifferentialLattice
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_mem_localDifferentialLattice_iff_differentialOrder_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_smul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleTraceResidue_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_smul_mem_localDifferentialLattice_iff_order_add_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_smul_mem_simplePoleDifferentialLattice_iff_order_add_neg_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorResidueTransport_directFactorResidueEquiv_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSmithTraceResidue_directBaseResidueRationalAdicEquiv_quotientResidueEquiv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_mem_support_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleSmulIntoDifferentialSpace_coe
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicIdealResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseFibreDirectFactor_infinityFibreEquivDirectFactors_apply_asIdeal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywisePolynomialDerivative_apply
attribute [local simp] Ideal.Factors.quotientResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicPolynomialDifferential
attribute [local simp] QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport.directFactorResidueEquiv_algebraMap
attribute [local simp] QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv_quotientResidueEquiv
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSmulIntoDifferentialSpace_coe
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicIdealResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor.infinityFibreEquivDirectFactors_apply_asIdeal
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_add
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_one
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywisePolynomialDerivative_apply


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open Filter
open scoped BigOperators Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
noncomputable local instance globalAdeleDifferentialResidueAlgebra :
    Algebra k F :=
  @AffinePlace.constantAlgebra k F _ _ π
local instance globalAdeleDifferentialResidueScalarTower :
    IsScalarTower k (RatFunc k) F :=
  directConstantScalarTower (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
namespace GlobalPlace
variable [IsFullConstantField k F]
def globalAdeleSimplePoleSubmodule (omega : Differential k F) :
    Submodule k (GlobalAdele (k := k) (F := F)) where
  carrier := {a | ∀ P : GlobalPlace k F,
    a.val P • omega ∈ Differential.simplePoleDifferentialLattice P}
  zero_mem' := by
    intro P
    change (0 : F) • omega ∈ Differential.simplePoleDifferentialLattice P
    rw [zero_smul]
    exact (Differential.simplePoleDifferentialLattice P).zero_mem
  add_mem' {a b} ha hb := by
    intro P
    change (a.val P + b.val P) • omega ∈
      Differential.simplePoleDifferentialLattice P
    rw [add_smul]
    exact (Differential.simplePoleDifferentialLattice P).add_mem (ha P) (hb P)
  smul_mem' c a ha := by
    intro P
    let cP : P.valuationRing := constantsToValuationRing P c
    have h := (Differential.simplePoleDifferentialLattice P).smul_mem cP (ha P)
    have h' : (algebraMap k F c * a.val P) • omega ∈
        Differential.simplePoleDifferentialLattice P := by
      rw [mul_smul]
      exact h
    change (c • a.val P) • omega ∈ Differential.simplePoleDifferentialLattice P
    simpa only [Algebra.smul_def] using h'
theorem adeleDifferentialResidue_globalAdeleExceptionalFinite
    (a : GlobalAdele (k := k) (F := F)) :
    {P : GlobalPlace k F | ¬P.valuation (a.val P) ≤ 1}.Finite :=
  (Filter.eventually_cofinite.mp a.property).subset (by
    intro P hP
    change a.val P ∉ P.valuationRing
    rw [mem_valuationRing_iff]
    exact hP)
noncomputable def globalAdeleSimplePoleResidueCoefficient
    (omega : Differential k F) (homega : omega ≠ 0)
    (a : globalAdeleSimplePoleSubmodule (k := k) (F := F) omega)
    (P : GlobalPlace k F) : k :=
  Differential.simplePoleTraceResidue (k := k) (F := F) P
    (((a : GlobalAdele (k := k) (F := F)).val P) • omega) (a.property P)
theorem globalAdeleSimplePoleResidueCoefficient_support_finite
    (omega : Differential k F) (homega : omega ≠ 0)
    (a : globalAdeleSimplePoleSubmodule (k := k) (F := F) omega) :
    (Function.support fun P : GlobalPlace k F =>
      globalAdeleSimplePoleResidueCoefficient
        (k := k) (F := F) omega homega a P).Finite := by
  let K := FunctionFieldDifferential.differentialDivisor
    (k := k) (F := F) omega homega
  refine ((adeleDifferentialResidue_globalAdeleExceptionalFinite
    (k := k) (F := F) (a : GlobalAdele (k := k) (F := F))).union
      K.support.finite_toSet).subset ?_
  intro P hcoefficient
  by_contra houtside
  have haIntegral :
      P.valuation ((a : GlobalAdele (k := k) (F := F)).val P) ≤ 1 := by
    by_contra hnot
    exact houtside (Set.mem_union_left _ hnot)
  have hKnot : P ∉ K.support := by
    intro hP
    exact houtside (Set.mem_union_right _ hP)
  have hKzero : K P = 0 := by
    by_contra hne
    exact hKnot (Finsupp.mem_support_iff.mpr hne)
  have homegaRegular :
      omega ∈ Differential.localDifferentialLattice P := by
    apply (Differential.mem_localDifferentialLattice_iff_differentialOrder_nonnegative
      (k := k) (F := F) P omega homega).mpr
    have horder : FunctionFieldDifferential.differentialOrder
        (k := k) (F := F) P omega homega = 0 := by
      simpa only [K,
        FunctionFieldDifferential.differentialDivisor_apply] using hKzero
    rw [horder]
  let aP : P.valuationRing :=
    ⟨(a : GlobalAdele (k := k) (F := F)).val P,
      (mem_valuationRing_iff P _).mpr haIntegral⟩
  have hproductRegular :
      ((a : GlobalAdele (k := k) (F := F)).val P) • omega ∈
        Differential.localDifferentialLattice P := by
    have h := (Differential.localDifferentialLattice P).smul_mem
      aP homegaRegular
    exact h
  apply hcoefficient
  exact Differential.simplePoleTraceResidue_eq_zero_of_mem_localDifferentialLattice
    (k := k) (F := F) P _ (a.property P) hproductRegular
noncomputable def globalAdeleSimplePoleResidue
    (omega : Differential k F) (homega : omega ≠ 0)
    (a : globalAdeleSimplePoleSubmodule (k := k) (F := F) omega) :
    GlobalPlace k F →₀ k :=
  Finsupp.ofSupportFinite
    (globalAdeleSimplePoleResidueCoefficient
      (k := k) (F := F) omega homega a)
    (globalAdeleSimplePoleResidueCoefficient_support_finite
      (k := k) (F := F) omega homega a)
theorem simplePoleTraceResidue_algebraMap_smul
    (P : GlobalPlace k F) (c : k) (eta : Differential k F)
    (heta : eta ∈ Differential.simplePoleDifferentialLattice P)
    (hscaled : (algebraMap k F c) • eta ∈
      Differential.simplePoleDifferentialLattice P) :
    Differential.simplePoleTraceResidue (k := k) (F := F) P
        ((algebraMap k F c) • eta) hscaled =
      c • Differential.simplePoleTraceResidue
        (k := k) (F := F) P eta heta := by
  letI : Algebra k P.residueField := residueAlgebra P
  letI : FiniteDimensional k P.residueField :=
    residueField_finiteDimensional P
  let cP : P.valuationRing := constantsToValuationRing P c
  have hsubtype :
      (⟨(algebraMap k F c) • eta, hscaled⟩ :
          Differential.simplePoleDifferentialLattice P) =
        cP • ⟨eta, heta⟩ := by
    apply Subtype.ext
    rfl
  change Algebra.trace k P.residueField
      (Differential.simplePoleResidue (k := k) (F := F) P
        ⟨(algebraMap k F c) • eta, hscaled⟩) = _
  rw [hsubtype,
    Differential.simplePoleResidue_smul (k := k) (F := F)]
  change Algebra.trace k P.residueField
      (algebraMap k P.residueField c *
        Differential.simplePoleResidue (k := k) (F := F) P ⟨eta, heta⟩) = _
  rw [← Algebra.smul_def, map_smul]
  rfl
theorem simplePoleTraceResidue_congr
    (P : GlobalPlace k F) {eta theta : Differential k F}
    (heta : eta ∈ Differential.simplePoleDifferentialLattice P)
    (htheta : theta ∈ Differential.simplePoleDifferentialLattice P)
    (h : eta = theta) :
    Differential.simplePoleTraceResidue (k := k) (F := F) P eta heta =
      Differential.simplePoleTraceResidue (k := k) (F := F) P theta htheta := by
  subst theta
  rfl
theorem globalAdeleSimplePoleResidue_add
    (omega : Differential k F) (homega : omega ≠ 0)
    (a b : globalAdeleSimplePoleSubmodule (k := k) (F := F) omega) :
    globalAdeleSimplePoleResidue (k := k) (F := F) omega homega (a + b) =
      globalAdeleSimplePoleResidue (k := k) (F := F) omega homega a +
        globalAdeleSimplePoleResidue (k := k) (F := F) omega homega b := by
  ext P
  change Differential.simplePoleTraceResidue (k := k) (F := F) P
      ((((a : GlobalAdele (k := k) (F := F)).val P +
        (b : GlobalAdele (k := k) (F := F)).val P) • omega)) _ =
    Differential.simplePoleTraceResidue (k := k) (F := F) P
        (((a : GlobalAdele (k := k) (F := F)).val P) • omega) (a.property P) +
      Differential.simplePoleTraceResidue (k := k) (F := F) P
        (((b : GlobalAdele (k := k) (F := F)).val P) • omega) (b.property P)
  calc
    _ = Differential.simplePoleTraceResidue (k := k) (F := F) P
        ((((a : GlobalAdele (k := k) (F := F)).val P) • omega) +
          (((b : GlobalAdele (k := k) (F := F)).val P) • omega))
        ((Differential.simplePoleDifferentialLattice P).add_mem
          (a.property P) (b.property P)) := by
      apply simplePoleTraceResidue_congr (k := k) (F := F) P
      exact add_smul _ _ _
    _ = _ := Differential.simplePoleTraceResidue_add
      (k := k) (F := F) P _ _ (a.property P) (b.property P)
theorem globalAdeleSimplePoleResidue_smul
    (omega : Differential k F) (homega : omega ≠ 0) (c : k)
    (a : globalAdeleSimplePoleSubmodule (k := k) (F := F) omega) :
    globalAdeleSimplePoleResidue (k := k) (F := F) omega homega (c • a) =
      c • globalAdeleSimplePoleResidue
        (k := k) (F := F) omega homega a := by
  ext P
  let eta : Differential k F :=
    ((a : GlobalAdele (k := k) (F := F)).val P) • omega
  have heta : eta ∈ Differential.simplePoleDifferentialLattice P := by
    simpa only [eta] using a.property P
  have hraw :
      ((algebraMap k F c *
        (a : GlobalAdele (k := k) (F := F)).val P) • omega) ∈
        Differential.simplePoleDifferentialLattice P := by
    have hmem := (c • a).property P
    change (c • (a : GlobalAdele (k := k) (F := F)).val P) • omega ∈
      Differential.simplePoleDifferentialLattice P at hmem
    simpa only [Algebra.smul_def] using hmem
  have hscaled :
      (algebraMap k F c) • eta ∈
        Differential.simplePoleDifferentialLattice P := by
    change (algebraMap k F c) •
      (((a : GlobalAdele (k := k) (F := F)).val P) • omega) ∈
        Differential.simplePoleDifferentialLattice P
    rw [← mul_smul]
    exact hraw
  have heq :
      (algebraMap k F c *
        (a : GlobalAdele (k := k) (F := F)).val P) • omega =
        (algebraMap k F c) • eta := by
    change (algebraMap k F c *
      (a : GlobalAdele (k := k) (F := F)).val P) • omega =
        (algebraMap k F c) •
          ((a : GlobalAdele (k := k) (F := F)).val P) • omega
    exact mul_smul _ _ _
  change Differential.simplePoleTraceResidue (k := k) (F := F) P
      ((algebraMap k F c *
        (a : GlobalAdele (k := k) (F := F)).val P) • omega) hraw =
    c • Differential.simplePoleTraceResidue (k := k) (F := F) P
      eta heta
  calc
    _ = Differential.simplePoleTraceResidue (k := k) (F := F) P
        ((algebraMap k F c) • eta) hscaled :=
      simplePoleTraceResidue_congr (k := k) (F := F) P hraw hscaled heq
    _ = _ := simplePoleTraceResidue_algebraMap_smul
      (k := k) (F := F) P c eta heta hscaled
noncomputable def globalAdeleSimplePoleResidueSum
    (omega : Differential k F) (homega : omega ≠ 0) :
    globalAdeleSimplePoleSubmodule (k := k) (F := F) omega →ₗ[k] k where
  toFun a := (globalAdeleSimplePoleResidue
    (k := k) (F := F) omega homega a).sum (fun _ residue => residue)
  map_add' a b := by
    rw [globalAdeleSimplePoleResidue_add]
    exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)
  map_smul' c a := by
    rw [globalAdeleSimplePoleResidue_smul,
      Finsupp.sum_smul_index (fun _ => rfl),
      ← Finsupp.mul_sum]
    rfl
theorem globalAdeleFilter_product_mem_localDifferentialLattice
    (omega : Differential k F) (homega : omega ≠ 0)
    (a : globalAdeleFilter (k := k) (F := F)
      (FunctionFieldDifferential.differentialDivisor
        (k := k) (F := F) omega homega))
    (P : GlobalPlace k F) :
    ((a : GlobalAdele (k := k) (F := F)).val P) • omega ∈
      Differential.localDifferentialLattice P := by
  by_cases haP : (a : GlobalAdele (k := k) (F := F)).val P = 0
  · rw [haP, zero_smul]
    exact (Differential.localDifferentialLattice P).zero_mem
  · apply (Differential.smul_mem_localDifferentialLattice_iff_order_add_nonnegative
      (k := k) (F := F) P _ haP omega homega).mpr
    have hlog : WithZero.log
        (P.valuation ((a : GlobalAdele (k := k) (F := F)).val P)) ≤
      FunctionFieldDifferential.differentialDivisor
        (k := k) (F := F) omega homega P :=
      (WithZero.log_le_iff_le_exp ((P.valuation).ne_zero_iff.mpr haP)).mpr
        (a.property P)
    rw [FunctionFieldDifferential.differentialDivisor_apply] at hlog
    change 0 ≤ -WithZero.log
      (P.valuation ((a : GlobalAdele (k := k) (F := F)).val P)) +
        FunctionFieldDifferential.differentialOrder
          (k := k) (F := F) P omega homega
    omega
theorem globalAdeleFilter_le_globalAdeleSimplePoleSubmodule
    (omega : Differential k F) (homega : omega ≠ 0) :
    globalAdeleFilter (k := k) (F := F)
        (FunctionFieldDifferential.differentialDivisor
          (k := k) (F := F) omega homega) ≤
      globalAdeleSimplePoleSubmodule (k := k) (F := F) omega := by
  intro a ha P
  exact Differential.localDifferentialLattice_le_simplePoleDifferentialLattice
    P (globalAdeleFilter_product_mem_localDifferentialLattice
      (k := k) (F := F) omega homega ⟨a, ha⟩ P)
theorem globalAdeleFilter_add_placeDivisor_le_globalAdeleSimplePoleSubmodule
    (omega : Differential k F) (homega : omega ≠ 0)
    (P : GlobalPlace k F) :
    globalAdeleFilter (k := k) (F := F)
        (FunctionFieldDifferential.differentialDivisor
          (k := k) (F := F) omega homega + placeDivisor P) ≤
      globalAdeleSimplePoleSubmodule (k := k) (F := F) omega := by
  intro a ha Q
  by_cases haQ : a.val Q = 0
  · rw [haQ, zero_smul]
    exact (Differential.simplePoleDifferentialLattice Q).zero_mem
  · apply (Differential.smul_mem_simplePoleDifferentialLattice_iff_order_add_neg_one
      (k := k) (F := F) Q _ haQ omega homega).mpr
    have hlog : WithZero.log (Q.valuation (a.val Q)) ≤
        (FunctionFieldDifferential.differentialDivisor
          (k := k) (F := F) omega homega + placeDivisor P) Q :=
      (WithZero.log_le_iff_le_exp ((Q.valuation).ne_zero_iff.mpr haQ)).mpr
        (ha Q)
    rw [Finsupp.add_apply,
      FunctionFieldDifferential.differentialDivisor_apply] at hlog
    change -1 ≤ -WithZero.log (Q.valuation (a.val Q)) +
      FunctionFieldDifferential.differentialOrder
        (k := k) (F := F) Q omega homega
    by_cases hQP : Q = P
    · subst Q
      rw [placeDivisor_apply] at hlog
      omega
    · rw [placeDivisor_apply_of_ne P Q (Ne.symm hQP)] at hlog
      omega
end GlobalPlace
end
end QEC.Coding.AlgebraicGeometry


