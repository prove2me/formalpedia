-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCompactNormalForm
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCompactNormalForm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T13:28:47.365047+00:00
-- url     : https://prove2.me/theorems/d8ff167b-0dc7-4a44-bf97-f9286dfa4e1b
-- title:
--   Building Compact Normal Form
-- statement:
--   Definitions and structural lemmas for Building Compact Normal Form, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingCompactNormalForm.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingConstantKernel
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionSpecial_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCompactCyclicSemidirectHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingConstantMatrix_injective
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingConstantPGL_eq_of_quotientMk_eq
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingConstantPGL_mem_compactCyclicSubgroup
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCyclicGeneratorPGL_mem_compactCyclicSubgroup
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingGeneratorNeighborAtEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLatticeVertexMap_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerNormUnit_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_eq_zero_of_constantFrobenius_pow_eq_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_constant_mul_cyclic_pow_of_mem_compactCyclicSubgroup
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusPowerEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitGLHom_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitPGLHom_monomial
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCyclicGeneratorGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_skewLaurentIntSupport
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_quotientMk_eq_of_buildingConstantPGL_eq
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueBGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentMonomialUnit_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToGlobalMatrix_single
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_three
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_exists_scalar_mul_eq_of_projective_mk_eq
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourFundamentalHeckeAlgEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThreeFundamentalHeckeAlgEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting.residueTransvectionSpecial_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCompactCyclicSemidirectHom_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingGeneratorNeighborAtEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeVertexMap_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerNormUnit_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusPowerEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalIntegralUnitGLHom_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalIntegralUnitPGLHom_monomial
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCyclicGeneratorGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_skewLaurentIntSupport
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueBGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentMonomialUnit_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToGlobalMatrix_single
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_three
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_two
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankThree_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankThree_two
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourFundamentalHeckeAlgEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompoundGeneralLinear_inv_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThreeFundamentalHeckeAlgEquiv_apply


set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
theorem buildingCyclicGeneratorGL_pow_conj_constant
    (P : BasePrime) (r : Rank) (j : ℕ)
    (u : (ConstantExtension P r)ˣ) :
    buildingCyclicGeneratorGL P r ^ j * buildingConstantGL P r u *
        (buildingCyclicGeneratorGL P r ^ j)⁻¹ =
      buildingConstantGL P r ((constantFrobeniusUnitEquiv P r ^ j) u) := by
  induction j generalizing u with
  | zero => simp
  | succ j ih =>
      calc
        buildingCyclicGeneratorGL P r ^ (j + 1) *
              buildingConstantGL P r u *
              (buildingCyclicGeneratorGL P r ^ (j + 1))⁻¹ =
            buildingCyclicGeneratorGL P r ^ j *
              (buildingCyclicGeneratorGL P r *
                buildingConstantGL P r u *
                (buildingCyclicGeneratorGL P r)⁻¹) *
              (buildingCyclicGeneratorGL P r ^ j)⁻¹ := by
                rw [pow_succ]
                group
        _ = buildingCyclicGeneratorGL P r ^ j *
              buildingConstantGL P r (constantFrobeniusUnitEquiv P r u) *
              (buildingCyclicGeneratorGL P r ^ j)⁻¹ := by
                rw [buildingCyclicGeneratorGL_conj_constant]
        _ = buildingConstantGL P r
              ((constantFrobeniusUnitEquiv P r ^ j)
                (constantFrobeniusUnitEquiv P r u)) :=
              ih (constantFrobeniusUnitEquiv P r u)
        _ = buildingConstantGL P r
              ((constantFrobeniusUnitEquiv P r ^ (j + 1)) u) := by
                rw [pow_succ]
                rfl
theorem buildingNormalFormGL_conj_constant
    (P : BasePrime) (r : Rank)
    (u w : (ConstantExtension P r)ˣ) (j : ℕ) :
    (buildingConstantGL P r u * buildingCyclicGeneratorGL P r ^ j) *
        buildingConstantGL P r w *
        (buildingConstantGL P r u *
          buildingCyclicGeneratorGL P r ^ j)⁻¹ =
      buildingConstantGL P r
        ((constantFrobeniusUnitEquiv P r ^ j) w) := by
  rw [mul_inv_rev]
  calc
    (buildingConstantGL P r u * buildingCyclicGeneratorGL P r ^ j) *
          buildingConstantGL P r w *
          ((buildingCyclicGeneratorGL P r ^ j)⁻¹ *
            (buildingConstantGL P r u)⁻¹) =
        buildingConstantGL P r u *
          (buildingCyclicGeneratorGL P r ^ j *
            buildingConstantGL P r w *
            (buildingCyclicGeneratorGL P r ^ j)⁻¹) *
          (buildingConstantGL P r u)⁻¹ := by group
    _ = buildingConstantGL P r u *
          buildingConstantGL P r
            ((constantFrobeniusUnitEquiv P r ^ j) w) *
          (buildingConstantGL P r u)⁻¹ := by
            rw [buildingCyclicGeneratorGL_pow_conj_constant]
    _ = buildingConstantGL P r
          ((constantFrobeniusUnitEquiv P r ^ j) w) := by
      change buildingConstantGLHom P r u *
          buildingConstantGLHom P r
            ((constantFrobeniusUnitEquiv P r ^ j) w) *
          (buildingConstantGLHom P r u)⁻¹ = _
      rw [← map_inv, ← map_mul, ← map_mul]
      simp [mul_comm]
set_option maxHeartbeats 400000 in
theorem buildingNormalForm_exponent_eq
    (P : BasePrime) (r : Rank)
    (u v : (ConstantExtension P r)ˣ) (j k : ℕ)
    (hj : j < r.matrixRank) (hk : k < r.matrixRank)
    (h : buildingConstantPGLHom P r u *
          buildingCyclicGeneratorPGL P r ^ j =
        buildingConstantPGLHom P r v *
          buildingCyclicGeneratorPGL P r ^ k) :
    j = k := by
  change Matrix.ProjGenLinGroup.mk
      (buildingConstantGL P r u * buildingCyclicGeneratorGL P r ^ j) =
    Matrix.ProjGenLinGroup.mk
      (buildingConstantGL P r v * buildingCyclicGeneratorGL P r ^ k) at h
  obtain ⟨a, ha⟩ :=
    SphericalHecke.exists_scalar_mul_eq_of_projective_mk_eq h
  let A := buildingConstantGL P r u * buildingCyclicGeneratorGL P r ^ j
  let B := buildingConstantGL P r v * buildingCyclicGeneratorGL P r ^ k
  let S := Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank) a
  have hAB : A = S * B := ha
  have hScomm (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (BuildingLocalField P)) :
      (S : Matrix _ _ _) * M = M * (S : Matrix _ _ _) := by
    dsimp [S]
    exact Matrix.scalar_comm _ (fun b => Commute.all _ b) M
  have hScancel (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (BuildingLocalField P)) :
      (S : Matrix _ _ _) * M *
        ((S⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (BuildingLocalField P)) : Matrix _ _ _) = M := by
    rw [hScomm]
    simp only [mul_assoc]
    rw [← Units.val_mul]
    simp
  have haction (w : (ConstantExtension P r)ˣ) :
      (constantFrobeniusUnitEquiv P r ^ j) w =
        (constantFrobeniusUnitEquiv P r ^ k) w := by
    apply Units.ext
    apply buildingConstantMatrix_injective P r
    rw [← buildingConstantGL_coe, ← buildingConstantGL_coe]
    rw [← buildingNormalFormGL_conj_constant P r u w j,
      ← buildingNormalFormGL_conj_constant P r v w k]
    change (↑(A * buildingConstantGL P r w * A⁻¹) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P)) =
      (↑(B * buildingConstantGL P r w * B⁻¹) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P))
    rw [hAB]
    calc
      (((S * B : Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (BuildingLocalField P)) : Matrix _ _ _) *
          buildingConstantMatrix P r w *
          (((S * B)⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (BuildingLocalField P)) : Matrix _ _ _)) =
        (S : Matrix _ _ _) *
          ((B : Matrix _ _ _) * buildingConstantMatrix P r w *
            ((B⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (BuildingLocalField P)) : Matrix _ _ _)) *
          ((S⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (BuildingLocalField P)) : Matrix _ _ _) := by
              simp only [mul_inv_rev, Units.val_mul]
              group
      _ = _ := by
        let M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (BuildingLocalField P) :=
          (B : Matrix _ _ _) * buildingConstantMatrix P r w *
            ((B⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (BuildingLocalField P)) : Matrix _ _ _)
        calc
          _ = (S : Matrix _ _ _) * M *
              ((S⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
                (BuildingLocalField P)) : Matrix _ _ _) := by dsimp [M]
          _ = M := hScancel M
          _ = _ := by dsimp [M]
  have hfrob : constantFrobenius P r ^ j = constantFrobenius P r ^ k := by
    apply AlgEquiv.ext
    intro c
    by_cases hc0 : c = 0
    · simp [hc0]
    · let w : (ConstantExtension P r)ˣ := Units.mk0 c hc0
      have hw := congrArg Units.val (haction w)
      have hpow (n : ℕ) (x : (ConstantExtension P r)ˣ) :
          ((constantFrobeniusUnitEquiv P r ^ n) x : ConstantExtension P r) =
            (constantFrobenius P r ^ n) (x : ConstantExtension P r) := by
        induction n generalizing x with
        | zero => rfl
        | succ n ih =>
            change ((constantFrobeniusUnitEquiv P r ^ n)
                (constantFrobeniusUnitEquiv P r x) : ConstantExtension P r) =
              (constantFrobenius P r ^ n)
                (constantFrobenius P r (x : ConstantExtension P r))
            rw [ih]
            rfl
      exact (hpow j w).symm.trans (hw.trans (hpow k w))
  by_cases hkj : k ≤ j
  · have hpow : constantFrobenius P r ^ (j - k) = 1 := by
      apply mul_right_cancel (b := constantFrobenius P r ^ k)
      rw [← pow_add, Nat.sub_add_cancel hkj, hfrob, one_mul]
    have hzero := eq_zero_of_constantFrobenius_pow_eq_one P r (j - k)
      (lt_of_le_of_lt (Nat.sub_le j k) hj) hpow
    omega
  · have hjk : j ≤ k := Nat.le_of_not_ge hkj
    have hpow : constantFrobenius P r ^ (k - j) = 1 := by
      apply mul_right_cancel (b := constantFrobenius P r ^ j)
      rw [← pow_add, Nat.sub_add_cancel hjk, hfrob.symm, one_mul]
    have hzero := eq_zero_of_constantFrobenius_pow_eq_one P r (k - j)
      (lt_of_le_of_lt (Nat.sub_le k j) hk) hpow
    omega
theorem buildingNormalForm_source_eq
    (P : BasePrime) (r : Rank)
    (u v : (ConstantExtension P r)ˣ) (j k : ℕ)
    (hj : j < r.matrixRank) (hk : k < r.matrixRank)
    (h : buildingConstantPGLHom P r u *
          buildingCyclicGeneratorPGL P r ^ j =
        buildingConstantPGLHom P r v *
          buildingCyclicGeneratorPGL P r ^ k) :
    (QuotientGroup.mk u : ConstantProjectiveClass P r) =
        QuotientGroup.mk v ∧ j = k := by
  have hjk := buildingNormalForm_exponent_eq P r u v j k hj hk h
  subst k
  have hconstant : buildingConstantPGLHom P r u =
      buildingConstantPGLHom P r v := by
    apply mul_right_cancel (b := buildingCyclicGeneratorPGL P r ^ j)
    exact h
  exact ⟨quotientMk_eq_of_buildingConstantPGL_eq P r u v hconstant, rfl⟩
noncomputable def buildingCompactProjectiveNormalForm
    (P : BasePrime) (r : Rank) :
    ConstantProjectiveClass P r × Fin r.matrixRank →
      BuildingCompactCyclicSubgroup P r :=
  fun x => ⟨buildingConstantPGLHom P r
      (constantClassRepresentative P r x.1) *
        buildingCyclicGeneratorPGL P r ^ (x.2 : ℕ), by
    exact (BuildingCompactCyclicSubgroup P r).mul_mem
      (buildingConstantPGL_mem_compactCyclicSubgroup P r
        (constantClassRepresentative P r x.1))
      ((BuildingCompactCyclicSubgroup P r).pow_mem
        (buildingCyclicGeneratorPGL_mem_compactCyclicSubgroup P r) x.2)⟩
theorem buildingCompactProjectiveNormalForm_bijective
    (P : BasePrime) (r : Rank) :
    Function.Bijective (buildingCompactProjectiveNormalForm P r) := by
  constructor
  · rintro ⟨x, j⟩ ⟨y, k⟩ hxy
    have hval := congrArg Subtype.val hxy
    obtain ⟨hconst, hexp⟩ := buildingNormalForm_source_eq P r
      (constantClassRepresentative P r x)
      (constantClassRepresentative P r y) j k j.isLt k.isLt hval
    apply Prod.ext
    · simpa [constantClassRepresentative] using hconst
    · exact Fin.ext hexp
  · rintro ⟨g, hg⟩
    obtain ⟨c, j, hj, hform⟩ :=
      exists_constant_mul_cyclic_pow_of_mem_compactCyclicSubgroup P r g hg
    let x : ConstantProjectiveClass P r := QuotientGroup.mk c
    let jf : Fin r.matrixRank := ⟨j, hj⟩
    refine ⟨(x, jf), ?_⟩
    apply Subtype.ext
    change buildingConstantPGLHom P r (constantClassRepresentative P r x) *
        buildingCyclicGeneratorPGL P r ^ j = g
    rw [buildingConstantPGL_eq_of_quotientMk_eq P r
      (constantClassRepresentative P r x) c]
    · exact hform.symm
    · simp [x, constantClassRepresentative]
noncomputable def buildingCompactProjectiveNormalFormEquiv
    (P : BasePrime) (r : Rank) :
    ConstantProjectiveClass P r × Fin r.matrixRank ≃
      BuildingCompactCyclicSubgroup P r :=
  Equiv.ofBijective (buildingCompactProjectiveNormalForm P r)
    (buildingCompactProjectiveNormalForm_bijective P r)
noncomputable def globalIntegralCompactEquivBuildingCompact
    (P : BasePrime) (r : Rank) :
    GlobalIntegralCompactCyclicSubgroup P r ≃
      BuildingCompactCyclicSubgroup P r :=
  (globalIntegralProjectiveNormalFormEquiv P r).symm.trans
    (buildingCompactProjectiveNormalFormEquiv P r)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


