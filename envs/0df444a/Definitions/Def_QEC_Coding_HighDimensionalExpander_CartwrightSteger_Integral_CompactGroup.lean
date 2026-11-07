-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_CompactGroup
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_CompactGroup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:39:48.938481+00:00
-- url     : https://prove2.me/theorems/59421656-c058-408b-83aa-ea000a696d62
-- title:
--   Compact Group
-- statement:
--   Definitions and structural lemmas for Compact Group, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/CompactGroup.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_ProjectiveUnits
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Rank_two_le_matrixRank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGenerator_pow_matrixRank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitGLHom_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitPGLHom_eq_constant_mul_zpow
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitPGLHom_monomial
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_skewLaurentIntSupport
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_range_globalIntegralUnitPGLHom
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentMonomialUnit_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToGlobalMatrix_single
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalIntegralUnitGLHom_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalIntegralUnitPGLHom_monomial
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_skewLaurentIntSupport
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentMonomialUnit_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToGlobalMatrix_single


set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
theorem globalCyclicGeneratorPGL_pow_matrixRank
    (P : BasePrime) (r : Rank) :
    globalCyclicGeneratorPGL P r ^ r.matrixRank = 1 := by
  change Matrix.ProjGenLinGroup.mk
      (cyclicGenerator P r ^ r.matrixRank) = 1
  let a : (SplittingFunctionField P r)ˣ :=
    Units.mk0 (onePlusY P r) (onePlusY_ne_zero P r)
  have hgl : cyclicGenerator P r ^ r.matrixRank =
      Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank) a := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val]
    rw [cyclicGenerator_val, cyclicGenerator_pow_matrixRank]
    change (onePlusY P r) •
        (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)) =
      Matrix.scalar (Fin r.matrixRank) (onePlusY P r)
    rw [Matrix.scalar_apply]
    exact Matrix.smul_one_eq_diagonal _
  rw [hgl]
  exact Matrix.ProjGenLinGroup.mk_scalar _
theorem exists_constant_mul_cyclic_pow_of_mem_globalIntegralCompact
    (P : BasePrime) (r : Rank)
    (g : Matrix.ProjGenLinGroup (Fin r.matrixRank)
      (SplittingFunctionField P r))
    (hg : g ∈ GlobalIntegralCompactCyclicSubgroup P r) :
    ∃ c : (ConstantExtension P r)ˣ, ∃ j : ℕ,
      j < r.matrixRank ∧
      g = globalConstantPGLHom P r c *
        globalCyclicGeneratorPGL P r ^ j := by
  have hgRange : g ∈ (globalIntegralUnitPGLHom P r).range := by
    rw [range_globalIntegralUnitPGLHom]
    exact hg
  obtain ⟨u, rfl⟩ := hgRange
  obtain ⟨c, n, hn⟩ :=
    globalIntegralUnitPGLHom_eq_constant_mul_zpow P r u
  have hdNat : 0 < r.matrixRank :=
    lt_of_lt_of_le (by norm_num) (Rank.two_le_matrixRank r)
  have hd : (0 : ℤ) < (r.matrixRank : ℤ) := by exact_mod_cast hdNat
  let m : ℤ := n % (r.matrixRank : ℤ)
  have hmNonneg : 0 ≤ m := Int.emod_nonneg n (ne_of_gt hd)
  have hmLt : m < (r.matrixRank : ℤ) := Int.emod_lt_of_pos n hd
  let j : ℕ := m.toNat
  have hj : j < r.matrixRank := by
    exact (Int.toNat_lt_of_ne_zero (ne_of_gt hdNat)).2 hmLt
  refine ⟨c, j, hj, ?_⟩
  rw [hn]
  have hreduce : globalCyclicGeneratorPGL P r ^ n =
      globalCyclicGeneratorPGL P r ^ m := by
    exact zpow_eq_zpow_emod' n
      (globalCyclicGeneratorPGL_pow_matrixRank P r)
  rw [hreduce]
  congr 1
  rw [← zpow_natCast]
  congr 1
  exact (Int.toNat_of_nonneg hmNonneg).symm
noncomputable def globalIntegralCompactFiniteNormalForm
    (P : BasePrime) (r : Rank) :
    (ConstantExtension P r)ˣ × Fin r.matrixRank →
      GlobalIntegralCompactCyclicSubgroup P r :=
  fun x => ⟨globalConstantPGLHom P r x.1 *
      globalCyclicGeneratorPGL P r ^ (x.2 : ℕ), by
    exact (GlobalIntegralCompactCyclicSubgroup P r).mul_mem
      (Subgroup.subset_closure
        (Set.mem_union_left _ (Set.mem_range_self x.1)))
      ((GlobalIntegralCompactCyclicSubgroup P r).pow_mem
        (Subgroup.subset_closure
          (Set.mem_union_right _ (Set.mem_singleton _))) x.2)⟩
theorem globalIntegralCompactFiniteNormalForm_surjective
    (P : BasePrime) (r : Rank) :
    Function.Surjective (globalIntegralCompactFiniteNormalForm P r) := by
  rintro ⟨g, hg⟩
  obtain ⟨c, j, hj, hform⟩ :=
    exists_constant_mul_cyclic_pow_of_mem_globalIntegralCompact P r g hg
  refine ⟨(c, ⟨j, hj⟩), ?_⟩
  apply Subtype.ext
  exact hform.symm
noncomputable instance globalIntegralCompactCyclicSubgroup_finite
    (P : BasePrime) (r : Rank) :
    Finite (GlobalIntegralCompactCyclicSubgroup P r) :=
  Finite.of_surjective (globalIntegralCompactFiniteNormalForm P r)
    (globalIntegralCompactFiniteNormalForm_surjective P r)
noncomputable instance globalIntegralCompactCyclicSubgroup_fintype
    (P : BasePrime) (r : Rank) :
    Fintype (GlobalIntegralCompactCyclicSubgroup P r) :=
  Fintype.ofFinite _
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


