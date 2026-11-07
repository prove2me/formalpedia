-- Prove2me | Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
-- name    : QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:54:59.508056+00:00
-- url     : https://prove2.me/theorems/a5e072f2-4b31-419a-8292-e23c5a02c1a0
-- title:
--   Area
-- statement:
--   Definitions and structural lemmas for Area, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Area.lean

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeBridge
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeVolume
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_LevelSets
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply


set_option autoImplicit false
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise
noncomputable def north : Sphere :=
  ⟨EuclideanSpace.basisFun (Fin 3) ℝ 0, by
    simpa only [mem_sphere, dist_zero_right] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one 0⟩
def opposite (u : Sphere) : Sphere := ⟨-(u : Space), by simpa using u.property⟩
end QEC.Coding.ProbabilisticConstruction.SphericalCap


