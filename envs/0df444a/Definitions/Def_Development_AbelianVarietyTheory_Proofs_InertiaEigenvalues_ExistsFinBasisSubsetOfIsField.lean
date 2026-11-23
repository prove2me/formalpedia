-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFinBasisSubsetOfIsField
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFinBasisSubsetOfIsField
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:48.22981+00:00
-- url     : https://prove2.me/theorems/0fc2f5a4-f633-4e74-831d-cefb2bfa1e2c
-- title:
--   Exists Fin Basis Subset Of Is Field
-- statement:
--   Definitions and structural lemmas for Exists Fin Basis Subset Of Is Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsFinBasisSubsetOfIsField.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Theorems.Thm_GlobalTheory_DRFil_actVdR_tmul
import Theorems.Thm_GlobalTheory_DRFil_sm_mul
import Theorems.Thm_GlobalTheory_DRFil_sm_one_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.DRFil.actVdR_tmul


set_option autoImplicit false
noncomputable section
namespace GlobalTheory.DRFil
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module
section Period
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
def mulRHom (Qp : Type) [Field Qp] (F : Type) [CommRing F] [Algebra Qp F] (V : Type) [AddCommGroup V]
    [Module Qp V] : F →+* Module.End Qp (V ⊗[Qp] F) where
  toFun b := mulR Qp F Qp V b
  map_one' := LinearMap.ext fun x => by
    rw [← sm_one_tmul, ← Algebra.TensorProduct.one_def, sm_one]; rfl
  map_mul' a b := LinearMap.ext fun x => by
    rw [Module.End.mul_apply, ← sm_one_tmul, ← sm_one_tmul, ← sm_one_tmul, ← sm_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  map_zero' := LinearMap.ext fun x => by
    rw [← sm_one_tmul, TensorProduct.tmul_zero, map_zero]
  map_add' a b := LinearMap.ext fun x => by
    rw [LinearMap.add_apply, ← sm_one_tmul, ← sm_one_tmul, ← sm_one_tmul, TensorProduct.tmul_add,
      map_add, LinearMap.add_apply]
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
variable (Qp) in

def resRep (ρ : Representation LL G V) : Representation Qp G V where
  toFun g := (ρ g).restrictScalars Qp
  map_one' := LinearMap.ext fun x => by simp
  map_mul' a b := LinearMap.ext fun x => by simp
end Period
end GlobalTheory.DRFil


