-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:51:01.521038+00:00
-- url     : https://prove2.me/theorems/efde522a-d012-4f7d-a1f7-351c98630697
-- title:
--   Unramified Quadratic Norms Trace Uniformizer Facts
-- statement:
--   Definitions and structural lemmas for Unramified Quadratic Norms Trace Uniformizer Facts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedQuadraticNormsTraceUniformizerFacts.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UnitLemma.UnramNorm
open IsLocalRing Polynomial
variable (K : UQ)
open IsLocalRing Polynomial in
variable (K : _root_.GlobalTheory.UnitLemma.UQ) in
theorem _root_.GlobalTheory.UnitLemma.UnramNorm.alg_inj :
    Function.Injective (algebraMap K.O K.E) :=
  IsFractionRing.injective K.O K.E
def cOf (x : K.O) : K.O := Classical.choose (K.c_int x)
open IsLocalRing Polynomial in
variable (K : _root_.GlobalTheory.UnitLemma.UQ) in
theorem _root_.GlobalTheory.UnitLemma.UnramNorm.cOf_spec (x : K.O) :
    algebraMap K.O K.E (_root_.GlobalTheory.UnitLemma.UnramNorm.cOf K x) = K.c (algebraMap K.O K.E x) :=
  (Classical.choose_spec (K.c_int x)).symm
def cO : K.O ≃+* K.O where
  toFun := cOf K
  invFun := cOf K
  left_inv x := alg_inj K (by rw [cOf_spec, cOf_spec, K.c_c])
  right_inv x := alg_inj K (by rw [cOf_spec, cOf_spec, K.c_c])
  map_mul' x y := alg_inj K (by rw [cOf_spec, map_mul, map_mul, map_mul, cOf_spec, cOf_spec])
  map_add' x y := alg_inj K (by rw [cOf_spec, map_add, map_add, map_add, cOf_spec, cOf_spec])
end GlobalTheory.UnitLemma.UnramNorm


