-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_GenericIrreducibility_GenericUnitary_NormEqOneOfValuationEqOne
-- name    : Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_GenericIrreducibility_GenericUnitary_NormEqOneOfValuationEqOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:52.302612+00:00
-- url     : https://prove2.me/theorems/a8854f56-8131-460e-8a5c-880da3d3181e
-- title:
--   Norm Eq One Of Valuation Eq One
-- statement:
--   Definitions and structural lemmas for Norm Eq One Of Valuation Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/GenericIrreducibility/GenericUnitary/NormEqOneOfValuationEqOne.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Theorems.Thm_GlobalTheory_SmGL_nabs_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel
namespace PositivityTheory.RgUd.Exp.Rpow
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def ordHom (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    kˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (ord k x)
  map_one' := by simp [ord_eq_zero (k := k) (x := 1) (by simp)]
  map_mul' x y := by simp [ord_mul]
def nabsHom (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    kˣ →* ℝ where
  toFun := nabs k
  map_one' := nabs_eq_one k (by simp)
  map_mul' := nabs_mul' k
def normHom (χ : kˣ →* ℂˣ) : kˣ →* ℝ where
  toFun z := ‖(χ z : ℂ)‖
  map_one' := by simp
  map_mul' x y := by simp
end PositivityTheory.RgUd.Exp.Rpow


