-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MonicFactorizationConvolutionFiniteCommAssocAdd
-- name    : Development_AbelianVarietyTheory_Proofs_CharacterTheory_MonicFactorizationConvolutionFiniteCommAssocAdd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:09:35.465962+00:00
-- url     : https://prove2.me/theorems/edede877-67f8-47e3-a509-2394a1ebdba6
-- title:
--   Monic Factorization Convolution Finite Comm Assoc Add
-- statement:
--   Definitions and structural lemmas for Monic Factorization Convolution Finite Comm Assoc Add, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/MonicFactorizationConvolutionFiniteCommAssocAdd.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
variable {F : Type} [Field F]
theorem finite_monic_factorisations (P : F[X]) :
    {x : F[X] × F[X] | x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P}.Finite := by
  by_cases hP : P = 0
  · convert Set.finite_empty
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2, h3⟩
    exact (h1.mul h2).ne_zero (h3.trans hP)
  · have hfin : {D : F[X] | D.Monic ∧ D ∣ P}.Finite := by
      letI : Fintype {D : F[X] | D.Monic ∧ D ∣ P} := Polynomial.fintypeSubtypeMonicDvd P hP
      exact Set.toFinite _
    refine (hfin.prod hfin).subset ?_
    rintro x ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h3 ▸ dvd_mul_right _ _⟩, ⟨h2, h3 ▸ dvd_mul_left _ _⟩⟩
end GlobalTheory.CuspGL


