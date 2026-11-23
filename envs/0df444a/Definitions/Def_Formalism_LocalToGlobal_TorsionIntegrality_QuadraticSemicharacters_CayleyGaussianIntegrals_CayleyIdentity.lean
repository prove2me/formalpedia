-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyIdentity
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyIdentity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:12:45.344148+00:00
-- url     : https://prove2.me/theorems/f5bbea8b-261a-4e99-ad5b-7ea2c04cb81e
-- title:
--   Cayley Identity
-- statement:
--   Definitions and structural lemmas for Cayley Identity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/CayleyIdentity.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.H
section Diag
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
@[reducible] def coreOf (H : Sesq V) (hH : IsHerm H) (hP : IsPosDef H) : InnerProductSpace.Core ℂ V where
  inner x y := H y x
  conj_inner_symm x y := (hH x y).symm
  re_inner_nonneg x := by
    by_cases h : x = 0
    · simp [h]
    · exact (hP x h).le
  add_left x y z := by simp
  smul_left x y r := by simp
  definite x hx := by
    by_contra h
    have := hP x h
    rw [hx] at this
    simp at this
end Diag
end Formalism.L2.Th1.H


