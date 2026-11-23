-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussSumNondegenerateFiniteHermitianModule
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussSumNondegenerateFiniteHermitianModule
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:02.326856+00:00
-- url     : https://prove2.me/theorems/41f2d87a-d2f0-4836-bc5f-82d273969591
-- title:
--   Gauss Sum Nondegenerate Finite Hermitian Module
-- statement:
--   Definitions and structural lemmas for Gauss Sum Nondegenerate Finite Hermitian Module, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussSumNondegenerateFiniteHermitianModule.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumEqZeroAddUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
namespace GlobalTheory.HermitianGauss
section Fin
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype M]
noncomputable def pts (B : Submodule R M) : Finset M := Finset.univ.filter (· ∈ B)
variable {σ : R →+* R} {β : M → M → ℂ}
def perp (hadd : ∀ x y z, β (x + y) z = β x z * β y z) (hadj : ∀ (r : R) x y, β (r • x) y = β x (σ r • y))
    (h0 : ∀ y, β 0 y = 1) (B N : Submodule R M) : Submodule R M where
  carrier := {x | x ∈ B ∧ ∀ y ∈ N, β x y = 1}
  add_mem' := fun {a b} ha hb => ⟨B.add_mem ha.1 hb.1, fun y hy => by rw [hadd, ha.2 y hy, hb.2 y hy, one_mul]⟩
  zero_mem' := ⟨B.zero_mem, fun y _ => h0 y⟩
  smul_mem' := fun r a ha => ⟨B.smul_mem r ha.1, fun y hy => by rw [hadj]; exact ha.2 _ (N.smul_mem _ hy)⟩
end Fin
end GlobalTheory.HermitianGauss


