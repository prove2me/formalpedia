-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionLatticeSeparatedComplete
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionLatticeSeparatedComplete
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:23:55.824596+00:00
-- url     : https://prove2.me/theorems/f7082b26-ad0d-4b0d-9e1b-ba6fe5332fb3
-- title:
--   Adelic Completion Lattice Separated Complete
-- statement:
--   Definitions and structural lemmas for Adelic Completion Lattice Separated Complete, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicCompletionLatticeSeparatedComplete.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_SmulBasisMemHatIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IntegralFiniteAdeleCompleteSeparated
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk


set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
namespace GlobalTheory.AdLat.Complete
section
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
noncomputable def comb {m : ℕ} (e : Fin m → Fin n → E) :
    (Fin m → FiniteAdeleRing (𝓞 F) F) →+ (Fin n → RA F E) where
  toFun a := ∑ i, fun j => a i ⊗ₜ[F] e i j
  map_zero' := by funext j; simp
  map_add' a b := by funext j; simp [TensorProduct.add_tmul, Finset.sum_add_distrib]
end
end GlobalTheory.AdLat.Complete


