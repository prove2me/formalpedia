-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TransferStatementBis
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TransferStatementBis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:54:19.956744+00:00
-- url     : https://prove2.me/theorems/cfdbf411-2b27-4a11-a8a9-d41943eedda4
-- title:
--   Transfer Statement Bis
-- statement:
--   Definitions and structural lemmas for Transfer Statement Bis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TransferStatementBis.lean

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithfulStatement
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil


set_option autoImplicit false
open CompanionTheory.Rg.Fl
open CompanionTheory.D.gk.admitted (stdPoly word word_nil word_cons)
noncomputable section
namespace GlobalTheory.CompanionTheory.HeckeTransfer
section Words
variable {R : Type*} [Ring R]
end Words
variable {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def phi (K : Subgroup G) (σ : G →* (H →L[ℂ] H)) (v : H) : ((G ⧸ K) →₀ ℂ) →ₗ[ℂ] H :=
  Finsupp.linearCombination ℂ fun x : G ⧸ K => σ (Quotient.out x) v
abbrev dlt (K : Subgroup G) : (G ⧸ K) →₀ ℂ := Finsupp.single ((1 : G) : G ⧸ K) 1
variable {K : Subgroup G} {σ : G →* (H →L[ℂ] H)} {v : H}
end GlobalTheory.CompanionTheory.HeckeTransfer


