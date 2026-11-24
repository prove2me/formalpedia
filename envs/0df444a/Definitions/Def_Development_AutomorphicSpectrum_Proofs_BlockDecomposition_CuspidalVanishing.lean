-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalVanishing
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalVanishing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:56.251798+00:00
-- url     : https://prove2.me/theorems/3c863bf8-6326-48cc-976e-36a24ad3787c
-- title:
--   Cuspidal Vanishing
-- statement:
--   Definitions and structural lemmas for Cuspidal Vanishing, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalVanishing.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
namespace GlobalTheory.CompanionTheory.TyFin.CuspVan
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def rankMap {κ : Type} [Fintype κ] {s : ℕ} (β : κ → Fin s) :
    κ → Fin (Finset.univ.image β).card := fun i =>
  ((Finset.univ.image β).orderIsoOfFin rfl).symm ⟨β i, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
def extHom {s : ℕ} (b : ι → Fin s) (c : Fin s) : GL {i // b i = c} K →* GL ι K :=
  (leviEmb K (fun i => b i = c)).comp (MonoidHom.inl _ _)
end GlobalTheory.CompanionTheory.TyFin.CuspVan


