-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConsequenceOfMackey
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConsequenceOfMackey
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:52.440216+00:00
-- url     : https://prove2.me/theorems/4f9ff0cb-c4bd-4a33-972b-d24e4e3b7bff
-- title:
--   Consequence Of Mackey
-- statement:
--   Definitions and structural lemmas for Consequence Of Mackey, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConsequenceOfMackey.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MaschkeProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalIsomorphismProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
namespace GlobalTheory.CompanionTheory.TyFin.FromMackey
section Gen
variable {Γ : Type} [Group Γ] [Fintype Γ]
end Gen
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable {K}
end GlobalTheory.CompanionTheory.TyFin.FromMackey


