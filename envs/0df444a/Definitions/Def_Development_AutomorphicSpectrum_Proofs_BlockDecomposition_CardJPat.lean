-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardJPat
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardJPat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:07.864032+00:00
-- url     : https://prove2.me/theorems/c743683b-d78d-4d0c-bf93-be9b37e68c4a
-- title:
--   Card JPat
-- statement:
--   Definitions and structural lemmas for Card JPat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardJPat.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatementStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
noncomputable section
namespace GlobalTheory.CompanionTheory.TyFin.WtFormPf
open ReciprocityTheory.Ty.Fin.Lq
section Dat
variable (g N : ℕ) [Fact g.Prime] [NeZero g] (P : Matrix (Fin N) (Fin N) (ZMod g) → Prop)
  (φ : Matrix (Fin N) (Fin N) (ZMod g) → ZMod g) (ψ₀ : AddChar (ZMod g) ℂ)
end Dat
end GlobalTheory.CompanionTheory.TyFin.WtFormPf


