-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerColumnRecursion
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerColumnRecursion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:41.748855+00:00
-- url     : https://prove2.me/theorems/4cca8fe7-c17c-4903-a1cd-c2545b3681ca
-- title:
--   Whittaker Column Recursion
-- statement:
--   Definitions and structural lemmas for Whittaker Column Recursion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerColumnRecursion.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
noncomputable section
namespace GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
def colEntries {d j : ℕ} (hj : j < d) (u : GL (Fin d) K) : Fin j → K :=
  fun i => (u : Matrix (Fin d) (Fin d) K) ⟨i, i.2.trans hj⟩ ⟨j, hj⟩
end GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier


