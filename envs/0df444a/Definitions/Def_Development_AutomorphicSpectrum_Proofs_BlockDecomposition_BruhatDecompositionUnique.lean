-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BruhatDecompositionUnique
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BruhatDecompositionUnique
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:15:00.673789+00:00
-- url     : https://prove2.me/theorems/c41779e1-5f62-48da-bf53-9016b1bc29d0
-- title:
--   Bruhat Decomposition Unique
-- statement:
--   Definitions and structural lemmas for Bruhat Decomposition Unique, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BruhatDecompositionUnique.lean

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
open ReciprocityTheory.Ty.Fin Formalism.IrreducibleCountingLemmas.TYPES
noncomputable section
namespace GlobalTheory.CompanionTheory.BruhatInv
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
def ind (K : Type) [Field K] {ι : Type} [DecidableEq ι] (p : ι → Prop) [DecidablePred p] :
    Matrix ι ι K :=
  Matrix.diagonal fun i => if p i then 1 else 0
def cnt {s s' : ℕ} (b : ι → Fin s) (b' : ι → Fin s') (σ : Equiv.Perm ι) (a a' : ℕ) : ℕ :=
  (Finset.univ.filter fun j => (b j : ℕ) < a ∧ a' ≤ (b' (σ j) : ℕ)).card
end GlobalTheory.CompanionTheory.BruhatInv


