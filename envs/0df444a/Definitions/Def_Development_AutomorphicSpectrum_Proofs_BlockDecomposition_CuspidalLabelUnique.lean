-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalLabelUnique
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalLabelUnique
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:41.648495+00:00
-- url     : https://prove2.me/theorems/d5bb7bdf-5ef2-4337-b66e-35d696560a1c
-- title:
--   Cuspidal Label Unique
-- statement:
--   Definitions and structural lemmas for Cuspidal Label Unique, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalLabelUnique.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OrthogonalIntVectorsNotAgreeOnRegular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RegularIffNatDegreeAndExistsEllipticGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InnerProductRootPowerSumEqOfFrobeniusModEq
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
open Polynomial CategoryTheory
namespace GlobalTheory.CompanionTheory.TyFin.LabelUniq
def orb (q d N s : ℕ) : Finset ℕ := (Finset.range d).image fun i => s * q ^ i % N
def ind (S : Finset ℕ) (k : ℕ) : ℤ := if k ∈ S then 1 else 0
section Field
variable {K : Type} [Field K] [Fintype K]
end Field
end GlobalTheory.CompanionTheory.TyFin.LabelUniq
namespace GlobalTheory.CompanionTheory.TyFin.LabelUniq
section Label
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
end Label
end GlobalTheory.CompanionTheory.TyFin.LabelUniq


