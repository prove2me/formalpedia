-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalResidueLength
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalResidueLength
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:06:06.099643+00:00
-- url     : https://prove2.me/theorems/42b919f2-89a5-5344-915e-8d6720a3fd78
-- title:
--   Statements Semilocal Residue Length
-- statement:
--   Definitions and structural lemmas for Statements Semilocal Residue Length, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsSemilocalResidueLength.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalFiniteRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
set_option synthInstance.maxHeartbeats 400000 in

def SemilocalResidueLength.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W →
    haveI := hP'.isPrime
    ∀ W' (hW' : W' ∈ fibrePrimes j P' W),
      haveI := hW'.1.isPrime
      ∃ 𝔪 : Ideal (degZeroLoc P' (fibrePrimes j P' W)),
        (∀ x : degZeroLoc P' (fibrePrimes j P' W),
          x ∈ 𝔪 ↔ ¬ ∃ y ∈ degZeroLoc P' {W'}, (x : FractionRing (MRing ι' F ⧸ P')) * y = 1) ∧
        Module.length (degZeroLoc (contractPrime j P') {W})
            (degZeroLoc P' (fibrePrimes j P' W) ⧸ 𝔪) = (relDeg j W' : ℕ∞)
end
end GroundTheory.Heights₂.Heights.FieldNumbers


