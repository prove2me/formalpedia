-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalLengthSum
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalLengthSum
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:14:45.182527+00:00
-- url     : https://prove2.me/theorems/276a8dd0-64fc-49db-8ab9-bfd865f3758d
-- title:
--   Statements Semilocal Length Sum
-- statement:
--   Definitions and structural lemmas for Statements Semilocal Length Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsSemilocalLengthSum.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalLength
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
section Fibre
variable {K K' : Type} [DecidableEq K] [DecidableEq K'] {F : Type*} [Field F]
  (j : K ↪ K') {ι' : K' → Type}
end Fibre
open Classical in
set_option synthInstance.maxHeartbeats 400000 in

def SemilocalLengthSum.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ (c : K → ℕ) (a h : MRing (fun k => ι' (j k)) F), IsMultiHomog a c → IsMultiHomog h c →
    a ∉ contractPrime j P' →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W → h ∉ W →
    ∀ d : Ideal (MRing ι' F) → ℕ,
      (∀ W' (hW' : IsMultiProjPrime W'), contractPrime j W' = W →
        haveI := hW'.isPrime
        d W' = relDeg j W') →
      haveI := hP'.isPrime
      ∀ α : degZeroLoc (contractPrime j P') {W},
        (α : FractionRing (MRing (fun k => ι' (j k)) F ⧸ contractPrime j P')) =
            algebraMap (MRing (fun k => ι' (j k)) F ⧸ contractPrime j P') _
                (Ideal.Quotient.mk (contractPrime j P') a) /
              algebraMap (MRing (fun k => ι' (j k)) F ⧸ contractPrime j P') _
                (Ideal.Quotient.mk (contractPrime j P') h) →
      ∀ β : (W' : Ideal (MRing ι' F)) → degZeroLoc P' {W'},
        (∀ W' ∈ fibrePrimes j P' W,
          (β W' : FractionRing (MRing ι' F ⧸ P')) = contractFracMap j P' (α : _)) →
        ∃ hfin : (fibrePrimes j P' W).Finite,
          Module.length (degZeroLoc (contractPrime j P') {W})
              (degZeroLoc P' (fibrePrimes j P' W) ⧸
                LinearMap.range (LinearMap.lsmul (degZeroLoc (contractPrime j P') {W})
                  (degZeroLoc P' (fibrePrimes j P' W)) α)) =
            ∑ W' ∈ hfin.toFinset with rename (blockIncl j ι') a ∈ W',
              Ring.ord (degZeroLoc P' {W'}) (β W') * (d W' : ℕ∞)
end
end GroundTheory.Heights₂.Heights.FieldNumbers


