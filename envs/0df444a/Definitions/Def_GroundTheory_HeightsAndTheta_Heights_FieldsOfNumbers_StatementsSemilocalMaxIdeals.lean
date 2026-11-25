-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalMaxIdeals
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalMaxIdeals
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:42:30.621086+00:00
-- url     : https://prove2.me/theorems/f136ea43-aedb-428a-b87a-0a9a8ae0a877
-- title:
--   Statements Semilocal Max Ideals
-- statement:
--   Definitions and structural lemmas for Statements Semilocal Max Ideals, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsSemilocalMaxIdeals.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalLengthSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalFiniteRank
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_degZeroLoc_anti_2b5a3c1121df

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
abbrev degZeroLoc.algebraOfSubset {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
    (P : Ideal (MRing ι F)) [P.IsPrime] {𝒲₁ 𝒲₂ : Set (Ideal (MRing ι F))} (h𝒲 : 𝒲₁ ⊆ 𝒲₂) :
    Algebra (degZeroLoc P 𝒲₂) (degZeroLoc P 𝒲₁) :=
  (Subalgebra.inclusion (degZeroLoc_anti P h𝒲)).toRingHom.toAlgebra
set_option synthInstance.maxHeartbeats 400000 in

def SemilocalMaxIdeals.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W →
      haveI := hP'.isPrime
      ∃ (𝔪 : fibrePrimes j P' W → Ideal (degZeroLoc P' (fibrePrimes j P' W)))
        (h𝔪 : ∀ W', (𝔪 W').IsMaximal),
        Function.Injective 𝔪 ∧
        (∀ M : Ideal (degZeroLoc P' (fibrePrimes j P' W)), M.IsMaximal → ∃ W', M = 𝔪 W') ∧
        ∀ W' : fibrePrimes j P' W,
          (haveI := (h𝔪 W').isPrime
           letI := degZeroLoc.algebraOfSubset P' (Set.singleton_subset_iff.mpr W'.2)
           IsLocalization.AtPrime (degZeroLoc P' {W'.1}) (𝔪 W')) ∧
          haveI := W'.2.1.isPrime
          Module.length (degZeroLoc (contractPrime j P') {W})
              (degZeroLoc P' (fibrePrimes j P' W) ⧸ 𝔪 W') = (relDeg j W'.1 : ℕ∞)
end
end GroundTheory.Heights₂.Heights.FieldNumbers


