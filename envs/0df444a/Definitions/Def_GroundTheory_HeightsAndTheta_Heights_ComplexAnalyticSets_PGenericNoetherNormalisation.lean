-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericNoetherNormalisation
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericNoetherNormalisation
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T11:27:32.983005+00:00
-- url     : https://prove2.me/theorems/41a08a99-9f7c-4534-8bfe-dee7731af281
-- title:
--   PGeneric Noether Normalisation
-- statement:
--   Definitions and structural lemmas for PGeneric Noether Normalisation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericNoetherNormalisation.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericNoetherNormalisation
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SumRMulNe
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ProofSimp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open Polynomial MvPolynomial Ideal Nat RingHom List
namespace GenericNoetherNormalisation
section Nagata
variable {A : Type*} [CommRing A] [IsDomain A] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) A)
variable (v w : Fin (n + 1) →₀ ℕ)
local notation3 "up" => 2 + f.totalDegree
local notation3 "r" => fun (i : Fin (n + 1)) ↦ up ^ i.1
noncomputable abbrev nagata (c : A) :
    MvPolynomial (Fin (n + 1)) A →ₐ[A] MvPolynomial (Fin (n + 1)) A :=
  aeval fun i ↦ if i = 0 then X 0 else X i + c • X 0 ^ r i
omit [IsDomain A] in
theorem nagata_comp_neg (c : A) : (nagata f c).comp (nagata f (-c)) = AlgHom.id _ _ := by
  rw [comp_aeval, ← MvPolynomial.aeval_X_left]
  ext i v
  cases i using Fin.cases <;> simp
noncomputable abbrev nagataEquiv := AlgEquiv.ofAlgHom (nagata f 1) (nagata f (-1))
  (nagata_comp_neg f 1) (by simpa using nagata_comp_neg f (-1))
end Nagata
section Combination
variable {A D : Type*} [CommRing A] [CommRing D] [Algebra A D] {m : ℕ}
def CombAfterPower (c : A) (z : Fin m → D) (s : Finset D) (d : D) : Prop :=
  ∃ (k : ℕ) (cf : D → MvPolynomial (Fin m) A), c ^ k • d = ∑ t ∈ s, aeval z (cf t) * t
variable {c : A} {z : Fin m → D} {s : Finset D}
end Combination
universe u
end GenericNoetherNormalisation
end GroundTheory.Heights₂.Heights


