-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishLoc
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishLoc
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T09:34:46.826274+00:00
-- url     : https://prove2.me/theorems/d9c03301-f316-4bb6-b843-a55976d893ab
-- title:
--   PTilde Vanish Loc
-- statement:
--   Definitions and structural lemmas for PTilde Vanish Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanishLoc.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishCone
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_bijective_smul_of_isHomogeneous_7a9bef9a2abe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_monos_isHomogeneous_bb0f48dbdc12

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
section LocE
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  (M : FinGradedSub (S := S) (x := x) E)
def locConeE (I : Finset (Fin (N + 1))) (hI : I ⊆ support x) :
    LocMod S N M.coneSubE I →ₗ[Poly S N] ConeE S x E :=
  LocalizedModule.lift (monos I) M.coneSubE.subtype fun s => by
    rw [Module.End.isUnit_iff]
    obtain ⟨e, he⟩ := monos_isHomogeneous s.2
    exact bijective_smul_of_isHomogeneous he (aeval_ne_zero_of_mem_monos_support hI s.2)
def tildeGensE (c : ℤ) (I : Chart x) : Set E :=
  {y | ∃ (m : E) (s : Poly S N) (a : ℤ) (e : ℕ), s ∈ monos I.1 ∧ s.IsHomogeneous e ∧ m ∈ M.piece a ∧
    a - e = c ∧ y = (aeval x s)⁻¹ • m}
end LocE
end
end GroundTheory.Heights₂.Heights.Kleiman


