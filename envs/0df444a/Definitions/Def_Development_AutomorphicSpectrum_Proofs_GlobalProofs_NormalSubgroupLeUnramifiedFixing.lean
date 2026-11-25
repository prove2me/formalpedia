-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_NormalSubgroupLeUnramifiedFixing
-- name    : Development_AutomorphicSpectrum_Proofs_GlobalProofs_NormalSubgroupLeUnramifiedFixing
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T02:17:49.139877+00:00
-- url     : https://prove2.me/theorems/2da3ca34-1405-5178-ba31-2a7207fb9f1f
-- title:
--   Normal Subgroup Le Unramified Fixing
-- statement:
--   Definitions and structural lemmas for Normal Subgroup Le Unramified Fixing, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/NormalSubgroupLeUnramifiedFixing.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Theorems.Thm_GroundTheory_ProfCoh_IsUnramifiedOutside_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
namespace GlobalTheory.CompanionTheory.GlobalFiniteness
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
omit [NumberField F] [Algebra F Ω] [Field F] in

theorem mem_of_isIntegral_int (A : ValuationSubring Ω) {y : Ω} (hy : IsIntegral ℤ y) : y ∈ A := by
  have h1 : IsIntegral A y := hy.tower_top
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp h1
  rw [← hz]
  exact z.2
noncomputable def intToVal (A : ValuationSubring Ω) (M : IntermediateField F Ω) : 𝓞 M →+* A :=
  ((algebraMap M Ω).comp (algebraMap (𝓞 M) M)).codRestrict A fun z =>
    mem_of_isIntegral_int A ((RingOfIntegers.isIntegral_coe z).map (IsScalarTower.toAlgHom ℤ M Ω))
noncomputable def cutPrime (A : ValuationSubring Ω) (M : IntermediateField F Ω) : Ideal (𝓞 M) :=
  (IsLocalRing.maximalIdeal A).comap (intToVal A M)
instance (A : ValuationSubring Ω) (M : IntermediateField F Ω) : (cutPrime A M).IsPrime :=
  Ideal.comap_isPrime _ _
end GlobalTheory.CompanionTheory.GlobalFiniteness


