-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModChebOm
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModChebOm
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T21:47:12.662864+00:00
-- url     : https://prove2.me/theorems/48bf03b7-c30e-414f-a6cb-c99910558df7
-- title:
--   Mod Cheb Om
-- statement:
--   Definitions and structural lemmas for Mod Cheb Om, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModChebOm.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
namespace ReciprocityTheory.ChartRestriction.L1
def ChebOmSt : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (S : Set (HeightOneSpectrum (𝓞 E))) (hS : S.Finite) (H : Subgroup (Ω ≃ₐ[E] Ω)) (hn : H.Normal)
    (ho : IsOpen (H : Set (Ω ≃ₐ[E] Ω)))
    (hI : ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), LiesAbove A v → v ∉ S →
      ∀ g : Ω ≃ₐ[E] Ω, InertiaEl A g → g ∈ H) (σ : Ω ≃ₐ[E] Ω),
    ∃ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)) (φ : Ω ≃ₐ[E] Ω), LiesAbove A v ∧ v ∉ S ∧
      (Nat.card (𝓞 E ⧸ v.asIdeal)).Prime ∧ IsArithFrobenius A v φ ∧ σ⁻¹ * φ ∈ H
end ReciprocityTheory.ChartRestriction.L1


