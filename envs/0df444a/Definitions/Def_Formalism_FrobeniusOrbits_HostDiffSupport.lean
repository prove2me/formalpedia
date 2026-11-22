-- Prove2me | Definitions.Def_Formalism_FrobeniusOrbits_HostDiffSupport
-- name    : Formalism_FrobeniusOrbits_HostDiffSupport
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:31:12.000419+00:00
-- url     : https://prove2.me/theorems/0314dcbe-6e57-423b-872c-eb63f7c6cf4b
-- title:
--   Host Diff Support
-- statement:
--   Definitions and structural lemmas for Host Diff Support, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/HostDiffSupport.lean

import Definitions.Def_Formalism_FrobeniusOrbits_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
namespace Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
def KinE {L : Type*} [Field L] [Algebra ℚ L] (ζ a b : L) : IntermediateField ℚ (hostE ζ a b) :=
  ℚ⟮bE ζ a b⟯
def HostDiffSupport : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ P : Ideal (𝓞 (hostE ζ a b)), P.IsPrime →
    P ∣ differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) →
      ((2 : ℤ) : 𝓞 (hostE ζ a b)) ∈ P ∨ ((q : ℤ) : 𝓞 (hostE ζ a b)) ∈ P
def HostPrincipal : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, galE e ζ a b σ = cc e →
    ∃ 𝔟 : Ideal (𝓞 (hostE ζ a b)),
      differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) = 𝔟 * (σ • 𝔟) ∧ 𝔟 ⊔ σ • 𝔟 = ⊤
end Formalism.FrobeniusOrbits


