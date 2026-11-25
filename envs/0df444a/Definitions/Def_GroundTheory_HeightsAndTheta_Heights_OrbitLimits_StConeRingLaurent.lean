-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StConeRingLaurent
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StConeRingLaurent
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T14:06:22.0518+00:00
-- url     : https://prove2.me/theorems/31cc811f-30d5-5d0f-8cd2-0e0c6863aa94
-- title:
--   St Cone Ring Laurent
-- statement:
--   Definitions and structural lemmas for St Cone Ring Laurent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StConeRingLaurent.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ChartConeObjects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
def ConeRingLaurent.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) (i : (k : K) → ι k),
    (ratioMap i).Flat ∧ ∀ 𝔮 : Ideal (DehomRing i), 𝔮.IsPrime → (𝔮.map (ratioMap i)).IsPrime
def evalOnesDehom {K : Type} [Fintype K] {ι : K → Type} (i : (k : K) → ι k) : DehomRing i →+* ℂ :=
  Ideal.Quotient.lift (dehomIdeal i) (eval fun _ => (1 : ℂ)) (by
    have hle : dehomIdeal i ≤ RingHom.ker (eval fun _ => (1 : ℂ) : MvPolynomial (Σ k, ι k) ℂ →+* ℂ) := by
      rw [dehomIdeal, Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      simp
    exact fun a ha => hle ha)
end GroundTheory.Heights₂.Heights.Targets


