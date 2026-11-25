-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionMulInjSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionMulInjSt
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:27:33.207031+00:00
-- url     : https://prove2.me/theorems/267bfe5a-3222-4eda-b4c6-f53b66a64ce2
-- title:
--   Section Mul Inj St
-- statement:
--   Definitions and structural lemmas for Section Mul Inj St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/SectionMulInjSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperCutObj
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
def SectionMulInj.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (pp : Ideal (Poly k N)), pp.IsPrime → (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) →
    primeOf (S := k) x ≤ pp →
    ∀ (D M : LineBundle k x) (s : Ω), (∃ f ∈ zeroIdeal D.toSubSystem s, f ∉ pp) →
    ∀ (I : Chart x), ∀ y ∈ M.sub I,
      s * y ∈ ((M.toSubSystem.twist D.toSubSystem).twist (idealSys x pp)).sub I →
      y ∈ (M.toSubSystem.twist (idealSys x pp)).sub I
end
end GroundTheory.Heights₂.Heights.Kleiman


