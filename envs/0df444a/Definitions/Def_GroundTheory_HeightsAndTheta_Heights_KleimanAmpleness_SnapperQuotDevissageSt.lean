-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotDevissageSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotDevissageSt
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:27:30.627603+00:00
-- url     : https://prove2.me/theorems/a4972908-0f91-5daf-9fc8-c02726205a77
-- title:
--   Snapper Quot Devissage St
-- statement:
--   Definitions and structural lemmas for Snapper Quot Devissage St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/SnapperQuotDevissageSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperCutObj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
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
def SnapperQuotDevissage.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F₁ F₂ : SubFamily k x E), (∀ I, (F₁.sub I).FG) → (∀ I, F₂.sub I ≤ F₁.sub I) →
    ∀ J : Ideal (Poly k N), (∀ f ∈ J, ∀ d : ℕ, homogeneousComponent d f ∈ J) → primeOf (S := k) x ≤ J →
    (∀ I, (F₁.toSubSystem.twist (idealSys x J)).sub I ≤ F₂.sub I) →
    ∃ (r : ℕ) (pp : Fin r → Ideal (Poly k N)) (a : Fin r → ℤ),
      (∀ m, (pp m).IsPrime ∧ (∀ f ∈ pp m, ∀ d : ℕ, homogeneousComponent d f ∈ pp m) ∧ J ≤ pp m) ∧
      ∀ (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ),
        eulerCharQuot k
            ((F₁.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
            ((F₂.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c)) =
          ∑ m, pieceChar k (pp m) (a m) L n c
end
end GroundTheory.Heights₂.Heights.Kleiman


