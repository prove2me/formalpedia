-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StepTwoFiltSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StepTwoFiltSt
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:27:43.277292+00:00
-- url     : https://prove2.me/theorems/3679a9b5-24db-453c-81e2-5097b1ea3dd9
-- title:
--   Step Two Filt St
-- statement:
--   Definitions and structural lemmas for Step Two Filt St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StepTwoFiltSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
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
def StepTwo.Filt.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E]
    [IsScalarTower S Ω E] (M₁ M₂ : FinGradedSub (S := S) (x := x) E), (∀ c, M₂.piece c ≤ M₁.piece c) →
    ∀ J : Ideal (Poly S N), (∀ (f : Poly S N) (e : ℕ), f ∈ J → f.IsHomogeneous e → ∀ (a : ℤ),
      ∀ z ∈ M₁.piece a, aeval x f • z ∈ M₂.piece (a + e)) →
    ∃ (n : ℕ) (Nf : Fin (n + 1) → FinGradedSub (S := S) (x := x) E) (g : Fin n → E) (deg : Fin n → ℤ)
      (pr : Fin n → Ideal (Poly S N)),
      Nf 0 = M₂ ∧ Nf (Fin.last n) = M₁ ∧
      ∀ k : Fin n, (pr k).IsPrime ∧ (∀ p ∈ pr k, ∀ d : ℕ, homogeneousComponent d p ∈ pr k) ∧
        primeOf (S := S) x ≤ pr k ∧
        (∀ (f : Poly S N) (e : ℕ), f ∈ J → f.IsHomogeneous e → f ∈ pr k) ∧
        g k ∈ (Nf k.succ).piece (deg k) ∧
        (∀ c, (Nf k.succ).piece c = (Nf k.castSucc).piece c ⊔ Submodule.span S
          {z | ∃ (f : Poly S N) (d : ℕ), f.IsHomogeneous d ∧ deg k + d = c ∧ z = aeval x f • g k}) ∧
        ∀ (f : Poly S N) (d : ℕ), f.IsHomogeneous d →
          (f ∈ pr k ↔ aeval x f • g k ∈ (Nf k.castSucc).piece (deg k + d))
end
end GroundTheory.Heights₂.Heights.Kleiman


