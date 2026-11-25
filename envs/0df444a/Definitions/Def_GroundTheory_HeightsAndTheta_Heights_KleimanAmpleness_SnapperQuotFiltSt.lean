-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotFiltSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotFiltSt
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:32:52.615145+00:00
-- url     : https://prove2.me/theorems/36cc46d0-e4a8-5e71-b5c9-b3dfb8710cf0
-- title:
--   Snapper Quot Filt St
-- statement:
--   Definitions and structural lemmas for Snapper Quot Filt St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/SnapperQuotFiltSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotIsoSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotDevissageSt
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
def SnapperQuotFilt.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F₁ F₂ : SubFamily k x E), (∀ I, (F₁.sub I).FG) → (∀ I, F₂.sub I ≤ F₁.sub I) →
    ∀ J : Ideal (Poly k N), (∀ f ∈ J, ∀ d : ℕ, homogeneousComponent d f ∈ J) → primeOf (S := k) x ≤ J →
    (∀ I, (F₁.toSubSystem.twist (idealSys x J)).sub I ≤ F₂.sub I) →
    ∃ (r : ℕ) (G : ℕ → SubFamily k x E) (pp : Fin r → Ideal (Poly k N)) (a : Fin r → ℤ),
      (∀ m I, ((G m).sub I).FG) ∧ (G 0).toSubSystem = F₂.toSubSystem ∧
      (G r).toSubSystem = F₁.toSubSystem ∧ (∀ m < r, ∀ I, (G m).sub I ≤ (G (m + 1)).sub I) ∧
      (∀ m, (pp m).IsPrime ∧ (∀ f ∈ pp m, ∀ d : ℕ, homogeneousComponent d f ∈ pp m) ∧ J ≤ pp m) ∧
      ∀ (m : Fin r) (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ),
        Nonempty (QuotIso
          (((G (m + 1)).toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
          (((G m).toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
          (((twistSys k x (a m)).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
          ((((twistSys k x (a m)).twist (idealSys x (pp m))).twistPows t (fun j => (L j).toSubSystem) n).twist
            (twistSys k x c)))
end
end GroundTheory.Heights₂.Heights.Kleiman


