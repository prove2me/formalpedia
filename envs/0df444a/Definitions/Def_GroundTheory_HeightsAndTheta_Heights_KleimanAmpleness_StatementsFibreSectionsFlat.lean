-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsFibreSectionsFlat
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsFibreSectionsFlat
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:36:03.659258+00:00
-- url     : https://prove2.me/theorems/bd527e24-0d61-51f6-939c-1d276b28c0a4
-- title:
--   Statements Fibre Sections Flat
-- statement:
--   Definitions and structural lemmas for Statements Fibre Sections Flat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StatementsFibreSectionsFlat.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsNefGeneric
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
open MvPolynomial Filter
noncomputable section
universe u w
def FibreSectionsFlat.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsDedekindDomain S] (F : Type u) [Field F] [Algebra S F]
    [IsFractionRing S F] (Ω : Type w) [Field Ω] [Algebra S Ω] [Algebra F Ω] [IsScalarTower S F Ω]
    (N : ℕ) (x : Fin (N + 1) → Ω) (L : LineBundle S x) (𝔪 : Ideal S), 𝔪.IsMaximal →
    ∀ qq : Ideal (Poly S N), qq.IsPrime → (∀ s : S, (C s : Poly S N) ∈ qq → s = 0) →
    ∀ e : ℕ, IsSubvar x (qq.map (MvPolynomial.map (algebraMap S F))) e →
    ∀ᶠ c : ℕ in atTop,
      restrLen (qq.map (MvPolynomial.map (algebraMap S F)))
          ((L.toSubSystem.extend F).twist (twistSys F x (c : ℤ))) =
        restrLen (qq ⊔ 𝔪.map (C : S →+* Poly S N)) (L.toSubSystem.twist (twistSys S x (c : ℤ)))
end
end GroundTheory.Heights₂.Heights.Kleiman


