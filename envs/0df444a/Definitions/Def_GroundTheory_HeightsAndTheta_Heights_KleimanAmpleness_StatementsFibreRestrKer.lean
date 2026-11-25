-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsFibreRestrKer
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsFibreRestrKer
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T06:37:11.108649+00:00
-- url     : https://prove2.me/theorems/a99f9fda-0880-5448-87ff-e5ad434f1942
-- title:
--   Statements Fibre Restr Ker
-- statement:
--   Definitions and structural lemmas for Statements Fibre Restr Ker, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StatementsFibreRestrKer.lean

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
def FibreRestrKer.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsDedekindDomain S] (F : Type u) [Field F] [Algebra S F]
    [IsFractionRing S F] (Ω : Type w) [Field Ω] [Algebra S Ω] [Algebra F Ω] [IsScalarTower S F Ω]
    (N : ℕ) (x : Fin (N + 1) → Ω) (L : LineBundle S x) (𝔪 : Ideal S), 𝔪.IsMaximal →
    ∀ qq : Ideal (Poly S N), qq.IsPrime → (∀ s : S, (C s : Poly S N) ∈ qq → s = 0) →
    ∀ e : ℕ, IsSubvar x (qq.map (MvPolynomial.map (algebraMap S F))) e →
    ∀ᶠ c : ℕ in atTop,
      ((L.toSubSystem.twist (twistSys S x (c : ℤ))).twist (idealSys x (qq ⊔ 𝔪.map (C : S →+* Poly S N)))).secs =
        ((L.toSubSystem.twist (twistSys S x (c : ℤ))).twist (idealSys x qq)).secs ⊔
          𝔪 • (L.toSubSystem.twist (twistSys S x (c : ℤ))).secs
end
end GroundTheory.Heights₂.Heights.Kleiman


