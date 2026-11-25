-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LocalizeBundleSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LocalizeBundleSt
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:16:56.094476+00:00
-- url     : https://prove2.me/theorems/45633fd4-5809-51b1-9610-c0581338375a
-- title:
--   Localize Bundle St
-- statement:
--   Definitions and structural lemmas for Localize Bundle St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/LocalizeBundleSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeObj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
def LocalizeBundle.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (𝔪 : Ideal S) [𝔪.IsPrime] (O : Type) [CommRing O] [Algebra S O]
    [IsLocalization.AtPrime O 𝔪] (Ω : Type) [Field Ω] [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω]
    (N : ℕ) (x : Fin (N + 1) → Ω) (M : Kleiman.LineBundle S x),
    ∃ M' : Kleiman.LineBundle O x, M'.toSubSystem = M.toSubSystem.baseChange O
instance LocalizeBundle.hyps : (Ideal.span {(2 : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_two
abbrev LocalizeBundle.exO : Type := Localization.AtPrime (Ideal.span {(2 : ℤ)})
abbrev LocalizeBundle.exΩ : Type := FractionRing LocalizeBundle.exO
instance LocalizeBundle.exTower : @IsScalarTower ℤ LocalizeBundle.exO LocalizeBundle.exΩ Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
example (h : LocalizeBundle.Statement) :=
  h ℤ (Ideal.span {(2 : ℤ)}) LocalizeBundle.exO LocalizeBundle.exΩ 1 ![1, 1]
    (Kleiman.twistBundle ℤ ![1, 1] 1)
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization


