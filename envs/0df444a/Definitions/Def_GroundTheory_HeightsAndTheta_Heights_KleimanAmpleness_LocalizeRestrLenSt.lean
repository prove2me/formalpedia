-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LocalizeRestrLenSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LocalizeRestrLenSt
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T06:20:03.165053+00:00
-- url     : https://prove2.me/theorems/7553f94b-ddf2-406c-b017-84e302a55c8f
-- title:
--   Localize Restr Len St
-- statement:
--   Definitions and structural lemmas for Localize Restr Len St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/LocalizeRestrLenSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LocalizeNefAboveSt
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
open MvPolynomial
def LocalizeRestrLen.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (𝔪 : Ideal S) [𝔪.IsMaximal] (O : Type) [CommRing O] [Algebra S O]
    [IsLocalization.AtPrime O 𝔪] (Ω : Type) [Field Ω] [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω]
    (N : ℕ) (x : Fin (N + 1) → Ω) (pp' : Ideal (Kleiman.Poly O N)),
    (𝔪.map (algebraMap S O)).map (C : O →+* Kleiman.Poly O N) ≤ pp' →
    ∀ F : Kleiman.SubSystem S x Ω,
      Kleiman.restrLen pp' (F.baseChange O) =
        Kleiman.restrLen (pp'.comap (MvPolynomial.map (algebraMap S O) : Kleiman.Poly S N →+* Kleiman.Poly O N)) F
example (h : LocalizeRestrLen.Statement) :=
  h ℤ (Ideal.span {(2 : ℤ)}) LocalizeNefAbove.exO LocalizeNefAbove.exΩ 1 ![1, 1] _ le_rfl
    (Kleiman.twistSys ℤ ![1, 1] 1)
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization


