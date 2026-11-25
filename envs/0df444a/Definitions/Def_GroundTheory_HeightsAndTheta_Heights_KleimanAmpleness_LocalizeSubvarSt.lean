-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LocalizeSubvarSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LocalizeSubvarSt
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T06:06:41.751464+00:00
-- url     : https://prove2.me/theorems/d172b12a-6fe8-4b1a-a615-611733376e3d
-- title:
--   Localize Subvar St
-- statement:
--   Definitions and structural lemmas for Localize Subvar St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/LocalizeSubvarSt.lean

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
open MvPolynomial
def LocalizeSubvar.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (𝔪 : Ideal S) [𝔪.IsMaximal] (O : Type) [CommRing O] [Algebra S O]
    [IsLocalization.AtPrime O 𝔪] (Ω : Type) [Field Ω] [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω]
    (N : ℕ) (x : Fin (N + 1) → Ω) (pp' : Ideal (Kleiman.Poly O N)) (e : ℕ),
    (𝔪.map (algebraMap S O)).map (C : O →+* Kleiman.Poly O N) ≤ pp' → Kleiman.IsSubvar x pp' e →
    Kleiman.IsSubvar x
      (pp'.comap (MvPolynomial.map (algebraMap S O) : Kleiman.Poly S N →+* Kleiman.Poly O N)) e
instance LocalizeSubvar.exLoc (k : Type) [Field k] : IsLocalization.AtPrime k (⊥ : Ideal k) :=
  IsLocalization.of_le_isUnit fun a ha =>
    (IsUnit.mem_submonoid_iff a).mpr (isUnit_iff_ne_zero.mpr fun h => ha (h ▸ Ideal.zero_mem _))
theorem LocalizeSubvar.hyps (k : Type) [Field k] (N : ℕ) :
    ((⊥ : Ideal k).map (algebraMap k k)).map (C : k →+* Kleiman.Poly k N) ≤
        Kleiman.primeOf (S := k) (Kleiman.genericPt k N) ∧
      Kleiman.IsSubvar (Kleiman.genericPt k N) (Kleiman.primeOf (S := k) (Kleiman.genericPt k N)) N :=
  ⟨by rw [Ideal.map_bot, Ideal.map_bot]; exact bot_le, Kleiman.isSubvar_genericPt k N⟩
example (k : Type) [Field k] (h : LocalizeSubvar.Statement) :=
  h k ⊥ k (FractionRing (Kleiman.Poly k 1)) 1 (Kleiman.genericPt k 1) _ 1 (LocalizeSubvar.hyps k 1).1
    (LocalizeSubvar.hyps k 1).2
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization


