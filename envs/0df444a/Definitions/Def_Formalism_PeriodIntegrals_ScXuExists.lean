-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_ScXuExists
-- name    : Formalism_PeriodIntegrals_ScXuExists
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T12:42:11.725809+00:00
-- url     : https://prove2.me/theorems/788a1836-b38a-4a8e-adfb-e39e9c4136f6
-- title:
--   Sc Xu Exists
-- statement:
--   Definitions and structural lemmas for Sc Xu Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ScXuExists.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_PeriodIntegrals_ScRefExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S PI.ScRefExists
open scoped TensorProduct
open Matrix
namespace PI.ScXuExists
def OneOff (I : Formalism.MainNotions.S.AutInst) (g : ℕ) (x : I.Gf) : Prop :=
  ∀ m : ℕ, Nat.Coprime m g → ∀ y ∈ I.Lf, InAt I m m ((I.fmat x - 1) *ᵥ y)
def Target : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (Rf : RefData I g r k e f), 1 ≤ g →
    (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 I.F), (g : 𝓞 I.F) ∈ v.asIdeal →
      Nat.card {w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E) //
        w.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = v.asIdeal} = 2) →
    I.n = 2 * r + k + 1 →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (e b) = 0) →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (f a) (f b) = 0) →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (f b) = if a = b then 1 else 0) →
    (∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (e a) z = 0 ∧ Formalism.UG.hform (starRingEnd I.E) I.J (f a) z = 0) →
    (∃ t : ℕ, t ≡ 1 [MOD g] ∧ Formalism.UG.hform (starRingEnd I.E) I.J z z = -(t : I.E)) →
    (∀ a, InAt I g 1 (incl I (e a)) ∧ InAt I g 1 (incl I (f a))) →
    InAt I g 1 (incl I z) →
    ∃ x : I.Gf, (∀ a, I.fmat x *ᵥ incl I (e a) = incl I (e a) ∧ I.fmat x *ᵥ incl I (f a) = incl I (f a)) ∧
      InAt I g g (I.fmat x⁻¹ *ᵥ incl I z - Rf.z0) ∧ OneOff I g x ∧ x ∈ I.Kset
end PI.ScXuExists


