-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatNormalFibres
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatNormalFibres
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:29.936206+00:00
-- url     : https://prove2.me/theorems/7078aa87-a106-4b07-9ba5-8ec626b57522
-- title:
--   St Flat Normal Fibres
-- statement:
--   Definitions and structural lemmas for St Flat Normal Fibres, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StFlatNormalFibres.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
abbrev primeFibreLocalRing (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S] (P : Ideal S)
    [P.IsPrime] : Type _ :=
  Localization.AtPrime P ⧸
    Ideal.map (algebraMap S (Localization.AtPrime P)) (Ideal.map (algebraMap R S) (Ideal.comap (algebraMap R S) P))
def FlatNormalFibres.Statement : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S],
    IsNoetherianRing R → IsNoetherianRing S → IsLocalRing S → Module.Flat R S →
      IsDomain R → IsIntegrallyClosed R →
      (∀ (P : Ideal S) [P.IsPrime],
        IsDomain (primeFibreLocalRing R P) ∧ IsIntegrallyClosed (primeFibreLocalRing R P)) →
        IsDomain S ∧ IsIntegrallyClosed S
noncomputable def primeFibreLocalRing_complex_equiv (P : Ideal ℂ) [P.IsPrime] :
    primeFibreLocalRing ℂ P ≃+* ℂ := by
  have hP : P = ⊥ := (Ideal.eq_bot_or_top P).resolve_right (Ideal.IsPrime.ne_top ‹_›)
  have hmap : Ideal.map (algebraMap ℂ (Localization.AtPrime P))
      (Ideal.map (algebraMap ℂ ℂ) (Ideal.comap (algebraMap ℂ ℂ) P)) = ⊥ := by
    subst hP
    simp
  refine (Ideal.quotEquivOfEq hmap).trans (RingEquiv.quotientBot _) |>.trans ?_
  exact (IsLocalization.atUnits ℂ P.primeCompl (fun x hx => by
    subst hP
    exact isUnit_iff_ne_zero.2 (by simpa using hx))).toRingEquiv.symm
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


