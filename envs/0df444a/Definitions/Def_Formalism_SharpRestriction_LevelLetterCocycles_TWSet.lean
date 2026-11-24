-- Prove2me | Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_TWSet
-- name    : Formalism_SharpRestriction_LevelLetterCocycles_TWSet
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T18:34:15.498299+00:00
-- url     : https://prove2.me/theorems/9a5f0689-ae14-4682-95bf-79073b2e0f15
-- title:
--   TWSet
-- statement:
--   Definitions and structural lemmas for TWSet, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/TWSet.lean

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
namespace Formalism.MainNotions.NAdm
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  {LL0 : IntermediateField ℚ what₂.LL} {N : NData R H what₂}
def TWSet (tw : NTw R H what₂ LL0 N) (i : tw.Tw) (Q : Finset (PlE H)) : Prop :=
  ∀ v ∈ Q, IsSplitPl H v ∧ v ∉ placesOver H.E (tw.l i)
def AdmQ (tw : NTw R H what₂ LL0 N) (i : tw.Tw) (Q : Finset (PlE H)) (M : ℕ) : Prop :=
  TWSet tw i Q ∧ ∀ P ∈ Q, (∃ P' ∈ Q, IsConjPl H P P') ∧
    ∃ χ : G H.E N.Om →* Multiplicative (ZMod (tw.l i ^ M)),
      IsOpen (χ.ker : Set (G H.E N.Om)) ∧ AntiHom tw.cc χ ∧
      (∀ v ∈ placesOver H.E (tw.l i), ∀ A : ValuationSubring N.Om, IsPlaceOver A v →
        ∀ σ ∈ Dec (F := H.E) A, χ σ = 1) ∧
      (∀ v : PlE H, v ≠ P → ¬ IsConjPl H P v → ∀ A : ValuationSubring N.Om, IsPlaceOver A v →
        ∀ σ ∈ Ine (F := H.E) A, χ σ = 1) ∧
      ∀ A : ValuationSubring N.Om, IsPlaceOver A P →
        Function.Surjective fun σ : Ine (F := H.E) A => Multiplicative.toAdd (χ σ)
end Formalism.MainNotions.NAdm


