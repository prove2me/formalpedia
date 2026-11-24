-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_BaseChangeDistinctness
-- name    : Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_BaseChangeDistinctness
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T18:53:10.062496+00:00
-- url     : https://prove2.me/theorems/3c7afe28-33ab-4e97-ab38-6962ba8d99f9
-- title:
--   Base Change Distinctness
-- statement:
--   Definitions and structural lemmas for Base Change Distinctness, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/BaseChangeDistinctness.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeDistinctness
open NumberField Formalism.BasicNotions Formalism.MainNotions.N
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
def cmTypeOf (H : Host R) : Set (H.E →+* ℂ) := H.cmType
def SphericalInert (B : NBC A) (j : ℕ) (π : B.AU j) : Prop :=
  ∀ w : PlE H, ¬ IsSplitPl H w → B.sphAU j π w
structure IsBaseChange (B : NBC A) (j : ℕ) (π : B.AU j) (Pa : List (Part A.CG)) : Prop where

  discrete : ∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d

  conjSelfDual : ∀ p ∈ Pa, A.csd p.π

  distinct : Pa.Nodup

  rank : rankIso N A Pa = R.nV

  split : ∀ w : PlE H, IsSplitPl H w → isoLoc N A Pa w = B.locAU j π w

  inert : ∀ w : PlE H, ¬ IsSplitPl H w →
    A.unr (isoLoc N A Pa w) ∧ A.frobEig (isoLoc N A Pa w) = ubc R.nV (B.satAU j π w)

  inf : ∀ τ : H.E →+* ℂ, isoInf N A Pa τ = B.infW j (B.wtAU j π) τ

  inf_conj : ∀ τ ∈ cmTypeOf H,
    isoInf N A Pa (ComplexEmbedding.conjugate τ) = (B.infW j (B.wtAU j π) τ).map (fun z => -z)
def BaseChangeDefinite_at (B : NBC A) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ R.m → ∀ π : B.AU j, SphericalInert B j π →
    ∃ Pa : List (Part A.CG), IsBaseChange B j π Pa
end GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeDistinctness
end


