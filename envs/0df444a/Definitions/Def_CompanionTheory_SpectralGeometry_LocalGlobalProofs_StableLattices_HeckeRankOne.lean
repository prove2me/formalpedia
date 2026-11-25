-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeRankOne
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeRankOne
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T12:41:05.254701+00:00
-- url     : https://prove2.me/theorems/1c7a4075-faae-4ab6-b3a1-6d69bdfc8849
-- title:
--   Hecke Rank One
-- statement:
--   Definitions and structural lemmas for Hecke Rank One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeRankOne.lean

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_WhittakerZeroStatement
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantEquality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL ReciprocityTheory.ChartRestriction.DS.Lap.Capelli CompanionTheory.RgExh
namespace GlobalTheory.CompanionTheory.RgExhHecke
variable {n : ℕ}
section Key
variable {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) {q : ℕ}
  (R C : Fin (q + 2) → Fin n) (x : ℂ) (f : Fin n → V) (d : Fin n)
def dbl (i : Fin (q + 2)) (k : Fin (q + 1)) (l : Fin (q + 1)) : V :=
  cminor E ((R ∘ i.succAbove) ∘ k.succAbove) ((C ∘ Fin.succ) ∘ l.succAbove) (x - 1 - 1) (f (C l.succ))
end Key
abbrev minorOp {m : ℕ} (X : GMod (m + 1)) (y : ℂ) : Module.End ℂ (Fin (m + 1) → X.V) :=
  Hk.minorOp X y
end GlobalTheory.CompanionTheory.RgExhHecke


