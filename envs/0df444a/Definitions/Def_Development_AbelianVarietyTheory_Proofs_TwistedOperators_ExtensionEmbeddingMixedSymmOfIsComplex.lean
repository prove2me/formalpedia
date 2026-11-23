-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExtensionEmbeddingMixedSymmOfIsComplex
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExtensionEmbeddingMixedSymmOfIsComplex
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:44.423507+00:00
-- url     : https://prove2.me/theorems/77588492-3cc0-4975-bfda-8fa772a52b33
-- title:
--   Extension Embedding Mixed Symm Of Is Complex
-- statement:
--   Definitions and structural lemmas for Extension Embedding Mixed Symm Of Is Complex, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExtensionEmbeddingMixedSymmOfIsComplex.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HeckeLEntireAndNonzeroAtOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSmoothMulExtensionOfContinuousChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff
open Formalism.L2.Host (HChar)
open GlobalTheory.CMVal (Ideles)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleNorm)
namespace GlobalTheory.HeckeOne
variable (K : Type) [Field K] [NumberField K]
def mixedIdele : (mixedSpace K)ˣ →* Ideles K :=
  Units.map ((MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).comp
    (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.toMonoidHom)
def expScalar (x : ℝ) : (mixedSpace K)ˣ :=
  ⟨algebraMap ℝ _ (Real.exp x), algebraMap ℝ _ (Real.exp (-x)),
    by rw [← map_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, map_one],
    by rw [← map_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, map_one]⟩
variable {K}
end GlobalTheory.HeckeOne


