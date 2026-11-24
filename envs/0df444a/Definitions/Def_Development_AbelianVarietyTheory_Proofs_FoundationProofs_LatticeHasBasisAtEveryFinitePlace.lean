-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LatticeHasBasisAtEveryFinitePlace
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_LatticeHasBasisAtEveryFinitePlace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:32.11829+00:00
-- url     : https://prove2.me/theorems/68f55e11-99d2-4771-ba83-7c40e85c98fb
-- title:
--   Lattice Has Basis At Every Finite Place
-- statement:
--   Definitions and structural lemmas for Lattice Has Basis At Every Finite Place, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LatticeHasBasisAtEveryFinitePlace.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
namespace GlobalTheory.LatBasisAt
variable {K : Type} [Field K] [NumberField K]
abbrev locRing (w : HeightOneSpectrum (𝓞 K)) : Subalgebra (𝓞 K) K :=
  haveI := w.isPrime
  Localization.subalgebra.ofField K w.asIdeal.primeCompl w.asIdeal.primeCompl_le_nonZeroDivisors
end GlobalTheory.LatBasisAt


