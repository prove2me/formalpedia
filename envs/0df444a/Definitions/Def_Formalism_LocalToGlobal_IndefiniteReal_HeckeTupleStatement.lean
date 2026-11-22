-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_HeckeTupleStatement
-- name    : Formalism_LocalToGlobal_IndefiniteReal_HeckeTupleStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:15:40.348005+00:00
-- url     : https://prove2.me/theorems/3dd246ed-5e2e-4b3f-9150-eb88bb7144b9
-- title:
--   Hecke Tuple Statement
-- statement:
--   Definitions and structural lemmas for Hecke Tuple Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/HeckeTupleStatement.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.IndefR.HeckeTupleConditions
open NumberField IsDedekindDomain
open Formalism.DivisionValues Formalism.L2.Indef
noncomputable def Atup {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}
    (S : IndefData Df) (j : Bs.J) (t : Bs.Tup) (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  (S.Iw j t w : ℝ) + (S.Iw j t (conjPl w) : ℝ) + (jw (Df.HT j t) w (Df.Tl j t) : ℝ)
def UntwistedOfSupportAtTwistedPlaces : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df : DefSide Bs)
    (S : IndefData Df) (N : IndefNum Bs),
    (∀ w : HeightOneSpectrum (𝓞 K), (∃ j, Atup S j Bs.μ0 w ≠ 0 ∨ N.F0 w j ≠ 0) → S.μ w ≠ Bs.μ0) →
    (∀ w, w ∈ S.Tw ↔ S.μ w ≠ Bs.μ0) →
    S.Untwisted N
end Formalism.IndefR.HeckeTupleConditions


