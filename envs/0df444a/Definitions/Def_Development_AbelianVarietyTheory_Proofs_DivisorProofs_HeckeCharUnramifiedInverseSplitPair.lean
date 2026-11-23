-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeCharUnramifiedInverseSplitPair
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeCharUnramifiedInverseSplitPair
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:07:17.963179+00:00
-- url     : https://prove2.me/theorems/3c81a157-e3cd-4883-807f-55a51add4cc7
-- title:
--   Hecke Char Unramified Inverse Split Pair
-- statement:
--   Definitions and structural lemmas for Hecke Char Unramified Inverse Split Pair, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeCharUnramifiedInverseSplitPair.lean

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitsInCMFieldTwoPrimesDegreeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
namespace GlobalTheory.CMVal.Euler.SplitPair
variable {E : Type} [Field E] [NumberField E]
def unitF (a : OF E) (ha : a ≠ 0) : (maximalRealSubfield E)ˣ :=
  Units.mk0 (a : maximalRealSubfield E) (fun h => ha (RingOfIntegers.ext h))
def locF (P : HeightOneSpectrum (𝓞 E)) (a : OF E) (ha : a ≠ 0) : (P.adicCompletion E)ˣ :=
  Formalism.L2.Host.atFin P (Formalism.L2.Host.upF (maximalRealSubfield E) (unitF a ha))
end GlobalTheory.CMVal.Euler.SplitPair


