-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_Divisibility_FramesLemmas
-- name    : Formalism_LocalToGlobal_Divisibility_FramesLemmas
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:16:19.313728+00:00
-- url     : https://prove2.me/theorems/6b193e03-2ef8-49ce-b27a-d454b821c869
-- title:
--   Frames Lemmas
-- statement:
--   Definitions and structural lemmas for Frames Lemmas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/FramesLemmas.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
namespace Formalism.L2.DIV
open Formalism.DivisionValues
section SlopeTestRemainingChoices
end SlopeTestRemainingChoices
section Weight
variable {K : Type} [Field K] [NumberField K] {n : ℕ} {Ix : Type} [Fintype Ix]
end Weight
section Instances
variable (K : Type) [Field K] [NumberField K] [StarRing K]
def sumP : Matrix (Fin 1) (Fin 2) K := Matrix.of fun _ _ => 1
def diagE : Matrix (Fin 2) (Fin 1) K := Matrix.of fun _ _ => 1
end Instances
end Formalism.L2.DIV


