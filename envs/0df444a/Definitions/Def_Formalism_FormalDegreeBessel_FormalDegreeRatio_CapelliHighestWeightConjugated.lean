-- Prove2me | Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
-- name    : Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T14:34:14.843155+00:00
-- url     : https://prove2.me/theorems/52b12c23-2f7d-431a-9d16-1c769405ce8b
-- title:
--   Capelli Highest Weight Conjugated
-- statement:
--   Definitions and structural lemmas for Capelli Highest Weight Conjugated, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/CapelliHighestWeightConjugated.lean

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
namespace Formalism.QuantumDeterminants
open Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section Transport
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end Transport
section Central
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
def IOHRepr (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (Ealg : Fin n → Fin n → Module.End ℂ (ioS ε E)) : Prop :=
  ∀ (a b : Fin n) (F : Matrix (Fin n) (Fin n) ℂ → E) (x : ioS ε E), IORep F x.1 →
    IORep (Eop a b F) (Ealg a b x).1
variable (ε E) in

def iohE (P Q : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) : Module.End ℂ (ioS ε E) :=
  ∑ c, ∑ d, (P c a * Q b d) • ioE ε E c d
end Central
section Conj
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end Conj
end Formalism.QuantumDeterminants


