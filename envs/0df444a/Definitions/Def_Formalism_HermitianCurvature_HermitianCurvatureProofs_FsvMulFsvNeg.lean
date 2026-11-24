-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FsvMulFsvNeg
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_FsvMulFsvNeg
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T15:05:51.475642+00:00
-- url     : https://prove2.me/theorems/e44914ab-58c4-44b8-9dab-2751e466db4e
-- title:
--   Fsv Mul Fsv Neg
-- statement:
--   Definitions and structural lemmas for Fsv Mul Fsv Neg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FsvMulFsvNeg.lean

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexConjugate ContDiff
open Filter Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
namespace Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
section Leibniz
variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end Leibniz
section Reg
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
end Reg
section PairLemmas
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
end PairLemmas
end Formalism.FourierDecayAlt.P5


