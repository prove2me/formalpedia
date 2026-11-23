-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTuple
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTuple
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:56.18195+00:00
-- url     : https://prove2.me/theorems/ecae5790-24c9-4966-b619-01ae772c4869
-- title:
--   Exists Orth Tuple
-- statement:
--   Definitions and structural lemmas for Exists Orth Tuple, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsOrthTuple.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LinearIndependentOfGramDetNeZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SpanSInduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
def gram (h : V →ₗ⋆[K] V →ₗ[K] K) {n : ℕ} (x : Fin n → V) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => h (x i) (x j)
def spanS (S : Subring K) {n : ℕ} (x : Fin n → V) : Submodule S V :=
  Submodule.span S (Set.range x)
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}
end Formalism.HermitianLattices.Ext.L3.U0


