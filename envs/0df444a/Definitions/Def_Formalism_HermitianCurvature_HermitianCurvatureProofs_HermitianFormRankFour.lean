-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormRankFour
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormRankFour
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:57:10.209228+00:00
-- url     : https://prove2.me/theorems/6e5b0623-09ed-494a-8749-7ee5f2cadde6
-- title:
--   Hermitian Form Rank Four
-- statement:
--   Definitions and structural lemmas for Hermitian Form Rank Four, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormRankFour.lean

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD
namespace HermitianFormRankFour
section L2
open scoped Matrix.Norms.L2Operator
end L2
section Core
variable {N K J : Type} [Fintype N] [Fintype K] [Fintype J] [DecidableEq N] [DecidableEq K] [DecidableEq J]
variable {V : Matrix N K ℂ} {C : Matrix N J ℂ} {Vd : Matrix K N ℂ} {Cd : Matrix J N ℂ}
def colM (U : J → N → ℂ) : Matrix N J ℂ := Matrix.of fun p j => U j p
end Core
section Geo
variable {k r : ℕ}
abbrev JJ (r : ℕ) := Fin r ⊕ (Fin r ⊕ Unit)
def cvec (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : JJ r → Fin (2 * r + k + 1) → ℂ
  | Sum.inl a => bvec (eI k r a)
  | Sum.inr (Sum.inl a) => bvec (esI k r a)
  | Sum.inr (Sum.inr _) => z
def cvec' (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : JJ r → Fin (2 * r + k + 1) → ℂ
  | Sum.inl a => bvec (esI k r a)
  | Sum.inr (Sum.inl a) => bvec (eI k r a)
  | Sum.inr (Sum.inr _) => (star (herm (Hpk k r) z z))⁻¹ • z
end Geo
end HermitianFormRankFour
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P


