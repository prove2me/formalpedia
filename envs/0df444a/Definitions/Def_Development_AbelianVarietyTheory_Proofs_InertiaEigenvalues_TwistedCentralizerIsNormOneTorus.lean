-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TwistedCentralizerIsNormOneTorus
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TwistedCentralizerIsNormOneTorus
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:38.251805+00:00
-- url     : https://prove2.me/theorems/64289726-0b0e-4474-9d59-85bb61b219c6
-- title:
--   Twisted Centralizer Is Norm One Torus
-- statement:
--   Definitions and structural lemmas for Twisted Centralizer Is Norm One Torus, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedCentralizerIsNormOneTorus.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Tw Matrix Polynomial
noncomputable section
namespace GlobalTheory.Tw.CentralizerAdjoin
section Dual
variable {n : ℕ} {R : Type} [CommRing R]
def dm (U V : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) (DualNumber R) :=
  Matrix.of fun i j => TrivSqZeroExt.inl (U i j) + TrivSqZeroExt.inr (V i j)
end Dual
end GlobalTheory.Tw.CentralizerAdjoin
namespace GlobalTheory.Tw.CentralizerAdjoin
section Comm
variable {n : ℕ} {R : Type} [CommRing R]
end Comm
end GlobalTheory.Tw.CentralizerAdjoin
namespace GlobalTheory.Tw.CentralizerAdjoin
section Tw
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]
open GlobalTheory.Tw.Model
end Tw
end GlobalTheory.Tw.CentralizerAdjoin
namespace GlobalTheory.Tw.CentralizerAdjoin
section Cent
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]
open GlobalTheory.Tw.Model
end Cent
end GlobalTheory.Tw.CentralizerAdjoin


