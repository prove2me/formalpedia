-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MvPolynomialEqZeroOfVanishSkewHermitian
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_MvPolynomialEqZeroOfVanishSkewHermitian
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T01:22:27.757782+00:00
-- url     : https://prove2.me/theorems/6ae8ab7b-6612-4f57-a702-2a6c5839f830
-- title:
--   Mv Polynomial Eq Zero Of Vanish Skew Hermitian
-- statement:
--   Definitions and structural lemmas for Mv Polynomial Eq Zero Of Vanish Skew Hermitian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MvPolynomialEqZeroOfVanishSkewHermitian.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField
namespace GlobalTheory.SkewDense
def gen {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} (u v : Fin n) (x : E) : Matrix (Fin n) (Fin n) E :=
  Matrix.single u v x - Matrix.single v u (σ x)
end GlobalTheory.SkewDense


