-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:23.156322+00:00
-- url     : https://prove2.me/theorems/12252dd7-f761-407b-85fb-ed0172e72b82
-- title:
--   Norm Ideal
-- statement:
--   Definitions and structural lemmas for Norm Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIdeal.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace GlobalTheory.NormSheaf
def normForm (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] {m : ℕ} (x : Fin m → L) :
    MvPolynomial (Fin m) K :=
  (∑ i, (X i : MvPolynomial (Fin m) K) •
    (Algebra.leftMulMatrix (Module.finBasis K L) (x i)).map (C : K →+* MvPolynomial (Fin m) K)).det
def normIdeal (A K L B : Type) [CommRing A] [Field K] [Field L] [Algebra A K] [Algebra K L] [FiniteDimensional K L]
    [CommRing B] [Algebra B L] (J : Ideal B) : Ideal A :=
  Ideal.span {a | ∃ (m : ℕ) (g : Fin m → B), (∀ i, g i ∈ J) ∧
    ∃ s, algebraMap A K a = (normForm K L (fun i => algebraMap B L (g i))).coeff s}
end GlobalTheory.NormSheaf


