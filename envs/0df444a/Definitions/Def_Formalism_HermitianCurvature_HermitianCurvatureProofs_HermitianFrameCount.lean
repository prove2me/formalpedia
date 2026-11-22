-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:26:08.064255+00:00
-- url     : https://prove2.me/theorems/536b611c-e055-4642-8d88-00ab7fe0ed08
-- title:
--   Hermitian Frame Count
-- statement:
--   Definitions and structural lemmas for Hermitian Frame Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.S3x5
open Finset Formalism.FourierDecayAlt.S3
end Formalism.FourierDecayAlt.P.S3x5
namespace Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.S3x5
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.S3x5
open Matrix Polynomial Formalism.FourierDecayAlt.S3
@[reducible] def starRingOfCard (K : Type) [Field K] [Fintype K] (q : ℕ) (hc : Fintype.card K = q ^ 2) :
    StarRing K where
  star x := x ^ q
  star_involutive x := by
    show (x ^ q) ^ q = x
    rw [← pow_mul, ← sq, ← hc, FiniteField.pow_card]
  star_mul x y := by
    show (x * y) ^ q = y ^ q * x ^ q
    rw [mul_pow, mul_comm]
  star_add x y := by
    show (x + y) ^ q = x ^ q + y ^ q
    obtain ⟨p, hp⟩ := CharP.exists K
    obtain ⟨n, hpp, hn⟩ := FiniteField.card K p
    have : Fact p.Prime := ⟨hpp⟩
    have hd : q ∣ p ^ (n : ℕ) := by rw [← hn, hc]; exact dvd_pow_self q (by norm_num)
    obtain ⟨m, -, rfl⟩ := (Nat.dvd_prime_pow hpp).1 hd
    exact add_pow_char_pow x y p m
variable {K : Type} [Field K] [Fintype K]
variable [StarRing K]
end Formalism.FourierDecayAlt.P.S3x5
namespace Formalism.FourierDecayAlt.P.S3x5
open Matrix
variable {K : Type} [Field K] [Fintype K] [StarRing K]
end Formalism.FourierDecayAlt.P.S3x5
namespace Formalism.FourierDecayAlt.P.S3x5
open Matrix
variable {K : Type} [Field K] [Fintype K] [StarRing K]
end Formalism.FourierDecayAlt.P.S3x5
namespace Formalism.FourierDecayAlt.P.S3x5
open Matrix Formalism.FourierDecayAlt.S3
variable {K : Type} [Field K] [Fintype K] [StarRing K]
end Formalism.FourierDecayAlt.P.S3x5
namespace Formalism.FourierDecayAlt.P.S3x5
open Matrix Formalism.FourierDecayAlt.S3
variable {K : Type} [Field K] [Fintype K] [StarRing K]
end Formalism.FourierDecayAlt.P.S3x5
namespace Formalism.FourierDecayAlt.P
open Matrix Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.S3x5
end Formalism.FourierDecayAlt.P


