-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqProdOfMul
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqProdOfMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:24:33.862076+00:00
-- url     : https://prove2.me/theorems/dd66f874-07ee-4215-9b32-4ce657b5b894
-- title:
--   Eq Prod Of Mul
-- statement:
--   Definitions and structural lemmas for Eq Prod Of Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqProdOfMul.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEqStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
namespace GlobalTheory.PolyNorm
noncomputable def ev {r : ℕ} (Φ : MvPolynomial (Fin r) ℚ) {K : Type} [CommRing K] [Algebra ℚ K]
    (F : K[X]) : K :=
  MvPolynomial.aeval (fun i : Fin r => F.coeff i) Φ
noncomputable def gen {r : ℕ} {K : Type} [CommRing K] (f : Fin r → K) : K[X] :=
  ∑ i : Fin r, monomial (i : ℕ) (f i)
section
variable (N : ℤ[X] → ℚ) (Φ : (r : ℕ) → MvPolynomial (Fin r) ℚ)
  (hN : ∀ r (F : ℤ[X]), F.natDegree < r → N F = ev (Φ r) (F.map (Int.castRingHom ℚ)))
include hN
end
end GlobalTheory.PolyNorm


