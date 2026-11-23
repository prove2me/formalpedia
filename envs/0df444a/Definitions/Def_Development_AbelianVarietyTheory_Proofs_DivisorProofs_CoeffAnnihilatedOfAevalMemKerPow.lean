-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffAnnihilatedOfAevalMemKerPow
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffAnnihilatedOfAevalMemKerPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:27.016475+00:00
-- url     : https://prove2.me/theorems/a4830fdd-5384-4a0a-925a-2df65ed3408e
-- title:
--   Coeff Annihilated Of Aeval Mem Ker Pow
-- statement:
--   Definitions and structural lemmas for Coeff Annihilated Of Aeval Mem Ker Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffAnnihilatedOfAevalMemKerPow.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
namespace GlobalTheory.TriangularityLowCoeff
open MvPolynomial
noncomputable def iterDer {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {d : ℕ}
    (D : Fin d → Derivation R A A) : List (Fin d) → A →ₗ[R] A
  | [] => LinearMap.id
  | i :: L => (iterDer D L) ∘ₗ (D i).toLinearMap
noncomputable def expOf {d : ℕ} (L : List (Fin d)) : Fin d →₀ ℕ :=
  Multiset.toFinsupp (L : Multiset (Fin d))
noncomputable def fac {d : ℕ} : List (Fin d) → (Fin d →₀ ℕ) → ℕ
  | [], _ => 1
  | i :: L, m => ((m + expOf L) i + 1) * fac L m
end GlobalTheory.TriangularityLowCoeff


