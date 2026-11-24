-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierInjectiveMatrixSpace
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierInjectiveMatrixSpace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:35.23981+00:00
-- url     : https://prove2.me/theorems/3b37c298-0e06-4312-9baf-a03253ac256f
-- title:
--   Fourier Injective Matrix Space
-- statement:
--   Definitions and structural lemmas for Fourier Injective Matrix Space, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierInjectiveMatrixSpace.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Matrix FourierTransform InnerProductSpace ComplexConjugate
namespace GlobalTheory.CompanionTheory.FourierMat
noncomputable def entries (m n : ℕ) :
    (Fin m → Fin n → ℂ) ≃L[ℝ] EuclideanSpace ℂ (Fin m × Fin n) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun u => WithLp.toLp 2 (fun p => u p.1 p.2)
      invFun := fun x a j => x (a, j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
end GlobalTheory.CompanionTheory.FourierMat


