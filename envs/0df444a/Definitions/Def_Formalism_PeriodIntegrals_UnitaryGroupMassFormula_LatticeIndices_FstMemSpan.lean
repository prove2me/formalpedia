-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_FstMemSpan
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_FstMemSpan
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:52:54.135123+00:00
-- url     : https://prove2.me/theorems/987c44b7-41cb-4dbb-978e-c39f6749a673
-- title:
--   Fst Mem Span
-- statement:
--   Definitions and structural lemmas for Fst Mem Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/FstMemSpan.lean

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
namespace MassDataIdxSpl
variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (θ : T ≃ₐ[K] K × K) {n : Type}
def pr1 : (n → T) →ₗ[K] (n → K) where
  toFun v i := (θ (v i)).1
  map_add' v w := by funext i; simp
  map_smul' c v := by funext i; simp
def pr2 : (n → T) →ₗ[K] (n → K) where
  toFun v i := (θ (v i)).2
  map_add' v w := by funext i; simp
  map_smul' c v := by funext i; simp
def inj1 : (n → K) →ₗ[K] (n → T) where
  toFun w i := θ.symm (w i, 0)
  map_add' v w := by
    funext i
    simp only [Pi.add_apply]
    rw [← map_add]
    simp
  map_smul' c v := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← map_smul]
    simp
def inj2 : (n → K) →ₗ[K] (n → T) where
  toFun w i := θ.symm (0, w i)
  map_add' v w := by
    funext i
    simp only [Pi.add_apply]
    rw [← map_add]
    simp
  map_smul' c v := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← map_smul]
    simp
variable {ι : Type} (Y : ι → n → T) (s : Set ι)
end MassDataIdxSpl


