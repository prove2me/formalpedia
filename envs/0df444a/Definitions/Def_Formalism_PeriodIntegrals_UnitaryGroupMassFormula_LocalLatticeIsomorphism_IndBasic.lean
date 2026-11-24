-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T21:32:01.937864+00:00
-- url     : https://prove2.me/theorems/b9c4dc49-f6db-42c4-9f29-141246f5ade7
-- title:
--   Ind Basic
-- statement:
--   Definitions and structural lemmas for Ind Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/IndBasic.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
namespace PI.KLW.Ind
open PI.KLW
theorem hf_zero_left {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι] (w : ι → K) :
    hf c 0 w = 0 := by
  simp only [hf, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
theorem hf_single_right {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι] [DecidableEq ι]
    (i0 : ι) (v : ι → K) : hf c v (Pi.single i0 1) = v i0 := by
  unfold hf
  rw [Finset.sum_eq_single i0]
  · rw [Pi.single_eq_same, map_one, mul_one]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, map_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
theorem isom_injective {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι]
    (f : (ι → K) →ₗ[K] (ι → K)) (hf' : ∀ v w, hf c (f v) (f w) = hf c v w) :
    Function.Injective f := by
  classical
  intro v w hvw
  funext i
  have h := hf' (v - w) (Pi.single i 1)
  rw [map_sub, hvw, sub_self, hf_zero_left, hf_single_right, Pi.sub_apply] at h
  exact sub_eq_zero.mp h.symm
def mkU {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι]
    (f : (ι → K) →ₗ[K] (ι → K)) (hf' : ∀ v w, hf c (f v) (f w) = hf c v w) :
    (ι → K) ≃ₗ[K] (ι → K) :=
  LinearEquiv.ofInjectiveEndo f (isom_injective c f hf')
end PI.KLW.Ind


