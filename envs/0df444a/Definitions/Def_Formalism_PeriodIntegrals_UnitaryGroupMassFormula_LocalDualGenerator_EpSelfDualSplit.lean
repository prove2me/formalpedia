-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualSplit
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualSplit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:55:00.257222+00:00
-- url     : https://prove2.me/theorems/4b13f40e-1065-4e98-980e-9e1d127ccae6
-- title:
--   Ep Self Dual Split
-- statement:
--   Definitions and structural lemmas for Ep Self Dual Split, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/EpSelfDualSplit.lean

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
open ValuativeRel Module
namespace PI.LocDualGen.EpS
variable {K : Type} [Field K] {L : Type} [CommRing L] [Algebra K L]
theorem li (e : L) (he : IsIdempotentElem e) (h0 : e ≠ 0) (h1 : e ≠ 1) :
    LinearIndependent K ![e, 1 - e] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hf : IsIdempotentElem (1 - e) := he.one_sub
  have hef : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  have h0' : (1 - e) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hs : s • e = 0 := by
    have := congrArg (· * e) hst
    simp only [add_mul, smul_mul_assoc, he.eq, zero_mul] at this
    rwa [mul_comm (1 - e) e, hef, smul_zero, add_zero] at this
  have ht : t • (1 - e) = 0 := by
    have := congrArg (· * (1 - e)) hst
    simp only [add_mul, smul_mul_assoc, hf.eq, zero_mul, hef, smul_zero, zero_add] at this
    exact this
  exact ⟨(smul_eq_zero.mp hs).resolve_right h0, (smul_eq_zero.mp ht).resolve_right h0'⟩
section V
variable [ValuativeRel K]
end V
variable (hr : finrank K L = 2) (e : L) (he : IsIdempotentElem e) (h0 : e ≠ 0) (h1 : e ≠ 1)
def bas : Basis (Fin 2) K L :=
  basisOfLinearIndependentOfCardEqFinrank (li e he h0 h1) (by simp [hr])
theorem bas0 : bas hr e he h0 h1 0 = e := by simp [bas]
theorem bas1 : bas hr e he h0 h1 1 = 1 - e := by simp [bas]
theorem decomp (z : L) :
    z = (bas hr e he h0 h1).repr z 0 • e + (bas hr e he h0 h1).repr z 1 • (1 - e) := by
  conv_lhs => rw [← (bas hr e he h0 h1).sum_repr z]
  rw [Fin.sum_univ_two, bas0, bas1]
theorem repr_pair (s t : K) :
    (bas hr e he h0 h1).repr (s • e + t • (1 - e)) 0 = s ∧
    (bas hr e he h0 h1).repr (s • e + t • (1 - e)) 1 = t := by
  have : s • e + t • (1 - e) = s • bas hr e he h0 h1 0 + t • bas hr e he h0 h1 1 := by
    rw [bas0, bas1]
  rw [this]
  simp
theorem mul_decomp (z w : L) :
    z * w = ((bas hr e he h0 h1).repr z 0 * (bas hr e he h0 h1).repr w 0) • e +
      ((bas hr e he h0 h1).repr z 1 * (bas hr e he h0 h1).repr w 1) • (1 - e) := by
  have hf : IsIdempotentElem (1 - e) := he.one_sub
  have hef : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  have hfe : (1 - e) * e = 0 := by rw [mul_comm, hef]
  conv_lhs => rw [decomp hr e he h0 h1 z, decomp hr e he h0 h1 w]
  simp only [add_mul, mul_add, smul_mul_smul_comm, he.eq, hf.eq, hef, hfe, smul_zero, add_zero,
    zero_add]
def pr (i : Fin 2) : L →ₐ[K] K :=
  AlgHom.ofLinearMap ((bas hr e he h0 h1).coord i)
    (by
      have : (1 : L) = (1 : K) • e + (1 : K) • (1 - e) := by simp
      rw [Basis.coord_apply, this]
      fin_cases i
      · exact (repr_pair hr e he h0 h1 1 1).1
      · exact (repr_pair hr e he h0 h1 1 1).2)
    (by
      intro z w
      simp only [Basis.coord_apply]
      rw [mul_decomp hr e he h0 h1 z w]
      fin_cases i
      · exact (repr_pair hr e he h0 h1 _ _).1
      · exact (repr_pair hr e he h0 h1 _ _).2)
variable [ValuativeRel K]
end PI.LocDualGen.EpS


