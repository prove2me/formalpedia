-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceTower
-- name    : GroundTheory_PAdicHodge_NormalizedTraceTower
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:49.167592+00:00
-- url     : https://prove2.me/theorems/a32334df-0bea-4eac-9e6b-0cfbbefafb52
-- title:
--   Normalized Trace Tower
-- statement:
--   Definitions and structural lemmas for Normalized Trace Tower, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceTower.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Theorems.Thm_GroundTheory_PAdicHodge_cycl_mono
import Theorems.Thm_GroundTheory_PAdicHodge_finrank_eq_mul_finrank_extendScalars
import Theorems.Thm_GroundTheory_PAdicHodge_finrank_sup_mul_le
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_zero
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.normTrace_zero
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
def cyclotomicLayer (n : ℕ) : IntermediateField ℚ_[p] (PadicAlgCl p) := K ⊔ cycl p n
def cyclotomicLimit : IntermediateField ℚ_[p] (PadicAlgCl p) := ⨆ n, cyclotomicLayer K n
theorem cycl_le_cyclotomicLayer (n : ℕ) : cycl p n ≤ cyclotomicLayer K n := le_sup_right
theorem cyclotomicLayer_sup_cycl {n m : ℕ} (h : n ≤ m) :
    cyclotomicLayer K n ⊔ cycl p m = cyclotomicLayer K m := by
  rw [cyclotomicLayer, cyclotomicLayer, sup_assoc, sup_eq_right.2 (cycl_mono h)]
instance charZero_intermediateField (k : IntermediateField ℚ_[p] (PadicAlgCl p)) : CharZero k :=
  (algebraMap k (PadicAlgCl p)).charZero
variable [FiniteDimensional ℚ_[p] K]
instance finiteDimensional_cyclotomicLayer (n : ℕ) :
    FiniteDimensional ℚ_[p] (cyclotomicLayer K n) := by
  unfold cyclotomicLayer; infer_instance
def relDeg (n : ℕ) : ℕ := finrank (cycl p n) (extendScalars (cycl_le_cyclotomicLayer K n))
theorem finrank_cyclotomicLayer (n : ℕ) :
    finrank ℚ_[p] (cyclotomicLayer K n) = finrank ℚ_[p] (cycl p n) * relDeg K n :=
  finrank_eq_mul_finrank_extendScalars (cycl_le_cyclotomicLayer K n)
theorem relDeg_antitone : Antitone (relDeg K) := by
  intro n m h
  have c := finrank_sup_mul_le (k := cycl p n) (X := cyclotomicLayer K n) (Y := cycl p m)
    (cycl_le_cyclotomicLayer K n) (cycl_mono h)
  rw [cyclotomicLayer_sup_cycl K h, finrank_cyclotomicLayer, finrank_cyclotomicLayer] at c
  have pn : 0 < finrank ℚ_[p] (cycl p n) := Module.finrank_pos
  have pm : 0 < finrank ℚ_[p] (cycl p m) := Module.finrank_pos
  have : finrank ℚ_[p] (cycl p m) * finrank ℚ_[p] (cycl p n) * relDeg K m ≤
      finrank ℚ_[p] (cycl p m) * finrank ℚ_[p] (cycl p n) * relDeg K n := by
    calc _ = finrank ℚ_[p] (cycl p m) * relDeg K m * finrank ℚ_[p] (cycl p n) := by ring
      _ ≤ _ := c
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left this (Nat.mul_pos pm pn)
theorem exists_relDeg_stable : ∃ N, 2 ≤ N ∧ ∀ m, N ≤ m → relDeg K m = relDeg K N := by
  classical
  have hex : ∃ v, ∃ n, relDeg K n = v := ⟨_, 0, rfl⟩
  obtain ⟨n₀, hn₀⟩ := Nat.find_spec hex
  have hmin : ∀ m, relDeg K n₀ ≤ relDeg K m := fun m => hn₀ ▸ Nat.find_min' hex ⟨m, rfl⟩
  refine ⟨max n₀ 2, le_max_right _ _, fun m hm => le_antisymm (relDeg_antitone K hm) ?_⟩
  exact (relDeg_antitone K (le_max_left n₀ 2)).trans (hmin m)
def stableIndex : ℕ := Classical.choose (exists_relDeg_stable K)
theorem finiteDimensional_extendScalars {k E : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : k ≤ E)
    [FiniteDimensional ℚ_[p] E] : FiniteDimensional k (extendScalars h) := by
  apply Module.finite_of_finrank_pos
  have hE : 0 < finrank ℚ_[p] E := Module.finrank_pos
  rw [finrank_eq_mul_finrank_extendScalars h] at hE
  exact Nat.pos_of_ne_zero fun h0 => by simp [h0] at hE
instance finiteDimensional_cyclotomicLayer_cycl (n : ℕ) :
    FiniteDimensional (cycl p n) (extendScalars (cycl_le_cyclotomicLayer K n)) :=
  finiteDimensional_extendScalars _
def traceBasis : Basis (Fin (relDeg K (stableIndex K))) (cycl p (stableIndex K))
    (extendScalars (cycl_le_cyclotomicLayer K (stableIndex K))) :=
  Module.finBasis _ _
def traceDualBasis : Basis (Fin (relDeg K (stableIndex K))) (cycl p (stableIndex K))
    (extendScalars (cycl_le_cyclotomicLayer K (stableIndex K))) :=
  (Algebra.traceForm _ _).dualBasis (traceForm_nondegenerate _ _) (traceBasis K)
def towerVec (i : Fin (relDeg K (stableIndex K))) : PadicAlgCl p := (traceBasis K i : PadicAlgCl p)
def towerDualVec (i : Fin (relDeg K (stableIndex K))) : PadicAlgCl p :=
  (traceDualBasis K i : PadicAlgCl p)
def towerCoeff (m : ℕ) (y : PadicAlgCl p) (i : Fin (relDeg K (stableIndex K))) : PadicAlgCl p :=
  (relDeg K (stableIndex K) : PadicAlgCl p) * normTrace (cycl p m) (y * towerDualVec K i)
section Gamma
variable {n : ℕ} (γ : Gal(PadicAlgCl p/cyclotomicLayer K n))
end Gamma
end
end GroundTheory.PAdicHodge


