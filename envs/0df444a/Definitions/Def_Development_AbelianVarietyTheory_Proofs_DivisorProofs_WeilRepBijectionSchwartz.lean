-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilRepBijectionSchwartz
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilRepBijectionSchwartz
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:52.905301+00:00
-- url     : https://prove2.me/theorems/d4b31835-7bb4-4fc2-b1a7-79704c3267ed
-- title:
--   Weil Rep Bijection Schwartz
-- statement:
--   Definitions and structural lemmas for Weil Rep Bijection Schwartz, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeilRepBijectionSchwartz.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqSmulOfCommuteHeisenbergLinearModelSchwartzBruhStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
namespace GlobalTheory.SchurHeisReindex
variable {k : Type} [Field k] [TopologicalSpace k] {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
noncomputable def eL (k : Type) [Field k] (n : ℕ) (β : Type) [Fintype β] [DecidableEq β] :
    Matrix (Fin n) (Fin (Fintype.card β)) k ≃ₗ[k] Matrix (Fin n) β k :=
  Matrix.reindexLinearEquiv k k (Equiv.refl (Fin n)) (Fintype.equivFin β).symm
theorem eL_apply (C : Matrix (Fin n) (Fin (Fintype.card β)) k) (i : Fin n) (b : β) :
    eL k n β C i b = C i (Fintype.equivFin β b) := by
  simp [eL, reindexLinearEquiv_apply, reindex_apply, submatrix_apply]
theorem eL_symm_apply (D : Matrix (Fin n) β k) (i : Fin n) (j : Fin (Fintype.card β)) :
    (eL k n β).symm D i j = D i ((Fintype.equivFin β).symm j) := by
  simp [eL, reindexLinearEquiv_symm, reindexLinearEquiv_apply, reindex_apply, submatrix_apply]
theorem continuous_eL : Continuous (eL k n β) := by
  refine continuous_pi fun i => continuous_pi fun b => ?_
  simp only [eL_apply]
  exact (continuous_apply _).comp (continuous_apply i)
theorem continuous_eL_symm : Continuous (eL k n β).symm := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [eL_symm_apply]
  exact (continuous_apply _).comp (continuous_apply i)
noncomputable def eH (k : Type) [Field k] [TopologicalSpace k] (n : ℕ) (β : Type) [Fintype β] [DecidableEq β] :
    Matrix (Fin n) (Fin (Fintype.card β)) k ≃ₜ Matrix (Fin n) β k where
  toEquiv := (eL k n β).toEquiv
  continuous_toFun := continuous_eL
  continuous_invFun := continuous_eL_symm
end GlobalTheory.SchurHeisReindex


