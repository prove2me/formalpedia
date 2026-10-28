-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_DirectSumEmbedding_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_DirectSumEmbedding_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:04:34.666822+00:00
-- url     : https://prove2.me/theorems/a9a09b07-47d2-4ba2-8c99-b18eb9d75945
-- title:
--   Direct Sum Embedding — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for direct sum embedding used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
--
--   Include a subfamily by its actual direct-sum generators.
--
--   Restrict a direct sum to the same embedded family.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_DirectSumEmbedding.lean, selected declarations in lines 13–56; source SHA-256 549e959590a16429e9802007a7f498ac2c746f944c5a4000ad779536024c73f6; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.DirectSum.Module

set_option autoImplicit false

namespace LPCA

universe u

variable (R : Type u) [Ring R]
variable {I J : Type u} [DecidableEq I] [DecidableEq J] (A : J → Type u)
variable [∀ j, AddCommGroup (A j)] [∀ j, Module R (A j)]

/-- Include a subfamily by its actual direct-sum generators. -/
noncomputable def directSumAlongEmbedding (e : I ↪ J) :
    DirectSum I (fun i => A (e i)) →ₗ[R] DirectSum J A := by
  classical
  exact DirectSum.toModule R I (DirectSum J A) (fun i => DirectSum.lof R J A (e i))

theorem directSumAlongEmbedding_lof (e : I ↪ J) (i : I) (x : A (e i)) :
    directSumAlongEmbedding R A e
        (DirectSum.lof R I (fun i => A (e i)) i x) =
      DirectSum.lof R J A (e i) x := by
  classical
  simp only [directSumAlongEmbedding, DirectSum.toModule_lof]

/-- Restrict a direct sum to the same embedded family. -/
noncomputable def directSumEmbeddingProjection (e : I ↪ J) :
    DirectSum J A →ₗ[R] DirectSum I (fun i => A (e i)) where
  toFun := DFinsupp.comapDomain e e.injective
  map_add' := DFinsupp.comapDomain_add e e.injective
  map_smul' := DFinsupp.comapDomain_smul e e.injective

theorem directSumEmbeddingProjection_comp (e : I ↪ J) :
    (directSumEmbeddingProjection R A e).comp (directSumAlongEmbedding R A e) =
      LinearMap.id := by
  classical
  apply DirectSum.linearMap_ext
  intro i
  apply LinearMap.ext
  intro x
  change directSumEmbeddingProjection R A e
    (directSumAlongEmbedding R A e (DirectSum.lof R I (fun i => A (e i)) i x)) =
      DirectSum.lof R I (fun i => A (e i)) i x
  rw [directSumAlongEmbedding_lof]
  exact DFinsupp.comapDomain_single e e.injective i x

theorem directSumAlongEmbedding_injective (e : I ↪ J) :
    Function.Injective (directSumAlongEmbedding R A e) := by
  intro x y h
  have hp := congrArg (directSumEmbeddingProjection R A e) h
  have he := directSumEmbeddingProjection_comp R A e
  have hx := congrArg (fun f : DirectSum I (fun i => A (e i)) →ₗ[R]
    DirectSum I (fun i => A (e i)) => f x) he
  have hy := congrArg (fun f : DirectSum I (fun i => A (e i)) →ₗ[R]
    DirectSum I (fun i => A (e i)) => f y) he
  exact hx.symm.trans (hp.trans hy)

end LPCA


