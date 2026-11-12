-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_IdempotentDirectSum
-- name    : OddOrder_GroupTheory_RepresentationTheory_IdempotentDirectSum
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:36.126359+00:00
-- url     : https://prove2.me/theorems/1c86e717-2fcf-46a0-b414-7838923afe05
-- title:
--   Internal direct sum from a complete orthogonal family of idempotent endomorphisms
-- statement:
--   For the kernel-FPF count ($\dagger$) of Peterfalvi (9.1), the module $W=[V,U]$ decomposes into $U$-isotypic components, the ranges of the central idempotent projections of $Z(\bar{\mathbb{F}}_p[U])$. This file proves the needed general fact: a complete orthogonal family of idempotent endomorphisms $\pi:\iota\to\mathrm{End}_R M$ gives an internal direct sum $M=\bigoplus_i\mathrm{range}(\pi_i)$ (`isInternal_range_of_completeOrthogonalIdempotents`). It consists of lemmas only.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 1 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/IdempotentDirectSum.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/IdempotentDirectSum.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.RingTheory.Idempotents
import Mathlib.Algebra.DirectSum.Module

namespace OddOrder.GroupTheory.IdempotentDirectSum

variable {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]

open scoped DirectSum

/-- **Internal direct sum from idempotent endomorphisms.**  A complete orthogonal family of
idempotent endomorphisms `π : ι → Module.End R M` (pairwise `π i ∘ π j = 0`, summing to `id`)
decomposes `M = ⊕_i range (π i)` internally. -/
theorem isInternal_range_of_completeOrthogonalIdempotents
    {π : ι → Module.End R M} (hπ : CompleteOrthogonalIdempotents π) :
    DirectSum.IsInternal (fun i => LinearMap.range (π i)) := by
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · -- independence: `π i` fixes `range (π i)` but kills every other range.
    rw [iSupIndep_def]
    intro i
    rw [Submodule.disjoint_def]
    intro m hmi hmsup
    -- `π i` is the identity on `range (π i)`.
    obtain ⟨a, rfl⟩ := hmi
    have hfix : π i (π i a) = π i a := by
      have h := DFunLike.congr_fun (hπ.idem i) a
      rwa [Module.End.mul_apply] at h
    -- and `π i` annihilates `⨆ j ≠ i, range (π j)`.
    have hker : (⨆ j, ⨆ (_ : j ≠ i), LinearMap.range (π j)) ≤ LinearMap.ker (π i) := by
      refine iSup_le fun j => iSup_le fun hj => ?_
      rintro _ ⟨b, rfl⟩
      rw [LinearMap.mem_ker, ← Module.End.mul_apply, hπ.ortho (Ne.symm hj)]
      rfl
    have hz : π i (π i a) = 0 := LinearMap.mem_ker.mp (hker hmsup)
    rw [hfix] at hz
    exact hz
  · -- completeness: `m = (∑ π i) m = ∑ (π i m)`, each summand in its range.
    rw [eq_top_iff]
    intro m _
    have hsum : (∑ i, π i m) = m := by rw [← LinearMap.sum_apply, hπ.complete]; rfl
    rw [← hsum]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.mem_iSup_of_mem i (LinearMap.mem_range_self (π i) m)

end OddOrder.GroupTheory.IdempotentDirectSum


