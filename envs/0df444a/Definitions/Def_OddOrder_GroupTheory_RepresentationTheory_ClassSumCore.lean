-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassSumCore
-- name    : OddOrder_GroupTheory_RepresentationTheory_ClassSumCore
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:44:22.345337+00:00
-- url     : https://prove2.me/theorems/5fde903b-d12f-4585-a939-c07fbed9311d
-- title:
--   Class sums in a monoid algebra, indexed by conjugacy classes
-- statement:
--   Defines the class sum $\sum_{x\in C}x\in k[G]$ of a conjugacy class $C$ of a finite group, together with the two facts that make it useful: its coefficient at $x$ is the indicator of $x\in C$, and it is central in $k[G]$. This core is shared by the class-sum congruences of Peterfalvi (6.7) (over $\mathbb{C}$) and the class-sum basis of $Z(k[G])$ (over a field).
--
--   The main definition is `classSum`, the class sum of a conjugacy class.
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/ClassSumCore.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/ClassSumCore.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Mathlib_MonoidAlgebra
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Tactic.Group

namespace OddOrder.GroupTheory.CenterClassSum

open scoped MonoidAlgebra

variable {k G : Type*} [CommSemiring k] [Group G] [Fintype G] [DecidableEq (ConjClasses G)]

/-- The **class sum** `classSum C = ∑_{x ∈ C} x ∈ k[G]` of a conjugacy class `C`. -/
noncomputable def classSum (C : ConjClasses G) : MonoidAlgebra k G :=
  ∑ g : G, if ConjClasses.mk g = C then MonoidAlgebra.of k G g else 0

/-- The coefficient of `classSum C` at `x ∈ G` is `1` if `x ∈ C` and `0` otherwise. -/
theorem coeff_classSum (C : ConjClasses G) (x : G) :
    (classSum (k := k) C).coeff x = if ConjClasses.mk x = C then 1 else 0 := by
  classical
  have hsum : (classSum (k := k) C).coeff x
      = ∑ g : G, (if ConjClasses.mk g = C then MonoidAlgebra.of k G g else 0).coeff x := by
    rw [classSum]; exact MonoidAlgebra.coeff_finsetSum _ _ _
  have hzero : ((0 : MonoidAlgebra k G)).coeff x = 0 := rfl
  have hterm : ∀ g : G,
      (if ConjClasses.mk g = C then MonoidAlgebra.of k G g else 0).coeff x
      = if g = x then (if ConjClasses.mk g = C then (1 : k) else 0) else 0 := by
    intro g
    rw [apply_ite (fun f : MonoidAlgebra k G => f.coeff x), MonoidAlgebra.of_apply,
      MonoidAlgebra.coeff_single, Finsupp.single_apply, hzero]
    by_cases hg : g = x
    · rw [if_pos hg, if_pos hg]
    · rw [if_neg hg, if_neg hg, ite_self]
  rw [hsum, Finset.sum_congr rfl (fun g _ => hterm g),
    Finset.sum_ite_eq' Finset.univ x (fun g => if ConjClasses.mk g = C then (1 : k) else 0)]
  simp

/-- Each class sum is central in `k[G]`: `classSum C` commutes with every `of k G h` (conjugation
permutes the class `C`), hence with all of `k[G]` by linearity. -/
theorem classSum_mem_center (C : ConjClasses G) :
    classSum (k := k) C ∈ Subalgebra.center k (MonoidAlgebra k G) := by
  classical
  rw [Subalgebra.mem_center_iff]
  intro a
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | single h r =>
    have hof : (MonoidAlgebra.single h r : MonoidAlgebra k G) = r • MonoidAlgebra.of k G h := by
      rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rw [hof, smul_mul_assoc, mul_smul_comm]
    congr 1
    rw [classSum, Finset.mul_sum, Finset.sum_mul]
    rw [← Equiv.sum_comp (MulAut.conj h).toEquiv
      (fun g => (if ConjClasses.mk g = C then MonoidAlgebra.of k G g else 0) *
        MonoidAlgebra.of k G h)]
    refine Finset.sum_congr rfl fun g _ => ?_
    have hconj : (MulAut.conj h).toEquiv g = h * g * h⁻¹ := by simp [MulAut.conj_apply]
    rw [hconj]
    have hclass : ConjClasses.mk (h * g * h⁻¹) = ConjClasses.mk g :=
      ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨h⁻¹, by group⟩)
    rw [hclass]
    by_cases h0 : ConjClasses.mk g = C
    · simp only [h0, if_true]
      rw [← map_mul, ← map_mul]
      congr 1
      group
    · simp [h0]

end OddOrder.GroupTheory.CenterClassSum


