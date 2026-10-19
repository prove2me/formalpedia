-- Prove2me | Definitions.Def_OAI_GroupTheory_Hyperbolic_RePairing
-- name    : OAI_GroupTheory_Hyperbolic_RePairing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T06:41:14.193113+00:00
-- url     : https://prove2.me/theorems/ba45426d-1608-4afd-be5c-c7be054c9ae6
-- title:
--   The two-triangle dipole map and boundary cycles
-- statement:
--   Small combinatorial maps and the notion of a boundary cycle.
--
--   1. **Cycle counts commute.** For permutations $f,g$ of a finite set, $\mathrm{cyc}(fg)=\mathrm{cyc}(gf)$, since $g$ conjugates one into the other.
--   2. **The dipole.** On the darts $\{0,\dots,5\}$, the face permutation is the product of the two $3$-cycles $(0\,1\,2)(3\,4\,5)$, so it has two cycles. The reverse involution is
--   $$
--   (0\,3)(1\,5)(2\,4),
--   $$
--   which pairs the darts of two oppositely oriented triangles glued along their three edges.
--   3. **Boundaries.** A list $l$ of darts is a boundary of a permutation $f$ if it has no repetitions and $f$ acts on its entries as the cyclic shift of the list:
--   $$
--   f(a)=\mathrm{next}_l(a)\qquad(a\in l).
--   $$
--   The empty list is a boundary; boundaries are preserved by rotation, and the support of $l$ is $f$-invariant. The entries are darts, not necessarily distinct vertices or edges.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/RePairing.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/RePairing.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TorsionFreeHyperbolic mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity

namespace OAI

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

theorem cycleCount_mul_comm (f g : Perm A) : cycleCount (f*g) = cycleCount (g*f) :=
  cycleCount_intertwine (f*g) (g*f) g (fun _ => rfl)

end Release075.PermCycles

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

/-- Two oppositely oriented triangular faces. -/
noncomputable def dipoleFace : Perm (Fin 6) :=
  Equiv.swap 0 2 * Equiv.swap 0 1 * Equiv.swap 3 5 * Equiv.swap 3 4

@[simp] theorem dipoleFace_zero : dipoleFace 0 = 1 := by norm_num [dipoleFace,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
@[simp] theorem dipoleFace_one : dipoleFace 1 = 2 := by norm_num [dipoleFace,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
@[simp] theorem dipoleFace_two : dipoleFace 2 = 0 := by norm_num [dipoleFace,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
@[simp] theorem dipoleFace_three : dipoleFace 3 = 4 := by norm_num [dipoleFace,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
@[simp] theorem dipoleFace_four : dipoleFace 4 = 5 := by norm_num [dipoleFace,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
@[simp] theorem dipoleFace_five : dipoleFace 5 = 3 := by norm_num [dipoleFace,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]

noncomputable def dipoleReverse : Perm (Fin 6) :=
  Equiv.swap 0 3 * Equiv.swap 1 5 * Equiv.swap 2 4

@[simp] theorem dipoleReverse_zero : dipoleReverse 0 = 3 := by norm_num [dipoleReverse,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
@[simp] theorem dipoleReverse_one : dipoleReverse 1 = 5 := by norm_num [dipoleReverse,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
@[simp] theorem dipoleReverse_two : dipoleReverse 2 = 4 := by norm_num [dipoleReverse,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
@[simp] theorem dipoleReverse_three : dipoleReverse 3 = 0 := by norm_num [dipoleReverse,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
@[simp] theorem dipoleReverse_four : dipoleReverse 4 = 2 := by norm_num [dipoleReverse,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
@[simp] theorem dipoleReverse_five : dipoleReverse 5 = 1 := by norm_num [dipoleReverse,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]

theorem dipoleFace_count : cycleCount dipoleFace = 2 := by
  have h := card_eq_mul_cycles dipoleFace 3 (fun a => orbit_card_three dipoleFace a
    (by fin_cases a <;> norm_num [pow_succ',Perm.mul_apply,dipoleFace,Equiv.swap_apply_def,Fin.ext_iff])
    (by fin_cases a <;> norm_num [dipoleFace,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]))
  have hh : (6:ℕ) = 3 * cycleCount dipoleFace := by
    simpa only [Fintype.card_fin,cycleCount,Nat.card_eq_fintype_card] using h
  omega

end Release075.PermCycles

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A B : Type*} [Fintype A] [Fintype B]

end Release075.PermCycles

namespace Release075
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*}

/-- A specified exterior cycle, including the empty boundary. Its entries are
incidences (darts), not necessarily distinct vertices or geometric edges. -/
def IsBoundary (f : Perm A) (l : List A) : Prop :=
  l.Nodup ∧ ∀ a ∈ l, f a = l.formPerm a

theorem IsBoundary.mem_iff {f : Perm A} {l : List A} (h : IsBoundary f l) (a : A) :
    f a ∈ l ↔ a ∈ l := by
  constructor
  · intro ha
    let b := l.formPerm.symm (f a)
    have hb : b ∈ l := by
      apply List.mem_of_formPerm_apply_mem (l := l)
      simpa only [b,Equiv.apply_symm_apply] using ha
    have he : f b = f a := by rw [h.2 b hb]; exact l.formPerm.apply_symm_apply _
    rwa [f.injective he] at hb
  · intro ha
    rw [h.2 a ha]
    exact List.formPerm_apply_mem_of_mem ha

theorem formPerm_embedding {B : Type*} (e : A ↪ B) (l : List A) (a : A) :
    (l.map e).formPerm (e a) = e (l.formPerm a) := by
  induction l using List.twoStepInduction with
  | nil => rfl
  | singleton x => rfl
  | cons_cons x y xs _ ih =>
    change Equiv.swap (e x) (e y) (((y::xs).map e).formPerm (e a)) =
      e (Equiv.swap x y ((y::xs).formPerm a))
    rw [ih y,e.injective.swap_apply]

theorem IsBoundary.rotate {f : Perm A} {l : List A} (h : IsBoundary f l) (n : ℕ) :
    IsBoundary f (l.rotate n) := by
  refine ⟨List.nodup_rotate.mpr h.1,?_⟩
  intro a ha
  rw [List.formPerm_rotate l h.1 n]
  exact h.2 a (List.mem_rotate.mp ha)

end Release075

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

end Release075.PermCycles

end OAI


