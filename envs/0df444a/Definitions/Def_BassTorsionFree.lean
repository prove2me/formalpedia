-- Prove2me | Definitions.Def_BassTorsionFree
-- name    : BassTorsionFree
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:01.284889+00:00
-- url     : https://prove2.me/theorems/5ac1f314-eead-4c3b-8832-1e5a5f4949fa
-- statement:
--   For a group G and a finitely supported element a of the complex group algebra ℂ[G], the conjugacy-class coefficient at g is the sum of the coefficients of a over elements conjugate to g. This functional is complex-linear and cyclic: its values on ab and ba agree, as do its values on the matrix traces of AB and BA for compatible rectangular matrices. For any ring R, an idempotent consists of a finite square matrix e with e²=e. The defined presentation of K₀(R) is the free abelian group on these idempotents modulo the relations [e]=[f] whenever rectangular matrices A,B satisfy AB=e and BA=f, and [e⊕f]=[e]+[f], where ⊕ is block direct sum. Matrix trace is invariant under reindexing and additive on direct sums; consequently each conjugacy-class trace descends to an additive complex-valued Hattori–Stallings coefficient on K₀(ℂ[G]). Torsion-freeness is defined to mean that every finite-order element of G is the identity. Augmentation sums all coefficients, while the canonical trace extracts the identity coefficient and the corresponding matrix trace sums these over diagonal entries. Entrywise augmentation respects multiplication and trace. The trace of an idempotent complex matrix equals its rank, so assigning an idempotent over ℂ[G] the rank of its augmented matrix respects the K₀ relations and defines an integer-valued augmentation rank. The identity-class coefficient likewise defines an additive complex-valued trace on K₀. These constructions require no torsion-freeness assumption, and no equality between this trace and augmentation rank is asserted here.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BassTorsionFree.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BassTorsionFree.lean; bytes 16..11850
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-! Traces and augmentation rank on the idempotent presentation of algebraic K₀. -/

namespace BassTrace

open scoped Classical

noncomputable def classCoefficient {G : Type*} [Group G]
    (g : G) (a : MonoidAlgebra ℂ G) : ℂ := by
  classical
  exact a.coeff.sum fun h z => if IsConj h g then z else 0

variable {G : Type*} [Group G]

@[simp] theorem classCoefficient_zero (g : G) :
    classCoefficient g 0 = 0 := by
  simp [classCoefficient]

@[simp] theorem classCoefficient_single (g h : G) (z : ℂ) :
    classCoefficient g (MonoidAlgebra.single h z) = if IsConj h g then z else 0 := by
  classical
  simp [classCoefficient, Finsupp.sum_single_index]

@[simp] theorem classCoefficient_add (g : G) (a b : MonoidAlgebra ℂ G) :
    classCoefficient g (a + b) = classCoefficient g a + classCoefficient g b := by
  classical
  apply Finsupp.sum_add_index
  · intro h _
    simp
  · intro h _ z w
    split_ifs <;> simp

@[simp] theorem classCoefficient_smul (g : G) (z : ℂ) (a : MonoidAlgebra ℂ G) :
    classCoefficient g (z • a) = z * classCoefficient g a := by
  classical
  unfold classCoefficient
  rw [MonoidAlgebra.coeff_smul, Finsupp.sum_smul_index (fun _ => by simp)]
  rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  split_ifs <;> simp

@[simp] theorem classCoefficient_sum {ι : Type*} (g : G) (s : Finset ι)
    (f : ι → MonoidAlgebra ℂ G) :
    classCoefficient g (∑ i ∈ s, f i) = ∑ i ∈ s, classCoefficient g (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

theorem classCoefficient_mul_comm (g : G) (a b : MonoidAlgebra ℂ G) :
    classCoefficient g (a * b) = classCoefficient g (b * a) := by
  induction a using MonoidAlgebra.induction_on with
  | of h =>
      induction b using MonoidAlgebra.induction_on with
      | of k =>
          have hconj : IsConj (h * k) (k * h) := by
            apply isConj_iff.mpr
            exact ⟨k, by simp [mul_assoc]⟩
          have hiff : IsConj (h * k) g ↔ IsConj (k * h) g :=
            ⟨hconj.symm.trans, hconj.trans⟩
          change classCoefficient g (MonoidAlgebra.single h 1 * MonoidAlgebra.single k 1) =
            classCoefficient g (MonoidAlgebra.single k 1 * MonoidAlgebra.single h 1)
          simp only [MonoidAlgebra.single_mul_single, classCoefficient_single, hiff]
      | add b c hb hc => simp only [mul_add, add_mul, classCoefficient_add, hb, hc]
      | smul z b hb => simp only [mul_smul_comm, smul_mul_assoc, classCoefficient_smul, hb]
  | add a c ha hc => simp only [add_mul, mul_add, classCoefficient_add, ha, hc]
  | smul z a ha => simp only [mul_smul_comm, smul_mul_assoc, classCoefficient_smul, ha]

theorem classCoefficient_matrix_mul_comm {ι κ : Type*} [Fintype ι] [Fintype κ]
    (g : G) (a : Matrix ι κ (MonoidAlgebra ℂ G))
    (b : Matrix κ ι (MonoidAlgebra ℂ G)) :
    classCoefficient g (Matrix.trace (a * b)) =
      classCoefficient g (Matrix.trace (b * a)) := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, classCoefficient_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact classCoefficient_mul_comm g _ _

end BassTrace

noncomputable section

namespace BassTrace

open scoped Classical

namespace K0

open scoped Classical BigOperators

section

structure Idempotent (R : Type*) [Ring R] where
  size : ℕ
  matrix : Matrix (Fin size) (Fin size) R
  idem : matrix*matrix=matrix

variable {R : Type*} [Ring R]

def directSum (e f : Idempotent R) : Idempotent R where
  size := e.size+f.size
  matrix := Matrix.reindexRingEquiv R finSumFinEquiv (Matrix.fromBlocks e.matrix 0 0 f.matrix)
  idem := by
    rw [←map_mul,Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add,e.idem,f.idem]

def relationGenerators (R : Type*) [Ring R] : Set (FreeAbelianGroup (Idempotent R)) :=
  {x | (∃e f : Idempotent R,∃a : Matrix (Fin e.size) (Fin f.size) R,
    ∃b : Matrix (Fin f.size) (Fin e.size) R,
    a*b=e.matrix ∧ b*a=f.matrix ∧ x=FreeAbelianGroup.of e-FreeAbelianGroup.of f) ∨
    (∃e f : Idempotent R,x=FreeAbelianGroup.of (directSum e f)-FreeAbelianGroup.of e-FreeAbelianGroup.of f)}

def relations (R : Type*) [Ring R] : AddSubgroup (FreeAbelianGroup (Idempotent R)) :=
  AddSubgroup.closure (relationGenerators R)

instance relations_normal (R : Type*) [Ring R] : (relations R).Normal := inferInstance

abbrev Group (R : Type*) [Ring R] := FreeAbelianGroup (Idempotent R) ⧸ relations R

variable {G : Type*} [_root_.Group G]

instance groupRingRelations_normal : (relations (MonoidAlgebra ℂ G)).Normal := inferInstance

def rawCoefficient (g : G) : FreeAbelianGroup (Idempotent (MonoidAlgebra ℂ G)) →+ ℂ :=
  FreeAbelianGroup.lift (fun e=>classCoefficient g (Matrix.trace e.matrix))

end

end K0

end BassTrace

end

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.K0

section

open scoped Classical BigOperators

variable {R : Type*} [Ring R]

lemma trace_reindex {α β : Type*} [Fintype α] [Fintype β]
    (j : α≃β) (a : Matrix α α R) :
    Matrix.trace (Matrix.reindexRingEquiv R j a)=Matrix.trace a := by
  change (∑i, a (j.symm i) (j.symm i))=∑i,a i i
  exact Equiv.sum_comp j.symm (fun i=>a i i)

lemma trace_directSum (e f : Idempotent R) :
    Matrix.trace (directSum e f).matrix=Matrix.trace e.matrix+Matrix.trace f.matrix := by
  rw [directSum,trace_reindex]
  simp only [Matrix.trace,Matrix.diag,Fintype.sum_sum_type,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₂₂]

variable {G : Type*} [_root_.Group G]

lemma relations_in_kernel (g : G) : relations (MonoidAlgebra ℂ G)≤(rawCoefficient g).ker := by
  apply (AddSubgroup.closure_le _).mpr
  intro x hx
  rcases hx with ⟨e,f,a,b,hab,hba,rfl⟩|⟨e,f,rfl⟩
  · change rawCoefficient g (FreeAbelianGroup.of e-FreeAbelianGroup.of f)=0
    simp only [map_sub,rawCoefficient,FreeAbelianGroup.lift_apply_of]
    apply sub_eq_zero.mpr
    rw [←hab,←hba]
    exact classCoefficient_matrix_mul_comm g a b
  · change rawCoefficient g (FreeAbelianGroup.of (directSum e f)-FreeAbelianGroup.of e-FreeAbelianGroup.of f)=0
    simp only [map_sub,rawCoefficient,FreeAbelianGroup.lift_apply_of,trace_directSum,classCoefficient_add]
    abel

def hsCoefficient (g : G) : Group (MonoidAlgebra ℂ G) →+ ℂ :=
  QuotientAddGroup.lift (relations (MonoidAlgebra ℂ G)) (rawCoefficient g) (relations_in_kernel g)

end

end BassTrace.K0

end

open scoped Classical BigOperators
noncomputable section
namespace TorsionFreeBass

/-- A group is torsion-free when its only finite-order element is the identity.
This is the usual group-theoretic condition, not the stronger unique-roots condition. -/
def TorsionFree (G : Type*) [Group G] : Prop := ∀ g : G, IsOfFinOrder g → g = 1

variable {G : Type*} [Group G]

/-- The sum of coefficients, or augmentation, of the complex group algebra. -/
def augmentation : MonoidAlgebra ℂ G →+* ℂ :=
  (MonoidAlgebra.lift ℂ ℂ G (1 : G →* ℂ)).toRingHom

/-- The canonical trace is the coefficient of the identity. -/
def canonicalTrace (a : MonoidAlgebra ℂ G) : ℂ := a.coeff 1

/-- The matrix trace obtained by applying the canonical trace to each diagonal entry. -/
def matrixTrace {q : ℕ} (e : Matrix (Fin q) (Fin q) (MonoidAlgebra ℂ G)) : ℂ :=
  ∑ i, canonicalTrace (e i i)

/-- Entrywise augmentation. -/
def augmentedMatrix {m n : ℕ} (e : Matrix (Fin m) (Fin n) (MonoidAlgebra ℂ G)) :
    Matrix (Fin m) (Fin n) ℂ := e.map augmentation

lemma augmentedMatrix_mul {m n p : ℕ}
    (a : Matrix (Fin m) (Fin n) (MonoidAlgebra ℂ G))
    (b : Matrix (Fin n) (Fin p) (MonoidAlgebra ℂ G)) :
    augmentedMatrix (a * b) = augmentedMatrix a * augmentedMatrix b := by
  exact Matrix.map_mul

lemma augmentedMatrix_trace {q : ℕ}
    (e : Matrix (Fin q) (Fin q) (MonoidAlgebra ℂ G)) :
    Matrix.trace (augmentedMatrix e) = augmentation (Matrix.trace e) := by
  simp [augmentedMatrix, Matrix.trace, Matrix.diag]

lemma idempotent_matrix_trace_eq_rank {q : ℕ} (a : Matrix (Fin q) (Fin q) ℂ)
    (ha : a * a = a) : Matrix.trace a = (a.rank : ℂ) := by
  have h : IsIdempotentElem a.toLin' := by
    change a.toLin'.comp a.toLin' = a.toLin'
    rw [← Matrix.toLin'_mul, ha]
  rw [← Matrix.trace_toLin'_eq, (LinearMap.IsIdempotentElem.isProj_range _ h).trace]
  rfl

open BassTrace.K0 in
/-- The augmentation rank on the free abelian group of idempotents, before imposing
isomorphism and direct-sum relations. -/
def rawAugmentationRank : FreeAbelianGroup (Idempotent (MonoidAlgebra ℂ G)) →+ ℤ :=
  FreeAbelianGroup.lift (fun e => ((augmentedMatrix e.matrix).rank : ℤ))

lemma rawAugmentationRank_of (e : BassTrace.K0.Idempotent (MonoidAlgebra ℂ G)) :
    ((rawAugmentationRank (FreeAbelianGroup.of e) : ℤ) : ℂ) =
      augmentation (Matrix.trace e.matrix) := by
  change (((augmentedMatrix e.matrix).rank : ℤ) : ℂ) = _
  rw [Int.cast_natCast, ← idempotent_matrix_trace_eq_rank]
  · exact augmentedMatrix_trace _
  · rw [← augmentedMatrix_mul, e.idem]

lemma augmentationRank_relations : BassTrace.K0.relations (MonoidAlgebra ℂ G) ≤
    (rawAugmentationRank (G := G)).ker := by
  apply (AddSubgroup.closure_le _).mpr
  intro x hx
  rcases hx with ⟨e,f,a,b,hab,hba,rfl⟩ | ⟨e,f,rfl⟩
  · change rawAugmentationRank (FreeAbelianGroup.of e - FreeAbelianGroup.of f) = 0
    apply Int.cast_injective (α := ℂ)
    rw [map_sub, Int.cast_sub, rawAugmentationRank_of, rawAugmentationRank_of, Int.cast_zero]
    apply sub_eq_zero.mpr
    rw [← augmentedMatrix_trace, ← augmentedMatrix_trace, ← hab, ← hba,
      augmentedMatrix_mul, augmentedMatrix_mul]
    exact Matrix.trace_mul_comm _ _
  · change rawAugmentationRank (FreeAbelianGroup.of (BassTrace.K0.directSum e f) -
      FreeAbelianGroup.of e - FreeAbelianGroup.of f) = 0
    apply Int.cast_injective (α := ℂ)
    simp only [map_sub, Int.cast_sub, rawAugmentationRank_of, Int.cast_zero,
      BassTrace.K0.trace_directSum, map_add]
    abel

/-- The integer-valued augmentation rank on the usual idempotent presentation of
algebraic K₀: on a generator it is the complex dimension of the augmented image. -/
def augmentationRank : BassTrace.K0.Group (MonoidAlgebra ℂ G) →+ ℤ :=
  QuotientAddGroup.lift (BassTrace.K0.relations (MonoidAlgebra ℂ G))
    rawAugmentationRank augmentationRank_relations

open BassTrace.K0 in
lemma traceK0_relations : relations (MonoidAlgebra ℂ G) ≤ (rawCoefficient (1 : G)).ker := by
  apply (AddSubgroup.closure_le _).mpr
  intro element membership
  rcases membership with
    ⟨idemLeft, idemRight, forward, backward, forward_backward, backward_forward, rfl⟩ |
    ⟨idemLeft, idemRight, rfl⟩
  · change rawCoefficient 1 (FreeAbelianGroup.of idemLeft - FreeAbelianGroup.of idemRight) = 0
    rw [map_sub]
    apply sub_eq_zero.mpr
    simp only [rawCoefficient, FreeAbelianGroup.lift_apply_of]
    rw [← forward_backward, ← backward_forward]
    exact BassTrace.classCoefficient_matrix_mul_comm 1 forward backward
  · change rawCoefficient 1 (FreeAbelianGroup.of (directSum idemLeft idemRight) -
      FreeAbelianGroup.of idemLeft - FreeAbelianGroup.of idemRight) = 0
    rw [map_sub, map_sub]
    simp only [rawCoefficient, FreeAbelianGroup.lift_apply_of]
    rw [trace_directSum, BassTrace.classCoefficient_add, add_sub_cancel_left, sub_self]

/-- Coefficient at the identity class of the Hattori--Stallings trace on K₀. -/
def traceK0 : BassTrace.K0.Group (MonoidAlgebra ℂ G) →+ ℂ :=
  QuotientAddGroup.lift (BassTrace.K0.relations (MonoidAlgebra ℂ G))
    (BassTrace.K0.rawCoefficient 1) traceK0_relations



end TorsionFreeBass
end
end OAI


