-- Prove2me | Definitions.Def_BassTrace
-- name    : BassTrace
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:01.359225+00:00
-- url     : https://prove2.me/theorems/58b6c137-29ca-4aff-bb4d-13fc9da888d0
-- statement:
--   For a group G and an element a of the complex group algebra ℂ[G], classCoefficient(g,a) is the sum of the coefficients of a on elements conjugate to g; classTrace(a) collects these sums into a finitely supported complex-valued function on the conjugacy classes of G. For any ring R, the matrix version of K₀(R) is the free abelian group on finite square idempotent matrices, modulo the relations [e]=[f] whenever rectangular matrices A,B satisfy AB=e and BA=f, and [e⊕f]=[e]+[f] for block diagonal sums. The Hattori–Stallings homomorphism sends the class of an idempotent over ℂ[G] to classTrace of its ordinary matrix trace. Its construction establishes additivity, invariance under exchanging products AB and BA, and compatibility with the defining relations. A second version of K₀(R) uses finitely generated projective right R-modules, represented as left modules over the opposite ring, modulo module isomorphism and additivity under finite direct sums. Such a module is realized as a retract of a finite free module: maps p and i satisfy p∘i=id, and i∘p determines an idempotent matrix over R using transpose and passage from the opposite ring. Retractions can be transported along module isomorphisms and combined for direct sums. The resulting matrix K₀ class is independent of the chosen retraction, invariant under isomorphism, and additive. Consequently there is a well-defined presentation homomorphism from module K₀ to matrix K₀; for ℂ[G], composing it with the matrix trace homomorphism defines the Hattori–Stallings trace on module K₀.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BassTrace.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BassTrace.lean; bytes 353..22499
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.Tactic

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

namespace BassTrace

open scoped Classical

noncomputable def classCoefficient {G : Type*} [Group G]
    (g : G) (a : MonoidAlgebra ℂ G) : ℂ := by
  classical
  exact a.coeff.sum fun h z => if IsConj h g then z else 0

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

def classOf (e : Idempotent R) : Group R := QuotientAddGroup.mk' (relations R) (FreeAbelianGroup.of e)

variable {G : Type*} [_root_.Group G]

instance groupRingRelations_normal : (relations (MonoidAlgebra ℂ G)).Normal := inferInstance

def rawCoefficient (g : G) : FreeAbelianGroup (Idempotent (MonoidAlgebra ℂ G)) →+ ℂ :=
  FreeAbelianGroup.lift (fun e=>classCoefficient g (Matrix.trace e.matrix))

end

variable {G : Type*} [_root_.Group G]

def classTrace (a : MonoidAlgebra ℂ G) : ConjClasses G →₀ ℂ :=
  Finsupp.mapDomain ConjClasses.mk a.coeff

def rawTrace : FreeAbelianGroup (Idempotent (MonoidAlgebra ℂ G)) →+ (ConjClasses G →₀ ℂ) :=
  FreeAbelianGroup.lift (fun e=>classTrace (Matrix.trace e.matrix))

def HattoriStallings : Group (MonoidAlgebra ℂ G) →+ (ConjClasses G →₀ ℂ) := by
  have classCoefficient_zero (g : G) :
      classCoefficient g 0 = 0 := by
    simp [classCoefficient]
  have classCoefficient_single (g h : G) (z : ℂ) :
      classCoefficient g (MonoidAlgebra.single h z) = if IsConj h g then z else 0 := by
    classical
    simp [classCoefficient, Finsupp.sum_single_index]
  have classCoefficient_add (g : G) (a b : MonoidAlgebra ℂ G) :
      classCoefficient g (a + b) = classCoefficient g a + classCoefficient g b := by
    classical
    apply Finsupp.sum_add_index
    · intro h _
      simp
    · intro h _ z w
      split_ifs <;> simp
  have classCoefficient_smul (g : G) (z : ℂ) (a : MonoidAlgebra ℂ G) :
      classCoefficient g (z • a) = z * classCoefficient g a := by
    classical
    unfold classCoefficient
    rw [MonoidAlgebra.coeff_smul, Finsupp.sum_smul_index (fun _ => by simp)]
    rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    split_ifs <;> simp
  have classCoefficient_sum {ι : Type} (g : G) (s : Finset ι)
      (f : ι → MonoidAlgebra ℂ G) :
      classCoefficient g (∑ i ∈ s, f i) = ∑ i ∈ s, classCoefficient g (f i) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp [classCoefficient_zero]
    | @insert a s ha ih => simp [classCoefficient_add, ha, ih]
  have classCoefficient_mul_comm (g : G) (a b : MonoidAlgebra ℂ G) :
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
  have classCoefficient_matrix_mul_comm {ι κ : Type} [Fintype ι] [Fintype κ]
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
  have trace_reindex {α β : Type} [Fintype α] [Fintype β]
      (j : α≃β) (a : Matrix α α (MonoidAlgebra ℂ G)) :
      Matrix.trace (Matrix.reindexRingEquiv (MonoidAlgebra ℂ G) j a)=Matrix.trace a := by
    change (∑i, a (j.symm i) (j.symm i))=∑i,a i i
    exact Equiv.sum_comp j.symm (fun i=>a i i)
  have trace_directSum (e f : Idempotent (MonoidAlgebra ℂ G)) :
      Matrix.trace (directSum e f).matrix=Matrix.trace e.matrix+Matrix.trace f.matrix := by
    rw [directSum,trace_reindex]
    simp only [Matrix.trace,Matrix.diag,Fintype.sum_sum_type,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₂₂]
  have relations_in_kernel (g : G) : relations (MonoidAlgebra ℂ G)≤(rawCoefficient g).ker := by
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
      rw [add_sub_cancel_left, sub_self]
  have classTrace_apply (a : MonoidAlgebra ℂ G) (g : G) :
      classTrace a (ConjClasses.mk g)=classCoefficient g a := by
    unfold classTrace classCoefficient
    simp only [Finsupp.mapDomain,Finsupp.sum_apply,Finsupp.single_apply]
    apply Finset.sum_congr rfl
    intro h hh
    dsimp only
    by_cases hc : IsConj h g
    · rw [ite_eq_left (ConjClasses.mk_eq_mk_iff_isConj.mpr hc), ite_eq_left hc]
    · rw [ite_eq_right (mt ConjClasses.mk_eq_mk_iff_isConj.mp hc), ite_eq_right hc]
  have rawTrace_apply (z : FreeAbelianGroup (Idempotent (MonoidAlgebra ℂ G))) (g : G) :
      rawTrace z (ConjClasses.mk g)=rawCoefficient g z := by
    induction z using FreeAbelianGroup.induction_on with
    | zero => simp only [map_zero,Finsupp.zero_apply]
    | of e =>
      simp only [rawTrace,rawCoefficient,FreeAbelianGroup.lift_apply_of]
      exact classTrace_apply _ g
    | neg e he => simp only [map_neg,Finsupp.neg_apply,he]
    | add x y hx hy => simp only [map_add,Finsupp.add_apply,hx,hy]
  have relations_in_trace_kernel : relations (MonoidAlgebra ℂ G)≤(rawTrace (G := G)).ker := by
    intro z hz
    change rawTrace z=0
    ext c
    obtain ⟨g,rfl⟩ := ConjClasses.mk_surjective c
    rw [rawTrace_apply,Finsupp.zero_apply]
    exact relations_in_kernel g hz
  exact QuotientAddGroup.lift (relations (MonoidAlgebra ℂ G)) rawTrace relations_in_trace_kernel

end K0

namespace RightProjective

open scoped Classical BigOperators

open MulOpposite

section

variable {R : Type*} [Ring R]

instance rightModuleIdentityRingHomInvPair :
    RingHomInvPair (RingHom.id Rᵐᵒᵖ) (RingHom.id Rᵐᵒᵖ) := RingHomInvPair.ids

def unopTranspose {m n : Type*} (a : Matrix m n Rᵐᵒᵖ) : Matrix n m R :=
  fun i j=>unop (a j i)

def rightMatrix {m n : ℕ} (f : (Fin m → Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] (Fin n → Rᵐᵒᵖ)) :
    Matrix (Fin n) (Fin m) R := unopTranspose (LinearMap.toMatrixRight' f)

structure Retraction (R M : Type*) [Ring R] [AddCommGroup M] [Module Rᵐᵒᵖ M] where
  size : ℕ
  proj : (Fin size →Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] M
  inc : M →ₗ[Rᵐᵒᵖ] (Fin size →Rᵐᵒᵖ)
  split : proj.comp inc=LinearMap.id

variable {M N : Type*} [AddCommGroup M] [Module Rᵐᵒᵖ M]
  [AddCommGroup N] [Module Rᵐᵒᵖ N]

def Retraction.idempotent (r : Retraction R M) : K0.Idempotent R := by
  have unopTranspose_mul {l m n : Type} [Fintype m]
      (a : Matrix l m Rᵐᵒᵖ) (b : Matrix m n Rᵐᵒᵖ) :
      unopTranspose (a*b)=unopTranspose b*unopTranspose a := by
    ext i j
    simp only [unopTranspose,Matrix.mul_apply]
    change (opAddEquiv.symm : Rᵐᵒᵖ≃+R) (∑k,a j k*b k i)=_
    rw [map_sum]
    rfl
  have rightMatrix_comp {l m n : ℕ}
      (f : (Fin l →Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] (Fin m →Rᵐᵒᵖ))
      (g : (Fin m →Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] (Fin n →Rᵐᵒᵖ)) :
      rightMatrix (g.comp f)=rightMatrix g*rightMatrix f := by
    simp only [rightMatrix,LinearMap.toMatrixRight'_comp,unopTranspose_mul]
  exact {
    size := r.size
    matrix := rightMatrix (r.inc.comp r.proj)
    idem := by
      rw [←rightMatrix_comp]
      congr 1
      calc (r.inc.comp r.proj).comp (r.inc.comp r.proj) =
          r.inc.comp ((r.proj.comp r.inc).comp r.proj) := by simp only [LinearMap.comp_assoc]
        _ = r.inc.comp r.proj := by rw [r.split,LinearMap.id_comp] }

def Retraction.transport (r : Retraction R M) (u : M≃ₗ[Rᵐᵒᵖ] N) : Retraction R N where
  size := r.size
  proj := u.toLinearMap.comp r.proj
  inc := r.inc.comp u.symm.toLinearMap
  split := by
    calc (u.toLinearMap.comp r.proj).comp (r.inc.comp u.symm.toLinearMap) =
      u.toLinearMap.comp ((r.proj.comp r.inc).comp u.symm.toLinearMap) := by simp only [LinearMap.comp_assoc]
      _ = LinearMap.id := by rw [r.split,LinearMap.id_comp,LinearEquiv.comp_symm]

def freeSplit (n m : ℕ) : (Fin (n+m)→Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] (Fin n→Rᵐᵒᵖ) × (Fin m→Rᵐᵒᵖ) :=
  (LinearEquiv.piCongrLeft' Rᵐᵒᵖ (fun _ : Fin (n+m)=>Rᵐᵒᵖ) finSumFinEquiv.symm).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin m) Rᵐᵒᵖ Rᵐᵒᵖ)

def Retraction.prod (r : Retraction R M) (s : Retraction R N) : Retraction R (M×N) where
  size := r.size+s.size
  proj := (r.proj.prodMap s.proj).comp (freeSplit r.size s.size).toLinearMap
  inc := (freeSplit r.size s.size).symm.toLinearMap.comp (r.inc.prodMap s.inc)
  split := by
    apply LinearMap.ext
    intro x
    change ((r.proj.prodMap s.proj) ((freeSplit r.size s.size)
      ((freeSplit r.size s.size).symm ((r.inc.prodMap s.inc) x))))=x
    rw [LinearEquiv.apply_symm_apply]
    have hr := LinearMap.congr_fun r.split x.1
    have hs := LinearMap.congr_fun s.split x.2
    exact Prod.ext hr hs

end

open scoped Classical

universe u v

structure Object (R : Type u) [Ring R] where
  carrier : Type v
  [addCommGroup : AddCommGroup carrier]
  [module : Module Rᵐᵒᵖ carrier]
  [finite : Module.Finite Rᵐᵒᵖ carrier]
  [projective : Module.Projective Rᵐᵒᵖ carrier]

attribute [instance] Object.addCommGroup Object.module Object.finite Object.projective

variable {R : Type u} [Ring R]

def Object.prod (P Q : Object.{u,v} R) : Object.{u,v} R where
  carrier := P.carrier × Q.carrier

def Object.retraction (P : Object.{u,v} R) : Retraction R P.carrier :=
  Classical.choice (by
    obtain ⟨n, f, g, _, _, h⟩ := Module.Finite.exists_comp_eq_id_of_projective Rᵐᵒᵖ P.carrier
    exact ⟨⟨n, f, g, h⟩⟩)

def Object.presentationClass (P : Object.{u,v} R) : K0.Group R :=
  K0.classOf P.retraction.idempotent

def moduleRelationGenerators (R : Type u) [Ring R] : Set (FreeAbelianGroup (Object.{u,v} R)) :=
  {x | (∃P Q : Object.{u,v} R, Nonempty (P.carrier≃ₗ[Rᵐᵒᵖ] Q.carrier) ∧
    x=FreeAbelianGroup.of P-FreeAbelianGroup.of Q) ∨
    (∃P Q : Object.{u,v} R,
      x=FreeAbelianGroup.of (P.prod Q)-FreeAbelianGroup.of P-FreeAbelianGroup.of Q)}

def moduleRelations (R : Type u) [Ring R] : AddSubgroup (FreeAbelianGroup (Object.{u,v} R)) :=
  AddSubgroup.closure (moduleRelationGenerators R)

abbrev ModuleK0 (R : Type u) [Ring R] :=
  FreeAbelianGroup (Object.{u,v} R) ⧸ moduleRelations R

def rawPresentation : FreeAbelianGroup (Object.{u,v} R) →+ K0.Group R :=
  FreeAbelianGroup.lift Object.presentationClass

def presentation : ModuleK0.{u,v} R →+ K0.Group R := by
  have unopTranspose_mul {l m n : ℕ}
      (a : Matrix (Fin l) (Fin m) Rᵐᵒᵖ) (b : Matrix (Fin m) (Fin n) Rᵐᵒᵖ) :
      unopTranspose (a*b)=unopTranspose b*unopTranspose a := by
    ext i j
    simp only [unopTranspose,Matrix.mul_apply]
    change (opAddEquiv.symm : Rᵐᵒᵖ≃+R) (∑k,a j k*b k i)=_
    rw [map_sum]
    rfl
  have rightMatrix_comp {l m n : ℕ}
      (f : (Fin l →Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] (Fin m →Rᵐᵒᵖ))
      (g : (Fin m →Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] (Fin n →Rᵐᵒᵖ)) :
      rightMatrix (g.comp f)=rightMatrix g*rightMatrix f := by
    simp only [rightMatrix,LinearMap.toMatrixRight'_comp,unopTranspose_mul]
  have classOf_eq_of_rectangular (e f : K0.Idempotent R)
      (a : Matrix (Fin e.size) (Fin f.size) R)
      (b : Matrix (Fin f.size) (Fin e.size) R) (hab : a*b=e.matrix) (hba : b*a=f.matrix) :
      K0.classOf e=K0.classOf f := by
    apply sub_eq_zero.mp
    change (QuotientAddGroup.mk' (K0.relations R)) (FreeAbelianGroup.of e)-
      (QuotientAddGroup.mk' (K0.relations R)) (FreeAbelianGroup.of f)=0
    rw [←map_sub]
    change (QuotientAddGroup.mk (FreeAbelianGroup.of e-FreeAbelianGroup.of f) : K0.Group R)=0
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    exact AddSubgroup.subset_closure (Or.inl ⟨e,f,a,b,hab,hba,rfl⟩)
  have Retraction.class_eq {M : Type v} [AddCommGroup M] [Module Rᵐᵒᵖ M] (r s : Retraction R M) :
      K0.classOf r.idempotent=K0.classOf s.idempotent := by
    apply classOf_eq_of_rectangular _ _
      (rightMatrix (r.inc.comp s.proj)) (rightMatrix (s.inc.comp r.proj))
    · change rightMatrix (r.inc.comp s.proj)*rightMatrix (s.inc.comp r.proj)=
        rightMatrix (r.inc.comp r.proj)
      rw [←rightMatrix_comp]
      congr 1
      calc (r.inc.comp s.proj).comp (s.inc.comp r.proj) =
          r.inc.comp ((s.proj.comp s.inc).comp r.proj) := by simp only [LinearMap.comp_assoc]
        _ = r.inc.comp r.proj := by rw [s.split,LinearMap.id_comp]
    · change rightMatrix (s.inc.comp r.proj)*rightMatrix (r.inc.comp s.proj)=
        rightMatrix (s.inc.comp s.proj)
      rw [←rightMatrix_comp]
      congr 1
      calc (s.inc.comp r.proj).comp (r.inc.comp s.proj) =
          s.inc.comp ((r.proj.comp r.inc).comp s.proj) := by simp only [LinearMap.comp_assoc]
        _ = s.inc.comp s.proj := by rw [r.split,LinearMap.id_comp]
  have Retraction.transport_idempotent {M N : Type v} [AddCommGroup M] [Module Rᵐᵒᵖ M] [AddCommGroup N] [Module Rᵐᵒᵖ N] (r : Retraction R M) (u : M≃ₗ[Rᵐᵒᵖ] N) :
      (r.transport u).idempotent=r.idempotent := by
    dsimp only [Retraction.idempotent]
    congr 1
    change rightMatrix ((r.inc.comp u.symm.toLinearMap).comp (u.toLinearMap.comp r.proj))=
      rightMatrix (r.inc.comp r.proj)
    congr 1
    apply LinearMap.ext
    intro x
    change r.inc (u.symm (u (r.proj x)))=r.inc (r.proj x)
    rw [u.symm_apply_apply]
  have freeSplit_apply_left (n m : ℕ) (v : Fin (n+m)→Rᵐᵒᵖ) (i : Fin n) :
      (freeSplit n m v).1 i=v (finSumFinEquiv (Sum.inl i)) := rfl
  have freeSplit_apply_right (n m : ℕ) (v : Fin (n+m)→Rᵐᵒᵖ) (i : Fin m) :
      (freeSplit n m v).2 i=v (finSumFinEquiv (Sum.inr i)) := rfl
  have freeSplit_symm_left (n m : ℕ) (v : Fin n→Rᵐᵒᵖ) (w : Fin m→Rᵐᵒᵖ) (i : Fin n) :
      (freeSplit n m).symm (v,w) (finSumFinEquiv (Sum.inl i))=v i := by
    have h := congrArg (fun x=>(x.1 : Fin n→Rᵐᵒᵖ) i) ((freeSplit (R := R) n m).apply_symm_apply (v,w))
    exact h
  have freeSplit_symm_right (n m : ℕ) (v : Fin n→Rᵐᵒᵖ) (w : Fin m→Rᵐᵒᵖ) (i : Fin m) :
      (freeSplit n m).symm (v,w) (finSumFinEquiv (Sum.inr i))=w i := by
    have h := congrArg (fun x=>(x.2 : Fin m→Rᵐᵒᵖ) i) ((freeSplit (R := R) n m).apply_symm_apply (v,w))
    exact h
  have freeSplit_single_left (n m : ℕ) (i : Fin n) :
      freeSplit (R := R) n m (Pi.single (finSumFinEquiv (Sum.inl i)) 1)=(Pi.single i 1,0) := by
    apply Prod.ext
    · ext j
      rw [freeSplit_apply_left]
      simp only [Pi.single_apply,Equiv.apply_eq_iff_eq,Sum.inl.injEq]
    · ext j
      rw [freeSplit_apply_right]
      simp only [Pi.single_apply,Equiv.apply_eq_iff_eq,Sum.inr_ne_inl,ite_false,Pi.zero_apply]
  have freeSplit_single_right (n m : ℕ) (i : Fin m) :
      freeSplit (R := R) n m (Pi.single (finSumFinEquiv (Sum.inr i)) 1)=(0,Pi.single i 1) := by
    apply Prod.ext
    · ext j
      rw [freeSplit_apply_left]
      simp only [Pi.single_apply,Equiv.apply_eq_iff_eq,Sum.inl_ne_inr,ite_false,Pi.zero_apply]
    · ext j
      rw [freeSplit_apply_right]
      simp only [Pi.single_apply,Equiv.apply_eq_iff_eq,Sum.inr.injEq]
  have Retraction.prod_matrix {M N : Type v} [AddCommGroup M] [Module Rᵐᵒᵖ M] [AddCommGroup N] [Module Rᵐᵒᵖ N] (r : Retraction R M) (s : Retraction R N) :
      (r.prod s).idempotent.matrix=(K0.directSum r.idempotent s.idempotent).matrix := by
    ext i j
    obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
    change unop ((freeSplit r.size s.size).symm ((r.inc.prodMap s.inc)
      ((r.proj.prodMap s.proj) ((freeSplit r.size s.size)
        (Pi.single (finSumFinEquiv j) 1)))) (finSumFinEquiv i))=
      Matrix.fromBlocks (rightMatrix (r.inc.comp r.proj)) 0 0 (rightMatrix (s.inc.comp s.proj))
        (finSumFinEquiv.symm (finSumFinEquiv i)) (finSumFinEquiv.symm (finSumFinEquiv j))
    simp only [Equiv.symm_apply_apply]
    cases i with | inl i => ?_ | inr i => ?_
    all_goals cases j with | inl j => ?_ | inr j => ?_
    · rw [freeSplit_single_left]
      simp only [LinearMap.prodMap_apply,map_zero,freeSplit_symm_left,Matrix.fromBlocks_apply₁₁]
      rfl
    · rw [freeSplit_single_right]
      simp only [LinearMap.prodMap_apply,map_zero,freeSplit_symm_left,Matrix.fromBlocks_apply₁₂,
        Pi.zero_apply,unop_zero,Matrix.zero_apply]
    · rw [freeSplit_single_left]
      simp only [LinearMap.prodMap_apply,map_zero,freeSplit_symm_right,Matrix.fromBlocks_apply₂₁,
        Pi.zero_apply,unop_zero,Matrix.zero_apply]
    · rw [freeSplit_single_right]
      simp only [LinearMap.prodMap_apply,map_zero,freeSplit_symm_right,Matrix.fromBlocks_apply₂₂]
      rfl
  have Retraction.prod_idempotent {M N : Type v} [AddCommGroup M] [Module Rᵐᵒᵖ M] [AddCommGroup N] [Module Rᵐᵒᵖ N] (r : Retraction R M) (s : Retraction R N) :
      (r.prod s).idempotent=K0.directSum r.idempotent s.idempotent := by
    dsimp only [Retraction.idempotent, K0.directSum]
    congr 1
    exact Retraction.prod_matrix r s
  have classOf_directSum (e f : K0.Idempotent R) :
      K0.classOf (K0.directSum e f)=K0.classOf e+K0.classOf f := by
    apply sub_eq_zero.mp
    change QuotientAddGroup.mk' (K0.relations R) (FreeAbelianGroup.of (K0.directSum e f))-
      (QuotientAddGroup.mk' (K0.relations R) (FreeAbelianGroup.of e)+
      QuotientAddGroup.mk' (K0.relations R) (FreeAbelianGroup.of f))=0
    rw [←map_add,←map_sub]
    change (QuotientAddGroup.mk (FreeAbelianGroup.of (K0.directSum e f)-
      (FreeAbelianGroup.of e+FreeAbelianGroup.of f)) : K0.Group R)=0
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    rw [sub_add_eq_sub_sub]
    exact AddSubgroup.subset_closure (Or.inr ⟨e,f,rfl⟩)
  have Object.presentationClass_eq (P : Object.{u,v} R) (r : Retraction R P.carrier) :
      P.presentationClass=K0.classOf r.idempotent := Retraction.class_eq P.retraction r
  have Object.presentationClass_iso (P Q : Object.{u,v} R)
      (i : P.carrier ≃ₗ[Rᵐᵒᵖ] Q.carrier) : P.presentationClass=Q.presentationClass := by
    rw [Object.presentationClass_eq Q (P.retraction.transport i), Retraction.transport_idempotent]
    rfl
  have Object.presentationClass_prod (P Q : Object.{u,v} R) :
      (P.prod Q).presentationClass=P.presentationClass+Q.presentationClass := by
    calc
      _ = K0.classOf (P.retraction.prod Q.retraction).idempotent :=
        Object.presentationClass_eq (P.prod Q) (P.retraction.prod Q.retraction)
      _ = P.presentationClass+Q.presentationClass := by
        rw [Retraction.prod_idempotent,classOf_directSum]
        rfl
  have moduleRelations_in_kernel : moduleRelations R≤(rawPresentation.{u,v} (R := R)).ker := by
    apply (AddSubgroup.closure_le _).mpr
    intro x hx
    rcases hx with ⟨P,Q,⟨i⟩,rfl⟩ | ⟨P,Q,rfl⟩
    · change rawPresentation (FreeAbelianGroup.of P-FreeAbelianGroup.of Q)=0
      simp only [map_sub,rawPresentation,FreeAbelianGroup.lift_apply_of]
      exact sub_eq_zero.mpr (Object.presentationClass_iso P Q i)
    · change rawPresentation
        (FreeAbelianGroup.of (P.prod Q)-FreeAbelianGroup.of P-FreeAbelianGroup.of Q)=0
      simp only [map_sub,rawPresentation,FreeAbelianGroup.lift_apply_of,Object.presentationClass_prod]
      abel
  exact QuotientAddGroup.lift (moduleRelations R) rawPresentation moduleRelations_in_kernel

variable {G : Type u} [_root_.Group G]

def HattoriStallings : ModuleK0.{u,v} (MonoidAlgebra ℂ G) →+ (ConjClasses G →₀ ℂ) :=
  K0.HattoriStallings.comp presentation



end RightProjective
end BassTrace
end
end OAI


