-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
-- name    : Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:13.638812+00:00
-- url     : https://prove2.me/theorems/ba971c62-6f2f-4ef1-b172-99ea78e85bc0
-- title:
--   Radford Shuffle Polynomial Holds
-- statement:
--   Definitions and structural lemmas for Radford Shuffle Polynomial Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
namespace Shuffle
variable {A : Type}
noncomputable def shuffle : List A → List A → Multiset (List A)
  | [], v => {v}
  | a :: u, [] => {a :: u}
  | a :: u, b :: v =>
      (shuffle u (b :: v)).map (List.cons a) + (shuffle (a :: u) v).map (List.cons b)
@[simp] theorem shuffle_nil_left (v : List A) : shuffle [] v = {v} := by
  rw [shuffle]
@[simp] theorem shuffle_nil_right (u : List A) : shuffle u [] = {u} := by
  cases u <;> rw [shuffle]
theorem shuffle_cons_cons (a b : A) (u v : List A) :
    shuffle (a :: u) (b :: v) =
      (shuffle u (b :: v)).map (List.cons a) + (shuffle (a :: u) v).map (List.cons b) := by
  rw [shuffle]
theorem shuffle_comm : ∀ u v : List A, shuffle u v = shuffle v u
  | [], v => by simp
  | a :: u, [] => by simp
  | a :: u, b :: v => by
      rw [shuffle_cons_cons, shuffle_cons_cons, shuffle_comm u (b :: v), shuffle_comm (a :: u) v,
        add_comm]
theorem bind_singleton_self (s : Multiset (List A)) : s.bind (fun x => {x}) = s := by
  simpa using Multiset.bind_singleton s id
theorem shuffle_assoc : ∀ u v w : List A,
    (shuffle u v).bind (fun x => shuffle x w) = (shuffle v w).bind (fun x => shuffle u x)
  | [], v, w => by simp [bind_singleton_self]
  | a :: u, [], w => by simp
  | a :: u, b :: v, [] => by simp [bind_singleton_self]
  | a :: u, b :: v, c :: w => by
      have h1 := shuffle_assoc u (b :: v) (c :: w)
      have h2 := shuffle_assoc (a :: u) v (c :: w)
      have h3 := shuffle_assoc (a :: u) (b :: v) w
      have e1 : (shuffle (a :: u) (b :: v)).bind (fun x => shuffle x (c :: w)) =
          ((shuffle u (b :: v)).bind (fun x => shuffle x (c :: w))).map (List.cons a) +
          ((shuffle (a :: u) v).bind (fun x => shuffle x (c :: w))).map (List.cons b) +
          ((shuffle (a :: u) (b :: v)).bind (fun x => shuffle x w)).map (List.cons c) := by
        simp only [shuffle_cons_cons a b, Multiset.add_bind, Multiset.bind_map,
          shuffle_cons_cons _ c, Multiset.bind_add, Multiset.map_bind, Multiset.map_add]
        abel
      have e2 : (shuffle (b :: v) (c :: w)).bind (fun x => shuffle (a :: u) x) =
          ((shuffle (b :: v) (c :: w)).bind (fun x => shuffle u x)).map (List.cons a) +
          ((shuffle v (c :: w)).bind (fun x => shuffle (a :: u) x)).map (List.cons b) +
          ((shuffle (b :: v) w).bind (fun x => shuffle (a :: u) x)).map (List.cons c) := by
        simp only [shuffle_cons_cons b c, Multiset.add_bind, Multiset.bind_map,
          shuffle_cons_cons a, Multiset.bind_add, Multiset.map_bind, Multiset.map_add]
        abel
      rw [e1, e2, h1, h2, h3]
termination_by u v w => u.length + v.length + w.length
end Shuffle
open Shuffle
def ShuffleAlgebra (K A : Type) [CommRing K] : Type := List A →₀ K
namespace ShuffleAlgebra
variable (K : Type) [CommRing K] {A : Type}
noncomputable instance : AddCommGroup (ShuffleAlgebra K A) :=
  inferInstanceAs (AddCommGroup (List A →₀ K))
noncomputable instance : Module K (ShuffleAlgebra K A) :=
  inferInstanceAs (Module K (List A →₀ K))
noncomputable def wordBasis (A : Type) : Module.Basis (List A) K (ShuffleAlgebra K A) :=
  (Finsupp.basisSingleOne : Module.Basis (List A) K (List A →₀ K))
noncomputable def word (w : List A) : ShuffleAlgebra K A := wordBasis K A w
theorem wordBasis_apply (w : List A) : wordBasis K A w = word K w := rfl
noncomputable def mulLin : ShuffleAlgebra K A →ₗ[K] ShuffleAlgebra K A →ₗ[K] ShuffleAlgebra K A :=
  (wordBasis K A).constr K fun u => (wordBasis K A).constr K fun v =>
    ((shuffle u v).map (word K)).sum
theorem mulLin_word (u v : List A) :
    mulLin K (word K u) (word K v) = ((shuffle u v).map (word K)).sum := by
  simp only [mulLin, ← wordBasis_apply, Module.Basis.constr_basis]
theorem mulLin_comm (x y : ShuffleAlgebra K A) : mulLin K x y = mulLin K y x := by
  have : mulLin K (A := A) = (mulLin K).flip := by
    refine (wordBasis K A).ext fun u => (wordBasis K A).ext fun v => ?_
    simp only [wordBasis_apply, LinearMap.flip_apply, mulLin_word, shuffle_comm u v]
  conv_lhs => rw [this]
  rfl
theorem mulLin_one (x : ShuffleAlgebra K A) : mulLin K (word K []) x = x := by
  have : mulLin K (word K ([] : List A)) = LinearMap.id := by
    refine (wordBasis K A).ext fun v => ?_
    simp [wordBasis_apply, mulLin_word]
  rw [this]; rfl
theorem mulLin_assoc (x y z : ShuffleAlgebra K A) :
    mulLin K (mulLin K x y) z = mulLin K x (mulLin K y z) := by
  have key : ∀ u v w : List A, mulLin K (mulLin K (word K u) (word K v)) (word K w) =
      mulLin K (word K u) (mulLin K (word K v) (word K w)) := by
    intro u v w
    have h := congrArg (fun s => (Multiset.map (word K) s).sum) (shuffle_assoc u v w)
    simp only [Multiset.map_bind, Multiset.sum_bind] at h
    rw [mulLin_comm, mulLin_word, mulLin_word, map_multiset_sum, map_multiset_sum,
      Multiset.map_map, Multiset.map_map]
    simp only [Function.comp_def, mulLin_word, shuffle_comm w]
    exact h
  have h3 : ∀ u v : List A, mulLin K (mulLin K (word K u) (word K v)) =
      mulLin K (word K u) ∘ₗ mulLin K (word K v) := fun u v =>
    (wordBasis K A).ext fun w => key u v w
  have h2 : ∀ u : List A, ((mulLin K).flip z) ∘ₗ mulLin K (word K u) =
      mulLin K (word K u) ∘ₗ (mulLin K).flip z := fun u =>
    (wordBasis K A).ext fun v => LinearMap.congr_fun (h3 u v) z
  have h1 : ((mulLin K).flip z) ∘ₗ (mulLin K).flip y = (mulLin K).flip (mulLin K y z) :=
    (wordBasis K A).ext fun u => LinearMap.congr_fun (h2 u) y
  exact LinearMap.congr_fun h1 x
noncomputable instance : CommRing (ShuffleAlgebra K A) where
  __ := (inferInstance : AddCommGroup (ShuffleAlgebra K A))
  mul x y := mulLin K x y
  one := word K []
  left_distrib x y z := (mulLin K x).map_add y z
  right_distrib x y z := LinearMap.map_add₂ (mulLin K) x y z
  zero_mul x := LinearMap.map_zero₂ (mulLin K) x
  mul_zero x := (mulLin K x).map_zero
  mul_assoc := mulLin_assoc K
  one_mul := mulLin_one K
  mul_one x := (mulLin_comm K _ _).trans (mulLin_one K x)
  mul_comm := mulLin_comm K
noncomputable instance : Algebra K (ShuffleAlgebra K A) :=
  Algebra.ofModule (fun r x y => LinearMap.map_smul₂ (mulLin K) r x y)
    (fun r x y => (mulLin K x).map_smul r y)
instance [Nontrivial K] : Nontrivial (ShuffleAlgebra K A) :=
  inferInstanceAs (Nontrivial (List A →₀ K))
end ShuffleAlgebra
def IsLyndon {A : Type} [LinearOrder A] (w : List A) : Prop :=
  w ≠ [] ∧ ∀ u v : List A, u ≠ [] → v ≠ [] → w = u ++ v → List.Lex (· < ·) w v
namespace Lyndon
variable {A : Type} [LinearOrder A]
def IsFactors (L : List (List A)) : Prop := (∀ l ∈ L, IsLyndon l) ∧ L.Pairwise (· ≥ ·)
noncomputable def Interleaves : List A → Multiset (List A) → Prop
  | [], S => ∀ u ∈ S, u = []
  | a :: w, S => ∃ u T, S = (a :: u) ::ₘ T ∧ Interleaves w (u ::ₘ T)
noncomputable def shuffleList {A : Type} : List (List A) → Multiset (List A)
  | [] => {[]}
  | u :: L => (shuffleList L).bind (shuffle u)
open ShuffleAlgebra
variable (K : Type) [Field K]
end Lyndon
namespace Published
def RadfordShufflePolynomial : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A : Type) [LinearOrder A],
    Function.Bijective
      (MvPolynomial.aeval (fun l : {w : List A // IsLyndon w} => ShuffleAlgebra.word K l.1) :
        MvPolynomial {w : List A // IsLyndon w} K →ₐ[K] ShuffleAlgebra K A)
end Published
end GlobalTheory


