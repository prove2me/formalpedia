-- Prove2me | Definitions.Def_IndividualStrongInfiniteness
-- name    : IndividualStrongInfiniteness
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:15.071855+00:00
-- url     : https://prove2.me/theorems/6fb9a127-916c-4dc8-83f1-3b70a03e14ee
-- statement:
--   For a non-unital C*-algebra A, ordered by its spectral order (so 0 ≤ x means x is positive), scalarCorner(h) is the 1×1 C*-matrix over A with entry h, and doubleCorner(h) is the 2×2 diagonal C*-matrix diag(h,h). Diagonalization(a,b,c,ε) says there exist s,t in A with ‖s*as − a‖<ε, ‖t*bt − b‖<ε and ‖s*ct‖<ε. UnrestrictedDiagonalization(A) is the proposition that this holds for all positive a,b, all c in A and all ε>0, while StronglyPurelyInfinite(A) is the proposition that for all positive x,y and ε>0, Diagonalization(x², y², xy, ε) holds. The block then builds the stabilization of A: Mat(A,n) denotes n×n C*-matrices over A, pad embeds Mat(A,n) into Mat(A,m) for n ≤ m by placing a matrix in the upper-left corner and zeros elsewhere, giving an isometric, multiplicative, star-preserving linear embedding forming a directed system. Its algebraic direct limit carries the common norm of the stages and is a normed non-unital C*-ring, and its completion, the Stabilization of A, inherits continuous multiplication and involution and is made into a non-unital C*-algebra, with each corner map from Mat(A,n) an isometric star-homomorphism compatible with padding. Finally, CuntzLE(d,v) in the stabilization means there is a sequence r_j with r_j* v r_j converging to d. An element h of A is ProperlyInfinite if the class of diag(h,h) is CuntzLE the class of the 1×1 matrix h, and PropertyP(A) is the defined proposition that every positive h is properly infinite.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/IndividualStrongInfiniteness.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/IndividualStrongInfiniteness.lean; bytes 16..14307
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
local instance positivityOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance positivityStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

def scalarCorner (h : A) : CStarMatrix (Fin 1) (Fin 1) A :=
  CStarMatrix.ofMatrix (fun _ _ => h)

def doubleCorner (h : A) : CStarMatrix (Fin 2) (Fin 2) A :=
  CStarMatrix.ofMatrix (Matrix.diagonal (fun _ => h))

def Diagonalization (a b c : A) (ε : ℝ) : Prop :=
  ∃ s t : A,
    ‖star s * a * s - a‖ < ε ∧
    ‖star t * b * t - b‖ < ε ∧
    ‖star s * c * t‖ < ε

def UnrestrictedDiagonalization (A : Type*) [NonUnitalCStarAlgebra A] : Prop :=
  ∀ a b : A, 0 ≤ a → 0 ≤ b → ∀ c : A, ∀ ε : ℝ, 0 < ε →
    Diagonalization a b c ε

def StronglyPurelyInfinite (A : Type*) [NonUnitalCStarAlgebra A] : Prop :=
  ∀ x y : A, 0 ≤ x → 0 ≤ y → ∀ ε : ℝ, 0 < ε →
    Diagonalization (x * x) (y * y) (x * y) ε

end MainGap

noncomputable section
open Filter
open scoped Topology
namespace MainGap.Stable
variable {A : Type*} [NonUnitalCStarAlgebra A]
local instance positivityOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance positivityStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

abbrev Mat (A : Type*) (n : ℕ) := CStarMatrix (Fin n) (Fin n) A

def pad {n m : ℕ} (_ : n ≤ m) (x : Mat A n) : Mat A m :=
  CStarMatrix.ofMatrix fun i j =>
    if hi : i.val < n then if hj : j.val < n then x ⟨i,hi⟩ ⟨j,hj⟩ else 0 else 0

@[simp] lemma pad_entry {n m : ℕ} (h : n ≤ m) (x : Mat A n) (i j : Fin m) :
    pad h x i j = (if hi : i.val < n then if hj : j.val < n then x ⟨i,hi⟩ ⟨j,hj⟩ else 0 else 0) := rfl

@[simp] lemma pad_apply {n m : ℕ} (h : n ≤ m) (x : Mat A n) (i j : Fin n) :
    pad h x (Fin.castLE h i) (Fin.castLE h j) = x i j := by simp [pad_entry]

lemma sum_pad {n m : ℕ} (h : n ≤ m) {B : Type*} [AddCommMonoid B] (f : Fin n → B) :
    ∑ k : Fin m, (if hk : k.val < n then f ⟨k,hk⟩ else 0) = ∑ k : Fin n, f k := by
  classical
  symm
  apply Finset.sum_bij_ne_zero (fun i _ _ => Fin.castLE h i)
  · simp
  · intro i _ _ j _ _ hij
    exact Fin.ext (congrArg (fun k : Fin m => k.val) hij)
  · intro j _ hj0
    have hj : j.val < n := by
      by_contra hn
      simp [hn] at hj0
    exact ⟨⟨j,hj⟩, Finset.mem_univ _, by simpa [hj] using hj0, rfl⟩
  · intro i _ _
    simp

lemma pad_mul {n m : ℕ} (h : n ≤ m) (x y : Mat A n) :
    pad h (x*y) = pad h x * pad h y := by
  ext i j
  by_cases hi : i.val < n <;> by_cases hj : j.val < n
  · simp only [pad_entry, dite_eq_left hi, dite_eq_left hj,
      CStarMatrix.mul_apply]
    rw [← sum_pad h (fun k => x ⟨i,hi⟩ k * y k ⟨j,hj⟩)]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k.val < n <;> simp [hk]
  · simp [pad_entry, hi, hj, CStarMatrix.mul_apply]
  · simp [pad_entry, hi, CStarMatrix.mul_apply]
  · simp [pad_entry, hi, CStarMatrix.mul_apply]

def padHom {n m : ℕ} (h : n ≤ m) : Mat A n →⋆ₙₐ[ℂ] Mat A m where
  toFun := pad h
  map_zero' := by ext i j; simp [pad_entry]
  map_add' x y := by ext i j; by_cases hi : i.val < n <;> by_cases hj : j.val < n <;> simp [pad_entry, hi, hj]
  map_mul' := pad_mul h
  map_smul' c x := by ext i j; by_cases hi : i.val < n <;> by_cases hj : j.val < n <;> simp [pad_entry, hi, hj]
  map_star' x := by ext i j; by_cases hi : i.val < n <;> by_cases hj : j.val < n <;> simp [pad_entry, hi, hj, CStarMatrix.star_apply]

lemma pad_injective {n m : ℕ} (h : n ≤ m) : Function.Injective (pad (A := A) h) := by
  intro x y hxy
  ext i j
  have hh := congrArg (fun z : Mat A m => z (Fin.castLE h i) (Fin.castLE h j)) hxy
  simpa using hh

lemma norm_pad {n m : ℕ} (h : n ≤ m) (x : Mat A n) : ‖pad h x‖ = ‖x‖ :=
  NonUnitalStarAlgHom.norm_map (padHom h) (pad_injective h) x

lemma pad_self (n : ℕ) (x : Mat A n) : pad le_rfl x = x := by
  ext i j
  simp [pad_entry]

lemma pad_pad {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k) (x : Mat A n) :
    pad h' (pad h x) = pad (h.trans h') x := by
  ext i j
  by_cases hi : i.val < n <;> by_cases hj : j.val < n
  · have hi' : i.val < m := lt_of_lt_of_le hi h
    have hj' : j.val < m := lt_of_lt_of_le hj h
    simp [pad_entry, hi, hj, hi', hj']
  · by_cases hi' : i.val < m <;> by_cases hj' : j.val < m <;> simp [pad_entry, hi, hj, hi', hj']
  · by_cases hi' : i.val < m <;> by_cases hj' : j.val < m <;> simp [pad_entry, hi, hi', hj']
  · by_cases hi' : i.val < m <;> by_cases hj' : j.val < m <;> simp [pad_entry, hi, hi', hj']

instance pad_directedSystem : DirectedSystem (Mat A) (fun _ _ h => padHom h) where
  map_self := fun {_} x => pad_self _ x
  map_map := fun {_ _ _} h h' x => pad_pad h h' x

abbrev Algebraic (A : Type*) [NonUnitalCStarAlgebra A] :=
  DirectLimit (Mat A) (fun _ _ h => padHom h)

local instance matLinear (n m : ℕ) :
    LinearMapClass (Mat A n →⋆ₙₐ[ℂ] Mat A m) ℂ (Mat A n) (Mat A m) where
  map_add f x y := f.map_add x y
  map_smulₛₗ f c x := f.map_smul c x

instance : Module ℂ (Algebraic A) := DirectLimit.instModule

instance : Norm (Algebraic A) where
  norm := DirectLimit.lift _ (fun _ x => ‖x‖) (fun _ _ h x => (norm_pad h x).symm)

@[simp] lemma norm_mk (n : ℕ) (x : Mat A n) :
    ‖(⟦⟨n,x⟩⟧ : Algebraic A)‖ = ‖x‖ := rfl

lemma normedCore : NormedSpace.Core ℂ (Algebraic A) where
  norm_nonneg := DirectLimit.induction _ fun n x => norm_nonneg x
  norm_smul c := DirectLimit.induction _ fun n x => by
    rw [DirectLimit.smul_def, norm_mk, norm_mk, norm_smul]
  norm_triangle := DirectLimit.induction₂ _ fun n x y => by
    rw [DirectLimit.add_def, norm_mk, norm_mk, norm_mk]
    exact norm_add_le x y
  norm_eq_zero_iff := DirectLimit.induction _ fun n x => by
    rw [norm_mk, norm_eq_zero]
    constructor
    · rintro rfl
      exact (DirectLimit.zero_def (f := fun _ _ h => padHom (A := A) h) n).symm
    · intro h
      apply pad_injective (le_rfl : n ≤ n)
      have hi := DirectLimit.mk_injective (fun _ _ h => padHom (A := A) h) (fun _ _ h => pad_injective h) n
      exact congrArg (pad le_rfl) (hi (h.trans (DirectLimit.zero_def (f := fun _ _ h => padHom (A := A) h) n)))

instance : NormedAddCommGroup (Algebraic A) := .ofCore (𝕜 := ℂ) (normedCore (A := A))
instance : NormedSpace ℂ (Algebraic A) := .ofCore (normedCore (A := A))
instance : NonUnitalNormedRing (Algebraic A) where
  dist_eq _ _ := rfl
  norm_mul_le := DirectLimit.induction₂ _ fun n x y => by
    rw [DirectLimit.mul_def, norm_mk, norm_mk, norm_mk]
    exact norm_mul_le x y
instance : CStarRing (Algebraic A) where
  norm_mul_self_le := DirectLimit.induction _ fun n x => by
    rw [DirectLimit.star_def, DirectLimit.mul_def, norm_mk, norm_mk]
    exact CStarRing.norm_mul_self_le x

def cornerAlg (n : ℕ) : Mat A n →⋆ₙₐ[ℂ] Algebraic A where
  __ := DirectLimit.NonUnitalAlgebra.of (Mat A) (fun _ _ h => padHom h) n
  map_star' _ := rfl

@[simp] lemma cornerAlg_apply (n : ℕ) (x : Mat A n) :
    cornerAlg n x = (⟦⟨n,x⟩⟧ : Algebraic A) := rfl

lemma cornerAlg_isometry (n : ℕ) : Isometry (cornerAlg (A := A) n) :=
  AddMonoidHomClass.isometry_of_norm (cornerAlg n) (fun _ => rfl)

abbrev Stabilization (A : Type*) [NonUnitalCStarAlgebra A] := UniformSpace.Completion (Algebraic A)

local instance algebraicTopology : TopologicalSpace (Algebraic A) :=
  (inferInstance : PseudoMetricSpace (Algebraic A)).toUniformSpace.toTopologicalSpace

open UniformSpace
open UniformSpace.Completion

instance : Mul (Stabilization A) :=
  ⟨Function.curry <| (isDenseInducing_coe.prodMap isDenseInducing_coe).extend
    ((↑) ∘ Function.uncurry (· * · : Algebraic A → Algebraic A → Algebraic A))⟩

@[simp, norm_cast] lemma coe_mul_stable (x y : Algebraic A) :
    ((x*y : Algebraic A) : Stabilization A) = (x : Stabilization A) * (y : Stabilization A) :=
  ((isDenseInducing_coe.prodMap isDenseInducing_coe).extend_eq
    ((continuous_coe _).comp continuous_mul) (x,y)).symm

instance : ContinuousMul (Stabilization A) where
  continuous_mul := by
    let m := (AddMonoidHom.mul : Algebraic A →+ Algebraic A →+ Algebraic A).compr₂ toCompl
    have hh : Continuous fun p : Algebraic A × Algebraic A => m p.1 p.2 :=
      (continuous_coe _).comp continuous_mul
    have di : IsDenseInducing (toCompl : Algebraic A → Stabilization A) := isDenseInducing_coe
    exact di.extend_Z_bilin di hh

instance : NonUnitalRing (Stabilization A) where
  __ : AddCommGroup (Stabilization A) := inferInstance
  zero_mul x := Completion.induction_on x (isClosed_eq (by fun_prop) continuous_const)
    fun x => by rw [← coe_zero, ← coe_mul_stable, zero_mul]
  mul_zero x := Completion.induction_on x (isClosed_eq (by fun_prop) continuous_const)
    fun x => by rw [← coe_zero, ← coe_mul_stable, mul_zero]
  mul_assoc x y z := Completion.induction_on₃ x y z
    (isClosed_eq (by fun_prop) (by fun_prop)) fun x y z => by
      rw [← coe_mul_stable, ← coe_mul_stable, ← coe_mul_stable, ← coe_mul_stable, mul_assoc]
  left_distrib x y z := Completion.induction_on₃ x y z
    (isClosed_eq (by fun_prop) (by fun_prop)) fun x y z => by
      rw [← coe_add, ← coe_mul_stable, ← coe_mul_stable, ← coe_mul_stable, ← coe_add, mul_add]
  right_distrib x y z := Completion.induction_on₃ x y z
    (isClosed_eq (by fun_prop) (by fun_prop)) fun x y z => by
      rw [← coe_add, ← coe_mul_stable, ← coe_mul_stable, ← coe_mul_stable, ← coe_add, add_mul]

instance : NonUnitalNormedRing (Stabilization A) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le x y := Completion.induction_on₂ x y
    (isClosed_le (by fun_prop) (by fun_prop)) fun x y => by
      simpa only [← coe_mul_stable, norm_coe] using norm_mul_le x y

instance : Star (Stabilization A) := ⟨Completion.map (star : Algebraic A → Algebraic A)⟩

@[simp, norm_cast] lemma coe_star_stable (x : Algebraic A) :
    ((star x : Algebraic A) : Stabilization A) = star (x : Stabilization A) :=
  (Completion.map_coe star_isometry.uniformContinuous x).symm

instance : ContinuousStar (Stabilization A) where
  continuous_star := Completion.continuous_map

instance : StarRing (Stabilization A) where
  star_involutive x := Completion.induction_on x
    (isClosed_eq (by fun_prop) continuous_id) fun x => by
      rw [← coe_star_stable, ← coe_star_stable, star_star]
  star_add x y := Completion.induction_on₂ x y
    (isClosed_eq (by fun_prop) (by fun_prop)) fun x y => by
      rw [← coe_add, ← coe_star_stable, ← coe_star_stable, ← coe_star_stable, ← coe_add, star_add]
  star_mul x y := Completion.induction_on₂ x y
    (isClosed_eq (by fun_prop) (by fun_prop)) fun x y => by
      rw [← coe_mul_stable, ← coe_star_stable, ← coe_star_stable, ← coe_star_stable,
        ← coe_mul_stable, star_mul]

instance : CStarRing (Stabilization A) where
  norm_mul_self_le x := Completion.induction_on x
    (isClosed_le (by fun_prop) (by fun_prop)) fun x => by
      simpa only [← coe_star_stable, ← coe_mul_stable, norm_coe] using CStarRing.norm_mul_self_le x

instance : IsScalarTower ℂ (Stabilization A) (Stabilization A) where
  smul_assoc c x y := by
    change (c • x) * y = c • (x*y)
    refine Completion.induction_on₂ x y ?_ ?_
    · exact isClosed_eq ((continuous_fst.const_smul c).mul continuous_snd)
        ((continuous_fst.mul continuous_snd).const_smul c)
    · intro x y
      rw [← coe_smul, ← coe_mul_stable, ← coe_mul_stable, ← coe_smul, smul_mul_assoc]

instance : SMulCommClass ℂ (Stabilization A) (Stabilization A) where
  smul_comm c x y := by
    change c • (x*y) = x * (c • y)
    refine Completion.induction_on₂ x y ?_ ?_
    · exact isClosed_eq ((continuous_fst.mul continuous_snd).const_smul c)
        (continuous_fst.mul (continuous_snd.const_smul c))
    · intro x y
      rw [← coe_mul_stable, ← coe_smul, ← coe_smul, ← coe_mul_stable, mul_smul_comm]

instance : StarModule ℂ (Stabilization A) where
  star_smul c x := by
    refine Completion.induction_on x ?_ ?_
    · exact isClosed_eq (continuous_star.comp (continuous_const_smul c))
        (continuous_star.const_smul (star c))
    · intro x
      rw [← coe_smul, ← coe_star_stable, ← coe_star_stable, ← coe_smul, star_smul]

@[instance_reducible] def stabilizationCStarAlgebra : NonUnitalCStarAlgebra (Stabilization A) where

def corner (n : ℕ) : Mat A n →⋆ₙₐ[ℂ] Stabilization A where
  toFun x := (cornerAlg n x : Stabilization A)
  map_zero' := by rw [map_zero, coe_zero]
  map_add' x y := by simp [map_add, coe_add]
  map_mul' x y := by simp [map_mul]
  map_smul' c x := by simp [map_smul, coe_smul]
  map_star' x := by simp [map_star]

@[simp] lemma corner_apply (n : ℕ) (x : Mat A n) :
    corner n x = (cornerAlg n x : Stabilization A) := rfl

lemma norm_corner (n : ℕ) (x : Mat A n) : ‖corner n x‖ = ‖x‖ := by
  rw [corner_apply, norm_coe, cornerAlg_apply, norm_mk]

lemma corner_isometry (n : ℕ) : Isometry (corner (A := A) n) :=
  AddMonoidHomClass.isometry_of_norm (corner n) (norm_corner n)

lemma corner_pad {n m : ℕ} (h : n ≤ m) (x : Mat A n) :
    corner m (pad h x) = corner n x := by
  change ((⟦⟨m,padHom h x⟩⟧ : Algebraic A) : Stabilization A) =
    ((⟦⟨n,x⟩⟧ : Algebraic A) : Stabilization A)
  rw [DirectLimit.mk_apply]

end MainGap.Stable

namespace MainGap.Manuscript
variable {A : Type*} [NonUnitalCStarAlgebra A]
local instance positivityOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance positivityStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

def CuntzLE (d v : Stable.Stabilization A) : Prop :=
  ∃ r : ℕ → Stable.Stabilization A,
    Tendsto (fun j => star (r j) * v * r j) atTop (𝓝 d)

def ProperlyInfinite (h : A) : Prop :=
  CuntzLE ((⟦⟨2, MainGap.doubleCorner h⟩⟧ : Stable.Algebraic A) : Stable.Stabilization A)
    ((⟦⟨1, MainGap.scalarCorner h⟩⟧ : Stable.Algebraic A) : Stable.Stabilization A)

def PropertyP (A : Type*) [NonUnitalCStarAlgebra A] : Prop :=
  ∀ h : A, 0 ≤ h → ProperlyInfinite h



end MainGap.Manuscript
end
end
end OAI


