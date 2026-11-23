-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_NonemptyRepresentations_NonemptyOfAntitone
-- name    : CompanionTheory_HarishChandraModules_NonemptyRepresentations_NonemptyOfAntitone
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:42.912535+00:00
-- url     : https://prove2.me/theorems/288880f6-52d3-407c-b747-7f24912489a8
-- title:
--   Nonempty Of Antitone
-- statement:
--   Definitions and structural lemmas for Nonempty Of Antitone, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/NonemptyRepresentations/NonemptyOfAntitone.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace CompanionTheory.D.Inhab
structure HWRep (k : ℕ) (ν : Fin k → ℤ) where
  I : Type
  [fin : Fintype I]
  [dec : DecidableEq I]
  ρ : Matrix (Fin k) (Fin k) ℂ → Matrix I I ℂ
  map_one : ρ 1 = 1
  map_mul : ∀ A B, ρ (A * B) = ρ A * ρ B
  map_star : ∀ A, ρ Aᴴ = (ρ A)ᴴ
  diff : ∀ A : Fin k → Fin k → ℂ, (Matrix.of A).det ≠ 0 → ∀ i j,
    DifferentiableAt ℂ (fun B : Fin k → Fin k → ℂ => ρ (Matrix.of B) i j) A
  v0 : I → ℂ
  v0_ne : v0 ≠ 0
  hw : ∀ b : Matrix (Fin k) (Fin k) ℂ, b.BlockTriangular id → b.det ≠ 0 →
    ρ b *ᵥ v0 = (∏ a, b a a ^ ν a) • v0
attribute [instance] HWRep.fin HWRep.dec
namespace HWRep
variable {k : ℕ}
theorem differentiable_det : Differentiable ℂ (fun B : Fin k → Fin k → ℂ => (Matrix.of B).det) := by
  simp only [Matrix.det_apply', Matrix.of_apply]
  fun_prop
def detPow (k : ℕ) (m : ℤ) : HWRep k (fun _ => m) where
  I := Unit
  ρ A := Matrix.of fun _ _ => A.det ^ m
  map_one := by ext i j; simp [Matrix.one_apply]
  map_mul A B := by ext i j; simp [Matrix.mul_apply, mul_zpow]
  map_star A := by ext i j; simp [Matrix.det_conjTranspose, Matrix.conjTranspose_apply]
  diff A hA i j := (differentiableAt_zpow.2 (Or.inl hA)).comp A (differentiable_det A)
  v0 := fun _ => 1
  v0_ne := fun h => by simpa using congrFun h ()
  hw b hb _ := by
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.det_of_upperTriangular hb, Finset.prod_zpow]
open Kronecker in

def tensor {ν μ : Fin k → ℤ} (R : HWRep k ν) (S : HWRep k μ) : HWRep k (ν + μ) where
  I := R.I × S.I
  ρ A := R.ρ A ⊗ₖ S.ρ A
  map_one := by rw [R.map_one, S.map_one, Matrix.one_kronecker_one]
  map_mul A B := by rw [R.map_mul, S.map_mul, Matrix.mul_kronecker_mul]
  map_star A := by rw [R.map_star, S.map_star, Matrix.conjTranspose_kronecker]
  diff A hA i j := (R.diff A hA i.1 j.1).mul (S.diff A hA i.2 j.2)
  v0 := fun p => R.v0 p.1 * S.v0 p.2
  v0_ne := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 R.v0_ne
    obtain ⟨j, hj⟩ := Function.ne_iff.1 S.v0_ne
    exact fun h => mul_ne_zero hi hj (congrFun h (i, j))
  hw b hb hd := by
    have hne : ∀ a, b a a ≠ 0 := by
      rw [Matrix.det_of_upperTriangular hb] at hd
      exact fun a => Finset.prod_ne_zero_iff.1 hd a (Finset.mem_univ a)
    ext p
    have h1 := congrFun (R.hw b hb hd) p.1
    have h2 := congrFun (S.hw b hb hd) p.2
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1 h2
    have e : (∏ a, b a a ^ (ν + μ) a) = (∏ a, b a a ^ ν a) * ∏ a, b a a ^ μ a := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun a _ => zpow_add₀ (hne a) _ _
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type, e]
    calc _ = (∑ x, R.ρ b p.1 x * R.v0 x) * ∑ y, S.ρ b p.2 y * S.v0 y := by
          rw [Finset.sum_mul_sum]
          exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
      _ = _ := by rw [h1, h2]; ring
section wedge
variable (p : Fin k → Prop) [DecidablePred p]
def tpow (A : Matrix (Fin k) (Fin k) ℂ) : Matrix ({a // p a} → Fin k) ({a // p a} → Fin k) ℂ :=
  Matrix.of fun I J => ∏ t, A (I t) (J t)
def inc (J : {a // p a} → Fin k) : Matrix {a // p a} {a // p a} ℂ :=
  Matrix.of fun q s => if J s = q.1 then 1 else 0
theorem tpow_mulVec (b : Matrix (Fin k) (Fin k) ℂ) (I : {a // p a} → Fin k) :
    (tpow p b *ᵥ fun J => (inc p J).det) I = (Matrix.of fun q s : {a // p a} => b (I s) q.1).det := by
  simp only [Matrix.mulVec, dotProduct, tpow, inc, Matrix.det_apply', Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_eq_single (fun s => (σ s).1)]
  · simp [mul_comm]
  · intro J _ hJ
    obtain ⟨s, hs⟩ := Function.ne_iff.1 hJ
    rw [Finset.prod_eq_zero (f := fun s => if J s = (σ s).1 then (1 : ℂ) else 0) (Finset.mem_univ s) (if_neg hs)]
    simp
  · simp
def wedge (hp : ∀ a b, a ≤ b → p b → p a) : HWRep k (fun a => if p a then 1 else 0) where
  I := {a // p a} → Fin k
  ρ := tpow p
  map_one := by
    ext I J
    simp only [tpow, Matrix.of_apply, Matrix.one_apply, Finset.prod_boole, funext_iff, Finset.mem_univ, true_imp_iff]
  map_mul A B := by
    ext I J
    simp only [tpow, Matrix.of_apply, Matrix.mul_apply, ← Finset.prod_mul_distrib]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  map_star A := by
    ext I J
    simp [tpow, Matrix.conjTranspose_apply]
  diff A _ I J := by
    simp only [tpow, Matrix.of_apply]
    fun_prop
  v0 := fun J => (inc p J).det
  v0_ne := by
    intro h
    have h1 := congrFun h (fun s => s.1)
    have : inc p (fun s => s.1) = 1 := by
      ext q s
      simp [inc, Matrix.one_apply, Subtype.ext_iff, eq_comm]
    simp [this] at h1
  hw b hb _ := by
    ext I
    rw [tpow_mulVec]
    have e : (Matrix.of fun q s : {a // p a} => b (I s) q.1) =
        (Matrix.of fun q q' : {a // p a} => b q.1 q'.1)ᵀ * inc p I := by
      ext q s
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, inc, mul_ite, mul_one, mul_zero]
      by_cases h : p (I s)
      · rw [Finset.sum_eq_single ⟨I s, h⟩]
        · simp
        · intro q' _ hq'
          exact if_neg fun e => hq' (Subtype.ext e.symm)
        · simp
      · rw [Finset.sum_eq_zero fun (q' : {a // p a}) _ => if_neg fun (e : I s = q'.1) => h (e ▸ q'.2)]
        exact hb (show q.1 < I s from lt_of_not_ge fun hle => h (hp _ _ hle q.2))
    have ht : (Matrix.of fun q q' : {a // p a} => b q.1 q'.1).BlockTriangular id :=
      fun q q' h => hb (show q'.1 < q.1 from h)
    rw [e, Matrix.det_mul, Matrix.det_transpose, Matrix.det_of_upperTriangular ht, Pi.smul_apply, smul_eq_mul]
    congr 1
    simp only [Matrix.of_apply]
    rw [← Finset.prod_subtype (Finset.univ.filter p) (by simp) (fun a => b a a), Finset.prod_filter]
    exact Finset.prod_congr rfl fun a _ => by split_ifs <;> simp
end wedge
end HWRep
end CompanionTheory.D.Inhab


