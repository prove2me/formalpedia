-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffDecomp
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffDecomp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:24.68046+00:00
-- url     : https://prove2.me/theorems/62f2c367-171a-4a8d-86ac-46e4f947987d
-- title:
--   Coeff Decomp
-- statement:
--   Definitions and structural lemmas for Coeff Decomp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CoeffDecomp.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_WFrobStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ZmodPrimeSqLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
namespace GlobalTheory.WFrob
variable {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {Tw : ATowerL R₀ p} {K : LAlg R₀}
lemma pow_add_sqz {A : Type*} [CommRing A] (u v : A) (hv : v * v = 0) (n : ℕ) :
    (u + v) ^ (n + 1) = u ^ (n + 1) + ((n : A) + 1) * u ^ n * v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination ((n : A) + 1) * u ^ n * hv
lemma p_ker (wd : WData Tw K) : wd.πW.1 (p : (wd.W : Type)) = 0 := by
  have : (p : (wd.W : Type)) ∈ RingHom.ker wd.πW.1 := by
    rw [wd.ker_πW]; exact Ideal.subset_span rfl
  exact this
lemma π_pmul (wd : WData Tw K) (x : (wd.W : Type)) : wd.πW.1 (p * x) = 0 := by
  rw [map_mul, p_ker, zero_mul]
lemma T_zero (wd : WData Tw K) : wd.T 0 = 0 := by
  have h := wd.witt_add 0 Fin.elim0
  rw [Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_empty] at h
  apply wd.T_kill
  have h2 := congrArg wd.πW.1 h
  rw [map_zero, map_add, π_pmul, add_zero] at h2
  exact h2.symm
lemma πT_add (wd : WData Tw K) (a b : wd.Rb) :
    wd.πW.1 (wd.T (a + b)) = wd.πW.1 (wd.T a) + wd.πW.1 (wd.T b) := by
  have h := wd.witt_add 2 ![a, b]
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at h
  have h2 := congrArg wd.πW.1 h
  rw [map_add, map_add, π_pmul, add_zero] at h2
  simpa using h2.symm
def φW (wd : WData Tw K) : wd.Rb →+* (Tw.R 0 : Type) where
  toFun c := wd.πW.1 (wd.T c)
  map_one' := by rw [map_one, map_one]
  map_mul' a b := by rw [map_mul, map_mul]
  map_zero' := by rw [T_zero, map_zero]
  map_add' := πT_add wd
lemma φW_apply (wd : WData Tw K) (c : wd.Rb) : φW wd c = wd.πW.1 (wd.T c) := rfl
lemma pmul_congr (wd : WData Tw K) (a b : (wd.W : Type)) (h : wd.πW.1 a = wd.πW.1 b) :
    (p : (wd.W : Type)) * a = p * b := by
  have := (wd.ann_p (a - b)).2 (by rw [map_sub, h, sub_self])
  rw [mul_sub, sub_eq_zero] at this
  exact this
lemma pow_p_teich (wd : WData Tw K) (u s : (wd.W : Type)) :
    (u + p * s) ^ p = u ^ p := by
  obtain ⟨k, hk⟩ : ∃ k, p = k + 1 := ⟨p - 1, (Nat.sub_add_cancel (Fact.out : p.Prime).one_le).symm⟩
  have hv : (p * s) * (p * s) = 0 := by
    have : (p : (wd.W : Type)) * p * (s * s) = 0 := by rw [← sq, wd.p_sq, zero_mul]
    linear_combination this
  have := pow_add_sqz u (p * s) hv k
  rw [← hk] at this
  rw [this]
  have hk' : ((k : (wd.W : Type)) + 1) = p := by
    have := congrArg (Nat.cast : ℕ → (wd.W : Type)) hk
    rw [this]; push_cast; ring
  rw [hk']
  have : (p : (wd.W : Type)) * u ^ k * (p * s) = (p : (wd.W : Type)) ^ 2 * (u ^ k * s) := by ring
  rw [this, wd.p_sq, zero_mul, add_zero]
lemma coeff_decomp (wd : WData Tw K) {g : ℕ} (G : MvPolynomial (Fin g) (wd.W : Type))
    (hG : ∀ m, (∃ i, ¬ p ∣ m i) →
      MvPolynomial.coeff m G ∈ Ideal.span {(p : (wd.W : Type))}) (m : Fin g →₀ ℕ) :
    ∃ d : wd.Rb, ∃ e : (wd.W : Type), MvPolynomial.coeff m G = wd.T d + p * e ∧
      (d = 0 ∨ ∀ i, p ∣ m i) := by
  by_cases h : ∃ i, ¬ p ∣ m i
  · obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (hG m h)
    exact ⟨0, e, by rw [T_zero, zero_add, ← he, mul_comm], Or.inl rfl⟩
  · obtain ⟨d, e, he⟩ := wd.decomp (MvPolynomial.coeff m G)
    refine ⟨d, e, he, Or.inr fun i => ?_⟩
    by_contra hi
    exact h ⟨i, hi⟩
lemma teich_term (wd : WData Tw K) {g : ℕ} (m : Fin g →₀ ℕ) (d : wd.Rb)
    (hd : d = 0 ∨ ∀ i, p ∣ m i) (η : Fin g → wd.Rb) (s : Fin g → (wd.W : Type)) :
    wd.T d * ∏ i, (wd.T (η i) + p * s i) ^ m i = wd.T (d * ∏ i, η i ^ m i) := by
  rcases hd with rfl | hd
  · rw [zero_mul, T_zero, zero_mul]
  · rw [map_mul, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    obtain ⟨k, hk⟩ := hd i
    rw [map_pow, hk, pow_mul, pow_p_teich, ← pow_mul]
lemma root_term (wd : WData Tw K) {g : ℕ} (m : Fin g →₀ ℕ) (d : wd.Rb)
    (hd : d = 0 ∨ ∀ i, p ∣ m i) (η : Fin g → wd.Rb) :
    (frobeniusEquiv wd.Rb p).symm (d * ∏ i, η i ^ m i) =
      (frobeniusEquiv wd.Rb p).symm d * ∏ i, η i ^ (m i / p) := by
  rcases hd with rfl | hd
  · rw [zero_mul, map_zero, zero_mul]
  · rw [map_mul, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [RingEquiv.symm_apply_eq, frobeniusEquiv_apply, frobenius_def, ← pow_mul,
      Nat.div_mul_cancel (hd i)]
theorem wFrob :
    (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {Tw : ATowerL R₀ p} {K : LAlg R₀}
      (wd : WData Tw K) (g : ℕ), WFrobStatement wd g) := by
  intro R₀ _ p _ Tw K wd g G hG
  classical
  choose d e hde hd using coeff_decomp wd G hG
  set n := G.support.card with hn
  let μ : Fin n → (Fin g →₀ ℕ) := fun j => (G.support.equivFin.symm j : Fin g →₀ ℕ)
  have hsum : ∀ (f : (Fin g →₀ ℕ) → (wd.W : Type)), ∑ m ∈ G.support, f m = ∑ j, f (μ j) := by
    intro f
    rw [← Finset.sum_coe_sort G.support f]
    exact (Equiv.sum_comp G.support.equivFin.symm (fun x => f x)).symm
  refine ⟨MvPolynomial.eval₂ (Int.castRingHom _)
      (fun j => MvPolynomial.C (φW wd ((frobeniusEquiv wd.Rb p).symm (d (μ j)))) *
        ∏ i, MvPolynomial.X i ^ (μ j i / p)) (wS p n) +
      ∑ j, MvPolynomial.C (wd.πW.1 (e (μ j))) * ∏ i, MvPolynomial.X i ^ (μ j i), ?_⟩
  intro y hy a ha
  choose η s hy' using fun i => wd.decomp (y i)
  have hπy : ∀ i, wd.πW.1 (y i) = φW wd (η i) := fun i => by
    rw [hy' i, map_add, π_pmul, add_zero, φW_apply]
  have hw := wd.witt_add n (fun j => d (μ j) * ∏ i, η i ^ μ j i)
  have hev : MvPolynomial.eval y G = ∑ j, wd.T (d (μ j) * ∏ i, η i ^ μ j i) +
      p * ∑ j, e (μ j) * ∏ i, y i ^ μ j i := by
    rw [MvPolynomial.eval_eq', hsum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hde, add_mul, ← teich_term wd (μ j) (d (μ j)) (hd _) η s, mul_assoc]
    simp only [← hy']
  rw [hw, add_assoc, ← mul_add] at hev
  have h0 : wd.T (∑ j, d (μ j) * ∏ i, η i ^ μ j i) = 0 := by
    apply wd.T_kill
    have h1 : wd.πW.1 (MvPolynomial.eval y G) = 0 := by
      rw [← wd.ker_πW] at hy
      exact hy
    rw [hev, map_add, π_pmul, add_zero] at h1
    exact h1
  rw [hev, h0, zero_add]
  apply pmul_congr
  rw [ha, map_add, map_add, ← φW_apply, MvPolynomial.eval₂_comp_left,
    MvPolynomial.eval₂_comp_left]
  congr 1
  · congr 1
    · exact RingHom.ext_int _ _
    · funext j
      rw [Function.comp_apply, Function.comp_apply, root_term wd (μ j) (d (μ j)) (hd _) η]
      simp only [map_mul, map_prod, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X, hπy]
  · simp only [map_sum, map_mul, map_prod, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X]
example (p : ℕ) [Fact p.Prime] : WFrobStatement (GlobalTheory.WModel.wModel p) 1 := wFrob _ _
end GlobalTheory.WFrob


