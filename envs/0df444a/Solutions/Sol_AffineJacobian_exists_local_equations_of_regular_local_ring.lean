-- Prove2me | solution 1 for AffineJacobian.exists_local_equations_of_regular_local_ring
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-03T18:22:23.679568+00:00
-- url     : https://prove2.me/submissions/4b81f94a-4f82-44a0-bbc8-f7e0c169283d

import Theorems.Thm_RegularLocalConormal_inf_maximalIdeal_sq_eq_mul
import Mathlib

section AffineJacobianBundle0

set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators

namespace AffineJacobian
namespace FirstOrder

open MvPolynomial
variable {K σ : Type*} [Field K] [Fintype σ]

noncomputable def remainder (a : σ → K) (P : MvPolynomial σ K) : MvPolynomial σ K :=
  P - C (eval a P) - ∑ j, C (eval a (pderiv j P)) * (X j - C (a j))

lemma remainder_C (a : σ → K) (c : K) : remainder a (C c) = 0 := by
  simp [remainder]

lemma remainder_add (a : σ → K) (P Q : MvPolynomial σ K) :
    remainder a (P + Q) = remainder a P + remainder a Q := by
  simp only [remainder, map_add, add_mul, Finset.sum_add_distrib]
  ring

lemma remainder_mul_X (a : σ → K) (P : MvPolynomial σ K) (j : σ) :
    remainder a (P * X j) =
      (P - C (eval a P)) * (X j - C (a j)) + C (a j) * remainder a P := by
  classical
  have ht (i : σ) : C (eval a (pderiv i (P * X j))) * (X i - C (a i)) =
      C (a j) * (C (eval a (pderiv i P)) * (X i - C (a i))) +
      if i = j then C (eval a P) * (X j - C (a j)) else 0 := by
    by_cases h : i = j
    · subst i
      simp only [pderiv_mul, pderiv_X_self, map_add, map_mul, eval_X,
        map_one, mul_one, ite_true]
      ring
    · simp only [pderiv_mul, pderiv_X_of_ne (Ne.symm h), map_add, map_mul,
        eval_X, map_zero, mul_zero, add_zero, if_neg h]
      ring
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => ht i)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, ← Finset.mul_sum] at hs
  simp only [remainder, hs, map_mul, eval_X]
  ring

lemma remainder_mem_square (a : σ → K) (P : MvPolynomial σ K) :
    remainder a P ∈ (RingHom.ker (eval a)) ^ 2 := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [remainder_C]
  | add P Q hP hQ => exact remainder_add a P Q ▸ Ideal.add_mem _ hP hQ
  | mul_X P j hP =>
    rw [remainder_mul_X]
    refine Ideal.add_mem _ ?_ (Ideal.mul_mem_left _ _ hP)
    rw [pow_two]
    apply Ideal.mul_mem_mul
    · change eval a (P - C (eval a P)) = 0
      simp
    · change eval a (X j - C (a j)) = 0
      simp

theorem mem_square_of_value_gradient_zero (a : σ → K) (P : MvPolynomial σ K)
    (hP : eval a P = 0) (hdP : ∀ j, eval a (pderiv j P) = 0) :
    P ∈ (RingHom.ker (eval a)) ^ 2 := by
  simpa [remainder, hP, hdP] using remainder_mem_square a P

end FirstOrder
end AffineJacobian

end AffineJacobianBundle0

section AffineJacobianBundle1

set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section

namespace AffineJacobian
namespace Gradient
open MvPolynomial
variable {K σ : Type*} [Field K] [Fintype σ]

def gradient (a : σ → K) : MvPolynomial σ K →ₗ[K] (σ → K) where
  toFun P j := eval a (pderiv j P)
  map_add' P Q := by ext j; simp
  map_smul' c P := by ext j; simp

theorem basis_equations (I : Ideal (MvPolynomial σ K)) (a : σ → K) :
    ∃ (r : ℕ) (P : Fin r → MvPolynomial σ K),
      (∀ i, P i ∈ I) ∧
      Function.Surjective (fun v : σ → K => fun i : Fin r =>
        ∑ j, eval a (pderiv j (P i)) * v j) ∧
      ∀ Q ∈ I, ∃ c : Fin r → K,
        ∀ j, eval a (pderiv j Q) = ∑ i, c i * eval a (pderiv j (P i)) := by
  classical
  let g := (gradient a).comp (I.restrictScalars K).subtype
  let W := LinearMap.range g
  let b := Module.finBasis K W
  have hb (i : Fin (Module.finrank K W)) : ∃ P : I, g P = (b i : σ → K) :=
    (b i).property
  choose P hP using hb
  refine ⟨Module.finrank K W, fun i => P i, fun i => (P i).property, ?_, ?_⟩
  · intro y
    let ψ : Module.Dual K W := b.constr K y
    let φ : Module.Dual K (σ → K) := Subspace.dualLift W ψ
    refine ⟨fun j => φ (Pi.single j 1), ?_⟩
    funext i
    change (∑ j, g (P i) j * φ (Pi.single j 1)) = y i
    rw [hP]
    calc
      _ = φ (∑ j, (b i : σ → K) j • Pi.single j (1 : K)) := by simp
      _ = φ (b i : σ → K) := by congr 1; ext j; simp [Pi.single_apply]
      _ = ψ (b i) := Subspace.dualLift_of_subtype _
      _ = y i := b.constr_basis K y i
  · intro Q hQ
    let w : W := ⟨g ⟨Q, hQ⟩, LinearMap.mem_range_self _ _⟩
    refine ⟨fun i => b.repr w i, fun j => ?_⟩
    change (w : σ → K) j = ∑ i, b.repr w i * g (P i) j
    have h := congrArg (fun z : W => (z : σ → K) j) (b.sum_repr w)
    simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
      Pi.smul_apply, smul_eq_mul, ← hP] using h.symm

end Gradient
end AffineJacobian

end
end AffineJacobianBundle1

section AffineJacobianBundle2

set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators

namespace AffineJacobian
namespace Denominators

theorem clear_finitely_generated_ideal {A : Type*} [CommRing A]
    (I J m : Ideal A) [m.IsPrime] (hI : I.FG)
    (hIJ : I.map (algebraMap A (Localization.AtPrime m)) ≤
      J.map (algebraMap A (Localization.AtPrime m))) :
    ∃ H : A, H ∉ m ∧ ∀ Q ∈ I, H * Q ∈ J := by
  classical
  obtain ⟨s, hs⟩ := hI
  have hd (Q : s) : ∃ d : A, d ∉ m ∧ d * (Q : A) ∈ J := by
    apply (IsLocalization.algebraMap_mem_map_algebraMap_iff
      m.primeCompl (Localization.AtPrime m) J (Q : A)).mp
    apply hIJ
    apply Ideal.mem_map_of_mem
    rw [← hs]
    exact Submodule.subset_span Q.property
  choose d hd using hd
  let H := ∏ Q : s, d Q
  have hH : H ∉ m := m.primeCompl.prod_mem (fun Q _ => (hd Q).1)
  refine ⟨H, hH, ?_⟩
  have hgen (Q : A) (hQ : Q ∈ s) : H * Q ∈ J := by
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ (⟨Q, hQ⟩ : s))
    change H = d ⟨Q, hQ⟩ * c at hc
    rw [hc, mul_right_comm]
    exact J.mul_mem_right c (hd ⟨Q, hQ⟩).2
  intro Q hQ
  rw [← hs] at hQ
  induction hQ using Submodule.span_induction with
  | mem Q hQ => exact hgen Q hQ
  | zero => simp
  | add Q Q' _ _ hQ hQ' => simpa only [mul_add] using J.add_mem hQ hQ'
  | smul c Q _ hQ =>
    simpa only [smul_eq_mul, mul_left_comm H c] using J.mul_mem_left c hQ

theorem zero_sets_of_local_span {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (a : σ → K)
    (m : Ideal (MvPolynomial σ K)) [m.IsPrime]
    (hm : m = RingHom.ker (MvPolynomial.eval a)) (hI : I.FG)
    {r : ℕ} (P : Fin r → MvPolynomial σ K) (hP : ∀ i, P i ∈ I)
    (hgen : I.map (algebraMap _ (Localization.AtPrime m)) =
      (Ideal.span (Set.range P)).map (algebraMap _ (Localization.AtPrime m))) :
    ∃ H : MvPolynomial σ K, MvPolynomial.eval a H ≠ 0 ∧
      ∀ v : σ → K, MvPolynomial.eval v H ≠ 0 →
        ((∀ i, MvPolynomial.eval v (P i) = 0) ↔
          ∀ Q ∈ I, MvPolynomial.eval v Q = 0) := by
  obtain ⟨H, hH, hclear⟩ := clear_finitely_generated_ideal I
    (Ideal.span (Set.range P)) m hI (le_of_eq hgen)
  refine ⟨H, ?_, fun v hv => ⟨?_, fun h i => h (P i) (hP i)⟩⟩
  · simpa only [hm, RingHom.mem_ker] using hH
  · intro heq Q hQ
    have hspan : Ideal.span (Set.range P) ≤ RingHom.ker (MvPolynomial.eval v) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact heq i
    have h := hspan (hclear Q hQ)
    change MvPolynomial.eval v (H * Q) = 0 at h
    rw [map_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hv

end Denominators
end AffineJacobian

end AffineJacobianBundle2

section AffineJacobianBundle3

set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators

namespace AffineJacobian
namespace LocalEquations
open MvPolynomial
variable {K σ : Type*} [Field K] [Fintype σ]

theorem local_span_of_conormal (I : Ideal (MvPolynomial σ K)) (a : σ → K)
    (m : MaximalSpectrum (MvPolynomial σ K))
    (hm : m.asIdeal = RingHom.ker (eval a)) (hIm : I ≤ m.asIdeal)
    {r : ℕ} (P : Fin r → MvPolynomial σ K) (hP : ∀ i, P i ∈ I)
    (hgrad : ∀ Q ∈ I, ∃ c : Fin r → K,
      ∀ j, eval a (pderiv j Q) = ∑ i, c i * eval a (pderiv j (P i)))
    (hconormal : I.map (algebraMap _ (Localization.AtPrime m.asIdeal)) ⊓
        (IsLocalRing.maximalIdeal (Localization.AtPrime m.asIdeal)) ^ 2 ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime m.asIdeal) *
        I.map (algebraMap _ (Localization.AtPrime m.asIdeal))) :
    I.map (algebraMap _ (Localization.AtPrime m.asIdeal)) =
      (Ideal.span (Set.range P)).map (algebraMap _ (Localization.AtPrime m.asIdeal)) := by
  classical
  let A := MvPolynomial σ K
  let R := Localization.AtPrime m.asIdeal
  let f := algebraMap A R
  let J : Ideal A := Ideal.span (Set.range P)
  let L := I.map f
  let N := J.map f
  let n := IsLocalRing.maximalIdeal R
  have hJI : J ≤ I := Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hP i)
  have hred : L ≤ N ⊔ n * L := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro Q hQ
    obtain ⟨c, hc⟩ := hgrad Q hQ
    let F := ∑ i, C (c i) * P i
    have hFJ : F ∈ J :=
      Ideal.sum_mem _ (fun i _ => J.mul_mem_left _ (Ideal.subset_span ⟨i, rfl⟩))
    have hFI : F ∈ I := hJI hFJ
    have hDI : Q - F ∈ I := I.sub_mem hQ hFI
    have hDval : eval a (Q - F) = 0 := by
      have h := hIm hDI
      rwa [hm, RingHom.mem_ker] at h
    have hDgrad (j : σ) : eval a (pderiv j (Q - F)) = 0 := by
      simp only [map_sub, F, map_sum, pderiv_C_mul, map_mul, eval_C, hc j, sub_self]
    have hDsq : Q - F ∈ m.asIdeal ^ 2 := by
      rw [hm]
      exact FirstOrder.mem_square_of_value_gradient_zero a (Q - F) hDval hDgrad
    have hlocsq : f (Q - F) ∈ n ^ 2 := by
      have h := Ideal.mem_map_of_mem f hDsq
      rwa [Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal] at h
    have hlocD : f (Q - F) ∈ n * L :=
      hconormal ⟨Ideal.mem_map_of_mem f hDI, hlocsq⟩
    change f Q ∈ N ⊔ n * L
    apply Submodule.mem_sup.mpr
    refine ⟨f F, Ideal.mem_map_of_mem f hFJ, f (Q - F), hlocD, ?_⟩
    rw [map_sub]
    ring
  have hLN : L ≤ N := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot L.fg_of_isNoetherianRing
      (I := n)
    · exact (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top).ge
    · simpa only [Ideal.smul_eq_mul] using hred
  exact hLN.antisymm (Ideal.map_mono hJI)

theorem equations_of_conormal (I : Ideal (MvPolynomial σ K)) (a : σ → K)
    (m : MaximalSpectrum (MvPolynomial σ K))
    (hm : m.asIdeal = RingHom.ker (eval a)) (hIm : I ≤ m.asIdeal)
    (hconormal : I.map (algebraMap _ (Localization.AtPrime m.asIdeal)) ⊓
        (IsLocalRing.maximalIdeal (Localization.AtPrime m.asIdeal)) ^ 2 ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime m.asIdeal) *
        I.map (algebraMap _ (Localization.AtPrime m.asIdeal))) :
    ∃ (r : ℕ) (P : Fin r → MvPolynomial σ K) (H : MvPolynomial σ K),
      (∀ i, P i ∈ I) ∧ eval a H ≠ 0 ∧
      Function.Surjective (fun v : σ → K => fun i : Fin r =>
        ∑ j, eval a (pderiv j (P i)) * v j) ∧
      (∀ v : σ → K, eval v H ≠ 0 →
        ((∀ i, eval v (P i) = 0) ↔ ∀ Q ∈ I, eval v Q = 0)) := by
  obtain ⟨r, P, hP, hsurj, hgrad⟩ := Gradient.basis_equations I a
  have hgen := local_span_of_conormal I a m hm hIm P hP hgrad hconormal
  obtain ⟨H, hHa, hH⟩ := Denominators.zero_sets_of_local_span I a m.asIdeal hm
    I.fg_of_isNoetherianRing P hP hgen
  exact ⟨r, P, H, hP, hHa, hsurj, hH⟩

end LocalEquations
end AffineJacobian

end AffineJacobianBundle3

open scoped BigOperators

theorem solution
    (K σ : Type*) [Field K] [IsAlgClosed K] [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) (a : σ → K)
    (m : MaximalSpectrum (MvPolynomial σ K))
    (hm : m.asIdeal = RingHom.ker (MvPolynomial.eval a))
    (hI : I.IsRadical) (hIm : I ≤ m.asIdeal)
    (hreg : IsRegularLocalRing ((Localization.AtPrime m.asIdeal) ⧸
      I.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime m.asIdeal)))) :
    ∃ (r : ℕ) (P : Fin r → MvPolynomial σ K) (H : MvPolynomial σ K),
      (∀ i, P i ∈ I) ∧ MvPolynomial.eval a H ≠ 0 ∧
      Function.Surjective (fun v : σ → K => fun i : Fin r =>
        ∑ j, MvPolynomial.eval a (MvPolynomial.pderiv j (P i)) * v j) ∧
      (∀ v : σ → K, MvPolynomial.eval v H ≠ 0 →
        ((∀ i, MvPolynomial.eval v (P i) = 0) ↔
          ∀ Q ∈ I, MvPolynomial.eval v Q = 0)) := by
  letI := hreg
  apply AffineJacobian.LocalEquations.equations_of_conormal I a m hm hIm
  exact le_of_eq (RegularLocalConormal.inf_maximalIdeal_sq_eq_mul
    (Localization.AtPrime m.asIdeal)
    (I.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime m.asIdeal))))
