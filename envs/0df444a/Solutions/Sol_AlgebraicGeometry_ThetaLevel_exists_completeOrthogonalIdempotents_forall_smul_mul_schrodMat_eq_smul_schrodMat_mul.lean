-- Prove2me | solution 1 for AlgebraicGeometry.ThetaLevel.exists_completeOrthogonalIdempotents_forall_smul_mul_schrodMat_eq_smul_schrodMat_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/917d1957-0663-565b-9697-4744d6d7f8f6

import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import Theorems.Thm_AlgebraicGeometry_ThetaLevel_schrodMat_one_and_schrodMat_mul
import Theorems.Thm_exists_completeOrthogonalIdempotents_mul_eq_pow_mul_of_pow_eq_one_of_forall_isUnit_one_sub_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ThetaLevel_exists_completeOrthogonalIdempotents_forall_smul_mul_schrodMat_eq_smul_schrodMat_mul

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped BigOperators
open AlgebraicGeometry AlgebraicGeometry.ThetaLevel

namespace AlgLGN

section HeisPow

variable {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d]

omit [NeZero d] in
theorem pair_nsmul_left (n : ℕ) (k h : HH δ) : pair δ d (n • k) h = n • pair δ d k h := by
  induction n with
  | zero => simp [pair_zero_left]
  | succ n ih => rw [succ_nsmul, pair_add_left, ih, succ_nsmul]

theorem pow_h (z : Heis δ d) (n : ℕ) : (z ^ n).h = n • z.h := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Heis.mul_h, ih, succ_nsmul]

theorem pow_k (z : Heis δ d) (n : ℕ) : (z ^ n).k = n • z.k := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Heis.mul_k, ih, succ_nsmul]

theorem pow_a (z : Heis δ d) (n : ℕ) : (z ^ n).a = n • z.a + (n.choose 2) • pair δ d z.k z.h := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Heis.mul_a, ih, pow_k, pair_nsmul_left, Nat.choose_succ_succ', Nat.choose_one_right, succ_nsmul,
        add_smul]
      abel

omit [NeZero d] in
theorem nsmul_HH (hδd : ∏ i, δ i = d) (x : HH δ) : d • x = 0 := by
  funext i
  have hdvd : δ i ∣ d := hδd ▸ Finset.dvd_prod_of_mem δ (Finset.mem_univ i)
  rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, (ZMod.natCast_eq_zero_iff d (δ i)).mpr hdvd, zero_mul]

omit [NeZero d] in
theorem nsmul_pair (hδd : ∏ i, δ i = d) (k h : HH δ) : d • pair δ d k h = 0 := by
  rw [← pair_nsmul_left, nsmul_HH δ d hδd, pair_zero_left]

theorem pow_d_eq_cen (hδd : ∏ i, δ i = d) (z : Heis δ d) : z ^ d = Heis.cen ((z ^ d).a) := by
  refine Heis.ext rfl ?_ ?_
  · rw [pow_h, nsmul_HH δ d hδd]; rfl
  · rw [pow_k, nsmul_HH δ d hδd]; rfl

theorem pow_two_d (hδd : ∏ i, δ i = d) (z : Heis δ d) : z ^ (2 * d) = 1 := by
  refine Heis.ext ?_ ?_ ?_
  · rw [pow_a, Heis.one_a, nsmul_eq_mul, ZMod.natCast_self, zero_mul, zero_add, Nat.choose_two_right,
      show 2 * d * (2 * d - 1) / 2 = (2 * d - 1) * d by
        rw [mul_assoc, Nat.mul_div_cancel_left _ (by norm_num), mul_comm],
      mul_smul, nsmul_pair δ d hδd, smul_zero]
  · rw [pow_h, Heis.one_h, mul_comm, mul_smul, nsmul_HH δ d hδd]
  · rw [pow_k, Heis.one_k, mul_comm, mul_smul, nsmul_HH δ d hδd]

end HeisPow

section Schrod

variable {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] (R : Type) [CommRing R] (ω : R)
  {n : ℕ} (e : Fin n ≃ HH δ)

theorem schrodMat_cen (a : ZMod (2 * d)) :
    schrodMat δ d R ω e (Heis.cen a) = omegaPow d R ω a • (1 : Matrix (Fin n) (Fin n) R) := by
  ext i j
  rw [schrodMat_apply, Matrix.smul_apply, Matrix.one_apply]
  simp only [Heis.cen_h, Heis.cen_a, Heis.cen_k, add_zero, pair_zero_left, smul_eq_mul]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg (fun h => hij (e.injective h)), if_neg hij, mul_zero]

theorem schrodMat_mk (hω : ω ^ (2 * d) = 1) (a : ZMod (2 * d)) (h k : HH δ) :
    schrodMat δ d R ω e ⟨a, h, k⟩ = omegaPow d R ω a • schrodMat δ d R ω e ⟨0, h, k⟩ := by
  ext i j
  rw [Matrix.smul_apply, schrodMat_apply, schrodMat_apply, smul_eq_mul]
  dsimp only
  by_cases hij : e i = e j + h
  · rw [if_pos hij, if_pos hij, zero_add, omegaPow_add d R ω hω]
  · rw [if_neg hij, if_neg hij, mul_zero]

theorem schrodMat_pow (hω : ω ^ (2 * d) = 1) (z : Heis δ d) (m : ℕ) :
    schrodMat δ d R ω e (z ^ m) = schrodMat δ d R ω e z ^ m := by
  obtain ⟨h1, hmul⟩ := AlgebraicGeometry.ThetaLevel.schrodMat_one_and_schrodMat_mul δ d R ω hω e
  induction m with
  | zero => rw [pow_zero, pow_zero, h1]
  | succ m ih => rw [pow_succ, pow_succ, hmul, ih]

end Schrod

end AlgLGN

namespace GPJUL

variable {S : Type} [CommRing S]

theorem idem_binom {ε : S} (hε : IsIdempotentElem ε) (x y : S) (n : ℕ) :
    (ε * x + (1 - ε) * y) ^ n = ε * x ^ n + (1 - ε) * y ^ n := by
  induction n with
  | zero => ring
  | succ n ih =>
    rw [pow_succ, ih]
    have h' : ε * ε = ε := hε
    linear_combination (x ^ n * x - x ^ n * y - x * y ^ n + y ^ n * y) * h'

theorem piece_pow_congr {p x y : S} (h : p * x = p * y) (n : ℕ) : p * x ^ n = p * y ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc p * x ^ (n + 1) = p * x ^ n * x := by ring
      _ = p * y ^ n * x := by rw [ih]
      _ = y ^ n * (p * x) := by ring
      _ = y ^ n * (p * y) := by rw [h]
      _ = p * y ^ (n + 1) := by ring

theorem coi_prod {I J : Type} [Fintype I] [Fintype J] {e : I → S} {f : J → S}
    (he : CompleteOrthogonalIdempotents e) (hf : CompleteOrthogonalIdempotents f) :
    CompleteOrthogonalIdempotents (fun p : I × J => e p.1 * f p.2) where
  idem p := by
    change e p.1 * f p.2 * (e p.1 * f p.2) = e p.1 * f p.2
    have h1 : e p.1 * e p.1 = e p.1 := he.idem p.1
    have h2 : f p.2 * f p.2 = f p.2 := hf.idem p.2
    calc e p.1 * f p.2 * (e p.1 * f p.2) = (e p.1 * e p.1) * (f p.2 * f p.2) := by ring
      _ = e p.1 * f p.2 := by rw [h1, h2]
  ortho := by
    intro p q hpq
    show e p.1 * f p.2 * (e q.1 * f q.2) = 0
    by_cases h : p.1 = q.1
    · have h2 : p.2 ≠ q.2 := fun h2 => hpq (Prod.ext h h2)
      have := hf.ortho h2
      calc e p.1 * f p.2 * (e q.1 * f q.2) = (e p.1 * e q.1) * (f p.2 * f q.2) := by ring
        _ = 0 := by rw [this, mul_zero]
    · have := he.ortho h
      calc e p.1 * f p.2 * (e q.1 * f q.2) = (e p.1 * e q.1) * (f p.2 * f q.2) := by ring
        _ = 0 := by rw [this, zero_mul]
  complete := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, hf.complete, mul_one]
    exact he.complete

theorem coi_pushforward {K I : Type} [Fintype K] [Fintype I] [DecidableEq I] {κ : K → S}
    (hκ : CompleteOrthogonalIdempotents κ) (j : K → I) :
    CompleteOrthogonalIdempotents (fun i : I => ∑ k, if j k = i then κ k else 0) where
  idem i := by
    change (∑ k, if j k = i then κ k else 0) * (∑ k, if j k = i then κ k else 0) = ∑ k, if j k = i then κ k else 0
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single k (fun k' _ hk' => ?_) (fun h => absurd (Finset.mem_univ k) h)]
    · split_ifs with h
      · exact hκ.idem k
      · rw [mul_zero]
    · split_ifs with h1 h2
      · exact hκ.ortho (Ne.symm hk')
      · rw [mul_zero]
      · rw [zero_mul]
      · rw [mul_zero]
  ortho := by
    intro i i' hii'
    show (∑ k, if j k = i then κ k else 0) * (∑ k, if j k = i' then κ k else 0) = 0
    rw [Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun k' _ => ?_
    split_ifs with h1 h2
    · have hkk' : k ≠ k' := fun hkk' => hii' (h1 ▸ h2 ▸ (congrArg j hkk'))
      exact hκ.ortho hkk'
    · rw [mul_zero]
    · rw [zero_mul]
    · rw [mul_zero]
  complete := by
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact hκ.complete

theorem finish (N : ℕ) (ω : S) (hω2d : ω ^ (2 * (N + 1)) = 1) (ε u : S)
    {K : Type} [Fintype K] (κ : K → S) (hκ : CompleteOrthogonalIdempotents κ) (j : K → ℕ)
    (hj : ∀ k, ε * κ k * u = ε * κ k * ω ^ (j k)) :
    ∃ F : ZMod (2 * (N + 1)) → S, CompleteOrthogonalIdempotents F ∧
      ∀ a : ZMod (2 * (N + 1)), ε * F a * u = ε * F a * ω ^ a.val := by
  classical
  refine ⟨fun a => ∑ k, if (j k : ZMod (2 * (N + 1))) = a then κ k else 0,
    coi_pushforward hκ (fun k => (j k : ZMod (2 * (N + 1)))), fun a => ?_⟩
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with h
  · rw [hj k]
    have hmod : ω ^ (j k) = ω ^ (j k % (2 * (N + 1))) := by
      conv_lhs => rw [← Nat.mod_add_div (j k) (2 * (N + 1)), pow_add, pow_mul, hω2d, one_pow, mul_one]
    rw [hmod, ← h, ZMod.val_natCast]
  · simp

end GPJUL

namespace GPJUL

variable {S : Type} [CommRing S]

theorem omega_pow_eq_neg_one (N : ℕ) (ζ : S) (hζ : ζ ^ (N + 1) = 1)
    (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j)) (ω : S) (hω : ω ^ 2 = ζ)
    (r : ℕ) (hr : N + 1 = 2 * r) : ω ^ (N + 1) = -1 := by
  have hr0 : 0 < r := by omega
  have hrl : r < N + 1 := by omega
  have hunit := hζu r hr0 hrl
  have hzero : (1 - ζ ^ r) * (1 + ζ ^ r) = 0 := by
    have : (1 - ζ ^ r) * (1 + ζ ^ r) = 1 - ζ ^ (2 * r) := by ring
    rw [this, ← hr, hζ, sub_self]
  have h1 : 1 + ζ ^ r = 0 := (hunit.mul_right_eq_zero).mp hzero
  calc ω ^ (N + 1) = (ω ^ 2) ^ r := by rw [← pow_mul, hr]
    _ = ζ ^ r := by rw [hω]
    _ = -1 := by linear_combination h1

theorem unit_loc (S : Type) [CommRing S] (N : ℕ) (hd : IsUnit ((N + 1 : ℕ) : S))
    (ζ : S) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (ω : S) (hω : ω ^ 2 = ζ)
    (ε : S) (hε : IsIdempotentElem ε) (u : S)
    (h2 : ε * u ^ (2 * (N + 1)) = ε) (m : ℕ) (h1 : ε * u ^ (N + 1) = ε * ω ^ m) :
    ∃ F : ZMod (2 * (N + 1)) → S, CompleteOrthogonalIdempotents F ∧
      ∀ a : ZMod (2 * (N + 1)), ε * F a * u = ε * F a * ω ^ a.val := by
  classical
  have hεε : ε * ε = ε := hε
  have hω2d : ω ^ (2 * (N + 1)) = 1 := by rw [pow_mul, hω, hζ]

  set v : S := ε * u ^ 2 + (1 - ε) * 1 with hv
  have hvd : v ^ (N + 1) = 1 := by
    rw [hv, idem_binom hε, one_pow, mul_one, ← pow_mul, h2]; ring
  obtain ⟨e, he, hue⟩ :=
    exists_completeOrthogonalIdempotents_mul_eq_pow_mul_of_pow_eq_one_of_forall_isUnit_one_sub_pow S N hd ζ hζ hζu v hvd

  have hsq : ∀ k : Fin (N + 1), ε * e k * u ^ 2 = ε * e k * ζ ^ (k : ℕ) := fun k => by
    have := hue k
    have hεv : ε * v = ε * u ^ 2 := by rw [hv]; linear_combination (u ^ 2 - 1) * hεε
    calc ε * e k * u ^ 2 = (ε * u ^ 2) * e k := by ring
      _ = ε * (v * e k) := by rw [← hεv]; ring
      _ = ε * (ζ ^ (k : ℕ) * e k) := by rw [this]
      _ = ε * e k * ζ ^ (k : ℕ) := by ring
  rcases Nat.even_or_odd (N + 1) with ⟨r, hr⟩ | ⟨r, hr⟩
  ·
    have hr2 : N + 1 = 2 * r := by omega
    have hneg : ω ^ (N + 1) = -1 := omega_pow_eq_neg_one N ζ hζ hζu ω hω r hr2
    have h2u : IsUnit ((1 + 1 : ℕ) : S) := by
      have : ((N + 1 : ℕ) : S) = ((1 + 1 : ℕ) : S) * (r : S) := by rw [hr2]; push_cast; ring
      exact isUnit_of_mul_isUnit_left (this ▸ hd)

    set w : S := ∑ k : Fin (N + 1), e k * ω ^ (2 * (N + 1) - (k : ℕ)) with hw
    have hew : ∀ k : Fin (N + 1), e k * w = e k * ω ^ (2 * (N + 1) - (k : ℕ)) := fun k => by
      rw [hw, Finset.mul_sum]
      rw [Finset.sum_eq_single k (fun k' _ hk' => by rw [← mul_assoc, he.ortho (Ne.symm hk'), zero_mul])
        (fun h => absurd (Finset.mem_univ k) h)]
      rw [← mul_assoc, he.idem k]
    have hεuw : ε * (u * w) ^ 2 = ε := by
      have : ε * (u * w) ^ 2 = ∑ k : Fin (N + 1), ε * e k * (u * w) ^ 2 := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, he.complete, mul_one]
      rw [this]
      conv_rhs => rw [← mul_one ε, ← he.complete, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hk : (k : ℕ) ≤ 2 * (N + 1) := by omega
      calc ε * e k * (u * w) ^ 2 = (ε * e k * u ^ 2) * (e k * w) * w := by
              have := he.idem k; rw [IsIdempotentElem] at this
              linear_combination (-(ε * u ^ 2 * w * w)) * this
        _ = (ε * e k * ζ ^ (k : ℕ)) * (e k * ω ^ (2 * (N + 1) - (k : ℕ))) * w := by rw [hsq k, hew k]
        _ = ε * ζ ^ (k : ℕ) * ω ^ (2 * (N + 1) - (k : ℕ)) * (e k * w) := by
              have := he.idem k; rw [IsIdempotentElem] at this
              linear_combination (ε * ζ ^ (k : ℕ) * ω ^ (2 * (N + 1) - (k : ℕ)) * w) * this
        _ = ε * e k * (ζ ^ (k : ℕ) * (ω ^ (2 * (N + 1) - (k : ℕ))) ^ 2) := by rw [hew k]; ring
        _ = ε * e k := by
              have : ζ ^ (k : ℕ) * (ω ^ (2 * (N + 1) - (k : ℕ))) ^ 2 = 1 := by
                rw [← hω, ← pow_mul, ← pow_mul, ← pow_add,
                  show 2 * (k : ℕ) + (2 * (N + 1) - (k : ℕ)) * 2 = 2 * (N + 1) + 2 * (N + 1) by omega,
                  pow_add, hω2d, one_mul]
              rw [this, mul_one]

    set s : S := ε * (u * w) + (1 - ε) * 1 with hs
    have hs2 : s ^ (1 + 1) = 1 := by
      rw [hs, idem_binom hε, one_pow, mul_one, hεuw]; ring
    obtain ⟨f, hf, hsf⟩ :=
      exists_completeOrthogonalIdempotents_mul_eq_pow_mul_of_pow_eq_one_of_forall_isUnit_one_sub_pow S 1 h2u (-1)
        (by norm_num) (fun j hj hj' => by
          obtain rfl : j = 1 := by omega
          have : (1 : S) - (-1) ^ 1 = ((1 + 1 : ℕ) : S) := by push_cast; ring
          rw [this]; exact h2u) s hs2
    have hεs : ε * s = ε * (u * w) := by rw [hs]; linear_combination (u * w - 1) * hεε

    refine finish N ω hω2d ε u (fun p : Fin (N + 1) × Fin (1 + 1) => e p.1 * f p.2) (coi_prod he hf)
      (fun p => (N + 1) * (p.2 : ℕ) + (p.1 : ℕ)) fun p => ?_
    obtain ⟨k, b⟩ := p
    have hk : (k : ℕ) ≤ 2 * (N + 1) := by omega

    have hb : ε * f b * (u * w) = ε * f b * (-1) ^ (b : ℕ) := by
      calc ε * f b * (u * w) = (ε * s) * f b := by rw [hεs]; ring
        _ = ε * (s * f b) := by ring
        _ = ε * ((-1) ^ (b : ℕ) * f b) := by rw [hsf b]
        _ = ε * f b * (-1) ^ (b : ℕ) := by ring
    show ε * (e k * f b) * u = ε * (e k * f b) * ω ^ ((N + 1) * (b : ℕ) + (k : ℕ))
    calc ε * (e k * f b) * u = ε * (e k * f b) * u * (ω ^ (2 * (N + 1) - (k : ℕ)) * ω ^ (k : ℕ)) := by
            rw [← pow_add, show 2 * (N + 1) - (k : ℕ) + (k : ℕ) = 2 * (N + 1) by omega, hω2d, mul_one]
      _ = (ε * f b * (u * (e k * ω ^ (2 * (N + 1) - (k : ℕ))))) * ω ^ (k : ℕ) := by ring
      _ = (ε * f b * (u * (e k * w))) * ω ^ (k : ℕ) := by rw [hew k]
      _ = (ε * f b * (u * w)) * e k * ω ^ (k : ℕ) := by ring
      _ = (ε * f b * (-1) ^ (b : ℕ)) * e k * ω ^ (k : ℕ) := by rw [hb]
      _ = ε * (e k * f b) * ((ω ^ (N + 1)) ^ (b : ℕ) * ω ^ (k : ℕ)) := by rw [hneg]; ring
      _ = ε * (e k * f b) * ω ^ ((N + 1) * (b : ℕ) + (k : ℕ)) := by rw [← pow_mul, ← pow_add]
  ·
    refine finish N ω hω2d ε u (fun p : Fin (N + 1) × Fin 1 => e p.1 * (1 : Fin 1 → S) p.2)
      (coi_prod he ⟨⟨fun _ => by simp [IsIdempotentElem], fun i j h => absurd (Subsingleton.elim i j) h⟩, by simp⟩)
      (fun p => 2 * (p.1 : ℕ) * (r + 1) + m) fun p => ?_
    obtain ⟨k, b⟩ := p
    show ε * (e k * (1 : Fin 1 → S) b) * u = ε * (e k * (1 : Fin 1 → S) b) * ω ^ (2 * (k : ℕ) * (r + 1) + m)
    simp only [Pi.one_apply, mul_one]
    have hpow : ε * e k * (u ^ 2) ^ (r + 1) = ε * e k * (ζ ^ (k : ℕ)) ^ (r + 1) := piece_pow_congr (hsq k) (r + 1)
    calc ε * e k * u = ε * e k * u * (ε * u ^ (2 * (N + 1))) := by
            rw [h2]; linear_combination (-(e k * u)) * hεε
      _ = ε * (ε * e k * (u ^ 2) ^ (r + 1)) * u ^ (N + 1) := by
            rw [← pow_mul, show 2 * (r + 1) = (N + 1) + 1 by omega]; ring
      _ = ε * (ε * e k * (ζ ^ (k : ℕ)) ^ (r + 1)) * u ^ (N + 1) := by rw [hpow]
      _ = (ε * u ^ (N + 1)) * e k * (ζ ^ (k : ℕ)) ^ (r + 1) := by linear_combination (e k * (ζ ^ (k:ℕ)) ^ (r+1) * u ^ (N+1)) * hεε
      _ = (ε * ω ^ m) * e k * (ζ ^ (k : ℕ)) ^ (r + 1) := by rw [h1]
      _ = ε * e k * ω ^ (2 * (k : ℕ) * (r + 1) + m) := by rw [← hω, ← pow_mul, ← pow_mul, pow_add]; ring

end GPJUL

namespace AlgLGN

section COI

variable {S : Type} [CommRing S]

theorem coi_of {ι : Type} [Fintype ι] (f : ι → S) (horth : ∀ i j, i ≠ j → f i * f j = 0) (hsum : ∑ i, f i = 1) :
    CompleteOrthogonalIdempotents f :=
  CompleteOrthogonalIdempotents.iff_ortho_complete.mpr ⟨fun _ _ h => horth _ _ h, hsum⟩

theorem coi_prodIdx {C A : Type} [Fintype C] [Fintype A] [DecidableEq C] [DecidableEq A]
    (E : C → S) (hE : CompleteOrthogonalIdempotents E) (F : C → A → S)
    (hF : ∀ c, CompleteOrthogonalIdempotents (F c)) :
    CompleteOrthogonalIdempotents (fun i : C × A => E i.1 * F i.1 i.2) := by
  refine coi_of _ ?_ ?_
  · rintro ⟨c, a⟩ ⟨c', a'⟩ hne
    by_cases hc : c = c'
    · subst hc
      have ha : a ≠ a' := fun h => hne (by rw [h])
      calc E c * F c a * (E c * F c a') = E c * E c * (F c a * F c a') := by ring
        _ = 0 := by rw [(hF c).ortho ha, mul_zero]
    · calc E c * F c a * (E c' * F c' a') = E c * E c' * (F c a * F c' a') := by ring
        _ = 0 := by rw [hE.ortho hc, zero_mul]
  · rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, (hF _).complete, mul_one]
    exact hE.complete

theorem coi_pi {Z ι : Type} [Fintype Z] [DecidableEq Z] [Fintype ι] [DecidableEq ι]
    (G : Z → ι → S) (hG : ∀ z, CompleteOrthogonalIdempotents (G z)) :
    CompleteOrthogonalIdempotents (fun q : Z → ι => ∏ z, G z (q z)) := by
  refine coi_of _ ?_ ?_
  · intro q q' hne
    obtain ⟨z₀, hz₀⟩ : ∃ z, q z ≠ q' z := Function.ne_iff.mp hne
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_zero (Finset.mem_univ z₀) ((hG z₀).ortho hz₀)
  · have h := Finset.prod_univ_sum (fun _ : Z => (Finset.univ : Finset ι)) (fun z i => G z i)
    rw [Fintype.piFinset_univ] at h
    rw [← h]
    simp_rw [(hG _).complete]
    exact Finset.prod_const_one

theorem coi_equiv {Q : Type} [Fintype Q] {m : ℕ} (eq : Q ≃ Fin m) (ε : Q → S)
    (hε : CompleteOrthogonalIdempotents ε) :
    CompleteOrthogonalIdempotents (fun p : Fin m => ε (eq.symm p)) := by
  refine coi_of _ ?_ ?_
  · intro p p' hne
    exact hε.ortho (fun h => hne (eq.symm.injective h))
  · rw [Equiv.sum_comp eq.symm ε]
    exact hε.complete

theorem pi_mul_factor {Z ι : Type} [Fintype Z] [DecidableEq Z] [Fintype ι] (G : Z → ι → S)
    (hG : ∀ z, CompleteOrthogonalIdempotents (G z)) (q : Z → ι) (z : Z) :
    (∏ z', G z' (q z')) * G z (q z) = ∏ z', G z' (q z') := by
  rw [← Finset.mul_prod_erase Finset.univ (fun z' => G z' (q z')) (Finset.mem_univ z), mul_right_comm,
    ((hG z).idem (q z)).eq]

theorem isolate {n : ℕ} {C : Type} [Fintype C] [DecidableEq C] (ε : C → S) (hε : CompleteOrthogonalIdempotents ε)
    (u : S) (M : C → Matrix (Fin n) (Fin n) S) (T X : Matrix (Fin n) (Fin n) S)
    (h : X = (∑ c, ε c • (u • M c)) * T) (c₀ : C) :
    ε c₀ • X = ε c₀ • (u • M c₀ * T) := by
  rw [h, Finset.sum_mul, Finset.smul_sum, Fintype.sum_eq_single c₀]
  · rw [smul_mul_assoc, smul_smul, ((hε.idem c₀)).eq, smul_mul_assoc]
  · intro c hc
    rw [smul_mul_assoc, smul_smul, hε.ortho (Ne.symm hc), zero_smul]

theorem conj_pow {n : ℕ} (ε : S) (hε : IsIdempotentElem ε) (u : S) (T M M₀ : Matrix (Fin n) (Fin n) S)
    (h : ε • (T * M) = ε • (u • M₀ * T)) (m : ℕ) :
    ε • (T * M ^ m) = ε • (u ^ m • (M₀ ^ m * T)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have key : u ^ m • (M₀ ^ m * (ε • (T * M))) = u ^ m • (M₀ ^ m * (ε • (u • M₀ * T))) := by rw [h]
    have lhs : ε • (T * M ^ (m + 1)) = u ^ m • (M₀ ^ m * (ε • (T * M))) := by
      rw [pow_succ, ← Matrix.mul_assoc, ← smul_mul_assoc, ih]
      simp only [smul_mul_assoc, Matrix.mul_smul, Matrix.mul_assoc, smul_smul]
      congr 1
      ring
    have rhs : u ^ m • (M₀ ^ m * (ε • (u • M₀ * T))) = ε • (u ^ (m + 1) • (M₀ ^ (m + 1) * T)) := by
      simp only [smul_mul_assoc, Matrix.mul_smul, ← Matrix.mul_assoc, smul_smul, pow_succ]
      congr 1
      ring
    rw [lhs, key, rhs]

theorem scalar_of_smul_one {n : ℕ} (a b : S) (h : a • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) S) = b • 1) : a = b := by
  have := congrFun (congrFun h 0) 0
  simpa using this

theorem idem_mix_pow (ε : S) (hε : IsIdempotentElem ε) (x y : S) (n : ℕ) :
    (ε * x + (1 - ε) * y) ^ n = ε * x ^ n + (1 - ε) * y ^ n := by
  have h1 : ε * ε = ε := hε.eq
  have h2 : ε * (1 - ε) = 0 := by rw [mul_sub, mul_one, h1, sub_self]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    have : (1 - ε) * (1 - ε) = 1 - ε := by
      have := hε.one_sub; exact this.eq
    calc (ε * x ^ n + (1 - ε) * y ^ n) * (ε * x + (1 - ε) * y)
        = ε * ε * (x ^ n * x) + ε * (1 - ε) * (x ^ n * y + y ^ n * x) + (1 - ε) * (1 - ε) * (y ^ n * y) := by ring
      _ = ε * x ^ (n + 1) + (1 - ε) * y ^ (n + 1) := by rw [h1, h2, this, pow_succ, pow_succ]; ring

end COI

section UnitLoc

private theorem _root_.AlgLGN.unit_loc (S : Type) [CommRing S] (N : ℕ) (hd : IsUnit ((N + 1 : ℕ) : S))
    (ζ : S) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (ω : S) (hω : ω ^ 2 = ζ)
    (ε : S) (hε : IsIdempotentElem ε) (u : S)
    (h2 : ε * u ^ (2 * (N + 1)) = ε) (m : ℕ) (h1 : ε * u ^ (N + 1) = ε * ω ^ m) :
    ∃ F : ZMod (2 * (N + 1)) → S, CompleteOrthogonalIdempotents F ∧
      ∀ a : ZMod (2 * (N + 1)), ε * F a * u = ε * F a * ω ^ a.val :=
  GPJUL.unit_loc S N hd ζ hζ hζu ω hω ε hε u h2 m h1

p2m_export "AlgLGN" "unit_loc"
end UnitLoc

end AlgLGN

open AlgLGN in
theorem solution
    {g : ℕ} (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (N : ℕ) (hδd : ∏ i, δ i = N + 1)
    (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    (B : Type) [CommRing B] (hd : IsUnit ((N + 1 : ℕ) : B))
    (ζ : B) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (ω : B) (hω : ω ^ 2 = ζ)
    {S : Type} [CommRing S] (φB : B →+* S)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) S) (hT : IsUnit T)
    (hmono : ∀ z : Heis δ (N + 1), ∃ (ε : ((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)) → S) (u : Sˣ),
      CompleteOrthogonalIdempotents ε ∧
        T * schrodMat δ (N + 1) S (φB ω) e z =
          (∑ c, ε c • ((u : S) • schrodMat δ (N + 1) S (φB ω) e ⟨0, c.1, c.2⟩)) * T) :
    ∃ (m : ℕ) (ε : Fin m → S) (w : Fin m → Heis δ (N + 1) → Heis δ (N + 1)),
      CompleteOrthogonalIdempotents ε ∧
      ∀ (p : Fin m) (z : Heis δ (N + 1)),
        ε p • (T * schrodMat δ (N + 1) S (φB ω) e z) = ε p • (schrodMat δ (N + 1) S (φB ω) e (w p z) * T) := by
  classical

  set ω' : S := φB ω with hω'
  set ζ' : S := φB ζ with hζ'
  have hζ' : ζ' ^ (N + 1) = 1 := by rw [hζ', ← map_pow, hζ, map_one]
  have hζu' : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ' ^ j) := by
    intro j hj hj'
    have := (hζu j hj hj').map φB
    simpa [hζ'] using this
  have hω'2 : ω' ^ 2 = ζ' := by rw [hω', ← map_pow, hω]
  have hd' : IsUnit ((N + 1 : ℕ) : S) := by have := hd.map φB; rwa [map_natCast] at this
  have hω2d : ω' ^ (2 * (N + 1)) = 1 := by rw [pow_mul, hω'2, hζ']
  let ϑ : Heis δ (N + 1) → Matrix (Fin (N + 1)) (Fin (N + 1)) S := schrodMat δ (N + 1) S ω' e
  obtain ⟨Ti, hTi⟩ := hT.exists_right_inv

  choose E U hEU using hmono
  have hE : ∀ z, CompleteOrthogonalIdempotents (E z) := fun z => (hEU z).1

  have hiso : ∀ (z : Heis δ (N + 1)) (c : HH δ × HH δ),
      E z c • (T * ϑ z) = E z c • ((U z : S) • ϑ ⟨0, c.1, c.2⟩ * T) := by
    intro z c
    exact isolate (E z) (hE z) (U z : S) (fun c => ϑ ⟨0, c.1, c.2⟩) T _ (hEU z).2 c

  have hscal : ∀ (z : Heis δ (N + 1)) (c : HH δ × HH δ),
      E z c * (U z : S) ^ (2 * (N + 1)) = E z c ∧
      ∃ m : ℕ, E z c * (U z : S) ^ (N + 1) = E z c * ω' ^ m := by
    intro z c
    have hεi : IsIdempotentElem (E z c) := (hE z).idem c
    have hpow := conj_pow (E z c) hεi (U z : S) T (ϑ z) (ϑ ⟨0, c.1, c.2⟩) (hiso z c)
    constructor
    · have h := hpow (2 * (N + 1))
      rw [← schrodMat_pow δ (N + 1) S ω' e hω2d, ← schrodMat_pow δ (N + 1) S ω' e hω2d, pow_two_d δ (N + 1) hδd,
        pow_two_d δ (N + 1) hδd, (schrodMat_one_and_schrodMat_mul δ (N + 1) S ω' hω2d e).1, Matrix.mul_one,
        Matrix.one_mul] at h

      have h' := congrArg (· * Ti) h
      simp only [smul_mul_assoc, hTi, smul_smul] at h'
      exact (scalar_of_smul_one _ _ h').symm
    · have h := hpow (N + 1)
      rw [← schrodMat_pow δ (N + 1) S ω' e hω2d, ← schrodMat_pow δ (N + 1) S ω' e hω2d, pow_d_eq_cen δ (N + 1) hδd z,
        pow_d_eq_cen δ (N + 1) hδd ⟨0, c.1, c.2⟩, schrodMat_cen, schrodMat_cen] at h
      set A := ((z ^ (N + 1)).a : ZMod (2 * (N + 1))) with hA
      set A' := (((⟨0, c.1, c.2⟩ : Heis δ (N + 1)) ^ (N + 1)).a : ZMod (2 * (N + 1))) with hA'

      rw [Matrix.mul_smul, Matrix.mul_one, smul_mul_assoc, Matrix.one_mul, smul_smul, smul_smul] at h
      have h' := congrArg (· * Ti) h
      simp only [smul_mul_assoc, hTi, smul_smul] at h'
      have h'' := scalar_of_smul_one _ _ h'

      refine ⟨A.val + (2 * (N + 1) - A'.val), ?_⟩
      have hle : A'.val ≤ 2 * (N + 1) := (ZMod.val_lt A').le
      have hcomp : ω' ^ A'.val * ω' ^ (2 * (N + 1) - A'.val) = 1 := by
        rw [← pow_add, Nat.add_sub_cancel' hle, hω2d]
      simp only [omegaPow] at h''
      rw [pow_add]
      linear_combination (-(ω' ^ (2 * (N + 1) - A'.val))) * h'' + (-(E z c * (U z : S) ^ (N + 1))) * hcomp

  choose mzc hmzc using fun z c => (hscal z c).2
  have hF := fun z c => unit_loc S N hd' ζ' hζ' hζu' ω' hω'2 (E z c) ((hE z).idem c) (U z : S) (hscal z c).1 (mzc z c)
    (hmzc z c)
  choose F hF' using hF
  have hFcoi : ∀ z c, CompleteOrthogonalIdempotents (F z c) := fun z c => (hF' z c).1
  have hFu : ∀ z c a, E z c * F z c a * (U z : S) = E z c * F z c a * ω' ^ a.val := fun z c a => (hF' z c).2 a

  have hpiece : ∀ (z : Heis δ (N + 1)) (c : HH δ × HH δ) (a : ZMod (2 * (N + 1))),
      (E z c * F z c a) • (T * ϑ z) = (E z c * F z c a) • (ϑ ⟨a, c.1, c.2⟩ * T) := by
    intro z c a
    calc (E z c * F z c a) • (T * ϑ z) = F z c a • (E z c • (T * ϑ z)) := by rw [mul_comm, smul_smul]
      _ = F z c a • (E z c • ((U z : S) • ϑ ⟨0, c.1, c.2⟩ * T)) := by rw [hiso]
      _ = (E z c * F z c a * (U z : S)) • (ϑ ⟨0, c.1, c.2⟩ * T) := by
          rw [smul_mul_assoc, smul_smul, smul_smul]; congr 1; ring
      _ = (E z c * F z c a * ω' ^ a.val) • (ϑ ⟨0, c.1, c.2⟩ * T) := by rw [hFu]
      _ = (E z c * F z c a) • (ϑ ⟨a, c.1, c.2⟩ * T) := by
          rw [show ϑ ⟨a, c.1, c.2⟩ = omegaPow (N + 1) S ω' a • ϑ ⟨0, c.1, c.2⟩ from
            schrodMat_mk δ (N + 1) S ω' e hω2d a c.1 c.2, smul_mul_assoc, smul_smul]
          rfl

  let G : Heis δ (N + 1) → (HH δ × HH δ) × ZMod (2 * (N + 1)) → S := fun z i => E z i.1 * F z i.1 i.2
  have hG : ∀ z, CompleteOrthogonalIdempotents (G z) := fun z => coi_prodIdx (E z) (hE z) (F z) (hFcoi z)
  let Q := Heis δ (N + 1) → (HH δ × HH δ) × ZMod (2 * (N + 1))
  let εQ : Q → S := fun q => ∏ z, G z (q z)
  have hεQ : CompleteOrthogonalIdempotents εQ := coi_pi G hG
  let wQ : Q → Heis δ (N + 1) → Heis δ (N + 1) := fun q z => ⟨(q z).2, (q z).1.1, (q z).1.2⟩
  have hmain : ∀ (q : Q) (z : Heis δ (N + 1)), εQ q • (T * ϑ z) = εQ q • (ϑ (wQ q z) * T) := by
    intro q z
    have hfac : εQ q * (E z (q z).1 * F z (q z).1 (q z).2) = εQ q := pi_mul_factor G hG q z
    have := congrArg (εQ q • ·) (hpiece z (q z).1 (q z).2)
    simp only [smul_smul] at this
    rw [hfac] at this
    exact this

  let eq := Fintype.equivFin Q
  refine ⟨Fintype.card Q, fun p => εQ (eq.symm p), fun p => wQ (eq.symm p), coi_equiv eq εQ hεQ, fun p z => ?_⟩
  exact hmain (eq.symm p) z

end S_AlgebraicGeometry_ThetaLevel_exists_completeOrthogonalIdempotents_forall_smul_mul_schrodMat_eq_smul_schrodMat_mul
end P2MW
export P2MW.S_AlgebraicGeometry_ThetaLevel_exists_completeOrthogonalIdempotents_forall_smul_mul_schrodMat_eq_smul_schrodMat_mul (solution)
