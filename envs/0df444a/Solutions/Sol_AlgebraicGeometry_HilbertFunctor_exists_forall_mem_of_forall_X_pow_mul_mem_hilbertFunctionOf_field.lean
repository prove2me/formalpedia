-- Prove2me | solution 1 for AlgebraicGeometry.HilbertFunctor.exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/9ef0ee5f-f3ee-5a9b-8119-dd412a496845

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_Nat_MacaulayPow
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_Point_I_eq_span_of_forall_finrank_piece_succ_le
import Theorems.Thm_MvPolynomial_exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval
import Theorems.Thm_MvPolynomial_finrank_piece_succ_le_macaulayPow
import Theorems.Thm_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow
import Theorems.Thm_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_map
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf_field

set_option autoImplicit false
set_option maxHeartbeats 3200000
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace SatHighField

variable {n : ℕ}

theorem homogeneous_of_span {K : Type} [CommRing K] {e : ℕ} (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) :
    ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J := by
  obtain ⟨s, hs, rfl⟩ := hJ
  have hh : (Ideal.span s).IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) K) := by
    apply Ideal.homogeneous_span
    intro x hx
    exact ⟨e, (mem_homogeneousSubmodule e x).mpr (hs x hx)⟩
  intro p hp i
  have := hh i hp
  rw [show ((DirectSum.decompose (homogeneousSubmodule (Fin (n + 1)) K) p i : MvPolynomial (Fin (n + 1)) K))
      = homogeneousComponent i p from decomposition.decompose'_apply p i] at this
  exact this

theorem finrank_piece_eq {K : Type} [Field K] {h : ℕ → ℕ} (p : Point K n h) (e : ℕ) :
    Module.finrank K (piece p.I e) = h e := by
  haveI := p.finite_piece e
  have h1 := p.rankAtStalk_piece e ⟨⊥, Ideal.isPrime_bot⟩
  rw [Module.rankAtStalk_eq_finrank_of_free] at h1
  exact h1

theorem mul_mem_of_forall_X_pow_mul_mem {K : Type} [CommRing K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (F : MvPolynomial (Fin (n + 1)) K) (N : ℕ) (hX : ∀ i : Fin (n + 1), X i ^ N * F ∈ J)
    (G : MvPolynomial (Fin (n + 1)) K) (hG : G.IsHomogeneous ((n + 1) * N)) : G * F ∈ J := by
  classical
  rw [G.as_sum, Finset.sum_mul]
  refine Ideal.sum_mem _ fun s hs => ?_

  have hdeg : s.degree = (n + 1) * N := by
    have := hG (mem_support_iff.mp hs)
    simp [Finsupp.weight_apply, Finsupp.degree] at this
    exact this
  obtain ⟨i, hi⟩ : ∃ i : Fin (n + 1), N ≤ s i := by
    by_contra hcon
    push Not at hcon
    have : s.degree < (n + 1) * N := by
      rw [Finsupp.degree_eq_sum]
      calc ∑ i, s i < ∑ _i : Fin (n + 1), N := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => hcon i)
        _ = (n + 1) * N := by simp [mul_comm]
    omega

  have hs' : s = (s - Finsupp.single i N) + Finsupp.single i N := by
    ext j
    simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
    split_ifs with hij
    · subst hij; omega
    · omega
  rw [hs', monomial_add_single, mul_assoc]
  exact Ideal.mul_mem_left _ _ (hX i)

theorem core (P : Polynomial ℚ) (m : ℕ) (hm1 : 1 ≤ m)
    (hgen : ∀ (K : Type) [Field K] (p : Point K n (hilbertFunctionOf n P m)),
      p.I = Ideal.span {f | f ∈ p.I ∧ f.IsHomogeneous m})
    (hmax : Nat.macaulayPow m (hilbertFunctionOf n P m m) = hilbertFunctionOf n P m (m + 1))
    (K : Type) [Field K] [Infinite K] (p : Point K n (hilbertFunctionOf n P m))
    (d : ℕ) (hd : m ≤ d) (F : MvPolynomial (Fin (n + 1)) K) (hF : F.IsHomogeneous d)
    (hsat : ∀ i : Fin (n + 1), ∃ N : ℕ, X i ^ N * F ∈ p.I) : F ∈ p.I := by
  classical

  choose Nf hNf using hsat
  set N : ℕ := Finset.univ.sup Nf with hN
  have hN' : ∀ i : Fin (n + 1), X i ^ N * F ∈ p.I := by
    intro i
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := Nf) (Finset.mem_univ i))
    have : (X i ^ N * F : MvPolynomial (Fin (n + 1)) K) = X i ^ c * (X i ^ Nf i * F) := by rw [hN, hc]; ring
    rw [this]; exact Ideal.mul_mem_left _ _ (hNf i)

  have hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ q ∈ s, q.IsHomogeneous m) ∧ p.I = Ideal.span s :=
    ⟨{f | f ∈ p.I ∧ f.IsHomogeneous m}, fun q hq => hq.2, hgen K p⟩
  have hmaxK : Module.finrank K (piece p.I (m + 1)) = Nat.macaulayPow m (Module.finrank K (piece p.I m)) := by
    rw [finrank_piece_eq, finrank_piece_eq, hmax]
  obtain ⟨G, hG0, hG⟩ := MvPolynomial.exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow n m K p.I hJ hmaxK

  obtain ⟨a, ha⟩ : ∃ a : Fin (n + 1) → K, MvPolynomial.eval a G ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hG0 (MvPolynomial.funext fun x => by rw [hcon x, map_zero])
  set ℓ : MvPolynomial (Fin (n + 1)) K := ∑ i, C (a i) * X i with hℓ
  have hℓhom : ℓ.IsHomogeneous 1 := by
    rw [hℓ]
    refine IsHomogeneous.sum _ _ _ fun i _ => ?_
    exact isHomogeneous_C_mul_X (a i) i

  have hbig : ℓ ^ ((n + 1) * N) * F ∈ p.I := by
    refine mul_mem_of_forall_X_pow_mul_mem p.I F N hN' _ ?_
    simpa using hℓhom.pow ((n + 1) * N)

  have hpeel : ∀ j : ℕ, ℓ ^ j * F ∈ p.I → F ∈ p.I := by
    intro j
    induction j with
    | zero => intro h; simpa using h
    | succ j ih =>
      intro h
      apply ih
      refine hG a ha (j + d) (by omega) (ℓ ^ j * F) (by simpa using (hℓhom.pow j).mul hF) ?_
      rw [hℓ] at h ⊢
      rw [pow_succ'] at h
      rwa [mul_assoc] at h
  exact hpeel _ hbig

end SatHighField

open SatHighField in
theorem solution
    (n : ℕ) (P : Polynomial ℚ)
    (hP : ∃ (K : Type) (_ : Field K) (I : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) ∧
      ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d → (Module.finrank K (piece I d) : ℚ) = P.eval (d : ℚ)) :
    ∃ D₀ : ℕ, ∀ m : ℕ, D₀ ≤ m → ∀ (K : Type) [Field K] (p : Point K n (hilbertFunctionOf n P m))
      (d : ℕ), m ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) K), F.IsHomogeneous d →
        (∀ i : Fin (n + 1), ∃ N : ℕ, X i ^ N * F ∈ p.I) → F ∈ p.I := by
  classical
  obtain ⟨Dg, hDg⟩ := MvPolynomial.exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval n P hP
  obtain ⟨K₀, _, I₀, hI₀, d₁, hd₁⟩ := hP

  set H : ℕ → ℕ := fun e => Int.toNat ⌊P.eval (e : ℚ)⌋ with hH
  have hHcast : ∀ e : ℕ, d₁ ≤ e → ((H e : ℕ) : ℚ) = P.eval (e : ℚ) := by
    intro e he
    rw [hH]; dsimp only
    rw [← hd₁ e he, Int.floor_natCast, Int.toNat_natCast]

  have hMac : ∀ e, max Dg (max d₁ 1) ≤ e → H (e + 1) ≤ Nat.macaulayPow e (H e) := by
    intro e he
    have heg : Dg ≤ e := le_trans (le_max_left _ _) he
    have he1 : d₁ ≤ e := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) he
    have he2 : 1 ≤ e := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) he
    obtain ⟨K₂, _, J₂, hJ₂, hJm, hJm1⟩ := (hDg e heg).2
    have hhom := homogeneous_of_span J₂ hJ₂
    have hM := MvPolynomial.finrank_piece_succ_le_macaulayPow n e he2 K₂ J₂ hhom
    have h1 : Module.finrank K₂ (piece J₂ e) = H e := by
      exact_mod_cast (hJm.trans (hHcast e he1).symm)
    have h2 : Module.finrank K₂ (piece J₂ (e + 1)) = H (e + 1) := by
      have := hHcast (e + 1) (by omega)
      push_cast at this hJm1
      exact_mod_cast (hJm1.trans this.symm)
    rw [← h1, ← h2]; exact hM
  obtain ⟨D₁, hD₁⟩ := Nat.exists_forall_eq_macaulayPow_of_forall_le_macaulayPow H (max Dg (max d₁ 1)) (le_trans (le_max_right _ _) (le_max_right _ _)) hMac
  refine ⟨max D₁ (max Dg (max d₁ 1)), fun m hm K _ p d hd F hF hsat => ?_⟩
  have hmD₁ : D₁ ≤ m := le_trans (le_max_left _ _) hm
  have hmg : Dg ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm
  have hm₁ : d₁ ≤ m := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hm
  have hm1 : 1 ≤ m := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hm

  have hhH : ∀ e, m ≤ e → hilbertFunctionOf n P m e = H e := by
    intro e he; simp [hilbertFunctionOf, not_lt.mpr he, hH]
  have hcast : ∀ e : ℕ, m ≤ e → ((hilbertFunctionOf n P m e : ℕ) : ℚ) = P.eval (e : ℚ) := by
    intro e he; rw [hhH e he]; exact hHcast e (le_trans hm₁ he)

  have hgen : ∀ (K : Type) [Field K] (p : Point K n (hilbertFunctionOf n P m)),
      p.I = Ideal.span {f | f ∈ p.I ∧ f.IsHomogeneous m} := by
    intro K _ p
    refine AlgebraicGeometry.HilbertFunctor.Point.I_eq_span_of_forall_finrank_piece_succ_le n m (hilbertFunctionOf n P m) ?_ ?_ K p
    · intro d hd; simp [hilbertFunctionOf, hd]
    · intro e he K' _ J hJ hJe
      have he1 : m ≤ e + 1 := Nat.le_succ_of_le he
      have h1 := (hDg e (le_trans hmg he)).1 K' J hJ (by rw [hJe]; exact hcast e he)
      rw [show ((e : ℚ) + 1) = ((e + 1 : ℕ) : ℚ) by push_cast; ring, ← hcast (e + 1) he1] at h1
      exact_mod_cast h1
  have hmax : Nat.macaulayPow m (hilbertFunctionOf n P m m) = hilbertFunctionOf n P m (m + 1) := by
    rw [hhH m le_rfl, hhH (m + 1) (Nat.le_succ m)]; exact (hD₁ m hmD₁).symm

  let K' := AlgebraicClosure K
  obtain ⟨p', hp'⟩ := AlgebraicGeometry.HilbertFunctor.exists_point_I_eq_map n (hilbertFunctionOf n P m) K K' p
  have hF' : MvPolynomial.map (algebraMap K K') F ∈ p'.I := by
    refine core P m hm1 hgen hmax K' p' d hd _ (hF.map _) fun i => ?_
    obtain ⟨Ni, hNi⟩ := hsat i
    refine ⟨Ni, ?_⟩
    rw [hp']
    have : (X i ^ Ni * MvPolynomial.map (algebraMap K K') F : MvPolynomial (Fin (n + 1)) K') =
        MvPolynomial.map (algebraMap K K') (X i ^ Ni * F) := by simp [map_mul, map_pow, map_X]
    rw [this]; exact Ideal.mem_map_of_mem _ hNi

  obtain ⟨-, hbc⟩ := AlgebraicGeometry.HilbertFunctor.exists_linearEquiv_baseChange_piece_map n K K' p.I p.homogeneous
  obtain ⟨e, he⟩ := hbc d
  let G : ↥(homogeneousSubmodule (Fin (n + 1)) K d) := ⟨F, (mem_homogeneousSubmodule d F).mpr hF⟩
  have hzero' : e ((1 : K') ⊗ₜ[K] (Submodule.Quotient.mk G : piece p.I d)) = 0 := by
    rw [he F hF, Submodule.Quotient.mk_eq_zero]
    simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.restrictScalars_mem]
    rw [← hp']; exact hF'
  have hzero : ((1 : K') ⊗ₜ[K] (Submodule.Quotient.mk G : piece p.I d)) = 0 :=
    (LinearEquiv.map_eq_zero_iff e).mp hzero'

  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K K')
    (LinearMap.ker_eq_bot.mpr (by exact (algebraMap K K').injective))
  have hx : (Submodule.Quotient.mk G : piece p.I d) = 0 := by
    have := congrArg (fun z => TensorProduct.lid K (piece p.I d) (r.rTensor (piece p.I d) z)) hzero
    simp only [map_zero, LinearMap.rTensor_tmul] at this
    have hr1 : r (1 : K') = 1 := by
      have := LinearMap.congr_fun hr (1 : K)
      simpa using this
    rw [hr1, TensorProduct.lid_tmul, one_smul] at this
    exact this
  rw [Submodule.Quotient.mk_eq_zero] at hx
  simpa [Submodule.mem_comap] using hx

end
end S_AlgebraicGeometry_HilbertFunctor_exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf_field
end P2MW
export P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf_field (solution)
