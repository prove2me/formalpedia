-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsUnitFormSelfOfNotMem
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsUnitFormSelfOfNotMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:15:38.257125+00:00
-- url     : https://prove2.me/theorems/2c517e71-e91a-40a3-8fc5-e0e4f38a1c77
-- title:
--   Exists Is Unit Form Self Of Not Mem
-- statement:
--   Definitions and structural lemmas for Exists Is Unit Form Self Of Not Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsIsUnitFormSelfOfNotMem.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
namespace GlobalTheory.QuadraticEtale
section Galois
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (σ : S →+* S)
variable [IsLocalRing R]
theorem algebraMap_mem_of_isMaximal [Algebra.IsIntegral R S] (n : Ideal S) [n.IsMaximal]
    {r : R} (hr : r ∈ maximalIdeal R) : algebraMap R S r ∈ n := by
  have h := eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) n)
  rw [← h] at hr
  exact hr
variable {M : Type*} [AddCommGroup M] [Module S M]
end Galois
section Quadratic
open TensorProduct Module
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
theorem exists_basis_one [IsLocalRing R] [Module.Free R S] (hrank : finrank R S = 2) :
    ∃ B : Basis (Fin 2) R S, B 0 = 1 := by
  haveI : Module.Finite R S := Module.finite_of_finrank_pos (by omega)
  haveI : Nontrivial S := Module.nontrivial_of_finrank_pos (R := R) (by omega)
  have aux : ∀ b : Basis (Fin 2) R S, IsUnit (b.repr 1 0) → ∃ B : Basis (Fin 2) R S, B 0 = 1 := by
    intro b hb
    have h1 : (1 : S) = b.repr 1 0 • b 0 + b.repr 1 1 • b 1 := by
      conv_lhs => rw [← b.sum_repr 1]
      rw [Fin.sum_univ_two]
    obtain ⟨w, hw⟩ := hb.exists_left_inv
    have hli : LinearIndependent R ![(1 : S), b 1] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h0 := congrArg (fun x => b.repr x 0) hst
      have h2 := congrArg (fun x => b.repr x 1) hst
      simp at h0 h2
      have hs : s = 0 := by linear_combination w * h0 - s * hw
      exact ⟨hs, by simpa [hs] using h2⟩
    have hsp : ⊤ ≤ Submodule.span R (Set.range ![(1 : S), b 1]) := by
      rw [← b.span_eq, Submodule.span_le]
      have m1 : (1 : S) ∈ Submodule.span R (Set.range ![(1 : S), b 1]) :=
        Submodule.subset_span ⟨0, rfl⟩
      have m2 : b 1 ∈ Submodule.span R (Set.range ![(1 : S), b 1]) :=
        Submodule.subset_span ⟨1, rfl⟩
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · have : b 0 = w • (1 - b.repr 1 1 • b 1) := by
          conv_rhs => rw [sub_eq_of_eq_add h1, smul_smul, hw, one_smul]
        simp only [Fin.zero_eta, SetLike.mem_coe]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.sub_mem _ m1 (Submodule.smul_mem _ _ m2))
      · exact m2
    exact ⟨Basis.mk hli hsp, by simp⟩
  let b := Module.finBasisOfFinrankEq R S hrank
  by_cases h0 : IsUnit (b.repr 1 0)
  · exact aux b h0
  by_cases h1 : IsUnit (b.repr 1 1)
  · exact aux (b.reindex (Equiv.swap 0 1)) (by simpa using h1)
  exfalso
  obtain ⟨n, hn⟩ := Ideal.exists_maximal S
  apply hn.ne_top
  rw [Ideal.eq_top_iff_one, ← b.sum_repr 1, Fin.sum_univ_two, Algebra.smul_def, Algebra.smul_def]
  exact n.add_mem (n.mul_mem_right _ (algebraMap_mem_of_isMaximal n h0))
    (n.mul_mem_right _ (algebraMap_mem_of_isMaximal n h1))
theorem eq_coord (B : Basis (Fin 2) R S) (hB : B 0 = 1) (x : S) :
    x = algebraMap R S (B.repr x 0) + algebraMap R S (B.repr x 1) * B 1 := by
  conv_lhs => rw [← B.sum_repr x]
  rw [Fin.sum_univ_two, hB, Algebra.smul_def, Algebra.smul_def, mul_one]
theorem repr_coord_zero (B : Basis (Fin 2) R S) (hB : B 0 = 1) (r s : R) :
    B.repr (algebraMap R S r + algebraMap R S s * B 1) 0 = r := by
  rw [← mul_one (algebraMap R S r), ← hB, ← Algebra.smul_def, ← Algebra.smul_def]
  simp
theorem repr_coord_one (B : Basis (Fin 2) R S) (hB : B 0 = 1) (r s : R) :
    B.repr (algebraMap R S r + algebraMap R S s * B 1) 1 = s := by
  rw [← mul_one (algebraMap R S r), ← hB, ← Algebra.smul_def, ← Algebra.smul_def]
  simp
theorem coord_inj (B : Basis (Fin 2) R S) (hB : B 0 = 1) {r s r' s' : R}
    (h : algebraMap R S r + algebraMap R S s * B 1 = algebraMap R S r' + algebraMap R S s' * B 1) :
    r = r' ∧ s = s' :=
  ⟨by rw [← repr_coord_zero B hB r s, h, repr_coord_zero B hB],
    by rw [← repr_coord_one B hB r s, h, repr_coord_one B hB]⟩
theorem trace_coord (B : Basis (Fin 2) R S) (hB : B 0 = 1) {a b : R}
    (hab : B 1 * B 1 = algebraMap R S b + algebraMap R S a * B 1) (r s : R) :
    Algebra.trace R S (algebraMap R S r + algebraMap R S s * B 1) = 2 * r + s * a := by
  rw [Algebra.trace_eq_matrix_trace B, Matrix.trace_fin_two, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, hB, mul_one, repr_coord_zero B hB]
  have : (algebraMap R S r + algebraMap R S s * B 1) * B 1
      = algebraMap R S (s * b) + algebraMap R S (r + s * a) * B 1 := by
    simp only [map_add, map_mul]
    linear_combination (algebraMap R S s) * hab
  rw [this, repr_coord_one B hB]
  ring
theorem isUnit_different [Algebra.FormallyUnramified R S] (B : Basis (Fin 2) R S) (hB : B 0 = 1)
    {a b : R} (hab : B 1 * B 1 = algebraMap R S b + algebraMap R S a * B 1) :
    IsUnit (2 * B 1 - algebraMap R S a) := by
  haveI : Module.Finite R S := Module.Finite.of_basis B
  let L : S ⊗[R] S →ₗ[R] S :=
    LinearMap.mul' R S ∘ₗ LinearMap.lTensor S (Algebra.linearMap R S ∘ₗ B.coord 1)
  have hL : ∀ x y, L (x ⊗ₜ y) = x * algebraMap R S (B.repr y 1) := fun x y => by simp [L]
  have h1 : ∀ (s : S) z, L ((s ⊗ₜ 1) * z) = s * L z := by
    intro s z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => rw [Algebra.TensorProduct.tmul_mul_tmul, hL, hL, one_mul, mul_assoc]
    | add x y hx hy => rw [mul_add, map_add, map_add, hx, hy, mul_add]
  have h2 : ∀ z, Algebra.TensorProduct.lmul' R (S := S) z
      = L ((1 ⊗ₜ B 1) * z) + (B 1 - algebraMap R S a) * L z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, hL, hL, one_mul,
        Algebra.TensorProduct.lmul'_apply_tmul]
      have hy := eq_coord B hB y
      have : B 1 * y = algebraMap R S (B.repr y 1 * b)
          + algebraMap R S (B.repr y 0 + B.repr y 1 * a) * B 1 := by
        simp only [map_add, map_mul]
        linear_combination (algebraMap R S (B.repr y 1)) * hab + B 1 * hy
      rw [this, repr_coord_one B hB]
      simp only [map_add, map_mul]
      linear_combination x * hy
    | add x y hx hy => rw [mul_add, map_add, map_add, map_add, hx, hy]; ring
  have h3 := h2 (Algebra.FormallyUnramified.elem R S)
  rw [Algebra.FormallyUnramified.lmul_elem, Algebra.FormallyUnramified.one_tmul_mul_elem, h1] at h3
  exact IsUnit.of_mul_eq_one (L (Algebra.FormallyUnramified.elem R S)) (by linear_combination -h3)
theorem apply_eq_of_ne_one [IsLocalRing R] [Algebra.FormallyUnramified R S]
    (B : Basis (Fin 2) R S) (hB : B 0 = 1)
    {a b : R} (hab : B 1 * B 1 = algebraMap R S b + algebraMap R S a * B 1)
    (σ : S ≃ₐ[R] S) (hσ : σ ≠ 1) : σ (B 1) = algebraMap R S a - B 1 := by
  haveI : Module.Finite R S := Module.Finite.of_basis B
  haveI : Nontrivial S := ⟨⟨B 0, 0, B.ne_zero 0⟩⟩
  have hD : IsUnit (a ^ 2 + 4 * b) := by
    by_contra hD
    obtain ⟨n, hn⟩ := Ideal.exists_maximal S
    have h1 := algebraMap_mem_of_isMaximal n (r := a ^ 2 + 4 * b) hD
    have h2 := (isUnit_different B hB hab).pow 2
    refine hn.ne_top (n.eq_top_of_isUnit_mem h1 ?_)
    convert h2 using 1
    simp only [map_add, map_mul, map_pow, map_ofNat]
    linear_combination (-4) * hab
  obtain ⟨c, d, hcd⟩ : ∃ c d : R, σ (B 1) = algebraMap R S c + algebraMap R S d * B 1 :=
    ⟨_, _, eq_coord B hB _⟩
  have hd : IsUnit d := by
    obtain ⟨r, s, hrs⟩ : ∃ r s : R, σ.symm (B 1) = algebraMap R S r + algebraMap R S s * B 1 :=
      ⟨_, _, eq_coord B hB _⟩
    have h1 := congrArg σ hrs
    rw [AlgEquiv.apply_symm_apply, map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes,
      hcd] at h1
    have h2 := coord_inj B hB (r := r + s * c) (s := d * s) (r' := 0) (s' := 1) (by
      simp only [map_add, map_mul, map_zero, map_one]; linear_combination -h1)
    exact IsUnit.of_mul_eq_one s h2.2
  have h1 := congrArg σ hab
  rw [map_add, map_mul, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hcd] at h1
  obtain ⟨e1, e2⟩ := coord_inj B hB (r := c ^ 2 + d ^ 2 * b) (s := d * (2 * c + d * a))
    (r' := b + a * c) (s' := d * a) (by
      simp only [map_add, map_mul, map_pow, map_ofNat]
      linear_combination h1 - (algebraMap R S d) ^ 2 * hab)
  have e3 : 2 * c + d * a = a := hd.mul_left_cancel e2
  have e4 : (1 - d) * (1 + d) = 0 := by
    apply hD.mul_left_cancel
    linear_combination (-4) * e1 + (2 * c - a - d * a) * e3
  have e5 : c * (c - a) = 0 := by linear_combination e1 + b * e4
  have hne : ¬ (c = 0 ∧ d = 1) := by
    rintro ⟨rfl, rfl⟩
    apply hσ
    ext x
    rw [eq_coord B hB x]
    simp only [map_add, map_mul, AlgEquiv.commutes, hcd, AlgEquiv.one_apply]
    simp
  have h2a : IsUnit (2 : R) ∨ IsUnit a := by
    rcases isUnit_or_isUnit_of_isUnit_add hD with h | h
    · exact Or.inr (isUnit_pow_iff two_ne_zero |>.1 h)
    · refine Or.inl (isUnit_of_mul_isUnit_left (y := 2 * b) ?_)
      convert h using 1; ring
  have main : c = a ∧ d = -1 := by
    by_cases hd1 : IsUnit (1 - d)
    · have hd' : d = -1 := by
        have : 1 + d = 0 := hd1.mul_left_cancel (by rw [e4, mul_zero])
        linear_combination this
      subst hd'
      have h2 : IsUnit (2 : R) := by convert hd1 using 1; ring
      exact ⟨h2.mul_left_cancel (by linear_combination e3), rfl⟩
    · rcases h2a with h2 | ha
      · exfalso
        have h3 : IsUnit (1 + d) := by
          have : IsUnit ((1 - d) + (1 + d)) := by convert h2 using 1; ring
          exact (isUnit_or_isUnit_of_isUnit_add this).resolve_left hd1
        have hd' : d = 1 := by
          have : 1 - d = 0 := h3.mul_right_cancel (by rw [e4, zero_mul])
          linear_combination -this
        subst hd'
        exact hne ⟨h2.mul_left_cancel (by linear_combination e3), rfl⟩
      · have : IsUnit (c + (a - c)) := by convert ha using 1; ring
        rcases isUnit_or_isUnit_of_isUnit_add this with hc | hc
        · have hca : c = a := by
            have : c - a = 0 := hc.mul_left_cancel (by rw [e5, mul_zero])
            linear_combination this
          subst hca
          exact ⟨rfl, ha.mul_left_cancel (by linear_combination e3)⟩
        · exfalso
          have hc0 : c = 0 := hc.mul_left_cancel (by linear_combination -e5)
          subst hc0
          exact hne ⟨rfl, ha.mul_left_cancel (by linear_combination e3)⟩
  rw [hcd, main.1, main.2]
  simp only [map_neg, map_one]
  ring
end Quadratic
section Unramified
open Module
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
  [Module.Free R S] [Algebra.FormallyUnramified R S]
theorem add_apply_eq_trace (hrank : finrank R S = 2) (σ : S ≃ₐ[R] S) (hσ : σ ≠ 1) (x : S) :
    x + σ x = algebraMap R S (Algebra.trace R S x) := by
  obtain ⟨B, hB⟩ := exists_basis_one hrank
  have hab := eq_coord B hB (B 1 * B 1)
  have h := apply_eq_of_ne_one B hB hab σ hσ
  rw [eq_coord B hB x, trace_coord B hB hab]
  simp only [map_add, map_mul, AlgEquiv.commutes, h, map_ofNat]
  ring
theorem existsUnique_ne_one (hrank : finrank R S = 2) : ∃! σ : S ≃ₐ[R] S, σ ≠ 1 := by
  haveI : Nontrivial S := Module.nontrivial_of_finrank_pos (R := R) (by omega)
  refine existsUnique_of_exists_of_unique ?_ fun σ τ hσ hτ => ?_
  swap
  · ext x
    linear_combination add_apply_eq_trace hrank σ hσ x - add_apply_eq_trace hrank τ hτ x
  obtain ⟨B, hB⟩ := exists_basis_one hrank
  obtain ⟨a, b, hab⟩ : ∃ a b, B 1 * B 1 = algebraMap R S b + algebraMap R S a * B 1 :=
    ⟨_, _, eq_coord B hB _⟩
  let f : S →ₗ[R] S := Algebra.linearMap R S ∘ₗ Algebra.trace R S - LinearMap.id
  have hf : ∀ r s, f (algebraMap R S r + algebraMap R S s * B 1)
      = algebraMap R S (r + s * a) + algebraMap R S (-s) * B 1 := by
    intro r s
    simp only [f, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
      Algebra.linearMap_apply, trace_coord B hB hab]
    simp only [map_add, map_mul, map_neg, map_ofNat]
    ring
  have hc : ∀ x, ∃ r s, x = algebraMap R S r + algebraMap R S s * B 1 :=
    fun x => ⟨_, _, eq_coord B hB _⟩
  have hone : f 1 = 1 := by simpa using hf 1 0
  have hmul : ∀ x y, f (x * y) = f x * f y := by
    intro x y
    obtain ⟨r, s, rfl⟩ := hc x
    obtain ⟨r', s', rfl⟩ := hc y
    have : (algebraMap R S r + algebraMap R S s * B 1) * (algebraMap R S r' + algebraMap R S s' * B 1)
        = algebraMap R S (r * r' + s * s' * b)
          + algebraMap R S (r * s' + s * r' + s * s' * a) * B 1 := by
      simp only [map_add, map_mul]
      linear_combination (algebraMap R S s * algebraMap R S s') * hab
    rw [this, hf, hf, hf]
    simp only [map_add, map_mul, map_neg]
    linear_combination (-(algebraMap R S s * algebraMap R S s')) * hab
  have hinv : ∀ x, f (f x) = x := by
    intro x
    obtain ⟨r, s, rfl⟩ := hc x
    rw [hf, hf]
    simp only [map_add, map_mul, map_neg]
    ring
  let g : S →ₐ[R] S := AlgHom.ofLinearMap f hone hmul
  refine ⟨AlgEquiv.ofAlgHom g g (AlgHom.ext hinv) (AlgHom.ext hinv), fun h => ?_⟩
  have h1 : f (B 1) = B 1 := congrArg (fun σ : S ≃ₐ[R] S => σ (B 1)) h
  have h2 := hf 0 1
  simp only [map_zero, map_one, zero_add, one_mul, map_neg, h1] at h2
  have h3 := isUnit_different B hB hab
  rw [show 2 * B 1 - algebraMap R S a = 0 by linear_combination h2] at h3
  exact not_isUnit_zero h3
section Star
variable [StarRing S]
end Star
end Unramified
example (R : Type) [CommRing R] [IsLocalRing R] : ∃! σ : (R × R) ≃ₐ[R] (R × R), σ ≠ 1 := by
  haveI : Algebra.FormallyUnramified R (Fin 2 → R) :=
    (Algebra.FormallyUnramified.pi_iff (R := R) fun _ : Fin 2 => R).2 fun _ => inferInstance
  haveI : Algebra.FormallyUnramified R (R × R) :=
    Algebra.FormallyUnramified.of_equiv
      (AlgEquiv.ofRingEquiv (f := RingEquiv.piFinTwo fun _ : Fin 2 => R) fun _ => rfl)
  exact existsUnique_ne_one (by simp)
end GlobalTheory.QuadraticEtale


