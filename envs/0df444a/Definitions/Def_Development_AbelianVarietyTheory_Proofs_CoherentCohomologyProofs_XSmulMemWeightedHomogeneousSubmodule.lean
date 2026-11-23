-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:26:09.139307+00:00
-- url     : https://prove2.me/theorems/cde5ae44-7c59-49f2-8a1e-7bc0e59ce870
-- title:
--   XSmul Mem Weighted Homogeneous Submodule
-- statement:
--   Definitions and structural lemmas for XSmul Mem Weighted Homogeneous Submodule, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/XSmulMemWeightedHomogeneousSubmodule.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter
namespace GlobalTheory
section Difference
variable {K : Type*} [Field K]
theorem coeff_comp_X_add_C_of_natDegree_le_add_one (P : K[X]) (r : K) (e : ℕ) (hP : P.natDegree ≤ e + 1) :
    (P.comp (X + C r)).coeff e = P.coeff e + r * (e + 1) * P.coeff (e + 1) := by
  rw [← taylor_apply, taylor_coeff]
  have hd : (hasseDeriv e P).natDegree ≤ 1 := by
    have := natDegree_hasseDeriv_le P e
    omega
  rw [eq_X_add_C_of_natDegree_le_one hd]
  simp only [eval_add, eval_mul, eval_C, eval_X, hasseDeriv_coeff]
  rw [show 1 + e = e + 1 by omega, zero_add, Nat.choose_self, Nat.choose_succ_self_right]
  push_cast
  ring
theorem coeff_comp_X_add_C_sub (P : K[X]) (r : K) (e : ℕ) (hP : P.degree ≤ (e + 1 : ℕ)) :
    (P.comp (X + C r) - P).coeff e = r * (e + 1) * P.coeff (e + 1) := by
  rw [coeff_sub, coeff_comp_X_add_C_of_natDegree_le_add_one P r e (natDegree_le_iff_degree_le.mpr hP)]
  ring
theorem coeff_comp_X_add_C_of_natDegree_le (P : K[X]) (r : K) (e : ℕ) (hP : P.natDegree ≤ e) :
    (P.comp (X + C r)).coeff e = P.coeff e := by
  rw [← taylor_apply, taylor_coeff]
  have hd : (hasseDeriv e P).natDegree = 0 := by
    have := natDegree_hasseDeriv_le P e
    omega
  rw [eq_C_of_natDegree_eq_zero hd, eval_C, hasseDeriv_coeff, zero_add, Nat.choose_self,
    Nat.cast_one, one_mul]
theorem degree_comp_X_add_C_sub_lt (P : K[X]) (r : K) (e : ℕ) (hP : P.degree ≤ (e : ℕ)) :
    (P.comp (X + C r) - P).degree < (e : ℕ) := by
  have hn : P.natDegree ≤ e := natDegree_le_iff_degree_le.mpr hP
  have h1 : (P.comp (X + C r)).natDegree ≤ e := by
    rw [← taylor_apply, natDegree_taylor]
    exact hn
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_sub]
  rcases hm.lt_or_eq with h | h
  · rw [coeff_eq_zero_of_natDegree_lt (p := P.comp (X + C r)) (by omega),
      coeff_eq_zero_of_natDegree_lt (p := P) (by omega), sub_zero]
  · rw [← h, coeff_comp_X_add_C_of_natDegree_le P r e hn, sub_self]
variable [CharZero K]
theorem exists_comp_X_add_one_sub_eq (d : ℕ) (Q : K[X]) (hQ : Q.degree < (d : ℕ)) :
    ∃ P : K[X], P.degree ≤ (d : ℕ) ∧ P.comp (X + C 1) - P = Q := by
  induction d generalizing Q with
  | zero =>
    have hQ0 : Q = 0 := by
      ext m
      simpa using (degree_lt_iff_coeff_zero Q 0).1 hQ m (Nat.zero_le m)
    exact ⟨0, by simp, by simp [hQ0]⟩
  | succ d ih =>
    have hd1 : (d : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero d
    have hR0 : (C (Q.coeff d / (d + 1)) * X ^ (d + 1)).degree ≤ ((d + 1 : ℕ) : WithBot ℕ) :=
      degree_C_mul_X_pow_le _ _
    have hQ' : (Q - ((C (Q.coeff d / (d + 1)) * X ^ (d + 1)).comp (X + C 1)
        - C (Q.coeff d / (d + 1)) * X ^ (d + 1))).degree < (d : WithBot ℕ) := by
      rw [degree_lt_iff_coeff_zero]
      intro m hm
      rw [coeff_sub]
      rcases hm.lt_or_eq with h | h
      · have h1 := degree_comp_X_add_C_sub_lt (C (Q.coeff d / (d + 1)) * X ^ (d + 1)) 1 (d + 1) hR0
        rw [(degree_lt_iff_coeff_zero _ _).1 hQ m (by omega),
          (degree_lt_iff_coeff_zero _ _).1 h1 m (by omega), sub_zero]
      · rw [← h, coeff_comp_X_add_C_sub _ 1 d hR0, coeff_C_mul_X_pow, if_pos rfl, one_mul,
          mul_div_cancel₀ _ hd1, sub_self]
    obtain ⟨P', hP'd, hP'⟩ := ih _ hQ'
    refine ⟨P' + C (Q.coeff d / (d + 1)) * X ^ (d + 1), ?_, ?_⟩
    · exact (degree_add_le _ _).trans (max_le (hP'd.trans (by exact_mod_cast Nat.le_succ d)) hR0)
    · rw [add_comp]
      linear_combination hP'
theorem eval_comp_X_add_one_sub_eq_eval_succ_sub (P : K[X]) (n : ℤ) :
    (P.comp (X + C 1) - P).eval (n : K) = P.eval ((n + 1 : ℤ) : K) - P.eval (n : K) := by
  simp [eval_comp]
theorem exists_polynomial_of_diff_from {f : ℤ → K} {Q : K[X]} {d : ℕ} (hQ : Q.degree < (d : ℕ))
    (N : ℤ) (h : ∀ n, N ≤ n → f (n + 1) - f n = Q.eval (n : K)) :
    ∃ P : K[X], P.degree ≤ (d : ℕ) ∧ P.comp (X + C 1) - P = Q ∧
      ∀ n, N ≤ n → f n = P.eval (n : K) := by
  obtain ⟨P0, hP0d, hP0⟩ := exists_comp_X_add_one_sub_eq d Q hQ
  have key : ∀ k : ℕ, f (N + k) - P0.eval ((N + k : ℤ) : K) = f N - P0.eval (N : K) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 := h (N + k) (by omega)
      have h2 := eval_comp_X_add_one_sub_eq_eval_succ_sub P0 (N + k)
      rw [hP0] at h2
      have e1 : (N + ((k + 1 : ℕ) : ℤ)) = N + k + 1 := by push_cast; ring
      rw [e1]
      linear_combination ih + h1 + h2
  refine ⟨P0 + C (f N - P0.eval (N : K)), ?_, ?_, ?_⟩
  · exact (degree_add_le _ _).trans (max_le hP0d (degree_C_le.trans (by exact_mod_cast Nat.zero_le d)))
  · rw [add_comp, C_comp]
    linear_combination hP0
  · intro n hn
    obtain ⟨k, rfl⟩ := Int.le.dest hn
    rw [eval_add, eval_C]
    linear_combination key k
theorem exists_polynomial_of_diff_eventually {f : ℤ → K} {Q : K[X]} {d : ℕ}
    (hQ : Q.degree < (d : ℕ)) (h : ∀ᶠ n : ℤ in atTop, f (n + 1) - f n = Q.eval (n : K)) :
    ∃ P : K[X], P.degree ≤ (d : ℕ) ∧ P.comp (X + C 1) - P = Q ∧
      (∀ e, d = e + 1 → Q.coeff e = d * P.coeff d) ∧
      ∀ᶠ n : ℤ in atTop, f n = P.eval (n : K) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h
  obtain ⟨P, hPd, hPQ, hP⟩ := exists_polynomial_of_diff_from hQ N hN
  refine ⟨P, hPd, hPQ, ?_, Filter.eventually_atTop.2 ⟨N, hP⟩⟩
  rintro e rfl
  rw [← hPQ, coeff_comp_X_add_C_sub P 1 e hPd]
  push_cast
  ring
end Difference
namespace GradedHilbert
open DirectSum
section Ring
variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
noncomputable def proj (ℳ : ℤ → Submodule R M) [Decomposition ℳ] (n : ℤ) : M →ₗ[R] M :=
  (ℳ n).subtype ∘ₗ component R ℤ (fun i => ℳ i) n ∘ₗ (decomposeLinearEquiv ℳ).toLinearMap
theorem proj_apply (ℳ : ℤ → Submodule R M) [Decomposition ℳ] (n : ℤ) (m : M) :
    proj ℳ n m = (decompose ℳ m n : M) := rfl
theorem proj_mem (ℳ : ℤ → Submodule R M) [Decomposition ℳ] (n : ℤ) (m : M) :
    proj ℳ n m ∈ ℳ n := by
  rw [proj_apply]
  exact (decompose ℳ m n).2
theorem proj_of_mem (ℳ : ℤ → Submodule R M) [Decomposition ℳ] {n : ℤ} {m : M} (h : m ∈ ℳ n) :
    proj ℳ n m = m := by rw [proj_apply, decompose_of_mem_same ℳ h]
theorem proj_of_mem_ne (ℳ : ℤ → Submodule R M) [Decomposition ℳ] {i n : ℤ} {m : M}
    (h : m ∈ ℳ i) (hi : i ≠ n) : proj ℳ n m = 0 := by rw [proj_apply, decompose_of_mem_ne ℳ h hi]
theorem proj_map (ℳ : ℤ → Submodule R M) [Decomposition ℳ] (𝒩 : ℤ → Submodule R N)
    [Decomposition 𝒩] (f : M →ₗ[R] N) (d : ℤ) (hf : ∀ n, ∀ m ∈ ℳ n, f m ∈ 𝒩 (n + d))
    (n : ℤ) (m : M) : proj 𝒩 (n + d) (f m) = f (proj ℳ n m) := by
  classical
  conv_lhs => rw [← sum_support_decompose ℳ m]
  rw [map_sum, map_sum, Finset.sum_eq_single n]
  · rw [proj_of_mem 𝒩 (hf n _ (decompose ℳ m n).2), proj_apply]
  · intro i _ hi
    exact proj_of_mem_ne 𝒩 (hf i _ (decompose ℳ m i).2) (by omega)
  · intro hn
    rw [DFinsupp.notMem_support_iff.1 hn]
    simp
theorem exists_bound_proj (ℳ : ℤ → Submodule R M) [Decomposition ℳ] (G : Finset M) :
    ∃ b : ℤ, ∀ g ∈ G, ∀ n : ℤ, b < |n| → proj ℳ n g = 0 := by
  classical
  refine ⟨∑ g ∈ G, ∑ i ∈ (decompose ℳ g).support, |i|, ?_⟩
  intro g hg n hn
  rw [proj_apply]
  by_contra hne
  have hmem : n ∈ (decompose ℳ g).support := by
    rw [DFinsupp.mem_support_iff]
    intro h0
    exact hne (by simp [h0])
  have h1 : |n| ≤ ∑ i ∈ (decompose ℳ g).support, |i| :=
    Finset.single_le_sum (f := fun i => |i|) (fun i _ => abs_nonneg i) hmem
  have h2 : ∑ i ∈ (decompose ℳ g).support, |i| ≤ ∑ g ∈ G, ∑ i ∈ (decompose ℳ g).support, |i| :=
    Finset.single_le_sum (f := fun g => ∑ i ∈ (decompose ℳ g).support, |i|)
      (fun g _ => Finset.sum_nonneg (fun i _ => abs_nonneg i)) hg
  linarith
variable {ι : Type*} [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
noncomputable abbrev mul (M : Type*) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M] (p : MvPolynomial ι R) : M →ₗ[R] M :=
  (LinearMap.lsmul (MvPolynomial ι R) M p).restrictScalars R
theorem smul_mem_of_X_smul_mem (P : Submodule R M)
    (hP : ∀ i, ∀ m ∈ P, (MvPolynomial.X i : MvPolynomial ι R) • m ∈ P)
    (p : MvPolynomial ι R) : ∀ m ∈ P, p • m ∈ P := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    intro m hm
    rw [← MvPolynomial.algebraMap_eq, algebraMap_smul]
    exact P.smul_mem a hm
  | add p q hp hq =>
    intro m hm
    rw [add_smul]
    exact P.add_mem (hp m hm) (hq m hm)
  | mul_X p i hp =>
    intro m hm
    rw [mul_smul]
    exact hp _ (hP i m hm)
theorem mem_of_mem_span (P : Submodule R M)
    (hP : ∀ i, ∀ m ∈ P, (MvPolynomial.X i : MvPolynomial ι R) • m ∈ P) {G : Set M}
    (hG : ∀ g ∈ G, g ∈ P) {m : M} (hm : m ∈ Submodule.span (MvPolynomial ι R) G) : m ∈ P := by
  induction hm using Submodule.span_induction with
  | mem x hx => exact hG x hx
  | zero => exact P.zero_mem
  | add x y _ _ hx hy => exact P.add_mem hx hy
  | smul a x _ hx => exact smul_mem_of_X_smul_mem P hP a x hx
variable (ℳ : ℤ → Submodule R M)
  (hX : ∀ (i : ι) (n : ℤ), ∀ m ∈ ℳ n, (MvPolynomial.X i : MvPolynomial ι R) • m ∈ ℳ (n + 1))
include hX
theorem X_pow_smul_mem_add_nat_cast (i : ι) (k : ℕ) (n : ℤ) (m : M) (hm : m ∈ ℳ n) :
    ((MvPolynomial.X i : MvPolynomial ι R) ^ k) • m ∈ ℳ (n + k) := by
  induction k with
  | zero => simpa using hm
  | succ k ih =>
    rw [pow_succ', mul_smul, Nat.cast_succ, ← add_assoc]
    exact hX i _ _ ih
theorem monomial_smul_mem_add_degree (s : ι →₀ ℕ) (a : R) :
    ∀ n : ℤ, ∀ m ∈ ℳ n, (MvPolynomial.monomial s a) • m ∈ ℳ (n + s.degree) := by
  refine Finsupp.induction s ?_ ?_
  · intro n m hm
    rw [← MvPolynomial.C_apply, ← MvPolynomial.algebraMap_eq, algebraMap_smul]
    simpa using (ℳ n).smul_mem a hm
  · intro i k s _ _ ih n m hm
    rw [MvPolynomial.monomial_single_add, mul_smul]
    have e : n + ((Finsupp.single i k + s).degree : ℤ) = n + s.degree + k := by
      rw [map_add, Finsupp.degree_single]
      push_cast
      ring
    rw [e]
    exact X_pow_smul_mem_add_nat_cast ℳ hX i k _ _ (ih n m hm)
theorem smul_mem_of_isHomogeneous {p : MvPolynomial ι R} {d : ℕ} (hp : p.IsHomogeneous d)
    (n : ℤ) (m : M) (hm : m ∈ ℳ n) : p • m ∈ ℳ (n + d) := by
  rw [p.as_sum, Finset.sum_smul]
  refine Submodule.sum_mem _ (fun s hs => ?_)
  have hsd : s.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (MvPolynomial.mem_support_iff.1 hs)
  have := monomial_smul_mem_add_degree ℳ hX s (p.coeff s) n m hm
  rwa [hsd] at this
variable [Decomposition ℳ]
theorem proj_X_smul (i : ι) (n : ℤ) (m : M) :
    proj ℳ n ((MvPolynomial.X i : MvPolynomial ι R) • m)
      = (MvPolynomial.X i : MvPolynomial ι R) • proj ℳ (n - 1) m := by
  have := proj_map ℳ ℳ (mul M (MvPolynomial.X i)) 1 (fun n m hm => hX i n m hm) (n - 1) m
  simpa [mul] using this
theorem finite_piece [Finite ι] [Module.Finite (MvPolynomial ι R) M] (n : ℤ) :
    Module.Finite R (ℳ n) := by
  classical
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := MvPolynomial ι R) (M := M)
  obtain ⟨b, hb⟩ := exists_bound_proj ℳ G
  have hmon : Submodule.span R (Set.range (fun s : ι →₀ ℕ =>
      (MvPolynomial.monomial s (1 : R) : MvPolynomial ι R))) = ⊤ := by
    have := (MvPolynomial.basisMonomials ι R).span_eq
    rwa [MvPolynomial.coe_basisMonomials] at this
  have hS0 := Submodule.span_smul_of_span_eq_top hmon (G : Set M)
  rw [hG, Submodule.restrictScalars_top] at hS0
  have hS : Submodule.span R (Set.image2 (fun a b => a • b) (Set.range (fun s : ι →₀ ℕ =>
      (MvPolynomial.monomial s (1 : R) : MvPolynomial ι R))) (G : Set M)) = ⊤ := hS0
  have hrange : ℳ n = Submodule.map (proj ℳ n) (Submodule.span R (Set.image2 (fun a b => a • b) (Set.range (fun s : ι →₀ ℕ =>
      (MvPolynomial.monomial s (1 : R) : MvPolynomial ι R))) (G : Set M))) := by
    rw [hS, Submodule.map_top]
    ext x
    rw [LinearMap.mem_range]
    constructor
    · intro hx
      exact ⟨x, proj_of_mem ℳ hx⟩
    · rintro ⟨y, rfl⟩
      exact proj_mem ℳ n y
  rw [Submodule.map_span] at hrange
  have hkey : ∀ (s : ι →₀ ℕ) (g : M),
      proj ℳ n ((MvPolynomial.monomial s (1 : R) : MvPolynomial ι R) • g)
        = (MvPolynomial.monomial s (1 : R) : MvPolynomial ι R) • proj ℳ (n - s.degree) g := by
    intro s g
    have := proj_map ℳ ℳ (mul M (MvPolynomial.monomial s (1 : R))) (s.degree : ℤ)
      (fun n' m hm => smul_mem_of_isHomogeneous ℳ hX
        (MvPolynomial.isHomogeneous_monomial _ rfl) n' m hm) (n - s.degree) g
    simpa [mul] using this
  have hT : ((fun q : M × (ι →₀ ℕ) => (MvPolynomial.monomial q.2 (1 : R) : MvPolynomial ι R) •
      proj ℳ (n - q.2.degree) q.1) ''
        ((G : Set M) ×ˢ {s : ι →₀ ℕ | s.degree ≤ (n + b).toNat})).Finite :=
    (G.finite_toSet.prod (Finsupp.finite_of_degree_le _)).image _
  have hfin : (proj ℳ n '' (Set.image2 (fun a b => a • b) (Set.range (fun s : ι →₀ ℕ =>
      (MvPolynomial.monomial s (1 : R) : MvPolynomial ι R))) (G : Set M))).Finite := by
    refine (hT.union (Set.finite_singleton (0 : M))).subset ?_
    rintro _ ⟨_, ⟨_, ⟨s, rfl⟩, g, hg, rfl⟩, rfl⟩
    rw [hkey]
    by_cases hs : s.degree ≤ (n + b).toNat
    · exact Or.inl ⟨(g, s), ⟨hg, hs⟩, rfl⟩
    · refine Or.inr ?_
      have h1 : n + b < (s.degree : ℤ) := by
        have := Int.self_le_toNat (n + b)
        have h2 : ((n + b).toNat : ℤ) < s.degree := by exact_mod_cast not_le.1 hs
        linarith
      have h4 : (s.degree : ℤ) - n ≤ |n - (s.degree : ℤ)| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      have h3 : b < |n - (s.degree : ℤ)| := by linarith
      rw [Set.mem_singleton_iff, hb g hg _ h3, smul_zero]
  rw [Module.Finite.iff_fg, hrange]
  exact Submodule.fg_span hfin
end Ring
section Field
open Module
variable {k : Type*} [Field k] {M N : Type*} [AddCommGroup M] [Module k M]
  [AddCommGroup N] [Module k N]
theorem finrank_map_add_finrank_inf_ker (f : M →ₗ[k] N) (B : Submodule k M)
    [Module.Finite k B] :
    finrank k (B.map f) + finrank k (B ⊓ LinearMap.ker f : Submodule k M) = finrank k B := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict B)
  rw [LinearMap.range_domRestrict] at h
  rw [← h]
  congr 1
  have hk : LinearMap.ker (f.domRestrict B) = Submodule.comap B.subtype (LinearMap.ker f) :=
    LinearMap.ker_comp B.subtype f
  rw [hk, ← Submodule.finrank_map_subtype_eq B (Submodule.comap B.subtype (LinearMap.ker f)),
    Submodule.map_comap_subtype]
theorem finrank_sup_map_add_finrank_inf_comap (f : M →ₗ[k] N) (B : Submodule k M)
    (A : Submodule k N) [Module.Finite k B] [Module.Finite k A] :
    finrank k (A ⊔ B.map f : Submodule k N) + finrank k (B ⊓ A.comap f : Submodule k M)
      = finrank k A + finrank k B := by
  have : Module.Finite k (B ⊓ A.comap f : Submodule k M) :=
    Submodule.finiteDimensional_of_le inf_le_left
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq A (B.map f)
  have h2 := finrank_map_add_finrank_inf_ker f B
  have h3 := finrank_map_add_finrank_inf_ker f (B ⊓ A.comap f)
  have e1 : (B ⊓ A.comap f).map f = A ⊓ B.map f := by
    ext y
    simp only [Submodule.mem_map, Submodule.mem_inf, Submodule.mem_comap]
    constructor
    · rintro ⟨x, ⟨hxB, hxA⟩, rfl⟩
      exact ⟨hxA, x, hxB, rfl⟩
    · rintro ⟨hyA, x, hxB, rfl⟩
      exact ⟨x, ⟨hxB, hyA⟩, rfl⟩
  have e2 : (B ⊓ A.comap f) ⊓ LinearMap.ker f = B ⊓ LinearMap.ker f := by
    ext x
    simp only [Submodule.mem_inf, Submodule.mem_comap, LinearMap.mem_ker]
    constructor
    · rintro ⟨⟨hB, _⟩, hk⟩
      exact ⟨hB, hk⟩
    · rintro ⟨hB, hk⟩
      exact ⟨⟨hB, by rw [hk]; exact A.zero_mem⟩, hk⟩
  rw [e1, e2] at h3
  omega
variable {ι : Type*} [Module (MvPolynomial ι k) M] [IsScalarTower k (MvPolynomial ι k) M]
  (ℳ : ℤ → Submodule k M) [Decomposition ℳ]
  (hX : ∀ (i : ι) (n : ℤ), ∀ m ∈ ℳ n, (MvPolynomial.X i : MvPolynomial ι k) • m ∈ ℳ (n + 1))
include hX
theorem eventually_mem_of_homogeneous_mem_of_X_smul_mem [Finite ι] [Module.Finite (MvPolynomial ι k) M]
    (A B : Submodule (MvPolynomial ι k) M) (hA : ∀ n, ∀ m ∈ A, proj ℳ n m ∈ A)
    (hs : ∀ i, ∀ m ∈ B, (MvPolynomial.X i : MvPolynomial ι k) • m ∈ A) :
    ∀ᶠ n : ℤ in atTop, ∀ m ∈ B, m ∈ ℳ n → m ∈ A := by
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian B : B.FG)
  obtain ⟨b, hb⟩ := exists_bound_proj ℳ G
  let Q : Submodule k M :=
    { carrier := {x | x ∈ B ∧ ∀ n, b < n → proj ℳ n x ∈ A}
      add_mem' := fun {x y} hx hy => ⟨B.add_mem hx.1 hy.1, fun n hn => by
        rw [map_add]
        exact A.add_mem (hx.2 n hn) (hy.2 n hn)⟩
      zero_mem' := ⟨B.zero_mem, fun n _ => by
        rw [map_zero]
        exact A.zero_mem⟩
      smul_mem' := fun c x hx => ⟨B.smul_of_tower_mem c hx.1, fun n hn => by
        rw [map_smul]
        exact A.smul_of_tower_mem c (hx.2 n hn)⟩ }
  have hQX : ∀ i, ∀ m ∈ Q, (MvPolynomial.X i : MvPolynomial ι k) • m ∈ Q := by
    intro i m hm
    have hm' : m ∈ B ∧ ∀ n, b < n → proj ℳ n m ∈ A := hm
    show _ ∈ B ∧ ∀ n, b < n → _ ∈ A
    exact ⟨B.smul_mem _ hm'.1, fun n _ => hA n _ (hs i m hm'.1)⟩
  have hGQ : ∀ g ∈ (G : Set M), g ∈ Q := by
    intro g hg
    have hgB : g ∈ B := by
      rw [← hG]
      exact Submodule.subset_span hg
    show _ ∈ B ∧ ∀ n, b < n → _ ∈ A
    refine ⟨hgB, fun n hn => ?_⟩
    rw [hb g hg n (lt_of_lt_of_le hn (le_abs_self n))]
    exact A.zero_mem
  refine Filter.eventually_atTop.2 ⟨b + 1, fun n hn m hmB hmn => ?_⟩
  have hmQ : m ∈ Q := mem_of_mem_span Q hQX hGQ (by rw [hG]; exact hmB)
  have := (hmQ : m ∈ B ∧ ∀ n, b < n → proj ℳ n m ∈ A).2 n (by omega)
  rwa [proj_of_mem ℳ hmn] at this
theorem finrank_graded_inf_add_eq_of_X_smul_comap [Finite ι] [Module.Finite (MvPolynomial ι k) M] (i : ι)
    (A B : Submodule (MvPolynomial ι k) M) (hA : ∀ n, ∀ m ∈ A, proj ℳ n m ∈ A)
    (hB : ∀ n, ∀ m ∈ B, proj ℳ n m ∈ B) (n : ℤ) :
    finrank k ((A ⊔ B.map (LinearMap.lsmul (MvPolynomial ι k) M (MvPolynomial.X i))).restrictScalars k ⊓ ℳ (n + 1) : Submodule k M)
      + finrank k ((B ⊓ A.comap (LinearMap.lsmul (MvPolynomial ι k) M (MvPolynomial.X i))).restrictScalars k ⊓ ℳ n : Submodule k M)
    = finrank k (A.restrictScalars k ⊓ ℳ (n + 1) : Submodule k M)
      + finrank k (B.restrictScalars k ⊓ ℳ n : Submodule k M) := by
  have := finite_piece ℳ hX n
  have := finite_piece ℳ hX (n + 1)
  have : Module.Finite k (B.restrictScalars k ⊓ ℳ n : Submodule k M) :=
    Submodule.finiteDimensional_of_le inf_le_right
  have : Module.Finite k (A.restrictScalars k ⊓ ℳ (n + 1) : Submodule k M) :=
    Submodule.finiteDimensional_of_le inf_le_right
  have h := finrank_sup_map_add_finrank_inf_comap ((LinearMap.lsmul (MvPolynomial ι k) M (MvPolynomial.X i)).restrictScalars k)
    (B.restrictScalars k ⊓ ℳ n) (A.restrictScalars k ⊓ ℳ (n + 1))
  have e1 : ((A.restrictScalars k ⊓ ℳ (n + 1)) ⊔ (B.restrictScalars k ⊓ ℳ n).map ((LinearMap.lsmul (MvPolynomial ι k) M (MvPolynomial.X i)).restrictScalars k) :
      Submodule k M) = (A ⊔ B.map (LinearMap.lsmul (MvPolynomial ι k) M (MvPolynomial.X i))).restrictScalars k ⊓ ℳ (n + 1) := by
    apply le_antisymm
    · apply sup_le
      · exact inf_le_inf_right _ (fun x hx => Submodule.mem_sup_left hx)
      · rintro _ ⟨x, hx, rfl⟩
        obtain ⟨hxB, hxn⟩ := Submodule.mem_inf.1 hx
        exact Submodule.mem_inf.2 ⟨Submodule.mem_sup_right (Submodule.mem_map_of_mem hxB),
          hX i n x hxn⟩
    · intro y hy
      obtain ⟨hy, hyn⟩ := Submodule.mem_inf.1 hy
      obtain ⟨a, ha, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
      obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.1 hz
      rw [← proj_of_mem ℳ hyn, map_add]
      refine Submodule.add_mem_sup (Submodule.mem_inf.2 ⟨hA _ a ha, proj_mem ℳ _ a⟩) ?_
      refine Submodule.mem_map.2 ⟨proj ℳ n b, Submodule.mem_inf.2 ⟨hB n b hb, proj_mem ℳ n b⟩, ?_⟩
      have := proj_X_smul ℳ hX i (n + 1) b
      rw [add_sub_cancel_right] at this
      show (MvPolynomial.X i : MvPolynomial ι k) • proj ℳ n b
        = proj ℳ (n + 1) ((MvPolynomial.X i : MvPolynomial ι k) • b)
      rw [this]
  have e2 : ((B.restrictScalars k ⊓ ℳ n) ⊓ (A.restrictScalars k ⊓ ℳ (n + 1)).comap ((LinearMap.lsmul (MvPolynomial ι k) M (MvPolynomial.X i)).restrictScalars k) :
      Submodule k M) = (B ⊓ A.comap (LinearMap.lsmul (MvPolynomial ι k) M (MvPolynomial.X i))).restrictScalars k ⊓ ℳ n := by
    ext x
    simp only [Submodule.mem_inf, Submodule.mem_comap, Submodule.restrictScalars_mem]
    constructor
    · rintro ⟨⟨hxB, hxn⟩, hxA, _⟩
      exact ⟨⟨hxB, hxA⟩, hxn⟩
    · rintro ⟨⟨hxB, hxA⟩, hxn⟩
      exact ⟨⟨hxB, hxn⟩, hxA, hX i n x hxn⟩
  rw [e1, e2] at h
  exact h
theorem exists_polynomial_subquotient [Finite ι] [Module.Finite (MvPolynomial ι k) M]
    (s : Finset ι) (A B : Submodule (MvPolynomial ι k) M) (hAB : A ≤ B)
    (hA : ∀ n, ∀ m ∈ A, proj ℳ n m ∈ A) (hB : ∀ n, ∀ m ∈ B, proj ℳ n m ∈ B)
    (hs : ∀ i ∉ s, ∀ m ∈ B, (MvPolynomial.X i : MvPolynomial ι k) • m ∈ A) :
    ∃ P : ℚ[X], P.degree < (s.card : ℕ) ∧ ∀ᶠ n : ℤ in atTop,
      (finrank k (B.restrictScalars k ⊓ ℳ n : Submodule k M) : ℚ)
        - finrank k (A.restrictScalars k ⊓ ℳ n : Submodule k M) = P.eval (n : ℚ) := by
  classical
  induction s using Finset.induction_on generalizing A B with
  | empty =>
    refine ⟨0, by simp, ?_⟩
    filter_upwards [eventually_mem_of_homogeneous_mem_of_X_smul_mem ℳ hX A B hA (fun i => hs i (by simp))] with n hn
    have e : (B.restrictScalars k ⊓ ℳ n : Submodule k M) = A.restrictScalars k ⊓ ℳ n := by
      apply le_antisymm
      · intro x hx
        obtain ⟨hxB, hxn⟩ := Submodule.mem_inf.1 hx
        exact Submodule.mem_inf.2 ⟨hn x hxB hxn, hxn⟩
      · exact inf_le_inf_right _ (fun x hx => hAB hx)
    rw [e, sub_self, eval_zero]
  | @insert i s hi ih =>
    have hAK : A ≤ B ⊓ A.comap (LinearMap.lsmul (MvPolynomial ι k) M (MvPolynomial.X i)) := fun a ha =>
      Submodule.mem_inf.2 ⟨hAB ha, Submodule.mem_comap.2 (A.smul_mem _ ha)⟩
    have hK : ∀ n, ∀ m ∈ B ⊓ A.comap (LinearMap.lsmul (MvPolynomial ι k) M (MvPolynomial.X i)), proj ℳ n m ∈ B ⊓ A.comap (LinearMap.lsmul (MvPolynomial ι k) M (MvPolynomial.X i)) := by
      intro n m hm
      obtain ⟨hmB, hmA⟩ := Submodule.mem_inf.1 hm
      refine Submodule.mem_inf.2 ⟨hB n m hmB, Submodule.mem_comap.2 ?_⟩
      have := proj_X_smul ℳ hX i (n + 1) m
      rw [add_sub_cancel_right] at this
      rw [LinearMap.lsmul_apply, ← this]
      exact hA _ _ (Submodule.mem_comap.1 hmA)
    have hsK : ∀ j ∉ s, ∀ m ∈ B ⊓ A.comap (LinearMap.lsmul (MvPolynomial ι k) M (MvPolynomial.X i)),
        (MvPolynomial.X j : MvPolynomial ι k) • m ∈ A := by
      intro j hj m hm
      obtain ⟨hmB, hmA⟩ := Submodule.mem_inf.1 hm
      by_cases hji : j = i
      · subst hji
        exact Submodule.mem_comap.1 hmA
      · exact hs j (by simp [hji, hj]) m hmB
    have hB'B : A ⊔ B.map (LinearMap.lsmul (MvPolynomial ι k) M (MvPolynomial.X i)) ≤ B :=
      sup_le hAB (Submodule.map_le_iff_le_comap.2 (fun b hb => Submodule.mem_comap.2 (B.smul_mem _ hb)))
    have hB' : ∀ n, ∀ m ∈ A ⊔ B.map (LinearMap.lsmul (MvPolynomial ι k) M (MvPolynomial.X i)), proj ℳ n m ∈ A ⊔ B.map (LinearMap.lsmul (MvPolynomial ι k) M (MvPolynomial.X i)) := by
      intro n m hm
      obtain ⟨a, ha, z, hz, rfl⟩ := Submodule.mem_sup.1 hm
      obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.1 hz
      rw [map_add, LinearMap.lsmul_apply, proj_X_smul ℳ hX i n b]
      exact Submodule.add_mem_sup (hA n a ha) (Submodule.mem_map_of_mem (hB (n - 1) b hb))
    have hsB' : ∀ j ∉ s, ∀ m ∈ B, (MvPolynomial.X j : MvPolynomial ι k) • m ∈ A ⊔ B.map (LinearMap.lsmul (MvPolynomial ι k) M (MvPolynomial.X i)) := by
      intro j hj m hm
      by_cases hji : j = i
      · subst hji
        exact Submodule.mem_sup_right (Submodule.mem_map_of_mem hm)
      · exact Submodule.mem_sup_left (hs j (by simp [hji, hj]) m hm)
    obtain ⟨P1, hP1d, hP1⟩ := ih A (B ⊓ A.comap (LinearMap.lsmul (MvPolynomial ι k) M (MvPolynomial.X i))) hAK hA hK hsK
    obtain ⟨P2, hP2d, hP2⟩ := ih (A ⊔ B.map (LinearMap.lsmul (MvPolynomial ι k) M (MvPolynomial.X i))) B hB'B hB' hB hsB'
    obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.1 hP1
    obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.1 hP2
    have hdiff : ∀ᶠ n : ℤ in atTop,
        ((finrank k (B.restrictScalars k ⊓ ℳ (n + 1) : Submodule k M) : ℚ)
          - finrank k (A.restrictScalars k ⊓ ℳ (n + 1) : Submodule k M))
        - ((finrank k (B.restrictScalars k ⊓ ℳ n : Submodule k M) : ℚ)
          - finrank k (A.restrictScalars k ⊓ ℳ n : Submodule k M))
        = (P2.comp (X + C 1) - P1).eval (n : ℚ) := by
      refine Filter.eventually_atTop.2 ⟨max N1 N2, fun n hn => ?_⟩
      have h1 := hN1 n (le_of_max_le_left hn)
      have h2 := hN2 (n + 1) (by linarith [le_of_max_le_right hn])
      have h3 := finrank_graded_inf_add_eq_of_X_smul_comap ℳ hX i A B hA hB n
      have h3' : (finrank k ((A ⊔ B.map (LinearMap.lsmul (MvPolynomial ι k) M (MvPolynomial.X i))).restrictScalars k ⊓ ℳ (n + 1) : Submodule k M) : ℚ)
          + finrank k ((B ⊓ A.comap (LinearMap.lsmul (MvPolynomial ι k) M (MvPolynomial.X i))).restrictScalars k ⊓ ℳ n : Submodule k M)
          = finrank k (A.restrictScalars k ⊓ ℳ (n + 1) : Submodule k M)
            + finrank k (B.restrictScalars k ⊓ ℳ n : Submodule k M) := by
        exact_mod_cast h3
      simp only [eval_sub, eval_comp, eval_add, eval_X, eval_C]
      push_cast at h2
      linear_combination h2 - h1 + h3'
    have hQd : (P2.comp (X + C 1) - P1).degree < (s.card : ℕ) := by
      refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ hP1d)
      rw [← taylor_apply, degree_taylor]
      exact hP2d
    obtain ⟨P, hPd, -, -, hP⟩ := exists_polynomial_of_diff_eventually
      (f := fun n : ℤ => (finrank k (B.restrictScalars k ⊓ ℳ n : Submodule k M) : ℚ)
        - finrank k (A.restrictScalars k ⊓ ℳ n : Submodule k M)) hQd hdiff
    refine ⟨P, ?_, hP⟩
    rw [Finset.card_insert_of_notMem hi]
    exact lt_of_le_of_lt hPd (by exact_mod_cast Nat.lt_succ_self _)
end Field
end GradedHilbert
section Main
open DirectSum Module GradedHilbert
variable {k : Type*} [Field k] {M' M M'' : Type*} [AddCommGroup M'] [Module k M']
  [AddCommGroup M] [Module k M] [AddCommGroup M''] [Module k M'']
structure IsHilbertPoly (ℳ : ℤ → Submodule k M) (P : ℚ[X]) : Prop where
  finite : ∀ n, Module.Finite k (ℳ n)
  eventually_eq : ∀ᶠ n : ℤ in atTop, (finrank k (ℳ n) : ℚ) = P.eval (n : ℚ)
variable {ι : Type*} [Module (MvPolynomial ι k) M'] [IsScalarTower k (MvPolynomial ι k) M']
  [Module (MvPolynomial ι k) M] [IsScalarTower k (MvPolynomial ι k) M]
  [Module (MvPolynomial ι k) M''] [IsScalarTower k (MvPolynomial ι k) M'']
theorem exists_isHilbertPoly [Fintype ι] [Module.Finite (MvPolynomial ι k) M]
    (ℳ : ℤ → Submodule k M) [Decomposition ℳ]
    (hX : ∀ (i : ι) (n : ℤ), ∀ m ∈ ℳ n, (MvPolynomial.X i : MvPolynomial ι k) • m ∈ ℳ (n + 1)) :
    ∃ P : ℚ[X], IsHilbertPoly ℳ P ∧ P.degree < (Fintype.card ι : ℕ) := by
  obtain ⟨P, hPd, hP⟩ := exists_polynomial_subquotient ℳ hX Finset.univ ⊥ ⊤ bot_le
    (fun n m hm => by
      rw [(Submodule.mem_bot _).1 hm, map_zero]
      exact Submodule.zero_mem _)
    (fun _ _ _ => Submodule.mem_top) (fun i hi => absurd (Finset.mem_univ i) hi)
  refine ⟨P, ⟨finite_piece ℳ hX, ?_⟩, by simpa using hPd⟩
  filter_upwards [hP] with n hn
  rw [← hn, Submodule.restrictScalars_top, Submodule.restrictScalars_bot, top_inf_eq, bot_inf_eq,
    finrank_bot]
  simp
noncomputable def gradedHilbertPoly [Fintype ι] [Module.Finite (MvPolynomial ι k) M]
    (ℳ : ℤ → Submodule k M) [Decomposition ℳ]
    (hX : ∀ (i : ι) (n : ℤ), ∀ m ∈ ℳ n, (MvPolynomial.X i : MvPolynomial ι k) • m ∈ ℳ (n + 1)) :
    ℚ[X] :=
  (exists_isHilbertPoly ℳ hX).choose
section
variable [Fintype ι] [Module.Finite (MvPolynomial ι k) M] (ℳ : ℤ → Submodule k M)
  [Decomposition ℳ]
  (hX : ∀ (i : ι) (n : ℤ), ∀ m ∈ ℳ n, (MvPolynomial.X i : MvPolynomial ι k) • m ∈ ℳ (n + 1))
end
end Main
section PolynomialRing
open DirectSum Module MvPolynomial
variable (ι k : Type*) [Field k]
end PolynomialRing
end GlobalTheory


