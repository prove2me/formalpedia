-- Prove2me | solution 1 for Algebra.exists_ker_eq_span_of_surjective_truncated_of_ker_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/6dbe648f-2e3c-52cb-b363-cc29c1aa4ffd

import Mathlib
import Theorems.Thm_MvPolynomial_bijective_algHom_truncated_of_forall_exists_sub_mem_sq
import Theorems.Thm_MvPolynomial_nonempty_truncated_quotient_span_singleton_algEquiv_truncated_of_not_mem_sq
import Theorems.Thm_Ideal_exists_map_mk_span_singleton_eq_span_of_not_mem_smul
import Theorems.Thm_Algebra_exists_algEquiv_comp_eq_of_surjective_of_ker_le_sq_truncated
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_ker_eq_span_of_surjective_truncated_of_ker_eq_span

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Algebra
p2m_export "Algebra" "commutes mk algebraMap mem_top mem_bot exists_algEquiv_comp_eq_of_surjective_of_ker_le_sq_truncated"
namespace DevTrunc
p2m_open "Algebra"

open MvPolynomial IsLocalRing

variable (k : Type*) [Field k]

abbrev NN (n : ℕ) : Ideal (MvPolynomial (Fin n) k) := RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin n) k →+* k)

abbrev TT (n M : ℕ) : Type _ := MvPolynomial (Fin n) k ⧸ NN k n ^ (M + 1)

abbrev tt (n M : ℕ) : Ideal (TT k n M) := Ideal.map (Ideal.Quotient.mk (NN k n ^ (M + 1))) (NN k n)

section Local

variable (n M : ℕ)

theorem X_mem_NN (j : Fin n) : (MvPolynomial.X j : MvPolynomial (Fin n) k) ∈ NN k n := by
  rw [RingHom.mem_ker, MvPolynomial.constantCoeff_X]

theorem NN_ne_top : NN k n ≠ ⊤ := RingHom.ker_ne_top _

theorem NN_isMaximal : (NN k n).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨MvPolynomial.C c, MvPolynomial.constantCoeff_C _ c⟩)

theorem tt_pow_eq_bot : tt k n M ^ (M + 1) = ⊥ := by
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

theorem isNilpotent_of_mem_tt {x : TT k n M} (hx : x ∈ tt k n M) : IsNilpotent x :=
  ⟨M + 1, by have := Ideal.pow_mem_pow hx (M + 1); rwa [tt_pow_eq_bot, Ideal.mem_bot] at this⟩

theorem tt_ne_top : tt k n M ≠ ⊤ := by
  intro h
  have h1 : (1 : TT k n M) ∈ tt k n M := h ▸ Submodule.mem_top
  obtain ⟨f, hf, hf1⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp h1
  have : f - 1 ∈ NN k n ^ (M + 1) := by
    rw [← Ideal.Quotient.eq, hf1, map_one]
  have h2 : f - 1 ∈ NN k n := Ideal.pow_le_self (Nat.succ_ne_zero M) this
  exact NN_ne_top k n ((Ideal.eq_top_iff_one _).mpr (by simpa using (NN k n).sub_mem hf h2))

theorem tt_isMaximal : (tt k n M).IsMaximal :=
  (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective (NN_isMaximal k n)).resolve_left
    (tt_ne_top k n M)

theorem isUnit_of_not_mem_tt (x : TT k n M) (hx : x ∉ tt k n M) : IsUnit x := by
  obtain ⟨y, t, ht, hyt⟩ := (tt_isMaximal k n M).exists_inv hx
  have hu : IsUnit (y * x) := by
    rw [show y * x = 1 - t by rw [← hyt]; ring]
    exact (isNilpotent_of_mem_tt k n M ht).isUnit_one_sub
  exact isUnit_of_mul_isUnit_right hu

scoped instance isLocalRing_TT : IsLocalRing (TT k n M) :=
  IsLocalRing.of_unique_max_ideal ⟨tt k n M, tt_isMaximal k n M, fun J hJ =>
    hJ.eq_of_le (tt_ne_top k n M) fun x hx => by
      by_contra h
      exact hJ.ne_top (Ideal.eq_top_of_isUnit_mem _ hx (isUnit_of_not_mem_tt k n M x h))⟩

theorem maximalIdeal_TT : IsLocalRing.maximalIdeal (TT k n M) = tt k n M :=
  (IsLocalRing.eq_maximalIdeal (tt_isMaximal k n M)).symm

theorem ker_le_tt {C : Type*} [CommRing C] [Nontrivial C] [Algebra k C] (γ : TT k n M →ₐ[k] C) :
    RingHom.ker γ ≤ tt k n M := by
  intro x hx
  by_contra h
  have := (isUnit_of_not_mem_tt k n M x h).map γ
  rw [RingHom.mem_ker] at hx
  rw [hx] at this
  exact not_isUnit_zero this

end Local

section Step

variable {k}
variable {n M : ℕ} {C : Type*} [CommRing C] [Algebra k C] [IsLocalRing C]

theorem step (γ : TT k (n + 1) M →ₐ[k] C) (x : TT k (n + 1) M) (hxk : x ∈ RingHom.ker γ)
    (hx1 : x ∈ tt k (n + 1) M) (hx2 : x ∉ tt k (n + 1) M ^ 2) :
    ∃ (e : (TT k (n + 1) M ⧸ Ideal.span ({x} : Set (TT k (n + 1) M))) ≃ₐ[k] TT k n M) (γ' : TT k n M →ₐ[k] C),
      (∀ a, γ' (e (Ideal.Quotient.mk _ a)) = γ a) ∧ Function.Surjective γ' = Function.Surjective γ ∧
      RingHom.ker γ' = ((RingHom.ker γ).map (Ideal.Quotient.mk (Ideal.span ({x} : Set (TT k (n + 1) M))))).map (e.toRingEquiv : (TT k (n + 1) M ⧸ Ideal.span ({x} : Set (TT k (n + 1) M))) →+* TT k n M) := by
  classical
  obtain ⟨e⟩ := MvPolynomial.nonempty_truncated_quotient_span_singleton_algEquiv_truncated_of_not_mem_sq k n M x hx1 hx2
  have hle : Ideal.span ({x} : Set (TT k (n + 1) M)) ≤ RingHom.ker γ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hxk
  let γb : (TT k (n + 1) M ⧸ Ideal.span ({x} : Set (TT k (n + 1) M))) →ₐ[k] C :=
    Ideal.Quotient.liftₐ _ γ fun a ha => hle ha
  let γ' : TT k n M →ₐ[k] C := γb.comp (e.symm : TT k n M →ₐ[k] _)
  have hcomp : ∀ a, γ' (e (Ideal.Quotient.mk _ a)) = γ a := fun a => by
    show γb (e.symm (e (Ideal.Quotient.mk _ a))) = γ a
    rw [AlgEquiv.symm_apply_apply]; rfl
  refine ⟨e, γ', hcomp, ?_, ?_⟩
  · apply propext
    constructor
    · intro h c; obtain ⟨y, hy⟩ := h c
      obtain ⟨z, rfl⟩ := e.surjective y
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact ⟨a, (hcomp a).symm.trans hy⟩
    · intro h c; obtain ⟨a, ha⟩ := h c; exact ⟨e (Ideal.Quotient.mk _ a), (hcomp a).trans ha⟩
  · ext y
    obtain ⟨z, rfl⟩ := e.surjective y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [RingHom.mem_ker, hcomp a]
    constructor
    · intro ha
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (RingHom.mem_ker.mpr ha))
    · intro ha
      rw [Ideal.mem_map_iff_of_surjective _ (show Function.Surjective (e.toRingEquiv : (TT k (n + 1) M ⧸ Ideal.span ({x} : Set (TT k (n + 1) M))) →+* TT k n M) from e.surjective)] at ha
      obtain ⟨z, hz, hze⟩ := ha
      have hz' : z = Ideal.Quotient.mk _ a := e.injective hze
      subst hz'
      rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hz
      obtain ⟨b, hb, hba⟩ := hz
      rw [Ideal.Quotient.eq] at hba
      have : b - (b - a) ∈ RingHom.ker γ := (RingHom.ker γ).sub_mem hb (hle hba)
      simpa using this

theorem drop (γ : TT k (n + 1) M →ₐ[k] C) (g : Fin (n + 1) → TT k (n + 1) M) (hg : RingHom.ker γ = Ideal.span (Set.range g))
    (x : TT k (n + 1) M) (hxk : x ∈ RingHom.ker γ) (hx1 : x ∈ tt k (n + 1) M) (hx2 : x ∉ tt k (n + 1) M ^ 2) :
    ∃ (γ' : TT k n M →ₐ[k] C), (Function.Surjective γ → Function.Surjective γ') ∧
      ∃ g' : Fin n → TT k n M, RingHom.ker γ' = Ideal.span (Set.range g') := by
  classical
  obtain ⟨e, γ', hcomp, hsurj, hker⟩ := step γ x hxk hx1 hx2
  have hxm : x ∉ IsLocalRing.maximalIdeal (TT k (n + 1) M) • Ideal.span (Set.range g) := by
    rw [← hg, maximalIdeal_TT, Ideal.smul_eq_mul]
    intro h
    apply hx2
    rw [pow_two]
    exact Ideal.mul_mono_right (ker_le_tt k (n + 1) M γ) h
  obtain ⟨g₁, hg₁⟩ := Ideal.exists_map_mk_span_singleton_eq_span_of_not_mem_smul g x (hg ▸ hxk) hxm
  refine ⟨γ', fun h => hsurj ▸ h, fun i => e (g₁ i), ?_⟩
  rw [hker, hg, hg₁, Ideal.map_span, ← Set.range_comp]
  rfl

theorem lift (γ : TT k (n + 1) M →ₐ[k] C)
    (x : TT k (n + 1) M) (hxk : x ∈ RingHom.ker γ) (hx1 : x ∈ tt k (n + 1) M) (hx2 : x ∉ tt k (n + 1) M ^ 2) :
    ∃ (γ' : TT k n M →ₐ[k] C), (Function.Surjective γ → Function.Surjective γ') ∧
      ∀ h' : Fin n → TT k n M, RingHom.ker γ' = Ideal.span (Set.range h') →
        ∃ h : Fin (n + 1) → TT k (n + 1) M, RingHom.ker γ = Ideal.span (Set.range h) := by
  classical
  obtain ⟨e, γ', hcomp, hsurj, hker⟩ := step γ x hxk hx1 hx2
  refine ⟨γ', fun h => hsurj ▸ h, fun h' hh' => ?_⟩

  have hmk : (RingHom.ker γ).map (Ideal.Quotient.mk (Ideal.span ({x} : Set (TT k (n + 1) M)))) =
      Ideal.span (Set.range fun i => e.symm (h' i)) := by
    have := congrArg (Ideal.map e.toRingEquiv.symm.toRingHom) hker
    rw [RingEquiv.toRingHom_eq_coe, Ideal.map_of_equiv] at this
    rw [← this, hh', Ideal.map_span, ← Set.range_comp]
    rfl
  choose s hs using fun i => Ideal.Quotient.mk_surjective (I := Ideal.span ({x} : Set (TT k (n + 1) M))) (e.symm (h' i))
  refine ⟨Fin.cons x s, ?_⟩
  have hle : Ideal.span ({x} : Set (TT k (n + 1) M)) ≤ RingHom.ker γ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hxk
  have hcm : RingHom.ker γ = ((RingHom.ker γ).map (Ideal.Quotient.mk (Ideal.span ({x} : Set (TT k (n + 1) M))))).comap
      (Ideal.Quotient.mk (Ideal.span ({x} : Set (TT k (n + 1) M)))) := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.mpr hle]
  have hfun : (fun i => e.symm (h' i)) = (Ideal.Quotient.mk (Ideal.span ({x} : Set (TT k (n + 1) M)))) ∘ s :=
    funext fun i => (hs i).symm
  rw [hcm, hmk, hfun, Set.range_comp, ← Ideal.map_span, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, Fin.range_cons, Ideal.span_insert, sup_comm]

end Step

section CotangentCount

variable {k}
variable (n M : ℕ)

theorem NN_eq_span : NN k n = Ideal.span (Set.range (MvPolynomial.X : Fin n → MvPolynomial (Fin n) k)) := by
  apply le_antisymm
  · intro f hf
    rw [RingHom.mem_ker] at hf
    rw [show Set.range (MvPolynomial.X : Fin n → MvPolynomial (Fin n) k) = MvPolynomial.X '' Set.univ by simp,
      MvPolynomial.mem_ideal_span_X_image]
    intro mo hmo
    have : mo ≠ 0 := by
      rintro rfl
      rw [MvPolynomial.mem_support_iff] at hmo
      exact hmo hf
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp this
    exact ⟨i, Set.mem_univ i, hi⟩
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact X_mem_NN k n j

theorem two_le_degree_of_mem_sq {p : MvPolynomial (Fin n) k} (hp : p ∈ NN k n ^ 2) :
    ∀ d ∈ p.support, 2 ≤ d.degree := by
  classical
  rw [NN_eq_span, pow_two, Ideal.span_mul_span'] at hp
  induction hp using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ := Set.mem_mul.mp hg
    intro d hd
    have hsub : (MvPolynomial.X a * MvPolynomial.X b : MvPolynomial (Fin n) k).support ⊆ {Finsupp.single a 1 + Finsupp.single b 1} := by
      rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul]
      exact MvPolynomial.support_monomial_subset
    rw [Finset.mem_singleton.mp (hsub hd), (map_add Finsupp.degree), Finsupp.degree_single, Finsupp.degree_single]
  | zero => intro d hd; simp at hd
  | add f g _ _ hf hg =>
    intro d hd
    rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
    · exact hf d h
    · exact hg d h
  | smul q g _ hg =>
    intro d hd
    rw [smul_eq_mul] at hd
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul q g hd)
    rw [(map_add Finsupp.degree)]
    exact le_add_left (hg b hb)

theorem coeff_single_eq_zero_of_mem_sq {p : MvPolynomial (Fin n) k} (hp : p ∈ NN k n ^ 2) (j : Fin n) :
    MvPolynomial.coeff (Finsupp.single j 1) p = 0 := by
  by_contra h
  have := two_le_degree_of_mem_sq n hp (Finsupp.single j 1) (MvPolynomial.mem_support_iff.mpr h)
  rw [Finsupp.degree_single] at this
  omega

noncomputable def lin (c : Fin n → k) : MvPolynomial (Fin n) k := ∑ i, MvPolynomial.C (c i) * MvPolynomial.X i

theorem lin_add (c c' : Fin n → k) : lin n (c + c') = lin n c + lin n c' := by
  simp only [lin, Pi.add_apply, MvPolynomial.C_add, add_mul, Finset.sum_add_distrib]

theorem lin_smul (a : k) (c : Fin n → k) : lin n (a • c) = MvPolynomial.C a * lin n c := by
  simp only [lin, Pi.smul_apply, smul_eq_mul, MvPolynomial.C_mul, mul_assoc, Finset.mul_sum]

theorem lin_sub (c c' : Fin n → k) : lin n (c - c') = lin n c - lin n c' := by
  simp only [lin, Pi.sub_apply, MvPolynomial.C_sub, sub_mul, Finset.sum_sub_distrib]

theorem coeff_single_lin (c : Fin n → k) (j : Fin n) :
    MvPolynomial.coeff (Finsupp.single j 1) (lin n c) = c j := by
  classical
  rw [lin, MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X']
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [if_neg, mul_zero]
    intro h
    exact hij (Finsupp.single_left_injective one_ne_zero h)
  · intro h; exact absurd (Finset.mem_univ j) h

theorem mk_lin_mem_tt (c : Fin n → k) : (Ideal.Quotient.mk (NN k n ^ (M + 1)) (lin n c) : TT k n M) ∈ tt k n M := by
  rw [lin, map_sum]
  exact Ideal.sum_mem _ fun j _ => by rw [map_mul]; exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (X_mem_NN k n j))

variable {n M}

theorem mem_sq_of_mk_mem_tt_sq (hM : 1 ≤ M) {y : MvPolynomial (Fin n) k}
    (hy : Ideal.Quotient.mk (NN k n ^ (M + 1)) y ∈ tt k n M ^ 2) : y ∈ NN k n ^ 2 := by
  rw [tt, ← Ideal.map_pow, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hy
  obtain ⟨z, hz, hzy⟩ := hy
  rw [Ideal.Quotient.eq] at hzy
  have hle : NN k n ^ (M + 1) ≤ NN k n ^ 2 := Ideal.pow_le_pow_right (by omega)
  have : y = z - (z - y) := by ring
  rw [this]
  exact Ideal.sub_mem _ hz (hle hzy)

theorem eq_zero_of_mk_lin_mem_sq (hM : 1 ≤ M) (c : Fin n → k)
    (hc : Ideal.Quotient.mk (NN k n ^ (M + 1)) (lin n c) ∈ tt k n M ^ 2) : c = 0 := by
  funext j
  have h := coeff_single_eq_zero_of_mem_sq n (mem_sq_of_mk_mem_tt_sq hM hc) j
  rwa [coeff_single_lin] at h

theorem mk_X_mem_tt (j : Fin n) : (Ideal.Quotient.mk (NN k n ^ (M + 1)) (MvPolynomial.X j) : TT k n M) ∈ tt k n M :=
  Ideal.mem_map_of_mem _ (X_mem_NN k n j)

theorem tt_eq_span : tt k n M = Ideal.span (Set.range fun j : Fin n => (Ideal.Quotient.mk (NN k n ^ (M + 1)) (MvPolynomial.X j) : TT k n M)) := by
  have h : Ideal.map (Ideal.Quotient.mk (NN k n ^ (M + 1))) (Ideal.span (Set.range (MvPolynomial.X : Fin n → MvPolynomial (Fin n) k))) =
      Ideal.span (Set.range fun j : Fin n => (Ideal.Quotient.mk (NN k n ^ (M + 1)) (MvPolynomial.X j) : TT k n M)) := by
    rw [Ideal.map_span, ← Set.range_comp]; rfl
  rw [← h, ← NN_eq_span]

theorem exists_sub_algebraMap_mem_tt (t : TT k n M) : ∃ a : k, t - algebraMap k (TT k n M) a ∈ tt k n M := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective t
  refine ⟨MvPolynomial.constantCoeff p, ?_⟩
  rw [show algebraMap k (TT k n M) (MvPolynomial.constantCoeff p) =
      Ideal.Quotient.mk (NN k n ^ (M + 1)) (MvPolynomial.C (MvPolynomial.constantCoeff p)) from rfl, ← map_sub]
  exact Ideal.mem_map_of_mem _ (by rw [RingHom.mem_ker, map_sub, MvPolynomial.constantCoeff_C, sub_self])

theorem exists_sub_mk_lin_mem_sq (x : TT k n M) (hx : x ∈ tt k n M) :
    ∃ c : Fin n → k, x - Ideal.Quotient.mk (NN k n ^ (M + 1)) (lin n c) ∈ tt k n M ^ 2 := by
  classical
  rw [tt_eq_span] at hx
  obtain ⟨a, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hx
  choose c hc using fun j => exists_sub_algebraMap_mem_tt (a j)
  refine ⟨c, ?_⟩
  rw [lin, map_sum, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [map_mul, show (Ideal.Quotient.mk (NN k n ^ (M + 1))) (MvPolynomial.C (c j)) = algebraMap k (TT k n M) (c j) from rfl,
    ← sub_mul, pow_two]
  exact Ideal.mul_mem_mul (hc j) (mk_X_mem_tt j)

noncomputable def linElt (n M : ℕ) (c : Fin n → k) : ↥(tt k n M) :=
  ⟨Ideal.Quotient.mk (NN k n ^ (M + 1)) (lin n c), mk_lin_mem_tt n M c⟩

noncomputable def linForm (n M : ℕ) : (Fin n → k) →ₗ[k] (tt k n M).Cotangent where
  toFun c := (tt k n M).toCotangent (linElt n M c)
  map_add' c c' := by
    rw [← map_add]; congr 1; apply Subtype.ext
    simp only [linElt, lin_add, map_add, Submodule.coe_add]
  map_smul' a c := by
    have : linElt n M (a • c) = algebraMap k (TT k n M) a • linElt n M c := by
      apply Subtype.ext
      simp only [linElt, lin_smul, map_mul, Submodule.coe_smul, smul_eq_mul]
      rfl
    rw [RingHom.id_apply, this, LinearMap.map_smul, algebraMap_smul]

theorem linForm_apply (n M : ℕ) (c : Fin n → k) : linForm (k := k) n M c = (tt k n M).toCotangent (linElt n M c) := rfl

theorem linForm_surjective (n M : ℕ) : Function.Surjective (linForm (k := k) n M) := by
  intro ξ
  obtain ⟨⟨x, hx⟩, rfl⟩ := (tt k n M).toCotangent_surjective ξ
  obtain ⟨c, hc⟩ := exists_sub_mk_lin_mem_sq x hx
  refine ⟨c, ?_⟩
  rw [linForm_apply, Ideal.toCotangent_eq]
  have : -(x - Ideal.Quotient.mk (NN k n ^ (M + 1)) (lin n c)) ∈ tt k n M ^ 2 := (Ideal.neg_mem_iff _).mpr hc
  simpa only [linElt, Submodule.coe_sub, neg_sub] using this

theorem linForm_injective (hM : 1 ≤ M) (n : ℕ) : Function.Injective (linForm (k := k) n M) := by
  intro c c' h
  rw [← sub_eq_zero]
  apply eq_zero_of_mk_lin_mem_sq hM
  have h0 : linForm (k := k) n M (c - c') = 0 := by rw [map_sub, h, sub_self]
  rw [linForm_apply, Ideal.toCotangent_eq_zero] at h0
  exact h0

theorem finrank_cotangent_tt (hM : 1 ≤ M) (n : ℕ) : Module.finrank k (tt k n M).Cotangent = n := by
  rw [← (LinearEquiv.ofBijective (linForm n M) ⟨linForm_injective hM n, linForm_surjective n M⟩).finrank_eq,
    Module.finrank_fin_fun]

end CotangentCount

section Compare

variable {k}
variable {C : Type*} [CommRing C] [Algebra k C] [IsLocalRing C] {M : ℕ}

theorem tt_le_comap_algEquiv {n m : ℕ} (e : TT k n M ≃ₐ[k] TT k m M) :
    tt k n M ≤ (tt k m M).comap (e : TT k n M →ₐ[k] TT k m M) := by
  intro x hx
  rw [Ideal.mem_comap]
  rw [← maximalIdeal_TT, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  intro hu
  apply hx
  have := hu.map (e.symm : TT k m M →ₐ[k] TT k n M)
  simpa using this

noncomputable def cotangentEquivOfAlgEquiv {n m : ℕ} (e : TT k n M ≃ₐ[k] TT k m M) :
    (tt k n M).Cotangent ≃ₗ[k] (tt k m M).Cotangent := by
  refine LinearEquiv.ofLinear
    (Ideal.mapCotangent (tt k n M) (tt k m M) (e : TT k n M →ₐ[k] TT k m M) ?h1)
    (Ideal.mapCotangent (tt k m M) (tt k n M) (e.symm : TT k m M →ₐ[k] TT k n M) ?h2) ?h3 ?h4
  case h1 => exact tt_le_comap_algEquiv e
  case h2 => exact tt_le_comap_algEquiv e.symm
  case h3 =>
    apply LinearMap.ext
    intro ξ
    obtain ⟨x, rfl⟩ := (tt k m M).toCotangent_surjective ξ
    rw [LinearMap.comp_apply, Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent, LinearMap.id_apply]
    congr 1
    exact Subtype.ext (e.apply_symm_apply x)
  case h4 =>
    apply LinearMap.ext
    intro ξ
    obtain ⟨x, rfl⟩ := (tt k n M).toCotangent_surjective ξ
    rw [LinearMap.comp_apply, Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent, LinearMap.id_apply]
    congr 1
    exact Subtype.ext (e.symm_apply_apply x)

theorem exists_algHom_comp_eq {n m : ℕ} (γ : TT k n M →ₐ[k] C) (δ : TT k m M →ₐ[k] C) (hδ : Function.Surjective δ) :
    ∃ θ : TT k n M →ₐ[k] TT k m M, δ.comp θ = γ := by
  classical

  have hpre : ∀ j : Fin n, ∃ P : TT k m M, P ∈ tt k m M ∧ δ P = γ (Ideal.Quotient.mk _ (MvPolynomial.X j)) := by
    intro j
    obtain ⟨Q, hQ⟩ := hδ (γ (Ideal.Quotient.mk _ (MvPolynomial.X j)))
    obtain ⟨a, ha⟩ := exists_sub_algebraMap_mem_tt Q

    have h1 : γ (Ideal.Quotient.mk _ (MvPolynomial.X j)) ∈ IsLocalRing.maximalIdeal C := by
      have : IsNilpotent (γ (Ideal.Quotient.mk _ (MvPolynomial.X j))) :=
        (isNilpotent_of_mem_tt k n M (mk_X_mem_tt j)).map γ
      exact nilradical_le_prime _ (mem_nilradical.mpr this)
    have h2 : δ (Q - algebraMap k _ a) ∈ IsLocalRing.maximalIdeal C := by
      have : IsNilpotent (δ (Q - algebraMap k _ a)) := (isNilpotent_of_mem_tt k m M ha).map δ
      exact nilradical_le_prime _ (mem_nilradical.mpr this)
    have h3 : algebraMap k C a ∈ IsLocalRing.maximalIdeal C := by
      have : algebraMap k C a = δ Q - δ (Q - algebraMap k _ a) := by rw [map_sub, AlgHom.commutes, sub_sub_cancel]
      rw [this, hQ]
      exact Ideal.sub_mem _ h1 h2
    have ha0 : a = 0 := by
      by_contra hne
      exact (IsLocalRing.maximalIdeal.isMaximal C).ne_top
        (Ideal.eq_top_of_isUnit_mem _ h3 ((IsUnit.mk0 a hne).map (algebraMap k C)))
    refine ⟨Q - algebraMap k _ a, ha, ?_⟩
    rw [ha0, map_zero, sub_zero, hQ]
  choose P hP hPδ using hpre

  have hker : ∀ f ∈ NN k n ^ (M + 1), MvPolynomial.aeval P f = 0 := by
    intro f hf
    have hmap : Ideal.map (MvPolynomial.aeval P : MvPolynomial (Fin n) k →ₐ[k] TT k m M) (NN k n) ≤ tt k m M := by
      refine (Ideal.map_mono (le_of_eq (NN_eq_span n))).trans ?_
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      simpa using hP j
    have h1 : MvPolynomial.aeval P f ∈ Ideal.map (MvPolynomial.aeval P : MvPolynomial (Fin n) k →ₐ[k] TT k m M) (NN k n ^ (M + 1)) :=
      Ideal.mem_map_of_mem _ hf
    rw [Ideal.map_pow] at h1
    have h2 := Ideal.pow_right_mono hmap (M + 1) h1
    rwa [tt_pow_eq_bot, Ideal.mem_bot] at h2
  refine ⟨Ideal.Quotient.liftₐ (NN k n ^ (M + 1)) (MvPolynomial.aeval P) hker, ?_⟩

  apply AlgHom.ext
  intro t
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective t
  change δ (MvPolynomial.aeval P f) = γ (Ideal.Quotient.mkₐ k _ f)
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  refine MvPolynomial.algHom_ext fun j => ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, MvPolynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk, hPδ]

theorem bijective_of_comp_eq {n : ℕ} (γ : TT k n M →ₐ[k] C) (hγ2 : RingHom.ker γ ≤ tt k n M ^ 2)
    (φ : TT k n M →ₐ[k] TT k n M) (hφ : γ.comp φ = γ) : Function.Bijective φ := by
  refine MvPolynomial.bijective_algHom_truncated_of_forall_exists_sub_mem_sq k n M φ fun j =>
    ⟨Ideal.Quotient.mk _ (MvPolynomial.X j), hγ2 ?_⟩
  rw [RingHom.mem_ker, map_sub, ← AlgHom.comp_apply, hφ, sub_self]

theorem eq_of_ker_le_sq (hM : 1 ≤ M) {n m : ℕ}
    (γ : TT k n M →ₐ[k] C) (hγ : Function.Surjective γ) (hγ2 : RingHom.ker γ ≤ tt k n M ^ 2)
    (δ : TT k m M →ₐ[k] C) (hδ : Function.Surjective δ) (hδ2 : RingHom.ker δ ≤ tt k m M ^ 2) : n = m := by
  obtain ⟨θ, hθ⟩ := exists_algHom_comp_eq γ δ hδ
  obtain ⟨θ', hθ'⟩ := exists_algHom_comp_eq δ γ hγ
  have h1 : Function.Bijective (θ'.comp θ) :=
    bijective_of_comp_eq γ hγ2 _ (by rw [← AlgHom.comp_assoc, hθ', hθ])
  have h2 : Function.Bijective (θ.comp θ') :=
    bijective_of_comp_eq δ hδ2 _ (by rw [← AlgHom.comp_assoc, hθ, hθ'])
  have hθbij : Function.Bijective θ :=
    ⟨Function.Injective.of_comp (f := θ') h1.1, Function.Surjective.of_comp h2.2⟩
  have e := cotangentEquivOfAlgEquiv (AlgEquiv.ofBijective θ hθbij)
  have := e.finrank_eq
  rwa [finrank_cotangent_tt hM, finrank_cotangent_tt hM] at this

end Compare

section Descent

variable {k}
variable {M : ℕ} {C : Type*} [CommRing C] [Algebra k C] [IsLocalRing C]

theorem tt_zero_eq_bot : tt k 0 M = ⊥ := by
  rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  intro f hf
  rw [RingHom.mem_ker] at hf
  have hf' : MvPolynomial.coeff 0 f = 0 := hf
  have : f = 0 := by
    rw [MvPolynomial.eq_C_of_isEmpty f, hf', map_zero]
  rw [this]; exact zero_mem _

theorem exists_not_mem_sq {n : ℕ} (γ : TT k n M →ₐ[k] C) (h : ¬ RingHom.ker γ ≤ tt k n M ^ 2) :
    ∃ (s : ℕ) (hs : n = s + 1) (x : TT k n M), x ∈ RingHom.ker γ ∧ x ∈ tt k n M ∧ x ∉ tt k n M ^ 2 := by
  obtain ⟨x, hxk, hx2⟩ := Set.not_subset.mp h
  have hx1 : x ∈ tt k n M := ker_le_tt k n M γ hxk
  cases n with
  | zero =>
    exfalso; apply hx2
    rw [tt_zero_eq_bot] at hx1
    rw [hx1]; exact zero_mem _
  | succ s => exact ⟨s, rfl, x, hxk, hx1, hx2⟩

theorem exists_minimal : ∀ (r : ℕ) (β : TT k r M →ₐ[k] C), Function.Surjective β →
    (∃ g : Fin r → TT k r M, RingHom.ker β = Ideal.span (Set.range g)) →
    ∃ (m : ℕ) (δ : TT k m M →ₐ[k] C), Function.Surjective δ ∧ RingHom.ker δ ≤ tt k m M ^ 2 ∧
      ∃ g : Fin m → TT k m M, RingHom.ker δ = Ideal.span (Set.range g) := by
  intro r
  induction r with
  | zero =>
    intro β hβ hg
    refine ⟨0, β, hβ, ?_, hg⟩
    intro x hx
    have := ker_le_tt k 0 M β hx
    rw [tt_zero_eq_bot] at this
    rw [this]; exact zero_mem _
  | succ s ih =>
    intro β hβ hg
    by_cases hmin : RingHom.ker β ≤ tt k (s + 1) M ^ 2
    · exact ⟨s + 1, β, hβ, hmin, hg⟩
    · obtain ⟨x, hxk, hx2⟩ := Set.not_subset.mp hmin
      have hx1 : x ∈ tt k (s + 1) M := ker_le_tt k (s + 1) M β hxk
      obtain ⟨g, hg⟩ := hg
      obtain ⟨β', hβ', g', hg'⟩ := drop β g hg x hxk hx1 hx2
      exact ih β' (hβ' hβ) ⟨g', hg'⟩

theorem ker_eq_span_of_comp_eq {n : ℕ} (α δ : TT k n M →ₐ[k] C) (θ : TT k n M ≃ₐ[k] TT k n M)
    (hθ : δ.comp (θ : TT k n M →ₐ[k] TT k n M) = α) (g : Fin n → TT k n M)
    (hg : RingHom.ker δ = Ideal.span (Set.range g)) :
    RingHom.ker α = Ideal.span (Set.range fun i => θ.symm (g i)) := by
  have key : Ideal.span (Set.range fun i => θ.symm (g i)) =
      (Ideal.span (Set.range g)).map (θ.toRingEquiv.symm : TT k n M →+* TT k n M) := by
    rw [Ideal.map_span, ← Set.range_comp]; rfl
  ext y
  rw [RingHom.mem_ker, ← hθ, show (δ.comp (θ : TT k n M →ₐ[k] TT k n M)) y = δ (θ y) from rfl, ← RingHom.mem_ker, hg,
    key, Ideal.map_comap_of_equiv, Ideal.mem_comap, RingEquiv.symm_symm]
  rfl

variable [Module.Finite k C]

theorem exists_gen_of_minimal (hM : 1 ≤ M) {m : ℕ} (δ : TT k m M →ₐ[k] C) (hδ : Function.Surjective δ)
    (hδ2 : RingHom.ker δ ≤ tt k m M ^ 2) (gδ : Fin m → TT k m M) (hgδ : RingHom.ker δ = Ideal.span (Set.range gδ)) :
    ∀ (N : ℕ) (α : TT k N M →ₐ[k] C), Function.Surjective α →
      ∃ h : Fin N → TT k N M, RingHom.ker α = Ideal.span (Set.range h) := by
  intro N
  induction N with
  | zero =>
    intro α hα
    by_cases hmin : RingHom.ker α ≤ tt k 0 M ^ 2
    · have h0 := eq_of_ker_le_sq hM α hα hmin δ hδ hδ2
      subst h0
      obtain ⟨θ, hθ⟩ := Algebra.exists_algEquiv_comp_eq_of_surjective_of_ker_le_sq_truncated k C 0 M α δ hα hδ hmin hδ2
      exact ⟨fun i => θ.symm (gδ i), ker_eq_span_of_comp_eq α δ θ hθ gδ hgδ⟩
    · obtain ⟨s, hs, -⟩ := exists_not_mem_sq α hmin
      exact absurd hs (Nat.succ_ne_zero s).symm
  | succ s ih =>
    intro α hα
    by_cases hmin : RingHom.ker α ≤ tt k (s + 1) M ^ 2
    · have h0 := eq_of_ker_le_sq hM α hα hmin δ hδ hδ2
      subst h0
      obtain ⟨θ, hθ⟩ := Algebra.exists_algEquiv_comp_eq_of_surjective_of_ker_le_sq_truncated k C (s + 1) M α δ hα hδ hmin hδ2
      exact ⟨fun i => θ.symm (gδ i), ker_eq_span_of_comp_eq α δ θ hθ gδ hgδ⟩
    · obtain ⟨x, hxk, hx2⟩ := Set.not_subset.mp hmin
      have hx1 : x ∈ tt k (s + 1) M := ker_le_tt k (s + 1) M α hxk
      obtain ⟨α', hα', hlift⟩ := lift α x hxk hx1 hx2
      obtain ⟨h', hh'⟩ := ih α' (hα' hα)
      exact hlift h' hh'

end Descent

end Algebra.DevTrunc
p2m_reactivate "P2MW.S_Algebra_exists_ker_eq_span_of_surjective_truncated_of_ker_eq_span.Algebra P2MW.S_Algebra_exists_ker_eq_span_of_surjective_truncated_of_ker_eq_span.Algebra.DevTrunc"
p2m_reactivate "P2MW.S_Algebra_exists_ker_eq_span_of_surjective_truncated_of_ker_eq_span.Algebra"

end
p2m_reactivate "P2MW.S_Algebra_exists_ker_eq_span_of_surjective_truncated_of_ker_eq_span.Algebra P2MW.S_Algebra_exists_ker_eq_span_of_surjective_truncated_of_ker_eq_span.Algebra.DevTrunc"

theorem solution
    (k : Type*) [Field k] (C : Type*) [CommRing C] [Algebra k C] [IsLocalRing C] [Module.Finite k C]
    (M : ℕ)
    (r : ℕ) (β : (MvPolynomial (Fin r) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin r) k →+* k)) ^ (M + 1)) →ₐ[k] C)
    (hβ : Function.Surjective β)
    (gβ : Fin r → (MvPolynomial (Fin r) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin r) k →+* k)) ^ (M + 1)))
    (hgβ : RingHom.ker β = Ideal.span (Set.range gβ))
    (N : ℕ) (α : (MvPolynomial (Fin N) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k)) ^ (M + 1)) →ₐ[k] C)
    (hα : Function.Surjective α) :
    ∃ h : Fin N → (MvPolynomial (Fin N) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k)) ^ (M + 1)),
      RingHom.ker α = Ideal.span (Set.range h) := by
  classical
  by_cases hM : M = 0
  ·
    subst hM
    refine ⟨fun _ => 0, ?_⟩
    have hbot : Ideal.span (Set.range fun _ : Fin N => (0 : MvPolynomial (Fin N) k ⧸
        (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k)) ^ (0 + 1))) = ⊥ :=
      Ideal.span_eq_bot.mpr (by rintro _ ⟨i, rfl⟩; rfl)
    rw [hbot, eq_bot_iff]
    intro x hx
    have hx1 := Algebra.DevTrunc.ker_le_tt k N 0 α hx
    have := Ideal.pow_mem_pow hx1 (0 + 1)
    rw [Algebra.DevTrunc.tt_pow_eq_bot, Ideal.mem_bot] at this
    simpa using this
  · have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hM
    obtain ⟨m, δ, hδ, hδ2, gδ, hgδ⟩ := Algebra.DevTrunc.exists_minimal (k := k) r β hβ ⟨gβ, hgβ⟩
    exact Algebra.DevTrunc.exists_gen_of_minimal hM1 δ hδ hδ2 gδ hgδ N α hα

end S_Algebra_exists_ker_eq_span_of_surjective_truncated_of_ker_eq_span
end P2MW
export P2MW.S_Algebra_exists_ker_eq_span_of_surjective_truncated_of_ker_eq_span (solution)
