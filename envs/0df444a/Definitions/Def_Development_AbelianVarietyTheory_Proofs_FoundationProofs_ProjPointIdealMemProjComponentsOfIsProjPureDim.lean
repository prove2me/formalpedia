-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ProjPointIdealMemProjComponentsOfIsProjPureDim
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_ProjPointIdealMemProjComponentsOfIsProjPureDim
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T15:48:15.643808+00:00
-- url     : https://prove2.me/theorems/eddbd169-12ff-5fef-972b-f01e36871333
-- title:
--   Proj Point Ideal Mem Proj Components Of Is Proj Pure Dim
-- statement:
--   Definitions and structural lemmas for Proj Point Ideal Mem Proj Components Of Is Proj Pure Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ProjPointIdealMemProjComponentsOfIsProjPureDim.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialCountAndBinomialEstimates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Theorems.Thm_GlobalTheory_cast_hilbertDegree_of_degree_eq
import Theorems.Thm_GlobalTheory_coeff_nonneg_of_eventually_eval_nat
import Theorems.Thm_GlobalTheory_coeff_sub_comp_X_sub_C
import Theorems.Thm_GlobalTheory_degree_idealHilbertPoly_anti
import Theorems.Thm_GlobalTheory_degree_idealHilbertPoly_eq_of_isPrime
import Theorems.Thm_GlobalTheory_degree_idealHilbertPoly_lt
import Theorems.Thm_GlobalTheory_eventually_finrank_quotPiece
import Theorems.Thm_GlobalTheory_eventually_idealHilbertPoly_nonneg
import Theorems.Thm_GlobalTheory_exists_ringKrullDim_quotient_mvPolynomial_eq_nat
import Theorems.Thm_GlobalTheory_finrank_quotPiece_add
import Theorems.Thm_GlobalTheory_hilbertDegree_eq_zero_iff
import Theorems.Thm_GlobalTheory_idealHilbertPoly_ne_zero_of_X_notMem
import Theorems.Thm_GlobalTheory_idealHilbertPoly_sup_of_isPrime
import Theorems.Thm_GlobalTheory_isHomogeneous_of_mem_minimalPrimes
import Theorems.Thm_GlobalTheory_isHomogeneous_sup_span_singleton
import Theorems.Thm_GlobalTheory_natCard_degree_eq
import Theorems.Thm_GlobalTheory_polynomial_eq_of_eventually_eval_nat
import Theorems.Thm_GlobalTheory_ringKrullDim_quotient_add_one_of_mem_minimalPrimes_sup
import Theorems.Thm_GlobalTheory_sum_coeff_idealHilbertPoly_minimalPrimes_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Module
namespace GlobalTheory
attribute [local instance] MvPolynomial.gradedAlgebra
theorem ringKrullDim_quotient_add_one_le_of_lt {A : Type*} [CommRing A] {Q P : Ideal A}
    [Q.IsPrime] (h : Q < P) : ringKrullDim (A ⧸ P) + 1 ≤ ringKrullDim (A ⧸ Q) := by
  obtain ⟨g, hg, hgQ⟩ := SetLike.exists_of_lt h
  exact ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor h.le)
    (Ideal.Quotient.factor_surjective _) (r := Ideal.Quotient.mk Q g)
    (mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])) (by
      rwa [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem])
open MvPolynomial DirectSum
variable {ι k : Type*} [Field k]
section Points
theorem eval_smul_of_isHomogeneous {f : MvPolynomial ι k} {d : ℕ} (hf : f.IsHomogeneous d)
    (a : k) (v : ι → k) : MvPolynomial.eval (a • v) f = a ^ d * MvPolynomial.eval v f := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have : s.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hf (MvPolynomial.mem_support_iff.1 hs)
  rw [← this, Finsupp.degree_apply]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  ring
theorem eval_smul_eq_zero_of_isHomogeneous {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) {v : ι → k}
    (hv : ∀ g ∈ I, MvPolynomial.eval v g = 0) (a : k) :
    ∀ g ∈ I, MvPolynomial.eval (a • v) g = 0 := by
  intro g hg
  rw [← sum_homogeneousComponent g, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous i g),
    hv _ (homogeneousComponent_mem_of_mem hI hg i), mul_zero]
theorem mk_mem_projPoints_iff {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) {v : ι → k} (hv : v ≠ 0) :
    Projectivization.mk k v hv ∈ projPoints I ↔ ∀ g ∈ I, MvPolynomial.eval v g = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep k v hv
  rw [projPoints, Set.mem_setOf_eq, ← ha]
  refine ⟨fun h => ?_, fun h => eval_smul_eq_zero_of_isHomogeneous hI h a⟩
  have := eval_smul_eq_zero_of_isHomogeneous hI h (a⁻¹ : kˣ)
  rwa [Units.smul_def, smul_smul, Units.inv_mul, one_smul] at this
theorem mem_projPoints_sup_span {I : Ideal (MvPolynomial ι k)} {s : Set (MvPolynomial ι k)}
    {y : Projectivization k (ι → k)} :
    y ∈ projPoints (I ⊔ Ideal.span s) ↔
      y ∈ projPoints I ∧ ∀ f ∈ s, MvPolynomial.eval y.rep f = 0 := by
  change I ⊔ Ideal.span s ≤ RingHom.ker (MvPolynomial.eval y.rep) ↔ _
  rw [sup_le_iff, Ideal.span_le]
  rfl
noncomputable def projPointIdeal (y : Projectivization k (ι → k)) : Ideal (MvPolynomial ι k) :=
  ((RingHom.ker (MvPolynomial.eval y.rep)).homogeneousCore (homogeneousSubmodule ι k)).toIdeal
instance isPrime_projPointIdeal (y : Projectivization k (ι → k)) : (projPointIdeal y).IsPrime :=
  (RingHom.ker_isPrime _).homogeneousCore
theorem isHomogeneous_projPointIdeal (y : Projectivization k (ι → k)) :
    (projPointIdeal y).IsHomogeneous (homogeneousSubmodule ι k) :=
  HomogeneousIdeal.isHomogeneous _
theorem eval_eq_zero_of_mem_projPointIdeal {y : Projectivization k (ι → k)}
    {g : MvPolynomial ι k} (hg : g ∈ projPointIdeal y) : MvPolynomial.eval y.rep g = 0 :=
  Ideal.toIdeal_homogeneousCore_le _ _ hg
theorem mem_projPointIdeal_iff {y : Projectivization k (ι → k)} {g : MvPolynomial ι k} {d : ℕ}
    (hg : g.IsHomogeneous d) : g ∈ projPointIdeal y ↔ MvPolynomial.eval y.rep g = 0 :=
  ⟨eval_eq_zero_of_mem_projPointIdeal,
    fun h => Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨d, hg⟩ h⟩
theorem mem_projPoints_iff_le {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) {y : Projectivization k (ι → k)} :
    y ∈ projPoints I ↔ I ≤ projPointIdeal y := by
  refine ⟨fun h => ?_, fun h g hg => eval_eq_zero_of_mem_projPointIdeal (h hg)⟩
  exact hI.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ h)
theorem exists_X_notMem_projPointIdeal (y : Projectivization k (ι → k)) :
    ∃ i, (X i : MvPolynomial ι k) ∉ projPointIdeal y := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 y.rep_nonzero
  exact ⟨i, fun h => hi (by simpa using eval_eq_zero_of_mem_projPointIdeal h)⟩
theorem eq_of_projPointIdeal_le {y z : Projectivization k (ι → k)}
    (h : projPointIdeal y ≤ projPointIdeal z) : y = z := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 y.rep_nonzero
  have hi' : y.rep i ≠ 0 := hi
  have key : ∀ j, y.rep i * z.rep j = y.rep j * z.rep i := by
    intro j
    have hh : (MvPolynomial.C (y.rep i) * X j - MvPolynomial.C (y.rep j) * X i :
        MvPolynomial ι k).IsHomogeneous 1 :=
      ((isHomogeneous_X k j).C_mul _).sub ((isHomogeneous_X k i).C_mul _)
    have := (mem_projPointIdeal_iff hh).1 (h ((mem_projPointIdeal_iff hh).2 (by simp [mul_comm])))
    simpa [sub_eq_zero] using this
  rw [← y.mk_rep, ← z.mk_rep, eq_comm, Projectivization.mk_eq_mk_iff']
  refine ⟨z.rep i / y.rep i, funext fun j => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination -key j
theorem projPointIdeal_injective :
    Function.Injective (projPointIdeal : Projectivization k (ι → k) → _) :=
  fun _ _ h => eq_of_projPointIdeal_le h.le
variable [Finite ι]
theorem ncard_projPoints_le_of_forall_mem {I : Ideal (MvPolynomial ι k)}
    (h : ∀ y ∈ projPoints I, projPointIdeal y ∈ projComponents I) :
    (projPoints I).Finite ∧ (projPoints I).ncard ≤ (projComponents I).ncard :=
  ⟨Set.Finite.of_injOn h projPointIdeal_injective.injOn (finite_projComponents I),
    Set.ncard_le_ncard_of_injOn _ h projPointIdeal_injective.injOn (finite_projComponents I)⟩
theorem IsProjPureDim.mem_projComponents_of_le {I P : Ideal (MvPolynomial ι k)} [hp : P.IsPrime]
    (h : IsProjPureDim I 0) (hP : P.IsHomogeneous (homogeneousSubmodule ι k)) (hIP : I ≤ P)
    {i : ι} (hi : (X i : MvPolynomial ι k) ∉ P) : P ∈ projComponents I := by
  obtain ⟨Q, hQ, hle⟩ := Ideal.exists_minimalPrimes_le hIP
  have hQc : Q ∈ projComponents I := ⟨hQ, i, fun h => hi (hle h)⟩
  have hd := h Q hQc
  have := hQ.1.1
  by_cases heq : Q = P
  · exact heq ▸ hQc
  exfalso
  have h1 := ringKrullDim_quotient_add_one_le_of_lt (lt_of_le_of_ne hle heq)
  obtain ⟨δ, hδ⟩ := exists_ringKrullDim_quotient_mvPolynomial_eq_nat hp.ne_top
  rw [hd, hδ] at h1
  obtain rfl : δ = 0 := by
    have : δ + 1 ≤ 0 + 1 := by exact_mod_cast h1
    omega
  have h2 := degree_idealHilbertPoly_lt hP hδ.le
  exact idealHilbertPoly_ne_zero_of_X_notMem hP hi (by simpa using h2)
theorem projPointIdeal_mem_projComponents_of_isProjPureDim {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) (h : IsProjPureDim I 0)
    {y : Projectivization k (ι → k)} (hy : y ∈ projPoints I) :
    projPointIdeal y ∈ projComponents I := by
  obtain ⟨i, hi⟩ := exists_X_notMem_projPointIdeal y
  exact h.mem_projComponents_of_le (isHomogeneous_projPointIdeal y)
    ((mem_projPoints_iff_le hI).1 hy) hi
theorem projPointIdeal_mem_projComponents_of_finite [IsAlgClosed k]
    {I : Ideal (MvPolynomial ι k)} (hI : I.IsHomogeneous (homogeneousSubmodule ι k))
    (h : (projPoints I).Finite) {y : Projectivization k (ι → k)} (hy : y ∈ projPoints I) :
    projPointIdeal y ∈ projComponents I := by
  obtain ⟨i, hi⟩ := exists_X_notMem_projPointIdeal y
  refine ⟨⟨⟨inferInstance, (mem_projPoints_iff_le hI).1 hy⟩, ?_⟩, i, hi⟩
  rintro Q ⟨hQ, hIQ⟩ hQy
  have h1 : idealOfVars ι k ⊓ h.toFinset.inf projPointIdeal ≤ Q := by
    refine le_trans ?_ (hQ.radical_le_iff.2 hIQ)
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := k)]
    rintro g ⟨hg0, hg⟩ v hv
    by_cases hv0 : v = 0
    · subst hv0
      have : idealOfVars ι k ≤ RingHom.ker (MvPolynomial.eval (0 : ι → k)) := by
        rw [Ideal.span_le, Set.range_subset_iff]
        intro j
        simp
      exact this hg0
    · have hz : Projectivization.mk k v hv0 ∈ projPoints I :=
        (mk_mem_projPoints_iff hI hv0).2 hv
      exact (mk_mem_projPoints_iff (isHomogeneous_projPointIdeal _) hv0).1
        (fun _ => eval_eq_zero_of_mem_projPointIdeal) g
        ((Finset.inf_le (f := projPointIdeal) (h.mem_toFinset.2 hz) : _ ≤ _) hg)
  rcases hQ.inf_le.1 h1 with h2 | h2
  · exact absurd (hQy (h2 (Ideal.subset_span ⟨i, rfl⟩))) hi
  · obtain ⟨z, -, hz⟩ := hQ.inf_le'.1 h2
    obtain rfl := eq_of_projPointIdeal_le (hz.trans hQy)
    exact hz
end Points
section Degree
variable [Finite ι]
omit [Finite ι] in
theorem isHomogeneous_of_mem_projComponents {I P : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) (hP : P ∈ projComponents I) :
    P.IsHomogeneous (homogeneousSubmodule ι k) :=
  isHomogeneous_of_mem_minimalPrimes _ hI hP.1
theorem hilbertDegree_pos {P : Ideal (MvPolynomial ι k)} [P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule ι k)) {i : ι}
    (h : (X i : MvPolynomial ι k) ∉ P) : 0 < hilbertDegree P :=
  Nat.pos_of_ne_zero fun h0 =>
    idealHilbertPoly_ne_zero_of_X_notMem hP h ((hilbertDegree_eq_zero_iff hP).1 h0)
theorem ncard_projComponents_le_projSetDegree {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) :
    (projComponents I).ncard ≤ projSetDegree I := by
  rw [Set.ncard_eq_toFinset_card _ (finite_projComponents I), projSetDegree, Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum fun P hP => ?_
  rw [Set.Finite.mem_toFinset] at hP
  obtain ⟨i, hi⟩ := hP.2
  have := hP.1.1.1
  exact hilbertDegree_pos (isHomogeneous_of_mem_projComponents hI hP) hi
omit [Finite ι] in
theorem projComponents_of_isPrime {P : Ideal (MvPolynomial ι k)} [P.IsPrime] {i : ι}
    (h : (X i : MvPolynomial ι k) ∉ P) : projComponents P = {P} := by
  ext Q
  rw [projComponents, Set.mem_setOf_eq, Ideal.minimalPrimes_eq_subsingleton_self]
  exact ⟨fun h => h.1, fun hQ => ⟨hQ, i, hQ ▸ h⟩⟩
theorem projSetDegree_of_isPrime {P : Ideal (MvPolynomial ι k)} [P.IsPrime] {i : ι}
    (h : (X i : MvPolynomial ι k) ∉ P) : projSetDegree P = hilbertDegree P := by
  simp [projSetDegree, projComponents_of_isPrime h]
theorem exists_ringKrullDim_quotient_eq_succ {P : Ideal (MvPolynomial ι k)} [hp : P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule ι k)) {i : ι}
    (h : (X i : MvPolynomial ι k) ∉ P) :
    ∃ e : ℕ, ringKrullDim (MvPolynomial ι k ⧸ P) = (e + 1 : ℕ) := by
  obtain ⟨δ, hδ⟩ := exists_ringKrullDim_quotient_mvPolynomial_eq_nat hp.ne_top
  cases δ with
  | zero =>
    exact absurd (by simpa using degree_idealHilbertPoly_lt hP hδ.le)
      (idealHilbertPoly_ne_zero_of_X_notMem hP h)
  | succ e => exact ⟨e, hδ⟩
theorem ringKrullDim_of_mem_projComponents_sup {P Q : Ideal (MvPolynomial ι k)} [P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule ι k)) {e : ℕ}
    (he : ringKrullDim (MvPolynomial ι k ⧸ P) = (e + 1 : ℕ)) {f : MvPolynomial ι k} {d : ℕ}
    (hf : f.IsHomogeneous d) (hfP : f ∉ P) (hQ : Q ∈ projComponents (P ⊔ Ideal.span {f})) :
    ∃ e' : ℕ, e = e' + 1 ∧ ringKrullDim (MvPolynomial ι k ⧸ Q) = (e' + 1 : ℕ) := by
  obtain ⟨i, hi⟩ := hQ.2
  have := hQ.1.1.1
  obtain ⟨e', he'⟩ := exists_ringKrullDim_quotient_eq_succ
    (isHomogeneous_of_mem_projComponents (isHomogeneous_sup_span_singleton hP hf) hQ) hi
  have h1 := ringKrullDim_quotient_add_one_of_mem_minimalPrimes_sup k hfP hQ.1
  rw [he, he'] at h1
  have : e' + 1 + 1 = e + 1 := by exact_mod_cast h1
  exact ⟨e', by omega, he'⟩
theorem projSetDegree_sup_le_of_isPrime {P : Ideal (MvPolynomial ι k)} [P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule ι k)) {i : ι}
    (hi : (X i : MvPolynomial ι k) ∉ P) {f : MvPolynomial ι k} {d : ℕ}
    (hf : f.IsHomogeneous d) (hfP : f ∉ P) :
    projSetDegree (P ⊔ Ideal.span {f}) ≤ d * hilbertDegree P := by
  obtain ⟨e, he⟩ := exists_ringKrullDim_quotient_eq_succ hP hi
  have hJ := isHomogeneous_sup_span_singleton hP hf
  cases e with
  | zero =>
    rw [projSetDegree, Finset.sum_eq_zero]
    · exact Nat.zero_le _
    intro Q hQ
    rw [Set.Finite.mem_toFinset] at hQ
    obtain ⟨e', h, -⟩ := ringKrullDim_of_mem_projComponents_sup hP he hf hfP hQ
    omega
  | succ e =>
    have hdeg := degree_idealHilbertPoly_eq_of_isPrime hP he
    obtain ⟨h1, h2⟩ := coeff_sub_comp_X_sub_C (idealHilbertPoly P) (d : ℚ) e hdeg.le
    rw [← idealHilbertPoly_sup_of_isPrime hP hf hfP] at h1 h2
    have h3 : (idealHilbertPoly (P ⊔ Ideal.span {f})).degree ≤ e :=
      (degree_le_iff_coeff_zero _ _).2 fun m hm =>
        (degree_lt_iff_coeff_zero _ _).1 h1 m (by exact_mod_cast hm)
    have h4 := sum_coeff_idealHilbertPoly_minimalPrimes_le hJ h3
    have h5 : (projSetDegree (P ⊔ Ideal.span {f}) : ℚ) ≤ e.factorial *
        ∑ Q ∈ (P ⊔ Ideal.span {f}).finite_minimalPrimes_of_isNoetherianRing.toFinset,
          (idealHilbertPoly Q).coeff e := by
      rw [projSetDegree, Nat.cast_sum, Finset.mul_sum]
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun Q hQ => ?_))
        (Finset.sum_le_sum_of_subset_of_nonneg
          (s := (finite_projComponents (P ⊔ Ideal.span {f})).toFinset) (fun Q hQ => ?_) ?_)
      · rw [Set.Finite.mem_toFinset] at hQ
        obtain ⟨e', h, hQe⟩ := ringKrullDim_of_mem_projComponents_sup hP he hf hfP hQ
        obtain rfl : e = e' := by omega
        have := hQ.1.1.1
        have hQh := isHomogeneous_of_mem_projComponents hJ hQ
        exact cast_hilbertDegree_of_degree_eq hQh (degree_idealHilbertPoly_eq_of_isPrime hQh hQe)
      · rw [Set.Finite.mem_toFinset] at hQ ⊢
        exact hQ.1
      · intro Q hQ _
        rw [Set.Finite.mem_toFinset] at hQ
        have hQh := isHomogeneous_of_mem_minimalPrimes _ hJ hQ
        exact mul_nonneg (by positivity) (coeff_nonneg_of_eventually_eval_nat
          ((degree_idealHilbertPoly_anti hJ hQh hQ.1.2).trans h3)
          (eventually_idealHilbertPoly_nonneg hQh))
    have h6 := h5.trans (mul_le_mul_of_nonneg_left h4 (by positivity))
    rw [h2] at h6
    have h7 : (projSetDegree (P ⊔ Ideal.span {f}) : ℚ) ≤ d * hilbertDegree P := by
      rw [cast_hilbertDegree_of_degree_eq hP hdeg, Nat.factorial_succ]
      push_cast
      linarith
    exact_mod_cast h7
omit [Finite ι] in

theorem exists_mem_projComponents_sup {I J Q : Ideal (MvPolynomial ι k)}
    (hQ : Q ∈ projComponents (I ⊔ J)) :
    ∃ P ∈ projComponents I, Q ∈ projComponents (P ⊔ J) := by
  have := hQ.1.1.1
  obtain ⟨P, hP, hle⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hQ.1.1.2)
  obtain ⟨i, hi⟩ := hQ.2
  exact ⟨P, ⟨hP, i, fun h => hi (hle h)⟩, ⟨⟨this, sup_le hle (le_sup_right.trans hQ.1.1.2)⟩,
    fun R hR hRQ => hQ.1.2 ⟨hR.1, (sup_le_sup_right hP.1.2 J).trans hR.2⟩ hRQ⟩, i, hi⟩
theorem projSetDegree_sup_le_sum (I J : Ideal (MvPolynomial ι k)) :
    projSetDegree (I ⊔ J) ≤ ∑ P ∈ (finite_projComponents I).toFinset, projSetDegree (P ⊔ J) := by
  classical
  refine le_trans (Finset.sum_le_sum_of_subset (t := (finite_projComponents I).toFinset.biUnion
    fun P => (finite_projComponents (P ⊔ J)).toFinset) ?_) ?_
  · intro Q hQ
    simpa using exists_mem_projComponents_sup (by simpa using hQ)
  · generalize (finite_projComponents I).toFinset = s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      exact (Nat.le_add_right _ _).trans
        (Finset.sum_union_inter.le.trans (Nat.add_le_add_left ih _))
theorem projSetDegree_sup_le_of_forall_notMem {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) {f : MvPolynomial ι k} {d : ℕ}
    (hf : f.IsHomogeneous d) (h : ∀ P ∈ projComponents I, f ∉ P) :
    projSetDegree (I ⊔ Ideal.span {f}) ≤ d * projSetDegree I := by
  refine (projSetDegree_sup_le_sum I _).trans ?_
  rw [projSetDegree, Finset.mul_sum]
  refine Finset.sum_le_sum fun P hP => ?_
  rw [Set.Finite.mem_toFinset] at hP
  obtain ⟨i, hi⟩ := hP.2
  have := hP.1.1.1
  exact projSetDegree_sup_le_of_isPrime (isHomogeneous_of_mem_projComponents hI hP) hi hf (h P hP)
theorem projSetDegree_sup_le {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) {f : MvPolynomial ι k} {d : ℕ}
    (hf : f.IsHomogeneous d) (hd : 1 ≤ d) :
    projSetDegree (I ⊔ Ideal.span {f}) ≤ d * projSetDegree I := by
  refine (projSetDegree_sup_le_sum I _).trans ?_
  rw [projSetDegree, Finset.mul_sum]
  refine Finset.sum_le_sum fun P hP => ?_
  rw [Set.Finite.mem_toFinset] at hP
  obtain ⟨i, hi⟩ := hP.2
  have := hP.1.1.1
  by_cases hfP : f ∈ P
  · rw [sup_eq_left.2 ((Ideal.span_singleton_le_iff_mem _).2 hfP), projSetDegree_of_isPrime hi]
    exact Nat.le_mul_of_pos_left _ hd
  · exact projSetDegree_sup_le_of_isPrime (isHomogeneous_of_mem_projComponents hI hP) hi hf hfP
theorem IsProjPureDim.sup_span_singleton {I : Ideal (MvPolynomial ι k)} {e : ℕ}
    (he : IsProjPureDim I (e + 1)) (hI : I.IsHomogeneous (homogeneousSubmodule ι k))
    {f : MvPolynomial ι k} {d : ℕ} (hf : f.IsHomogeneous d)
    (h : ∀ P ∈ projComponents I, f ∉ P) : IsProjPureDim (I ⊔ Ideal.span {f}) e := by
  intro Q hQ
  obtain ⟨P, hP, hQP⟩ := exists_mem_projComponents_sup hQ
  have := hP.1.1.1
  obtain ⟨e', h1, h2⟩ := ringKrullDim_of_mem_projComponents_sup
    (isHomogeneous_of_mem_projComponents hI hP) (he P hP) hf (h P hP) hQP
  obtain rfl : e = e' := by omega
  exact h2
theorem IsProjPureDim.projComponents_sup_span_singleton {I : Ideal (MvPolynomial ι k)}
    (he : IsProjPureDim I 0) (hI : I.IsHomogeneous (homogeneousSubmodule ι k))
    {f : MvPolynomial ι k} {d : ℕ} (hf : f.IsHomogeneous d)
    (h : ∀ P ∈ projComponents I, f ∉ P) : projComponents (I ⊔ Ideal.span {f}) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun Q hQ => ?_
  obtain ⟨P, hP, hQP⟩ := exists_mem_projComponents_sup hQ
  have := hP.1.1.1
  obtain ⟨e', h1, -⟩ := ringKrullDim_of_mem_projComponents_sup
    (isHomogeneous_of_mem_projComponents hI hP) (he P hP) hf (h P hP) hQP
  omega
omit [Finite ι] in
theorem isHomogeneous_sup_span_range {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) {σ : Type*} {f : σ → MvPolynomial ι k}
    {d : σ → ℕ} (hf : ∀ j, (f j).IsHomogeneous (d j)) (s : Set σ) :
    (I ⊔ Ideal.span (f '' s)).IsHomogeneous (homogeneousSubmodule ι k) :=
  hI.sup (Ideal.homogeneous_span _ _ (by rintro x ⟨j, -, rfl⟩; exact ⟨d j, hf j⟩))
theorem projSetDegree_sup_span_image_le {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) {σ : Type*} {f : σ → MvPolynomial ι k}
    {d : σ → ℕ} (hf : ∀ j, (f j).IsHomogeneous (d j)) (s : Finset σ) (hd : ∀ j ∈ s, 1 ≤ d j) :
    projSetDegree (I ⊔ Ideal.span (f '' s)) ≤ projSetDegree I * ∏ j ∈ s, d j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.coe_insert, Set.image_insert_eq, Ideal.span_insert, sup_comm (Ideal.span {f a}),
      ← sup_assoc, Finset.prod_insert ha, mul_left_comm]
    exact (projSetDegree_sup_le (isHomogeneous_sup_span_range hI hf _) (hf a)
      (hd a (by simp))).trans (Nat.mul_le_mul_left _ (ih fun j hj => hd j (by simp [hj])))
def CutsProperly (I : Ideal (MvPolynomial ι k)) {s : ℕ} (f : Fin s → MvPolynomial ι k) : Prop :=
  ∀ j, ∀ P ∈ projComponents (I ⊔ Ideal.span (f '' Set.Iio j)), f j ∉ P
theorem CutsProperly.isProjPureDim_and_projSetDegree_le {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) {s : ℕ} {f : Fin s → MvPolynomial ι k}
    {d : Fin s → ℕ} (hf : ∀ j, (f j).IsHomogeneous (d j)) (h : CutsProperly I f) :
    (∀ e, IsProjPureDim I (e + s) → IsProjPureDim (I ⊔ Ideal.span (Set.range f)) e) ∧
      projSetDegree (I ⊔ Ideal.span (Set.range f)) ≤ projSetDegree I * ∏ j, d j := by
  induction s with
  | zero => simp
  | succ s ih =>
    have e1 : ∀ j : Fin s, (fun j => f (Fin.castSucc j)) '' Set.Iio j =
        f '' Set.Iio (Fin.castSucc j) := by
      intro j
      rw [← Fin.image_castSucc_Iio, Set.image_image]
    have e2 : f '' Set.Iio (Fin.last s) = Set.range fun j => f (Fin.castSucc j) := by
      ext x
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨j.castPred (ne_of_lt hj), by simp⟩
      · rintro ⟨j, rfl⟩
        exact ⟨_, Fin.castSucc_lt_last j, rfl⟩
    have e3 : Set.range f = insert (f (Fin.last s)) (Set.range fun j => f (Fin.castSucc j)) := by
      ext x
      simp [Fin.exists_fin_succ', or_comm, eq_comm]
    obtain ⟨h1, h2⟩ := ih (f := fun j => f (Fin.castSucc j)) (d := fun j => d (Fin.castSucc j))
      (fun j => hf _) (fun j => by rw [e1]; exact h _)
    have hJ := isHomogeneous_sup_span_range hI hf (Set.Iio (Fin.last s))
    have hl := h (Fin.last s)
    rw [e2] at hJ hl
    rw [e3, Ideal.span_insert, sup_comm (Ideal.span {f _}), ← sup_assoc, Fin.prod_univ_castSucc]
    refine ⟨fun e he => (h1 (e + 1) (by rwa [add_assoc, add_comm 1 s])).sup_span_singleton hJ
      (hf _) hl, (projSetDegree_sup_le_of_forall_notMem hJ (hf _) hl).trans ?_⟩
    rw [← mul_assoc, mul_comm]
    exact Nat.mul_le_mul_right _ h2
end Degree
section Ideal
variable [Finite ι]
theorem bezout_bound_ideal {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) :
    (∀ (d : ℕ) (f : MvPolynomial ι k), f.IsHomogeneous d → (∀ P ∈ projComponents I, f ∉ P) →
      projSetDegree (I ⊔ Ideal.span {f}) ≤ d * projSetDegree I ∧
      (∀ e, IsProjPureDim I (e + 1) → IsProjPureDim (I ⊔ Ideal.span {f}) e) ∧
      (IsProjPureDim I 0 → projComponents (I ⊔ Ideal.span {f}) = ∅)) ∧
    (∀ (e : ℕ) (d : Fin e → ℕ) (f : Fin e → MvPolynomial ι k), IsProjPureDim I e →
      (∀ j, (f j).IsHomogeneous (d j)) → CutsProperly I f →
      {y ∈ projPoints I | ∀ j, MvPolynomial.eval y.rep (f j) = 0}.Finite ∧
      {y ∈ projPoints I | ∀ j, MvPolynomial.eval y.rep (f j) = 0}.ncard ≤
        projSetDegree I * ∏ j, d j) ∧
    (∀ (s : ℕ) (d : Fin s → ℕ) (f : Fin s → MvPolynomial ι k),
      (∀ j, (f j).IsHomogeneous (d j)) → (∀ j, 1 ≤ d j) →
      projSetDegree (I ⊔ Ideal.span (Set.range f)) ≤ projSetDegree I * ∏ j, d j ∧
      (projComponents (I ⊔ Ideal.span (Set.range f))).ncard ≤ projSetDegree I * ∏ j, d j ∧
      (IsAlgClosed k → {y ∈ projPoints I | ∀ j, MvPolynomial.eval y.rep (f j) = 0}.Finite →
        {y ∈ projPoints I | ∀ j, MvPolynomial.eval y.rep (f j) = 0}.ncard ≤
          projSetDegree I * ∏ j, d j)) := by
  have hset : ∀ {s : ℕ} (f : Fin s → MvPolynomial ι k),
      {y ∈ projPoints I | ∀ j, MvPolynomial.eval y.rep (f j) = 0} =
        projPoints (I ⊔ Ideal.span (Set.range f)) := by
    intro s f
    ext y
    simp [mem_projPoints_sup_span]
  refine ⟨fun d f hf h => ⟨projSetDegree_sup_le_of_forall_notMem hI hf h,
    fun e he => he.sup_span_singleton hI hf h,
    fun he => he.projComponents_sup_span_singleton hI hf h⟩,
    fun e d f he hf h => ?_, fun s d f hf hd => ?_⟩
  · have hJ := isHomogeneous_sup_span_range hI hf Set.univ
    rw [Set.image_univ] at hJ
    obtain ⟨h1, h2⟩ := h.isProjPureDim_and_projSetDegree_le hI hf
    obtain ⟨h3, h4⟩ := ncard_projPoints_le_of_forall_mem fun y hy =>
      projPointIdeal_mem_projComponents_of_isProjPureDim hJ (h1 0 (by rwa [zero_add])) hy
    rw [hset]
    exact ⟨h3, h4.trans ((ncard_projComponents_le_projSetDegree hJ).trans h2)⟩
  · have hJ := isHomogeneous_sup_span_range hI hf Set.univ
    have h1 := projSetDegree_sup_span_image_le hI hf Finset.univ fun j _ => hd j
    rw [Finset.coe_univ, Set.image_univ] at h1
    rw [Set.image_univ] at hJ
    have h2 := (ncard_projComponents_le_projSetDegree hJ).trans h1
    refine ⟨h1, h2, fun _ hfin => ?_⟩
    rw [hset] at hfin ⊢
    exact (ncard_projPoints_le_of_forall_mem fun y hy =>
      projPointIdeal_mem_projComponents_of_finite hJ hfin hy).2.trans h2
end Ideal
section Space
theorem idealHilbertPoly_bot [Fintype ι] {n : ℕ} (hn : Fintype.card ι = n + 1) :
    idealHilbertPoly (⊥ : Ideal (MvPolynomial ι k)) = preHilbertPoly ℚ n 0 := by
  apply polynomial_eq_of_eventually_eval_nat
  filter_upwards [eventually_finrank_quotPiece (Ideal.IsHomogeneous.bot
    (homogeneousSubmodule ι k))] with m hm
  have h1 := finrank_quotPiece_add (⊥ : Ideal (MvPolynomial ι k)) m
  have h2 : finrank k (homogeneousSubmodule ι k m) = (m + Fintype.card ι - 1).choose m := by
    rw [← natCard_degree_eq, homogeneousSubmodule_eq_finsupp_supported]
    exact finrank_eq_nat_card_basis (basisRestrictSupport k _)
  rw [Submodule.restrictScalars_bot, bot_inf_eq, finrank_bot, add_zero, h2, hn] at h1
  rw [← hm, h1, preHilbertPoly_eq_choose_sub_add ℚ n (Nat.zero_le m), Nat.sub_zero,
    ← Nat.choose_symm_add]
  rfl
theorem projSetDegree_bot [Finite ι] [Nonempty ι] :
    projSetDegree (⊥ : Ideal (MvPolynomial ι k)) = 1 := by
  cases nonempty_fintype ι
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card ι = n + 1 := Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  rw [projSetDegree_of_isPrime (i := i) (by simp), hilbertDegree, idealHilbertPoly_bot hn,
    natDegree_preHilbertPoly, leadingCoeff_preHilbertPoly,
    mul_inv_cancel₀ (by exact_mod_cast n.factorial_ne_zero), Nat.floor_one]
theorem isProjPureDim_bot (n : ℕ) : IsProjPureDim (⊥ : Ideal (MvPolynomial (Fin (n + 1)) k)) n := by
  intro P hP
  rw [projComponents_of_isPrime (i := 0) (by simp), Set.mem_singleton_iff] at hP
  rw [hP, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp
theorem cutsProperly_bot {f : MvPolynomial ι k} (hf : f ≠ 0) :
    CutsProperly (⊥ : Ideal (MvPolynomial ι k)) ![f] := by
  intro j P hP
  obtain rfl : j = 0 := Subsingleton.elim _ _
  have h := hP.1
  rw [show Set.Iio (0 : Fin 1) = ∅ from Set.Iio_bot, Set.image_empty, Ideal.span_empty,
    sup_bot_eq, Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff] at h
  simpa [h] using hf
example {f : MvPolynomial (Fin 2) k} {d : ℕ} (hf : f.IsHomogeneous d) (h0 : f ≠ 0) :
    {y : Projectivization k (Fin 2 → k) | MvPolynomial.eval y.rep f = 0}.ncard ≤ d := by
  have := ((bezout_bound_ideal (Ideal.IsHomogeneous.bot _)).2.1 1 ![d] ![f] (isProjPureDim_bot 1)
    (by simpa using hf) (cutsProperly_bot h0)).2
  simpa [projSetDegree_bot, projPoints] using this
end Space
end GlobalTheory


