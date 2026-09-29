-- Prove2me | solution 1 for AlgebraicCurve.exists_aeval_sub_mem_smul_of_isMaximal_of_isIntegrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/af8d2d9d-a6a5-52db-affd-72856fb790d5

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_aeval_sub_mem_smul_of_isMaximal_of_isIntegrallyClosed

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial UniqueFactorizationMonoid

universe u v

noncomputable section

namespace FibreMonogenicSol

section Local

variable {B : Type v} [CommRing B] [IsDedekindDomain B]

theorem eq_span_sup_sq (Q : Ideal B) [Q.IsPrime] (hQ0 : Q ≠ ⊥) (t : B) (ht : t ∈ Q)
    (ht2 : t ∉ Q ^ 2) : Ideal.span {t} ⊔ Q ^ 2 = Q := by
  have hle : Ideal.span {t} ⊔ Q ^ 2 ≤ Q ^ 1 := by
    rw [pow_one]
    exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 ht) (Ideal.pow_le_self two_ne_zero)
  have hlt : Q ^ (1 + 1) < Ideal.span {t} ⊔ Q ^ 2 := by
    refine lt_of_le_of_ne le_sup_right fun h => ht2 ?_
    have : t ∈ Ideal.span {t} ⊔ Q ^ 2 := Ideal.mem_sup_left (Ideal.mem_span_singleton_self t)
    rw [← h] at this
    exact this
  have := Ideal.eq_prime_pow_of_succ_lt_of_le hQ0 hlt hle
  rw [this, pow_one]

theorem pow_le_span_pow_sup (Q : Ideal B) [Q.IsPrime] (hQ0 : Q ≠ ⊥) (t : B) (ht : t ∈ Q)
    (ht2 : t ∉ Q ^ 2) (k : ℕ) : Q ^ k ≤ Ideal.span {t ^ k} ⊔ Q ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hQ : Q = Ideal.span {t} ⊔ Q ^ 2 := (eq_span_sup_sq Q hQ0 t ht ht2).symm
    calc Q ^ (k + 1) = Q ^ k * Q := pow_succ Q k
      _ ≤ (Ideal.span {t ^ k} ⊔ Q ^ (k + 1)) * Q := Ideal.mul_mono_left ih
      _ = Ideal.span {t ^ k} * Q ⊔ Q ^ (k + 1) * Q := Ideal.sup_mul _ _ _
      _ ≤ Ideal.span {t ^ (k + 1)} ⊔ Q ^ (k + 1 + 1) := by
        refine sup_le ?_ ?_
        · conv_lhs => rw [hQ]
          rw [Ideal.mul_sup, Ideal.span_singleton_mul_span_singleton, ← pow_succ]
          refine sup_le le_sup_left (le_sup_right.trans' ?_)
          rw [show k + 1 + 1 = k + 2 by ring, pow_add]
          exact Ideal.mul_mono_left ((Ideal.span_singleton_le_iff_mem _).2
            (Ideal.pow_mem_pow ht k))
        · rw [← pow_succ]; exact le_sup_right

theorem exists_expansion (Q : Ideal B) [Q.IsPrime] (hQ0 : Q ≠ ⊥) (t : B) (ht : t ∈ Q)
    (ht2 : t ∉ Q ^ 2) {K : Type u} [Field K] (φ : K →+* B)
    (hres : ∀ b : B, ∃ a : K, b - φ a ∈ Q) (b : B) (k : ℕ) :
    ∃ a : ℕ → K, b - ∑ i ∈ Finset.range k, φ (a i) * t ^ i ∈ Q ^ k := by
  induction k with
  | zero => exact ⟨fun _ => 0, by simp⟩
  | succ k ih =>
    obtain ⟨a, ha⟩ := ih

    have hmem := pow_le_span_pow_sup Q hQ0 t ht ht2 k ha
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 hmem
    obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton'.1 hu
    obtain ⟨c, hc⟩ := hres b'
    refine ⟨Function.update a k c, ?_⟩
    rw [Finset.sum_range_succ, Function.update_self]
    have hsum : ∑ i ∈ Finset.range k, φ (Function.update a k c i) * t ^ i =
        ∑ i ∈ Finset.range k, φ (a i) * t ^ i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Function.update_of_ne (Finset.mem_range.1 hi).ne]
    rw [hsum]
    have : b - (∑ i ∈ Finset.range k, φ (a i) * t ^ i + φ c * t ^ k) =
        (b' - φ c) * t ^ k + w := by
      have e : b - ∑ i ∈ Finset.range k, φ (a i) * t ^ i = b' * t ^ k + w := huw.symm
      linear_combination e
    rw [this]
    refine Ideal.add_mem _ ?_ hw
    rw [pow_succ']
    exact Ideal.mul_mem_mul hc (Ideal.pow_mem_pow ht k)

end Local

section Main

variable {K : Type u} [Field K] [IsAlgClosed K] {B : Type v} [CommRing B] [IsDomain B]
  [IsIntegrallyClosed B] [Algebra K[X] B] [Module.Finite K[X] B] [FaithfulSMul K[X] B]

theorem main (P : Ideal K[X]) (hP : P.IsMaximal) :
    ∃ y : B, ∀ z : B, ∃ q : Polynomial K[X], z - aeval y q ∈ P • (⊤ : Submodule K[X] B) := by
  classical

  haveI : IsNoetherianRing B := IsNoetherianRing.of_finite K[X] B
  haveI : Algebra.IsIntegral K[X] B := inferInstance
  haveI : Ring.DimensionLEOne B := Ring.DimensionLEOne.of_isIntegral K[X] B
  haveI : IsDedekindRing B := { }
  haveI : IsDedekindDomain B := { }
  have hinj : Function.Injective (algebraMap K[X] B) := FaithfulSMul.algebraMap_injective K[X] B

  have hP0 : P ≠ ⊥ := by
    intro h; rw [h] at hP
    exact Polynomial.not_isField K (Ring.isField_iff_maximal_bot.2 hP)
  obtain ⟨c, hc⟩ : ∃ c : K, X - C c ∈ P := by
    obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal P).principal
    have hg0 : g ≠ 0 := by rintro rfl; apply hP0; rw [hg]; simp
    have hgP : g ∈ P := by rw [hg]; exact Ideal.mem_span_singleton_self g
    have hgu : ¬IsUnit g := fun hu => hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hgP hu)
    have hdeg : g.degree ≠ 0 := fun h => hgu (isUnit_iff_degree_eq_zero.2 h)
    obtain ⟨c, hcroot⟩ := IsAlgClosed.exists_root g hdeg
    refine ⟨c, ?_⟩
    have hgmem : g ∈ Ideal.span {X - C c} := by
      rw [Ideal.mem_span_singleton]; exact dvd_iff_isRoot.2 hcroot
    have hle : P ≤ Ideal.span {X - C c} := by
      rw [hg]; exact (Ideal.span_singleton_le_iff_mem _).2 hgmem
    have hne : Ideal.span {X - C c} ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top]; exact not_isUnit_X_sub_C c
    rw [hP.eq_of_le hne hle]
    exact Ideal.mem_span_singleton_self _
  let φ : K →+* B := (algebraMap K[X] B).comp C
  have hφ : ∀ a, φ a = algebraMap K[X] B (C a) := fun a => rfl

  have hred : ∀ (Q : Ideal B), Ideal.map (algebraMap K[X] B) P ≤ Q → ∀ g : K[X],
      algebraMap K[X] B g - φ (g.eval c) ∈ Q := by
    intro Q hQ g
    apply hQ
    rw [hφ, ← map_sub]
    apply Ideal.mem_map_of_mem
    have : g - C (g.eval c) ∈ Ideal.span {X - C c} := by
      rw [Ideal.mem_span_singleton, dvd_iff_isRoot]; simp
    obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.1 this
    rw [← hh]; exact P.mul_mem_left h hc

  have hres : ∀ (Q : Ideal B), Q.IsMaximal → Ideal.map (algebraMap K[X] B) P ≤ Q →
      ∀ b : B, ∃ a : K, b - φ a ∈ Q := by
    intro Q hQ hPQ b
    letI : Field (B ⧸ Q) := Ideal.Quotient.field Q
    let f : K →+* B ⧸ Q := (Ideal.Quotient.mk Q).comp φ
    have hf : f.IsIntegral := by
      intro x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨p, hpm, hp⟩ : IsIntegral K[X] b := Algebra.IsIntegral.isIntegral b
      refine ⟨p.map (evalRingHom c), hpm.map _, ?_⟩
      have hcomp : (Ideal.Quotient.mk Q).comp (algebraMap K[X] B) = f.comp (evalRingHom c) := by
        ext g
        · change Ideal.Quotient.mk Q (algebraMap K[X] B (C g)) = f ((C g).eval c)
          rw [eval_C]
          rfl
        · change Ideal.Quotient.mk Q (algebraMap K[X] B X) = Ideal.Quotient.mk Q (φ (X.eval c))
          rw [eval_X, Ideal.Quotient.eq]
          have := hred Q hPQ X
          rwa [eval_X] at this
      rw [eval₂_map, ← hcomp, ← hom_eval₂, hp, map_zero]
    obtain ⟨a, ha⟩ := (IsAlgClosed.ringHom_bijective_of_isIntegral f hf).2 (Ideal.Quotient.mk Q b)
    exact ⟨a, Ideal.Quotient.eq.1 ha.symm⟩

  set I : Ideal B := Ideal.map (algebraMap K[X] B) P with hIdef
  have hI0 : I ≠ ⊥ := by
    rw [hIdef, Ne, Ideal.map_eq_bot_iff_of_injective hinj]; exact hP0
  let S : Finset (Ideal B) := (factors I).toFinset
  let e : Ideal B → ℕ := fun Q => (factors I).count Q
  have hSprime : ∀ Q ∈ S, Prime Q := fun Q hQ => prime_of_factor Q (Multiset.mem_toFinset.1 hQ)
  have hSprime' : ∀ Q ∈ S, Q.IsPrime := fun Q hQ => Ideal.isPrime_of_prime (hSprime Q hQ)
  have hS0 : ∀ Q ∈ S, Q ≠ ⊥ := fun Q hQ => (hSprime Q hQ).ne_zero
  have hSmax : ∀ Q ∈ S, Q.IsMaximal := fun Q hQ => (hSprime' Q hQ).isMaximal (hS0 Q hQ)
  have hprod : ∏ Q ∈ S, Q ^ e Q = I := by
    calc ∏ Q ∈ S, Q ^ e Q = ((factors I).map fun Q => Q).prod :=
          (Finset.prod_multiset_map_count (factors I) id).symm
      _ = (factors I).prod := by rw [Multiset.map_id']
      _ = I := associated_iff_eq.mp (factors_prod hI0)
  have hinf : (S.inf fun Q => Q ^ e Q) = I := by
    rw [← hprod]
    exact IsDedekindDomain.inf_pow_eq_prod_of_prime S (fun Q => Q) e hSprime
      (fun i _ j _ hij => hij)
  have hIle : ∀ Q ∈ S, I ≤ Q := by
    intro Q hQ
    have h1 : I ≤ Q ^ e Q := by rw [← hinf]; exact Finset.inf_le hQ
    exact h1.trans (Ideal.pow_le_self (Multiset.count_ne_zero.2 (Multiset.mem_toFinset.1 hQ)))
  have hepos : ∀ Q ∈ S, 0 < e Q := fun Q hQ =>
    Multiset.count_pos.2 (Multiset.mem_toFinset.1 hQ)

  have hunif : ∀ Q ∈ S, ∃ t : B, t ∈ Q ∧ t ∉ Q ^ 2 := by
    intro Q hQ
    obtain ⟨t, ht1, ht2⟩ := Ideal.exists_mem_pow_notMem_pow_succ Q (hS0 Q hQ)
      (hSmax Q hQ).ne_top 1
    exact ⟨t, by rwa [pow_one] at ht1, ht2⟩
  choose! t ht ht2 using hunif

  obtain ⟨cS, hcS⟩ : ∃ cS : Ideal B → K, Set.InjOn cS S := by
    let emb : S ↪ K := ((Fintype.equivFin S).toEmbedding.trans Fin.valEmbedding).trans
      (Infinite.natEmbedding K)
    refine ⟨fun Q => if h : Q ∈ S then emb ⟨Q, h⟩ else 0, ?_⟩
    intro Q₁ h₁ Q₂ h₂ h12
    have h₁' : Q₁ ∈ S := Finset.mem_coe.1 h₁
    have h₂' : Q₂ ∈ S := Finset.mem_coe.1 h₂
    simp only [dif_pos h₁', dif_pos h₂'] at h12
    have := emb.injective h12
    exact congrArg Subtype.val this

  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun Q => Q) e hSprime
    (fun i _ j _ hij => hij) (fun Q => φ (cS Q) + t Q)
  refine ⟨y, fun z => ?_⟩

  have hyc : ∀ Q ∈ S, y - φ (cS Q) ∈ Q := by
    intro Q hQ
    have h1 : y - (φ (cS Q) + t Q) ∈ Q := Ideal.pow_le_self (hepos Q hQ).ne' (hy Q hQ)
    have : y - φ (cS Q) = (y - (φ (cS Q) + t Q)) + t Q := by ring
    rw [this]; exact Q.add_mem h1 (ht Q hQ)

  have hloc : ∀ Q ∈ S, ∃ qQ : K[X], z - (qQ.map C).eval₂ (algebraMap K[X] B) y ∈ Q ^ e Q := by
    intro Q hQ
    haveI := hSprime' Q hQ
    obtain ⟨a, ha⟩ := exists_expansion Q (hS0 Q hQ) (t Q) (ht Q hQ) (ht2 Q hQ) φ
      (hres Q (hSmax Q hQ) (hIle Q hQ)) z (e Q)
    refine ⟨∑ i ∈ Finset.range (e Q), C (a i) * (X - C (cS Q)) ^ i, ?_⟩
    have hev : (Polynomial.map C (∑ i ∈ Finset.range (e Q), C (a i) * (X - C (cS Q)) ^ i)).eval₂
        (algebraMap K[X] B) y = ∑ i ∈ Finset.range (e Q), φ (a i) * (y - φ (cS Q)) ^ i := by
      rw [eval₂_map]
      simp only [eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_pow, eval₂_sub, eval₂_X]
      rfl
    rw [hev]

    have hcong : (∑ i ∈ Finset.range (e Q), φ (a i) * t Q ^ i) -
        ∑ i ∈ Finset.range (e Q), φ (a i) * (y - φ (cS Q)) ^ i ∈ Q ^ e Q := by
      rw [← Ideal.Quotient.eq]
      simp only [map_sum, map_mul, map_pow]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 2
      rw [Ideal.Quotient.eq]
      have : t Q - (y - φ (cS Q)) = -(y - (φ (cS Q) + t Q)) := by ring
      rw [this]; exact Submodule.neg_mem _ (hy Q hQ)
    have : z - ∑ i ∈ Finset.range (e Q), φ (a i) * (y - φ (cS Q)) ^ i =
        (z - ∑ i ∈ Finset.range (e Q), φ (a i) * t Q ^ i) +
          ((∑ i ∈ Finset.range (e Q), φ (a i) * t Q ^ i) -
            ∑ i ∈ Finset.range (e Q), φ (a i) * (y - φ (cS Q)) ^ i) := by ring
    rw [this]
    exact Ideal.add_mem _ ha hcong
  choose! qQ hqQ using hloc

  have hTprime : ∀ Q ∈ S, Prime (Ideal.span {X - C (cS Q)} : Ideal K[X]) := fun Q _ =>
    (Ideal.prime_iff_isPrime (by rw [Ne, Ideal.span_singleton_eq_bot]; exact X_sub_C_ne_zero _)).2
      ((Ideal.span_singleton_prime (X_sub_C_ne_zero _)).2 (prime_X_sub_C _))
  have hTcop : ∀ Q₁ ∈ S, ∀ Q₂ ∈ S, Q₁ ≠ Q₂ →
      (Ideal.span {X - C (cS Q₁)} : Ideal K[X]) ≠ Ideal.span {X - C (cS Q₂)} := by
    intro Q₁ h₁ Q₂ h₂ hne heq
    apply hne
    apply hcS h₁ h₂
    have hmem : X - C (cS Q₁) ∈ Ideal.span {X - C (cS Q₂)} := by
      rw [← heq]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_span_singleton, dvd_iff_isRoot] at hmem
    simp only [IsRoot.def, eval_sub, eval_X, eval_C, sub_eq_zero] at hmem
    exact hmem.symm
  obtain ⟨q, hq⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S)
    (fun Q => (Ideal.span {X - C (cS Q)} : Ideal K[X])) e hTprime hTcop (fun Q => qQ Q)
  refine ⟨q.map C, ?_⟩

  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, ← hIdef, ← hinf, Submodule.mem_finsetInf]
  intro Q hQ
  have h1 := hqQ Q hQ
  have h2 : (Polynomial.map C (qQ Q)).eval₂ (algebraMap K[X] B) y -
      aeval y (Polynomial.map C q) ∈ Q ^ e Q := by
    obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.1
      ((Ideal.span_singleton_pow (X - C (cS Q)) (e Q)) ▸ hq Q hQ)

    have hdiff : Polynomial.map C (qQ Q) - Polynomial.map C q =
        -(Polynomial.map C h * (Polynomial.map C (X - C (cS Q))) ^ e Q) := by
      rw [← Polynomial.map_pow, ← Polynomial.map_mul, hh, Polynomial.map_sub]; ring
    rw [aeval_def, ← eval₂_sub, hdiff, eval₂_neg, eval₂_mul, eval₂_pow]
    refine Submodule.neg_mem _ (Ideal.mul_mem_left _ _ ?_)
    have : (Polynomial.map C (X - C (cS Q))).eval₂ (algebraMap K[X] B) y = y - φ (cS Q) := by
      rw [Polynomial.map_sub, map_X, map_C, eval₂_sub, eval₂_X, eval₂_C]
      rfl
    rw [this]
    exact Ideal.pow_mem_pow (hyc Q hQ) _
  have : z - aeval y (Polynomial.map C q) =
      (z - (Polynomial.map C (qQ Q)).eval₂ (algebraMap K[X] B) y) +
        ((Polynomial.map C (qQ Q)).eval₂ (algebraMap K[X] B) y - aeval y (Polynomial.map C q)) := by
    ring
  rw [this]
  exact Ideal.add_mem _ h1 h2

end Main

end FibreMonogenicSol

end

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] (B : Type v) [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] [Algebra K[X] B] [Module.Finite K[X] B] [FaithfulSMul K[X] B]
    (P : Ideal K[X]) (hP : P.IsMaximal) :
    ∃ y : B, ∀ z : B, ∃ q : Polynomial K[X], z - aeval y q ∈ P • (⊤ : Submodule K[X] B) :=
  FibreMonogenicSol.main P hP

end S_AlgebraicCurve_exists_aeval_sub_mem_smul_of_isMaximal_of_isIntegrallyClosed
end P2MW
export P2MW.S_AlgebraicCurve_exists_aeval_sub_mem_smul_of_isMaximal_of_isIntegrallyClosed (solution)
