-- Prove2me | solution 1 for AlgebraicCurve.Place.exists_gram_denominator_of_mulTable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/48ac2139-7fdd-5f71-8e5e-b44597bc46e7

import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_exists_gram_denominator_of_mulTable

set_option autoImplicit false

noncomputable section

open Polynomial

namespace mwGSolM

section chilane

variable {K₀ k F : Type*} [Field K₀] [Field k] [Field F] [Algebra K₀ k] [Algebra k F]

private theorem mwALGM_exists_mulMatrix_chi {j : F} (hj : Transcendental k j)
    (n : ℕ) (b : Fin n → F)
    (hbsp : ∀ x : F, ∃ (q : Polynomial k) (c : Fin n → Polynomial k), q ≠ 0 ∧
      x * Polynomial.aeval j q = ∑ i : Fin n, Polynomial.aeval j (c i) * b i)
    (d : Polynomial K₀) (hd : d ≠ 0) (A : Fin n → Matrix (Fin n) (Fin n) (Polynomial K₀))
    (hmul : ∀ i i' : Fin n, b i * b i' * Polynomial.aeval j (d.map (algebraMap K₀ k))
      = ∑ i'' : Fin n, Polynomial.aeval j ((A i i'' i').map (algebraMap K₀ k)) * b i'')
    (c₀ : Polynomial K₀) (cc : Fin n → Polynomial K₀) :
    ∃ (M : Matrix (Fin n) (Fin n) (Polynomial K₀)) (χ : Polynomial (Polynomial K₀)),
      χ.Monic ∧
      (∀ (m : ℕ) (i : Fin n),
        (Polynomial.aeval j (c₀.map (algebraMap K₀ k))
            + ∑ i' : Fin n, Polynomial.aeval j ((cc i' * d).map (algebraMap K₀ k)) * b i') ^ m
          * (Polynomial.aeval j (d.map (algebraMap K₀ k)) * b i)
        = ∑ i' : Fin n, Polynomial.aeval j (((M ^ m) i' i).map (algebraMap K₀ k))
            * (Polynomial.aeval j (d.map (algebraMap K₀ k)) * b i')) ∧
      Polynomial.eval₂
        ((Polynomial.aeval j).toRingHom.comp (Polynomial.mapRingHom (algebraMap K₀ k)))
        (Polynomial.aeval j (c₀.map (algebraMap K₀ k))
          + ∑ i' : Fin n, Polynomial.aeval j ((cc i' * d).map (algebraMap K₀ k)) * b i') χ
      = 0 := by
  classical
  set φ : K₀ →+* k := algebraMap K₀ k with hφ
  set dj : F := Polynomial.aeval j (d.map φ) with hdjdef
  set L : F := Polynomial.aeval j (c₀.map φ)
    + ∑ i' : Fin n, Polynomial.aeval j ((cc i' * d).map φ) * b i' with hLdef
  set M : Matrix (Fin n) (Fin n) (Polynomial K₀) :=
    Matrix.of fun i'' i' => (if i'' = i' then c₀ else 0) + ∑ t, cc t * A t i'' i' with hMdef

  have hbase : ∀ i' : Fin n,
      L * (dj * b i') = ∑ i'' : Fin n,
        Polynomial.aeval j ((M i'' i').map φ) * (dj * b i'') := by
    intro i'
    have hexp : L * (dj * b i')
        = Polynomial.aeval j (c₀.map φ) * (dj * b i')
          + ∑ t, Polynomial.aeval j ((cc t).map φ) * dj * (b t * b i' * dj) := by
      rw [hLdef, add_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Polynomial.map_mul, map_mul]
      rw [← hdjdef]
      ring
    rw [hexp]
    have hmid : (∑ t, Polynomial.aeval j ((cc t).map φ) * dj * (b t * b i' * dj))
        = ∑ i'' : Fin n, (∑ t, Polynomial.aeval j ((cc t).map φ)
            * Polynomial.aeval j ((A t i'' i').map φ)) * (dj * b i'') := by
      calc ∑ t, Polynomial.aeval j ((cc t).map φ) * dj * (b t * b i' * dj)
          = ∑ t, ∑ i'', Polynomial.aeval j ((cc t).map φ)
              * Polynomial.aeval j ((A t i'' i').map φ) * (dj * b i'') := by
            refine Finset.sum_congr rfl fun t _ => ?_
            rw [hmul t i', Finset.mul_sum]
            refine Finset.sum_congr rfl fun i'' _ => ?_
            ring
        _ = ∑ i'', ∑ t, Polynomial.aeval j ((cc t).map φ)
              * Polynomial.aeval j ((A t i'' i').map φ) * (dj * b i'') := Finset.sum_comm
        _ = ∑ i'', (∑ t, Polynomial.aeval j ((cc t).map φ)
              * Polynomial.aeval j ((A t i'' i').map φ)) * (dj * b i'') := by
            refine Finset.sum_congr rfl fun i'' _ => ?_
            rw [Finset.sum_mul]
    have hdelta : Polynomial.aeval j (c₀.map φ) * (dj * b i')
        = ∑ i'' : Fin n, (if i'' = i' then Polynomial.aeval j (c₀.map φ) else 0)
            * (dj * b i'') := by
      symm
      calc ∑ i'' : Fin n, (if i'' = i' then Polynomial.aeval j (c₀.map φ) else 0) * (dj * b i'')
          = ∑ i'' : Fin n, (if i'' = i' then Polynomial.aeval j (c₀.map φ) * (dj * b i'') else 0) := by
            refine Finset.sum_congr rfl fun i'' _ => ?_
            rw [ite_mul, zero_mul]
        _ = Polynomial.aeval j (c₀.map φ) * (dj * b i') := by
            rw [Finset.sum_ite_eq' Finset.univ i']
            simp
    rw [hmid, hdelta, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i'' _ => ?_
    rw [hMdef, Matrix.of_apply, Polynomial.map_add, map_add, add_mul]
    congr 1
    · congr 1
      split_ifs with h
      · rfl
      · rw [Polynomial.map_zero, map_zero]
    · congr 1
      rw [Polynomial.map_sum, map_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Polynomial.map_mul, map_mul]

  have hpow : ∀ (m : ℕ) (i : Fin n), L ^ m * (dj * b i)
      = ∑ i' : Fin n, Polynomial.aeval j (((M ^ m) i' i).map φ) * (dj * b i') := by
    intro m
    induction m with
    | zero =>
      intro i
      rw [pow_zero, one_mul, pow_zero]
      symm
      calc ∑ i' : Fin n,
            Polynomial.aeval j (((1 : Matrix (Fin n) (Fin n) (Polynomial K₀)) i' i).map φ)
              * (dj * b i')
          = ∑ i' : Fin n, (if i' = i then dj * b i' else 0) := by
            refine Finset.sum_congr rfl fun i' _ => ?_
            rw [Matrix.one_apply]
            split_ifs with h
            · rw [Polynomial.map_one, map_one, one_mul]
            · rw [Polynomial.map_zero, map_zero, zero_mul]
        _ = dj * b i := by
            rw [Finset.sum_ite_eq' Finset.univ i]
            simp
    | succ m ih =>
      intro i
      rw [pow_succ', mul_assoc, ih i, Finset.mul_sum]
      calc ∑ i' : Fin n, L * (Polynomial.aeval j (((M ^ m) i' i).map φ) * (dj * b i'))
          = ∑ i' : Fin n, Polynomial.aeval j (((M ^ m) i' i).map φ) * (L * (dj * b i')) := by
            refine Finset.sum_congr rfl fun i' _ => ?_
            ring
        _ = ∑ i' : Fin n, Polynomial.aeval j (((M ^ m) i' i).map φ)
              * (∑ i'' : Fin n, Polynomial.aeval j ((M i'' i').map φ) * (dj * b i'')) := by
            refine Finset.sum_congr rfl fun i' _ => ?_
            rw [hbase i']
        _ = ∑ i' : Fin n, ∑ i'' : Fin n, Polynomial.aeval j ((M i'' i').map φ)
              * Polynomial.aeval j (((M ^ m) i' i).map φ) * (dj * b i'') := by
            refine Finset.sum_congr rfl fun i' _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i'' _ => ?_
            ring
        _ = ∑ i'' : Fin n, ∑ i' : Fin n, Polynomial.aeval j ((M i'' i').map φ)
              * Polynomial.aeval j (((M ^ m) i' i).map φ) * (dj * b i'') := Finset.sum_comm
        _ = ∑ i'' : Fin n, Polynomial.aeval j (((M ^ (m + 1)) i'' i).map φ) * (dj * b i'') := by
            refine Finset.sum_congr rfl fun i'' _ => ?_
            rw [← Finset.sum_mul]
            congr 1
            rw [pow_succ' M m, Matrix.mul_apply, Polynomial.map_sum, map_sum]
            refine Finset.sum_congr rfl fun i' _ => ?_
            rw [Polynomial.map_mul, map_mul]

  have htrans : ∀ (χp : Polynomial (Polynomial K₀)) (i : Fin n),
      Polynomial.eval₂ ((Polynomial.aeval j).toRingHom.comp (Polynomial.mapRingHom φ)) L χp
          * (dj * b i)
        = ∑ i' : Fin n,
            Polynomial.aeval j (((Polynomial.aeval M χp) i' i).map φ) * (dj * b i') := by
    intro χp
    induction χp using Polynomial.induction_on' with
    | add p q hp hq =>
      intro i
      rw [Polynomial.eval₂_add, map_add, add_mul, hp i, hq i, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [Matrix.add_apply, Polynomial.map_add, map_add, add_mul]
    | monomial m q =>
      intro i
      rw [Polynomial.eval₂_monomial, Polynomial.aeval_monomial, mul_assoc, hpow m i,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i' _ => ?_
      have halg : (algebraMap (Polynomial K₀) (Matrix (Fin n) (Fin n) (Polynomial K₀)) q
          * M ^ m) i' i = q * (M ^ m) i' i := by
        rw [← Algebra.smul_def, Matrix.smul_apply, smul_eq_mul]
      rw [halg, Polynomial.map_mul, map_mul]
      have h1 : ((Polynomial.aeval j).toRingHom.comp (Polynomial.mapRingHom φ)) q
          = Polynomial.aeval j (q.map φ) := rfl
      rw [h1]
      ring

  have hbex : ∃ i, b i ≠ 0 := by
    obtain ⟨q, c, hq, hqe⟩ := hbsp 1
    by_contra hall
    have hall' : ∀ i, b i = 0 := fun i => by
      by_contra hbi
      exact hall ⟨i, hbi⟩
    rw [Finset.sum_eq_zero fun i _ => by rw [hall' i, mul_zero], one_mul] at hqe
    exact hj ⟨q, hq, hqe⟩
  have hdj : dj ≠ 0 := by
    rw [hdjdef]
    intro h0
    exact hj ⟨d.map φ, (Polynomial.map_ne_zero_iff (algebraMap K₀ k).injective).mpr hd, h0⟩

  refine ⟨M, M.charpoly, Matrix.charpoly_monic M, hpow, ?_⟩
  obtain ⟨i₀, hb0⟩ := hbex
  have h0 := htrans M.charpoly i₀
  rw [Matrix.aeval_self_charpoly] at h0
  simp only [Matrix.zero_apply, Polynomial.map_zero, map_zero, zero_mul,
    Finset.sum_const_zero] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · exact h
  · exact absurd h (mul_ne_zero hdj hb0)

private theorem mwALGM_isIntegral_form {j : F} (hj : Transcendental k j)
    (n : ℕ) (b : Fin n → F)
    (hbsp : ∀ x : F, ∃ (q : Polynomial k) (c : Fin n → Polynomial k), q ≠ 0 ∧
      x * Polynomial.aeval j q = ∑ i : Fin n, Polynomial.aeval j (c i) * b i)
    (d : Polynomial K₀) (hd : d ≠ 0) (A : Fin n → Matrix (Fin n) (Fin n) (Polynomial K₀))
    (hmul : ∀ i i' : Fin n, b i * b i' * Polynomial.aeval j (d.map (algebraMap K₀ k))
      = ∑ i'' : Fin n, Polynomial.aeval j ((A i i'' i').map (algebraMap K₀ k)) * b i'')
    (c₀ : Polynomial K₀) (cc : Fin n → Polynomial K₀) :
    IsIntegral (Algebra.adjoin k ({j} : Set F))
      (Polynomial.aeval j (c₀.map (algebraMap K₀ k))
        + ∑ i' : Fin n, Polynomial.aeval j ((cc i' * d).map (algebraMap K₀ k)) * b i') := by
  classical
  obtain ⟨M, χ, hmonic, hpow, hkill⟩ :=
    mwALGM_exists_mulMatrix_chi hj n b hbsp d hd A hmul c₀ cc
  have hmem : ∀ q : Polynomial K₀,
      ((Polynomial.aeval j).toRingHom.comp
        (Polynomial.mapRingHom (algebraMap K₀ k))) q ∈ Algebra.adjoin k ({j} : Set F) := by
    intro q
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨q.map (algebraMap K₀ k), rfl⟩
  set ψ : Polynomial K₀ →+* (Algebra.adjoin k ({j} : Set F)) :=
    ((Polynomial.aeval j).toRingHom.comp
      (Polynomial.mapRingHom (algebraMap K₀ k))).codRestrict
      (Algebra.adjoin k ({j} : Set F)) hmem with hψ
  refine ⟨χ.map ψ, hmonic.map ψ, ?_⟩
  rw [Polynomial.eval₂_map]
  have hcomp : (algebraMap (Algebra.adjoin k ({j} : Set F)) F).comp ψ
      = (Polynomial.aeval j).toRingHom.comp (Polynomial.mapRingHom (algebraMap K₀ k)) :=
    RingHom.ext fun q => rfl
  rw [hcomp]
  exact hkill

private theorem mwALGM_isIntegral_j {j : F} :
    IsIntegral (Algebra.adjoin k ({j} : Set F)) j := by
  have hmem : j ∈ Algebra.adjoin k ({j} : Set F) := Algebra.self_mem_adjoin_singleton k j
  exact isIntegral_algebraMap (x := (⟨j, hmem⟩ : Algebra.adjoin k ({j} : Set F)))

private theorem mwALGM_isIntegral_db {j : F} (hj : Transcendental k j)
    (n : ℕ) (b : Fin n → F)
    (hbsp : ∀ x : F, ∃ (q : Polynomial k) (c : Fin n → Polynomial k), q ≠ 0 ∧
      x * Polynomial.aeval j q = ∑ i : Fin n, Polynomial.aeval j (c i) * b i)
    (d : Polynomial K₀) (hd : d ≠ 0) (A : Fin n → Matrix (Fin n) (Fin n) (Polynomial K₀))
    (hmul : ∀ i i' : Fin n, b i * b i' * Polynomial.aeval j (d.map (algebraMap K₀ k))
      = ∑ i'' : Fin n, Polynomial.aeval j ((A i i'' i').map (algebraMap K₀ k)) * b i'') :
    ∀ i : Fin n, IsIntegral (Algebra.adjoin k ({j} : Set F))
      (Polynomial.aeval j (d.map (algebraMap K₀ k)) * b i) := by
  classical
  intro i
  have h := mwALGM_isIntegral_form hj n b hbsp d hd A hmul 0 (Pi.single i 1)
  have heq : Polynomial.aeval j ((0 : Polynomial K₀).map (algebraMap K₀ k))
      + ∑ i' : Fin n, Polynomial.aeval j
          (((Pi.single i 1 : Fin n → Polynomial K₀) i' * d).map (algebraMap K₀ k)) * b i'
      = Polynomial.aeval j (d.map (algebraMap K₀ k)) * b i := by
    rw [Polynomial.map_zero, map_zero, zero_add]
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, one_mul]
    · intro i' _ hne
      rw [Pi.single_eq_of_ne hne, zero_mul, Polynomial.map_zero, map_zero, zero_mul]
    · intro habs
      exact absurd (Finset.mem_univ i) habs
  rw [← heq]
  exact h

end chilane

section gstar

open IsDedekindDomain

open scoped IntermediateField.algebraAdjoinAdjoin

variable {K₀ k F : Type*} [Field K₀] [Field k] [Field F] [Algebra K₀ k] [Algebra k F]

private theorem mwALGM_isPrincipalIdealRing_adjoin (j : F) :
    IsPrincipalIdealRing (Algebra.adjoin k ({j} : Set F)) := by
  let e : (Polynomial.aeval j : Polynomial k →ₐ[k] F).range ≃ₐ[k] Algebra.adjoin k ({j} : Set F) :=
    Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval k j).symm
  let f : Polynomial k →ₐ[k] Algebra.adjoin k ({j} : Set F) :=
    e.toAlgHom.comp (Polynomial.aeval j).rangeRestrict
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨p, hp⟩ : ∃ p : Polynomial k, (Polynomial.aeval j).rangeRestrict p = e.symm y := by
      obtain ⟨p, hp⟩ := (e.symm y).2
      exact ⟨p, Subtype.ext hp⟩
    refine ⟨p, ?_⟩
    show e ((Polynomial.aeval j).rangeRestrict p) = y
    rw [hp]
    exact e.apply_symm_apply y
  exact IsPrincipalIdealRing.of_surjective f.toRingHom hf

private theorem mwALGM_exists_aeval_eq_trace_of_isIntegral {j : F}
    [FiniteDimensional (IntermediateField.adjoin k ({j} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin k ({j} : Set F)) F]
    {x : F} (hint : IsIntegral (Algebra.adjoin k ({j} : Set F)) x) :
    ∃ p : Polynomial k, Polynomial.aeval j p =
      ((Algebra.trace (IntermediateField.adjoin k ({j} : Set F)) F x :
        IntermediateField.adjoin k ({j} : Set F)) : F) := by
  haveI : IsPrincipalIdealRing (Algebra.adjoin k ({j} : Set F)) :=
    mwALGM_isPrincipalIdealRing_adjoin j
  have htr := Algebra.isIntegral_trace (L := IntermediateField.adjoin k ({j} : Set F)) hint
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral htr
  have hmem : ((Algebra.trace (IntermediateField.adjoin k ({j} : Set F)) F x :
      IntermediateField.adjoin k ({j} : Set F)) : F) ∈ Algebra.adjoin k ({j} : Set F) := by
    rw [← hy, IntermediateField.algebraAdjoinAdjoin.coe_algebraMap]
    exact y.2
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  exact hmem

private theorem mwALGM_exists_basis {j : F} (hj : Transcendental k j) (n : ℕ) (b : Fin n → F)
    (hbli : ∀ c : Fin n → Polynomial k,
      (∑ i : Fin n, Polynomial.aeval j (c i) * b i) = 0 → ∀ i, c i = 0)
    (hbsp : ∀ x : F, ∃ (q : Polynomial k) (c : Fin n → Polynomial k), q ≠ 0 ∧
      x * Polynomial.aeval j q = ∑ i : Fin n, Polynomial.aeval j (c i) * b i) :
    ∃ bE : Module.Basis (Fin n) (IntermediateField.adjoin k ({j} : Set F)) F, ⇑bE = b := by
  classical
  have haev : ∀ p : Polynomial k,
      Polynomial.aeval j p ∈ IntermediateField.adjoin k ({j} : Set F) := by
    intro p
    have h1 : Polynomial.aeval j p ∈ Algebra.adjoin k ({j} : Set F) := by
      rw [Algebra.adjoin_singleton_eq_range_aeval]
      exact ⟨p, rfl⟩
    exact IntermediateField.algebra_adjoin_le_adjoin k _ h1
  have hane : ∀ {p : Polynomial k}, p ≠ 0 → Polynomial.aeval j p ≠ 0 :=
    fun {p} hp h => hj ⟨p, hp, h⟩
  have hli : LinearIndependent (IntermediateField.adjoin k ({j} : Set F)) b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hrep : ∀ i, ∃ (r s : Polynomial k), s ≠ 0 ∧
        (g i : F) * Polynomial.aeval j s = Polynomial.aeval j r := by
      intro i
      obtain ⟨r, s, hrs⟩ :=
        (IntermediateField.mem_adjoin_simple_iff k (α := j) ((g i : F))).mp (g i).2
      by_cases hs : Polynomial.aeval j s = 0
      · exact ⟨0, 1, one_ne_zero, by rw [hrs, hs, div_zero, zero_mul, map_zero]⟩
      · exact ⟨r, s, fun h => hs (by rw [h, map_zero]), by rw [hrs, div_mul_cancel₀ _ hs]⟩
    choose r s hs0 hcl using hrep
    simp only [IntermediateField.smul_def, smul_eq_mul] at hg
    have hsum : (∑ i : Fin n,
        Polynomial.aeval j (r i * ∏ l ∈ Finset.univ.erase i, s l) * b i) = 0 := by
      calc ∑ i : Fin n, Polynomial.aeval j (r i * ∏ l ∈ Finset.univ.erase i, s l) * b i
          = ∑ i : Fin n, ((g i : F) * b i) * ∏ l : Fin n, Polynomial.aeval j (s l) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [map_mul, map_prod, ← hcl i,
              ← Finset.mul_prod_erase Finset.univ (fun l => Polynomial.aeval j (s l))
                (Finset.mem_univ i)]
            ring
        _ = (∑ i : Fin n, (g i : F) * b i) * ∏ l : Fin n, Polynomial.aeval j (s l) := by
            rw [Finset.sum_mul]
        _ = 0 := by rw [hg, zero_mul]
    intro i
    have hri := hbli _ hsum i
    have hprodne : (∏ l ∈ Finset.univ.erase i, s l) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun l _ => hs0 l
    have hr0 : r i = 0 := by
      rcases mul_eq_zero.mp hri with h | h
      · exact h
      · exact absurd h hprodne
    have hcli := hcl i
    rw [hr0, map_zero] at hcli
    rcases mul_eq_zero.mp hcli with h | h
    · exact Subtype.ext (by simpa using h)
    · exact absurd h (hane (hs0 i))
  have hsp : ⊤ ≤ Submodule.span (IntermediateField.adjoin k ({j} : Set F)) (Set.range b) := by
    intro x _
    obtain ⟨q, c, hq, heq⟩ := hbsp x
    have hQ : Polynomial.aeval j q ≠ 0 := hane hq
    have hx : x = ∑ i : Fin n,
        ((⟨Polynomial.aeval j (c i) * (Polynomial.aeval j q)⁻¹,
          mul_mem (haev (c i)) (inv_mem (haev q))⟩ :
            IntermediateField.adjoin k ({j} : Set F)) • b i) := by
      simp only [IntermediateField.smul_def, smul_eq_mul]
      calc x = (x * Polynomial.aeval j q) * (Polynomial.aeval j q)⁻¹ := by
              rw [mul_assoc, mul_inv_cancel₀ hQ, mul_one]
        _ = (∑ i : Fin n, Polynomial.aeval j (c i) * b i) * (Polynomial.aeval j q)⁻¹ := by
              rw [heq]
        _ = ∑ i : Fin n, Polynomial.aeval j (c i) * (Polynomial.aeval j q)⁻¹ * b i := by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun i _ => by ring
    rw [hx]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp, funext fun i => by rw [Module.Basis.coe_mk]⟩

private theorem mwALGM_gram_denom {j : F} (hj : Transcendental k j)
    [FiniteDimensional (IntermediateField.adjoin k ({j} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin k ({j} : Set F)) F]
    (n : ℕ) (b : Fin n → F)
    (hbli : ∀ c : Fin n → Polynomial k,
      (∑ i : Fin n, Polynomial.aeval j (c i) * b i) = 0 → ∀ i, c i = 0)
    (hbsp : ∀ x : F, ∃ (q : Polynomial k) (c : Fin n → Polynomial k), q ≠ 0 ∧
      x * Polynomial.aeval j q = ∑ i : Fin n, Polynomial.aeval j (c i) * b i)
    (d : Polynomial K₀) (hd : d ≠ 0) (A : Fin n → Matrix (Fin n) (Fin n) (Polynomial K₀))
    (hmul : ∀ i i' : Fin n, b i * b i' * Polynomial.aeval j (d.map (algebraMap K₀ k))
      = ∑ i'' : Fin n, Polynomial.aeval j ((A i i'' i').map (algebraMap K₀ k)) * b i'') :
    ∃ Δ : Polynomial K₀, Δ ≠ 0 ∧ ∀ x : F, IsIntegral (Algebra.adjoin k ({j} : Set F)) x →
      ∃ c : Fin n → Polynomial k,
        Polynomial.aeval j (Δ.map (algebraMap K₀ k)) * x
          = ∑ i : Fin n, Polynomial.aeval j (c i)
              * (Polynomial.aeval j (d.map (algebraMap K₀ k)) * b i) := by
  classical
  set φ : K₀ →+* k := algebraMap K₀ k with hφ
  obtain ⟨bE, hbE⟩ := mwALGM_exists_basis hj n b hbli hbsp
  set dj : F := Polynomial.aeval j (d.map φ) with hdjdef
  have hdj0 : dj ≠ 0 := by
    rw [hdjdef]
    intro h0
    exact hj ⟨d.map φ, (Polynomial.map_ne_zero_iff φ.injective).mpr hd, h0⟩
  have hjmem : j ∈ IntermediateField.adjoin k ({j} : Set F) :=
    IntermediateField.subset_adjoin k _ (Set.mem_singleton j)
  set jK : IntermediateField.adjoin k ({j} : Set F) := ⟨j, hjmem⟩ with hjKdef
  set ΨK : Polynomial K₀ →+* IntermediateField.adjoin k ({j} : Set F) :=
    ((Polynomial.aeval jK).toRingHom).comp (Polynomial.mapRingHom φ) with hΨKdef
  have hΨKcoe : ∀ q : Polynomial K₀,
      ((ΨK q : IntermediateField.adjoin k ({j} : Set F)) : F) = Polynomial.aeval j (q.map φ) := by
    intro q
    show ((Polynomial.aeval jK (q.map φ) : IntermediateField.adjoin k ({j} : Set F)) : F)
      = Polynomial.aeval j (q.map φ)
    have h := Polynomial.aeval_algebraMap_apply F jK (q.map φ)
    exact h.symm

  have hdbmul : ∀ r s : Fin n, (dj * b r) * (dj * b s)
      = ∑ t : Fin n, Polynomial.aeval j ((A r t s).map φ) * (dj * b t) := by
    intro r s
    calc (dj * b r) * (dj * b s) = (b r * b s * dj) * dj := by ring
      _ = (∑ t : Fin n, Polynomial.aeval j ((A r t s).map φ) * b t) * dj := by rw [hmul r s]
      _ = ∑ t : Fin n, Polynomial.aeval j ((A r t s).map φ) * (dj * b t) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun t _ => by ring

  have hdjK : dj ∈ IntermediateField.adjoin k ({j} : Set F) := by
    have h1 : Polynomial.aeval j (d.map φ) ∈ Algebra.adjoin k ({j} : Set F) := by
      rw [Algebra.adjoin_singleton_eq_range_aeval]
      exact ⟨d.map φ, rfl⟩
    rw [hdjdef]
    exact IntermediateField.algebra_adjoin_le_adjoin k _ h1
  have hdjK0 : (⟨dj, hdjK⟩ : IntermediateField.adjoin k ({j} : Set F)) ≠ 0 := by
    intro h0
    exact hdj0 (by simpa using congrArg Subtype.val h0)
  set bDB := bE.unitsSMul (fun _ => Units.mk0 _ hdjK0) with hbDBdef
  have hbDBa : ∀ i, bDB i = dj * b i := by
    intro i
    rw [hbDBdef, Module.Basis.unitsSMul_apply, Units.smul_def]
    show (⟨dj, hdjK⟩ : IntermediateField.adjoin k ({j} : Set F)) • bE i = dj * b i
    rw [IntermediateField.smul_def, smul_eq_mul]
    show dj * bE i = dj * b i
    rw [hbE]

  have hrepr : ∀ (c : Fin n → IntermediateField.adjoin k ({j} : Set F)) (w : Fin n),
      bDB.repr (∑ v : Fin n, c v • bDB v) w = c w := by
    intro c w
    have h1 : bDB.repr (∑ v : Fin n, c v • bDB v)
        = ∑ v : Fin n, c v • Finsupp.single v 1 := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [map_smul, Module.Basis.repr_self]
    rw [h1, Finsupp.finsetSum_apply]
    simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ w c]
    simp

  have htrace : ∀ z : F, Algebra.trace (IntermediateField.adjoin k ({j} : Set F)) F z
      = ∑ w : Fin n, bDB.repr (z * bDB w) w := by
    intro z
    rw [Algebra.trace_eq_matrix_trace bDB, Matrix.trace]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]

  set TT : Matrix (Fin n) (Fin n) (Polynomial K₀) :=
    Matrix.of fun r s => ∑ t : Fin n, A r t s * (∑ w : Fin n, A t w w) with hTTdef
  have hcoefmem : ∀ q : Polynomial K₀, Polynomial.aeval j (q.map φ)
      ∈ IntermediateField.adjoin k ({j} : Set F) := by
    intro q
    have h1 : Polynomial.aeval j (q.map φ) ∈ Algebra.adjoin k ({j} : Set F) := by
      rw [Algebra.adjoin_singleton_eq_range_aeval]
      exact ⟨q.map φ, rfl⟩
    exact IntermediateField.algebra_adjoin_le_adjoin k _ h1
  have hexp : ∀ r s w : Fin n, (bDB r * bDB s) * bDB w
      = ∑ v : Fin n, (⟨Polynomial.aeval j ((∑ t : Fin n, A r t s * A t v w).map φ),
          hcoefmem _⟩ : IntermediateField.adjoin k ({j} : Set F)) • bDB v := by
    intro r s w
    simp only [IntermediateField.smul_def, smul_eq_mul]
    calc (bDB r * bDB s) * bDB w
        = (∑ t : Fin n, Polynomial.aeval j ((A r t s).map φ) * (dj * b t)) * (dj * b w) := by
          rw [hbDBa r, hbDBa s, hbDBa w, hdbmul r s]
      _ = ∑ t : Fin n, Polynomial.aeval j ((A r t s).map φ) * ((dj * b t) * (dj * b w)) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun t _ => by ring
      _ = ∑ t : Fin n, Polynomial.aeval j ((A r t s).map φ)
            * (∑ v : Fin n, Polynomial.aeval j ((A t v w).map φ) * (dj * b v)) :=
          Finset.sum_congr rfl fun t _ => by rw [hdbmul t w]
      _ = ∑ t : Fin n, ∑ v : Fin n, Polynomial.aeval j ((A r t s).map φ)
            * Polynomial.aeval j ((A t v w).map φ) * (dj * b v) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun v _ => by ring
      _ = ∑ v : Fin n, ∑ t : Fin n, Polynomial.aeval j ((A r t s).map φ)
            * Polynomial.aeval j ((A t v w).map φ) * (dj * b v) := Finset.sum_comm
      _ = ∑ v : Fin n, Polynomial.aeval j ((∑ t : Fin n, A r t s * A t v w).map φ)
            * (dj * b v) := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [← Finset.sum_mul, Polynomial.map_sum, map_sum]
          congr 1
          exact Finset.sum_congr rfl fun t _ => by rw [Polynomial.map_mul, map_mul]
      _ = ∑ v : Fin n, Polynomial.aeval j ((∑ t : Fin n, A r t s * A t v w).map φ) * bDB v :=
          Finset.sum_congr rfl fun v _ => by rw [hbDBa v]
  have hTmat : ∀ r s : Fin n,
      Algebra.traceForm (IntermediateField.adjoin k ({j} : Set F)) F (bDB r) (bDB s)
        = ΨK (TT r s) := by
    intro r s
    apply Subtype.ext
    show ((Algebra.traceForm (IntermediateField.adjoin k ({j} : Set F)) F (bDB r) (bDB s) :
      IntermediateField.adjoin k ({j} : Set F)) : F) = ((ΨK (TT r s) :
      IntermediateField.adjoin k ({j} : Set F)) : F)
    rw [hΨKcoe, Algebra.traceForm_apply, htrace]
    rw [show (∑ w : Fin n, bDB.repr ((bDB r * bDB s) * bDB w) w) = ∑ w : Fin n,
        (⟨Polynomial.aeval j ((∑ t : Fin n, A r t s * A t w w).map φ), hcoefmem _⟩ :
          IntermediateField.adjoin k ({j} : Set F)) from
      Finset.sum_congr rfl fun w _ => by rw [hexp r s w, hrepr]]
    simp only [AddSubmonoidClass.coe_finsetSum]
    rw [hTTdef, Matrix.of_apply]
    calc ∑ w : Fin n, Polynomial.aeval j ((∑ t : Fin n, A r t s * A t w w).map φ)
        = ∑ w : Fin n, ∑ t : Fin n, Polynomial.aeval j ((A r t s).map φ)
            * Polynomial.aeval j ((A t w w).map φ) := by
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [Polynomial.map_sum, map_sum]
          exact Finset.sum_congr rfl fun t _ => by rw [Polynomial.map_mul, map_mul]
      _ = ∑ t : Fin n, ∑ w : Fin n, Polynomial.aeval j ((A r t s).map φ)
            * Polynomial.aeval j ((A t w w).map φ) := Finset.sum_comm
      _ = ∑ t : Fin n, Polynomial.aeval j ((A r t s * (∑ w : Fin n, A t w w)).map φ) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [← Finset.mul_sum, Polynomial.map_mul, map_mul, Polynomial.map_sum, map_sum]
      _ = Polynomial.aeval j ((∑ t : Fin n, A r t s * (∑ w : Fin n, A t w w)).map φ) := by
          rw [Polynomial.map_sum, map_sum]

  have hnd := traceForm_nondegenerate (IntermediateField.adjoin k ({j} : Set F)) F
  have hmatim : LinearMap.BilinForm.toMatrix bDB
      (Algebra.traceForm (IntermediateField.adjoin k ({j} : Set F)) F) = TT.map ΨK := by
    refine Matrix.ext fun r s => ?_
    rw [LinearMap.BilinForm.toMatrix_apply, Matrix.map_apply]
    exact hTmat r s
  have hdetK : (LinearMap.BilinForm.toMatrix bDB
      (Algebra.traceForm (IntermediateField.adjoin k ({j} : Set F)) F)).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero bDB).mp hnd
  have hΔ0 : TT.det ≠ 0 := by
    intro h0
    apply hdetK
    rw [hmatim, show TT.map ΨK = ΨK.mapMatrix TT from (RingHom.mapMatrix_apply ΨK TT).symm,
      ← RingHom.map_det, h0, map_zero]
  refine ⟨TT.det, hΔ0, ?_⟩
  intro x hx
  set T : Matrix (Fin n) (Fin n) (IntermediateField.adjoin k ({j} : Set F)) :=
    TT.map ΨK with hTdef
  set y : Fin n → IntermediateField.adjoin k ({j} : Set F) := fun s => bDB.repr x s with hydef

  have hsys : T.mulVec y = fun r =>
      Algebra.traceForm (IntermediateField.adjoin k ({j} : Set F)) F (bDB r) x := by
    funext r
    simp only [Matrix.mulVec, dotProduct]
    have hx2 : x = ∑ s : Fin n, y s • bDB s := by
      rw [hydef]
      exact (bDB.sum_repr x).symm
    conv_rhs => rw [hx2]
    rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, smul_eq_mul]
    show (TT.map ΨK) r s * y s
      = y s * Algebra.traceForm (IntermediateField.adjoin k ({j} : Set F)) F (bDB r) (bDB s)
    rw [Matrix.map_apply, ← hTmat r s]
    exact mul_comm _ _
  have hdetT : T.det = ΨK TT.det := by
    rw [hTdef, show TT.map ΨK = ΨK.mapMatrix TT from (RingHom.mapMatrix_apply ΨK TT).symm,
      ← RingHom.map_det]
  have hcram : (ΨK TT.det) • y = T.adjugate.mulVec (fun r =>
      Algebra.traceForm (IntermediateField.adjoin k ({j} : Set F)) F (bDB r) x) := by
    rw [← hsys, Matrix.mulVec_mulVec, Matrix.adjugate_mul, hdetT, Matrix.smul_mulVec,
      Matrix.one_mulVec]

  have htmem : ∀ r : Fin n, ∃ p : Polynomial k, Polynomial.aeval j p
      = ((Algebra.traceForm (IntermediateField.adjoin k ({j} : Set F)) F (bDB r) x :
          IntermediateField.adjoin k ({j} : Set F)) : F) := by
    intro r
    have hint : IsIntegral (Algebra.adjoin k ({j} : Set F)) (bDB r * x) := by
      have h1 : IsIntegral (Algebra.adjoin k ({j} : Set F)) (bDB r) := by
        rw [hbDBa r]
        exact mwALGM_isIntegral_db hj n b hbsp d hd A hmul r
      exact h1.mul hx
    have h2 := mwALGM_exists_aeval_eq_trace_of_isIntegral hint
    rw [Algebra.traceForm_apply]
    exact h2
  choose p hp using htmem

  have hadj : ∀ s r : Fin n, ((T.adjugate s r : IntermediateField.adjoin k ({j} : Set F)) : F)
      = Polynomial.aeval j ((TT.adjugate s r).map φ) := by
    intro s r
    rw [hTdef, show TT.map ΨK = ΨK.mapMatrix TT from (RingHom.mapMatrix_apply ΨK TT).symm,
      ← RingHom.map_adjugate, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact hΨKcoe _
  have hkey : ∀ s : Fin n, Polynomial.aeval j (TT.det.map φ) * ((y s :
      IntermediateField.adjoin k ({j} : Set F)) : F)
      = Polynomial.aeval j (∑ r : Fin n, ((TT.adjugate) s r).map φ * p r) := by
    intro s
    have h1 := congrFun hcram s
    have h2 := congrArg
      (fun z : IntermediateField.adjoin k ({j} : Set F) => ((z : _) : F)) h1
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    push_cast at h2
    rw [hΨKcoe] at h2
    rw [h2]
    simp only [Matrix.mulVec, dotProduct, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul]
    rw [map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_mul, hadj s r, hp r]

  refine ⟨fun s => ∑ r : Fin n, ((TT.adjugate) s r).map φ * p r, ?_⟩
  have hxrep : x = ∑ s : Fin n, ((y s : IntermediateField.adjoin k ({j} : Set F)) : F)
      * (dj * b s) := by
    conv_lhs => rw [← bDB.sum_repr x]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [IntermediateField.smul_def, smul_eq_mul, hbDBa s]
  calc Polynomial.aeval j (TT.det.map φ) * x
      = ∑ s : Fin n, (Polynomial.aeval j (TT.det.map φ)
          * ((y s : IntermediateField.adjoin k ({j} : Set F)) : F)) * (dj * b s) := by
        rw [hxrep, Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring
    _ = ∑ s : Fin n, Polynomial.aeval j (∑ r : Fin n, ((TT.adjugate) s r).map φ * p r)
          * (dj * b s) :=
        Finset.sum_congr rfl fun s _ => by rw [hkey s]

end gstar

end mwGSolM

theorem solution
    {K₀ k F : Type*} [Field K₀] [Field k] [Field F] [Algebra K₀ k] [Algebra k F]
    {j : F} (hj : Transcendental k j)
    [FiniteDimensional (IntermediateField.adjoin k ({j} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin k ({j} : Set F)) F]
    (n : ℕ) (b : Fin n → F)
    (hbli : ∀ c : Fin n → Polynomial k,
      (∑ i : Fin n, Polynomial.aeval j (c i) * b i) = 0 → ∀ i, c i = 0)
    (hbsp : ∀ x : F, ∃ (q : Polynomial k) (c : Fin n → Polynomial k), q ≠ 0 ∧
      x * Polynomial.aeval j q = ∑ i : Fin n, Polynomial.aeval j (c i) * b i)
    (d : Polynomial K₀) (hd : d ≠ 0) (A : Fin n → Matrix (Fin n) (Fin n) (Polynomial K₀))
    (hmul : ∀ i i' : Fin n, b i * b i' * Polynomial.aeval j (d.map (algebraMap K₀ k))
      = ∑ i'' : Fin n, Polynomial.aeval j ((A i i'' i').map (algebraMap K₀ k)) * b i'') :
    ∃ Δ : Polynomial K₀, Δ ≠ 0 ∧ ∀ x : F, IsIntegral (Algebra.adjoin k ({j} : Set F)) x →
      ∃ c : Fin n → Polynomial k,
        Polynomial.aeval j (Δ.map (algebraMap K₀ k)) * x
          = ∑ i : Fin n, Polynomial.aeval j (c i)
              * (Polynomial.aeval j (d.map (algebraMap K₀ k)) * b i) :=
  mwGSolM.mwALGM_gram_denom hj n b hbli hbsp d hd A hmul

end

end S_AlgebraicCurve_Place_exists_gram_denominator_of_mulTable
end P2MW
export P2MW.S_AlgebraicCurve_Place_exists_gram_denominator_of_mulTable (solution)
