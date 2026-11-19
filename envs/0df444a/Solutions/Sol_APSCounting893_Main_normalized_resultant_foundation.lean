-- Prove2me | solution 1 for APSCounting893.Main.normalized_resultant_foundation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:34:00.971569+00:00
-- url     : https://prove2.me/submissions/073a96c4-f0a9-4ded-8213-b2e7a1c19fed

import Definitions.Def_APSCounting893_Main_Resultant
import Definitions.Def_ResultantVNP_CoeffVar
import Definitions.Def_ResultantVNP_IsMultivariateResultant
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

section Component_0

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma totalDegree_pderiv_lt {K : Type*} [CommRing K] [IsDomain K] {ι : Type*}
    (p : MvPolynomial (ι) K) (i : ι) (h : pderiv i p ≠ 0) :
    (pderiv i p).totalDegree < p.totalDegree := by
  classical
  have hs (e : ι →₀ ℕ) (he : e ∈ (pderiv i p).support) :
      e.sum (fun _ k => k) + 1 ≤ p.totalDegree := by
    have hcoef := MvPolynomial.mem_support_iff.mp he
    rw [MvPolynomial.coeff_pderiv] at hcoef
    have hq : p.coeff (e + Finsupp.single i 1) ≠ 0 :=
      fun hz => hcoef (by rw [hz, zero_mul])
    have hh := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hq)
    have heq : (e + Finsupp.single i 1).sum (fun _ k => k) = e.sum (fun _ k => k) + 1 := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
      simp
    rwa [heq] at hh
  have hd : 0 < p.totalDegree := by
    obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr h
    have hh := hs e he
    omega
  have hb : (pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
    rw [MvPolynomial.totalDegree]
    apply Finset.sup_le
    intro e he
    have hh := hs e he
    omega
  omega

lemma eq_C_of_forall_pderiv_zero {K : Type*} [CommRing K] [IsDomain K] [CharZero K] {ι : Type*}
    (p : MvPolynomial (ι) K) (hp : ∀ i, pderiv i p = 0) :
    p = MvPolynomial.C (p.coeff 0) := by
  classical
  ext e
  by_cases he : e = 0
  · subst e
    simp
  have hi : ∃ i, e i ≠ 0 := by
    by_contra h
    push Not at h
    exact he (Finsupp.ext h)
  obtain ⟨i, hi⟩ := hi
  have hle : Finsupp.single i 1 ≤ e := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi)
  have hre : e - Finsupp.single i 1 + Finsupp.single i 1 = e := tsub_add_cancel_of_le hle
  have hc := congrArg (MvPolynomial.coeff (e - Finsupp.single i 1)) (hp i)
  rw [MvPolynomial.coeff_pderiv, MvPolynomial.coeff_zero, hre] at hc
  have hval : (e - Finsupp.single i 1 : ι →₀ ℕ) i + 1 = e i := by
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
    omega
  have hn : (((e - Finsupp.single i 1 : ι →₀ ℕ) i : ℕ) : K) + 1 ≠ 0 := by
    have hh : (((e - Finsupp.single i 1 : ι →₀ ℕ) i + 1 : ℕ) : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr (by omega)
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  have hpc : p.coeff e = 0 := (mul_eq_zero.mp hc).resolve_right hn
  simp [MvPolynomial.coeff_C, Ne.symm he, hpc]

lemma pderiv_aeval_chain {K : Type*} [CommRing K] [IsDomain K] {ι κ : Type*} [Fintype ι]
    (F : ι → MvPolynomial (κ) K) (p : MvPolynomial (ι) K) (j : κ) :
    pderiv j (MvPolynomial.aeval F p) =
      ∑ i, MvPolynomial.aeval F (pderiv i p) * pderiv j (F i) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp [MvPolynomial.aeval_C, MvPolynomial.pderiv_C]
  | add p q hp hq =>
    simp only [map_add, hp, hq, Finset.sum_add_distrib, add_mul]
  | mul_X p k hp =>
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.pderiv_mul, hp,
      map_add, MvPolynomial.pderiv_X, map_mul, MvPolynomial.aeval_X]
    simp only [add_mul, Finset.sum_add_distrib]
    have h1 : (∑ i, MvPolynomial.aeval F (pderiv i p) * pderiv j (F i)) * F k =
        ∑ i, MvPolynomial.aeval F (pderiv i p) * F k * pderiv j (F i) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [h1]
    congr 1
    simp [Pi.single_apply, Finset.mul_sum, mul_assoc]

end APSCounting893.Main
end Component_0

section Component_1

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma algebraicIndependent_of_jacobian_det_ne_zero
    {K : Type*} [CommRing K] [IsDomain K] [CharZero K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → MvPolynomial (ι) K)
    (hdet : (Matrix.of (fun i j : ι => pderiv j (F i))).det ≠ 0) :
    AlgebraicIndependent K F := by
  classical
  have hkill : ∀ d : ℕ, ∀ p : MvPolynomial (ι) K,
      p.totalDegree = d → MvPolynomial.aeval F p = 0 → p = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro p hdeg hp
      let J : Matrix (ι) (ι) (MvPolynomial (ι) K) := fun i j => pderiv j (F i)
      let v : ι → MvPolynomial (ι) K := fun i => MvPolynomial.aeval F (pderiv i p)
      have hvec : Matrix.vecMul v J = 0 := by
        funext j
        change (∑ i, MvPolynomial.aeval F (pderiv i p) * pderiv j (F i)) = 0
        rw [← pderiv_aeval_chain, hp, map_zero]
      have hv : v = 0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hvec
      have hd (i : ι) : pderiv i p = 0 := by
        by_cases h : pderiv i p = 0
        · exact h
        apply ih (pderiv i p).totalDegree (by rw [← hdeg]; exact totalDegree_pderiv_lt p i h)
          (pderiv i p) rfl
        exact congrFun hv i
      have hc := eq_C_of_forall_pderiv_zero p hd
      have he := congrArg (MvPolynomial.aeval F) hc
      rw [hp, MvPolynomial.aeval_C] at he
      have hc0 : p.coeff 0 = 0 := by
        apply MvPolynomial.C_injective (R := K) (σ := ι)
        change MvPolynomial.C (p.coeff 0) = MvPolynomial.C 0
        simpa only [MvPolynomial.algebraMap_eq, MvPolynomial.C_0] using he.symm
      rw [hc, hc0, MvPolynomial.C_0]
  apply algebraicIndependent_iff_injective_aeval.mpr
  apply (injective_iff_map_eq_zero (MvPolynomial.aeval F).toRingHom).mpr
  intro p hp
  exact hkill p.totalDegree p rfl hp

end APSCounting893.Main
end Component_1

section Component_2

set_option autoImplicit false
set_option maxHeartbeats 4000000
open MvPolynomial
namespace APSCounting893.Main

lemma homogeneousComponent_mul_homogeneous {K : Type*} [CommSemiring K] {σ : Type*}
    (p f : MvPolynomial σ K) {d D : ℕ} (hf : f.IsHomogeneous d) (hD : d ≤ D) :
    homogeneousComponent D (p * f) = homogeneousComponent (D-d) p * f := by
  classical
  letI := MvPolynomial.gradedAlgebra (σ := σ) (R := K)
  have hh := DirectSum.coe_decompose_mul_of_right_mem_of_le
    (MvPolynomial.homogeneousSubmodule σ K) (a := p) hf hD
  change (MvPolynomial.decomposition.decompose' (p*f) D : MvPolynomial σ K) =
    (MvPolynomial.decomposition.decompose' p (D-d) : MvPolynomial σ K) * f at hh
  simpa only [MvPolynomial.decomposition.decompose'_apply] using hh

lemma coordinate_power_mem_of_no_projective_root {K : Type*} [Field K] [IsAlgClosed K]
    {n m : ℕ} (f : Fin m → MvPolynomial (Fin n) K)
    (hroot : ∀ x : Fin n → K, (∀ i, MvPolynomial.eval x (f i) = 0) → x = 0)
    (j : Fin n) : ∃ N : ℕ, 0 < N ∧ MvPolynomial.X j ^ N ∈ Ideal.span (Set.range f) := by
  classical
  let I := Ideal.span (Set.range f)
  have hr : MvPolynomial.X j ∈ I.radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K)]
    intro x hx
    have hz : x = 0 := hroot x (fun i => by
      simpa only [MvPolynomial.aeval_eq_eval] using hx (f i) (Ideal.subset_span ⟨i, rfl⟩))
    simp [hz]
  obtain ⟨N, hN⟩ := hr
  exact ⟨N+1, Nat.succ_pos _, by
    rw [pow_succ]
    exact I.mul_mem_right _ hN⟩

lemma large_monomial_mem_of_coordinate_powers {K : Type*} [CommSemiring K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (N : Fin n → ℕ)
    (hN : ∀ i, 0 < N i ∧ MvPolynomial.X i ^ N i ∈ I)
    (e : Fin n →₀ ℕ) (he : (∑ i, (N i - 1)) < e.degree) :
    MvPolynomial.monomial e (1 : K) ∈ I := by
  classical
  have hi : ∃ i, N i ≤ e i := by
    by_contra h
    push Not at h
    have hh : (∑ i, e i) ≤ ∑ i, (N i - 1) :=
      Finset.sum_le_sum (fun i _ => by have := h i; omega)
    rw [Finsupp.degree_eq_sum] at he
    omega
  obtain ⟨i, hi⟩ := hi
  have hle : Finsupp.single i (N i) ≤ e := Finsupp.single_le_iff.mpr hi
  have hm : MvPolynomial.monomial e (1 : K) =
      MvPolynomial.monomial (e - Finsupp.single i (N i)) 1 * MvPolynomial.X i ^ N i := by
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul,
      tsub_add_cancel_of_le hle, one_mul]
  rw [hm]
  exact I.mul_mem_left _ (hN i).2

end APSCounting893.Main
end Component_2

section Component_3

set_option autoImplicit false
set_option maxHeartbeats 4000000
open MvPolynomial
namespace APSCounting893.Main

abbrev DegreeMonomial (n D : ℕ) := {e : Fin n →₀ ℕ // e.degree = D}

instance degreeMonomial_finite (n D : ℕ) : Finite (DegreeMonomial n D) := by
  apply Finite.of_injective
    (fun e : DegreeMonomial n D => fun i : Fin n =>
      (⟨e.1 i, Nat.lt_succ_of_le (by
        have h := Finsupp.le_degree i e.1
        rw [e.2] at h
        exact h)⟩ : Fin (D+1)))
  intro a b h
  apply Subtype.ext
  apply Finsupp.ext
  intro i
  exact congrArg Fin.val (congrFun h i)

noncomputable instance degreeMonomial_fintype (n D : ℕ) : Fintype (DegreeMonomial n D) :=
  Fintype.ofFinite _

lemma homogeneous_sum_monomials {K : Type*} [CommSemiring K] {n D : ℕ}
    (p : MvPolynomial (Fin n) K) (hp : p.IsHomogeneous D) :
    p = ∑ e : DegreeMonomial n D, MvPolynomial.monomial e.1 (p.coeff e.1) := by
  classical
  ext a
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  by_cases ha : a.degree = D
  · let a' : DegreeMonomial n D := ⟨a,ha⟩
    rw [Finset.sum_eq_single a']
    · simp [a']
    · intro b hb hba
      have hb : a ≠ b.1 := by
        intro heq
        apply hba
        exact Subtype.ext heq.symm
      simp [Ne.symm hb]
    · simp
  · rw [hp.coeff_eq_zero ha]
    symm
    apply Finset.sum_eq_zero
    intro b hb
    have hab : a ≠ b.1 := by intro h; exact ha (h ▸ b.2)
    simp [Ne.symm hab]

lemma eval₂_homogeneous_sum {K R : Type*} [CommSemiring K] [CommSemiring R]
    {n D : ℕ} (f : K →+* R) (x : Fin n → R)
    (p : MvPolynomial (Fin n) K) (hp : p.IsHomogeneous D) :
    MvPolynomial.eval₂ f x p =
      ∑ e : DegreeMonomial n D, f (p.coeff e.1) * ∏ i : Fin n, x i ^ e.1 i := by
  classical
  conv_lhs => rw [homogeneous_sum_monomials p hp]
  simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_monomial]
  apply Finset.sum_congr rfl
  intro e he
  congr 1
  exact Finsupp.prod_fintype _ _ (fun _ => by simp)

end APSCounting893.Main
end Component_3

section Component_4

set_option autoImplicit false
set_option maxHeartbeats 4000000
open MvPolynomial
namespace APSCounting893.Main

lemma homogeneous_matrix_certificate {K : Type*} [Field K] {σ : Type*} {n D : ℕ}
    (Q : DegreeMonomial n D → MvPolynomial (Fin n) (MvPolynomial σ K))
    (hQ : ∀ e, (Q e).IsHomogeneous D) (a : σ → K)
    (ha : ∀ e, MvPolynomial.map (MvPolynomial.eval a) (Q e) = MvPolynomial.monomial e.1 1) :
    ∃ q : MvPolynomial σ K, MvPolynomial.eval a q = 1 ∧
      ∀ (b : σ → K) (x : Fin n → K), x ≠ 0 →
        (∀ e, MvPolynomial.eval₂ (MvPolynomial.eval b) x (Q e) = 0) →
        MvPolynomial.eval b q = 0 := by
  classical
  let A : Matrix (DegreeMonomial n D) (DegreeMonomial n D) (MvPolynomial σ K) :=
    fun e f => (Q e).coeff f.1
  refine ⟨A.det, ?_, ?_⟩
  · rw [RingHom.map_det]
    have hmat : (MvPolynomial.eval a).mapMatrix A = 1 := by
      ext e f
      change MvPolynomial.eval a ((Q e).coeff f.1) = if e = f then 1 else 0
      have hh := congrArg (MvPolynomial.coeff f.1) (ha e)
      rw [MvPolynomial.coeff_map, MvPolynomial.coeff_monomial] at hh
      simpa only [Subtype.val_inj] using hh
    rw [hmat, Matrix.det_one]
  · intro b x hx hroot
    by_contra hdet
    have hd : ((MvPolynomial.eval b).mapMatrix A).det ≠ 0 := by
      rw [← RingHom.map_det]
      exact hdet
    let v : DegreeMonomial n D → K := fun e => ∏ j : Fin n, x j ^ e.1 j
    have hvec : ((MvPolynomial.eval b).mapMatrix A).mulVec v = 0 := by
      funext e
      change (∑ f : DegreeMonomial n D,
        MvPolynomial.eval b ((Q e).coeff f.1) * ∏ j : Fin n, x j ^ f.1 j) = 0
      rw [← eval₂_homogeneous_sum _ _ _ (hQ e)]
      exact hroot e
    have hv : v = 0 := Matrix.eq_zero_of_mulVec_eq_zero hd hvec
    have hix : ∃ j, x j ≠ 0 := by
      by_contra hh
      push Not at hh
      exact hx (funext hh)
    obtain ⟨j,hj⟩ := hix
    let e : DegreeMonomial n D := ⟨Finsupp.single j D, Finsupp.degree_single _ _⟩
    have he := congrFun hv e
    have hvj : v e = x j ^ D := by simp [v,e,Finsupp.single_apply]
    have hh : x j ^ D = 0 := hvj.symm.trans he
    exact (pow_ne_zero D hj) hh

end APSCounting893.Main
end Component_4

section Component_5

set_option autoImplicit false
set_option maxHeartbeats 4000000
open MvPolynomial
namespace APSCounting893.Main

lemma no_projective_root_polynomial_certificate {K : Type*} [Field K] [IsAlgClosed K]
    {σ : Type*} {n m : ℕ}
    (U : Fin m → MvPolynomial (Fin n) (MvPolynomial σ K)) (d : Fin m → ℕ)
    (hU : ∀ i, (U i).IsHomogeneous (d i)) (a : σ → K)
    (ha : ∀ x : Fin n → K,
      (∀ i, MvPolynomial.eval₂ (MvPolynomial.eval a) x (U i) = 0) → x = 0) :
    ∃ q : MvPolynomial σ K, MvPolynomial.eval a q = 1 ∧
      ∀ b : σ → K, (∃ x : Fin n → K, x ≠ 0 ∧
        ∀ i, MvPolynomial.eval₂ (MvPolynomial.eval b) x (U i) = 0) →
        MvPolynomial.eval b q = 0 := by
  classical
  let f : Fin m → MvPolynomial (Fin n) K := fun i => MvPolynomial.map (MvPolynomial.eval a) (U i)
  have hfroot : ∀ x : Fin n → K, (∀ i, MvPolynomial.eval x (f i) = 0) → x = 0 := by
    intro x hx
    apply ha x
    intro i
    simpa only [f,MvPolynomial.eval_map] using hx i
  choose N hN using coordinate_power_mem_of_no_projective_root f hfroot
  let D := (∑ j : Fin n, (N j - 1)) + (∑ i : Fin m, d i) + 1
  have hdD (i : Fin m) : d i ≤ D := by
    have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (d j))
      (Finset.mem_univ i)
    dsimp [D]
    omega
  have hm (e : DegreeMonomial n D) :
      MvPolynomial.monomial e.1 (1 : K) ∈ Ideal.span (Set.range f) := by
    apply large_monomial_mem_of_coordinate_powers _ N hN
    rw [e.2]
    dsimp [D]
    omega
  have hex (e : DegreeMonomial n D) :
      ∃ u : Fin m → MvPolynomial (Fin n) K,
        ∑ i, u i * f i = MvPolynomial.monomial e.1 1 :=
    Ideal.mem_span_range_iff_exists_fun.mp (hm e)
  choose u hu using hex
  let g (e : DegreeMonomial n D) (i : Fin m) := homogeneousComponent (D-d i) (u e i)
  have hg (e : DegreeMonomial n D) :
      ∑ i, g e i * f i = MvPolynomial.monomial e.1 1 := by
    have hh := congrArg (homogeneousComponent D) (hu e)
    rw [map_sum, homogeneousComponent_eq_self (isHomogeneous_monomial _ e.2)] at hh
    have hf (i : Fin m) : (f i).IsHomogeneous (d i) := (hU i).map _
    simp_rw [homogeneousComponent_mul_homogeneous _ _ (hf _) (hdD _)] at hh
    exact hh
  let Q (e : DegreeMonomial n D) : MvPolynomial (Fin n) (MvPolynomial σ K) :=
    ∑ i, MvPolynomial.map MvPolynomial.C (g e i) * U i
  have hQ (e : DegreeMonomial n D) : (Q e).IsHomogeneous D := by
    apply MvPolynomial.IsHomogeneous.sum
    intro i hi
    have hh := ((homogeneousComponent_isHomogeneous (D-d i) (u e i)).map
      (MvPolynomial.C : K →+* MvPolynomial σ K)).mul (hU i)
    simpa only [Nat.sub_add_cancel (hdD i)] using hh
  have hCQ (p : MvPolynomial (Fin n) K) :
      MvPolynomial.map (MvPolynomial.eval a) (MvPolynomial.map MvPolynomial.C p) = p := by
    apply MvPolynomial.ext
    intro e
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map, MvPolynomial.eval_C]
  have hQa (e : DegreeMonomial n D) :
      MvPolynomial.map (MvPolynomial.eval a) (Q e) = MvPolynomial.monomial e.1 1 := by
    simpa only [Q,map_sum,map_mul,hCQ] using hg e
  obtain ⟨q,hqa,hq⟩ := homogeneous_matrix_certificate Q hQ a hQa
  refine ⟨q,hqa,?_⟩
  rintro b ⟨x,hx,hroots⟩
  apply hq b x hx
  intro e
  simp only [Q,MvPolynomial.eval₂_sum,MvPolynomial.eval₂_mul,hroots,mul_zero,Finset.sum_const_zero]

end APSCounting893.Main
end Component_5

section Component_6

set_option autoImplicit false
set_option maxHeartbeats 4000000
open MvPolynomial
namespace APSCounting893.Main

noncomputable def universalForm {K : Type*} [CommSemiring K] {n : ℕ}
    (d : Fin n → ℕ) (i : Fin n) : MvPolynomial (Fin n) (MvPolynomial (ResultantVNP.CoeffVar d) K) :=
  ∑ e : {e : Fin n →₀ ℕ // ∑ j, e j = d i},
    MvPolynomial.monomial e.1 (MvPolynomial.X ⟨i,e⟩)

lemma universalForm_homogeneous {K : Type*} [CommSemiring K] {n : ℕ}
    (d : Fin n → ℕ) (i : Fin n) : (universalForm (K := K) d i).IsHomogeneous (d i) := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro e he
  exact MvPolynomial.isHomogeneous_monomial _ (by rw [Finsupp.degree_eq_sum]; exact e.2)

abbrev FreeResultantCoefficient {n : ℕ} (d : Fin (n+1) → ℕ) :=
  {v : ResultantVNP.CoeffVar d // v.2.1 ≠ Finsupp.single 0 (d v.1)}

abbrev ResultantChartVariable {n : ℕ} (d : Fin (n+1) → ℕ) :=
  Sum (FreeResultantCoefficient d) (Fin n)

noncomputable def resultantChartRoot {K : Type*} [CommRing K] {n : ℕ}
    (d : Fin (n+1) → ℕ) : Fin (n+1) → MvPolynomial (ResultantChartVariable d) K :=
  Fin.cons 1 (fun j => MvPolynomial.X (Sum.inr j))

noncomputable def resultantChartRemainder {K : Type*} [CommRing K] {n : ℕ}
    (d : Fin (n+1) → ℕ) (i : Fin (n+1)) : MvPolynomial (ResultantChartVariable d) K :=
  ∑ e : {e : Fin (n+1) →₀ ℕ // ∑ j, e j = d i},
    if h : e.1 = Finsupp.single 0 (d i) then 0 else
      MvPolynomial.X (Sum.inl ⟨⟨i,e⟩,h⟩) *
        ∏ j : Fin n, MvPolynomial.X (Sum.inr j) ^ e.1 j.succ

noncomputable def resultantChartCoefficient {K : Type*} [CommRing K] {n : ℕ}
    (d : Fin (n+1) → ℕ) (v : ResultantVNP.CoeffVar d) :
    MvPolynomial (ResultantChartVariable d) K :=
  if h : v.2.1 = Finsupp.single 0 (d v.1) then -resultantChartRemainder d v.1
  else MvPolynomial.X (Sum.inl ⟨v,h⟩)

lemma resultant_chart_is_root {K : Type*} [CommRing K] {n : ℕ}
    (d : Fin (n+1) → ℕ) (i : Fin (n+1)) :
    MvPolynomial.eval₂ (MvPolynomial.eval₂Hom MvPolynomial.C (resultantChartCoefficient (K := K) d))
      (resultantChartRoot (K := K) d) (universalForm (K := K) d i) = 0 := by
  classical
  let e0 : {e : Fin (n+1) →₀ ℕ // ∑ j, e j = d i} :=
    ⟨Finsupp.single 0 (d i), by simp⟩
  simp only [universalForm,MvPolynomial.eval₂_sum,MvPolynomial.eval₂_monomial,
    MvPolynomial.eval₂Hom_X']
  have hp (e : {e : Fin (n+1) →₀ ℕ // ∑ j, e j = d i}) :
      e.1.prod (fun j k => resultantChartRoot (K := K) d j ^ k) =
        ∏ j : Fin n, MvPolynomial.X (Sum.inr j) ^ e.1 j.succ := by
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_succ]
    simp [resultantChartRoot]
  simp_rw [hp]
  have he0 : ∏ j : Fin n, (MvPolynomial.X (Sum.inr j) : MvPolynomial (ResultantChartVariable d) K) ^
      e0.1 j.succ = 1 := by simp [e0]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e0)]
  rw [show resultantChartCoefficient (K := K) d ⟨i,e0⟩ = -resultantChartRemainder d i by
    simp [resultantChartCoefficient,e0]]
  rw [he0,mul_one]
  have hr : resultantChartRemainder (K := K) d i =
      ∑ e ∈ Finset.univ.erase e0,
        resultantChartCoefficient d ⟨i,e⟩ *
          ∏ j : Fin n, MvPolynomial.X (Sum.inr j) ^ e.1 j.succ := by
    unfold resultantChartRemainder
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e0)]
    simp only [e0,dif_pos,zero_add]
    apply Finset.sum_congr rfl
    intro e he
    have hn : e.1 ≠ Finsupp.single 0 (d i) := by
      intro hh
      exact (Finset.ne_of_mem_erase he) (Subtype.ext hh)
    simp [resultantChartCoefficient,hn]
  rw [hr,neg_add_cancel]

end APSCounting893.Main
end Component_6

section Component_7

set_option autoImplicit false
set_option maxHeartbeats 4000000
open MvPolynomial
namespace APSCounting893.Main

lemma pderiv_partial_aeval_right {K : Type*} [CommRing K] [IsDomain K] {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (c : α → K) (p : MvPolynomial (Sum α β) K) (j : β) :
    pderiv j (MvPolynomial.aeval (Sum.elim (fun i => MvPolynomial.C (c i)) MvPolynomial.X) p) =
      MvPolynomial.aeval (Sum.elim (fun i => MvPolynomial.C (c i)) MvPolynomial.X)
        (pderiv (Sum.inr j) p) := by
  classical
  rw [pderiv_aeval_chain,Fintype.sum_sum_type]
  simp [MvPolynomial.pderiv_C,MvPolynomial.pderiv_X,Pi.single_apply]

end APSCounting893.Main
end Component_7

section Component_8

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma algebraicIndependent_block_of_specialized_jacobian
    {K : Type*} [CommRing K] [IsDomain K] [CharZero K] {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (G : β → MvPolynomial (Sum α β) K) (φ : MvPolynomial (Sum α β) K →+* K)
    (a : β → K) (ha : ∀ i, a i ≠ 0)
    (hG : ∀ i j, φ (pderiv (Sum.inr j) (G i)) = if i = j then a i else 0) :
    AlgebraicIndependent K (Sum.elim (fun i : α => MvPolynomial.X (Sum.inl i)) G) := by
  classical
  apply algebraicIndependent_of_jacobian_det_ne_zero
  intro hz
  let J : Matrix (Sum α β) (Sum α β) (MvPolynomial (Sum α β) K) :=
    fun i j => pderiv j (Sum.elim (fun k : α => MvPolynomial.X (Sum.inl k)) G i)
  have hmap : φ.mapMatrix J = Matrix.fromBlocks (1 : Matrix α α K) 0
      (Matrix.of (fun i j => φ (pderiv (Sum.inl j) (G i)))) (Matrix.diagonal a) := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => simp [J,Matrix.fromBlocks, RingHom.mapMatrix_apply,MvPolynomial.pderiv_X,Pi.single_apply,Matrix.one_apply,eq_comm]
      | inr j => simp [J,Matrix.fromBlocks,RingHom.mapMatrix_apply,MvPolynomial.pderiv_X,Pi.single_apply]
    | inr i =>
      cases j with
      | inl j => rfl
      | inr j => simpa [J,Matrix.fromBlocks,RingHom.mapMatrix_apply,Matrix.diagonal_apply] using hG i j
  have hd : φ J.det = ∏ i, a i := by
    rw [RingHom.map_det,hmap,Matrix.det_fromBlocks_zero₁₂,Matrix.det_one,
      Matrix.det_diagonal,one_mul]
  have hj : J.det = 0 := hz
  rw [hj,map_zero] at hd
  exact (Finset.prod_ne_zero_iff.mpr (fun i _ => ha i)) hd.symm

end APSCounting893.Main
end Component_8

section Component_9

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def diagonalFreeCoefficient {K : Type*} [CommRing K] {n : ℕ}
    (d : Fin (n+1) → ℕ) (v : FreeResultantCoefficient d) : K :=
  if v.1.2.1 = Finsupp.single v.1.1 (d v.1.1) then 1 else 0

lemma chart_remainder_diagonal_specialization {K : Type*} [CommRing K] [IsDomain K] {n : ℕ}
    (d : Fin (n+1) → ℕ) (hd : ∀ i, 0 < d i) (i : Fin n) :
    MvPolynomial.aeval
      (Sum.elim (fun v => MvPolynomial.C (diagonalFreeCoefficient (K := K) d v)) MvPolynomial.X)
      (resultantChartRemainder (K := K) d i.succ) = (MvPolynomial.X i : MvPolynomial (Fin n) K) ^ d i.succ := by
  classical
  let e1 : {e : Fin (n+1) →₀ ℕ // ∑ j, e j = d i.succ} :=
    ⟨Finsupp.single i.succ (d i.succ),by simp⟩
  have he10 : e1.1 ≠ Finsupp.single 0 (d i.succ) := by
    intro hh
    have h := congrFun (congrArg DFunLike.coe hh) i.succ
    exact (Nat.ne_of_gt (hd i.succ)) (by simpa [e1] using h)
  simp only [resultantChartRemainder,map_sum]
  rw [Finset.sum_eq_single e1]
  · simp only [dif_neg he10,map_mul,MvPolynomial.aeval_X,Sum.elim_inl,
      diagonalFreeCoefficient,e1,if_pos rfl,MvPolynomial.C_1,one_mul,map_prod,map_pow,
      Sum.elim_inr]
    simp [Finsupp.single_apply]
  · intro e he hne
    by_cases he0 : e.1 = Finsupp.single 0 (d i.succ)
    · simp [he0]
    · have he1 : e.1 ≠ Finsupp.single i.succ (d i.succ) := by
        intro hh
        exact hne (Subtype.ext hh)
      simp [he0,diagonalFreeCoefficient,he1]
  · simp

lemma chart_selected_coefficients_independent {K : Type*} [CommRing K] [IsDomain K] [CharZero K] {n : ℕ}
    (d : Fin (n+1) → ℕ) (hd : ∀ i, 0 < d i) :
    AlgebraicIndependent K (Sum.elim
      (fun v : FreeResultantCoefficient d =>
        (MvPolynomial.X (Sum.inl v) : MvPolynomial (ResultantChartVariable d) K))
      (fun i : Fin n => -resultantChartRemainder d i.succ)) := by
  classical
  let ψ : MvPolynomial (ResultantChartVariable d) K →ₐ[K] MvPolynomial (Fin n) K :=
    MvPolynomial.aeval (Sum.elim (fun v => MvPolynomial.C (diagonalFreeCoefficient d v)) MvPolynomial.X)
  let φ : MvPolynomial (ResultantChartVariable d) K →+* K :=
    (MvPolynomial.eval (fun _ => 1)).comp ψ.toRingHom
  apply algebraicIndependent_block_of_specialized_jacobian _ φ
    (fun i : Fin n => -(d i.succ : K))
  · intro i
    exact neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hd i.succ)))
  · intro i j
    change MvPolynomial.eval (fun _ => 1) (ψ (pderiv (Sum.inr j) (-resultantChartRemainder d i.succ))) = _
    change MvPolynomial.eval (fun _ => 1)
      (MvPolynomial.aeval _ (pderiv (Sum.inr j) (-resultantChartRemainder d i.succ))) = _
    rw [← pderiv_partial_aeval_right, map_neg, chart_remainder_diagonal_specialization d hd i,
      map_neg, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X]
    by_cases hij : i = j
    · subst j
      simp [Pi.single_apply]
    · simp [Pi.single_apply,hij,Ne.symm hij]

end APSCounting893.Main
end Component_9

section Component_10

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def pureZeroCoefficient {n : ℕ} (d : Fin (n+1) → ℕ) (i : Fin (n+1)) :
    ResultantVNP.CoeffVar d := ⟨i,⟨Finsupp.single 0 (d i),by simp⟩⟩

noncomputable def chartCoefficientIndex {n : ℕ} (d : Fin (n+1) → ℕ) :
    ResultantChartVariable d → ResultantVNP.CoeffVar d :=
  Sum.elim Subtype.val (fun j => pureZeroCoefficient d j.succ)

lemma chartCoefficientIndex_injective {n : ℕ} (d : Fin (n+1) → ℕ) :
    Function.Injective (chartCoefficientIndex d) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Subtype.ext hab)
    | inr b =>
      have ha : a.1 = pureZeroCoefficient d b.succ := hab
      have hh : a.1.2.1 = Finsupp.single 0 (d a.1.1) := by rw [ha]; rfl
      exact (a.2 hh).elim
  | inr a =>
    cases b with
    | inl b =>
      have hb : b.1 = pureZeroCoefficient d a.succ := hab.symm
      have hh : b.1.2.1 = Finsupp.single 0 (d b.1.1) := by rw [hb]; rfl
      exact (b.2 hh).elim
    | inr b =>
      have hh : a.succ = b.succ := congrArg Sigma.fst hab
      exact congrArg Sum.inr (Fin.succ_injective _ hh)

lemma chartCoefficientIndex_ne_zero {n : ℕ} (d : Fin (n+1) → ℕ)
    (v : ResultantChartVariable d) : chartCoefficientIndex d v ≠ pureZeroCoefficient d 0 := by
  cases v with
  | inl v =>
    intro hv
    have hh : v.1.2.1 = Finsupp.single 0 (d v.1.1) := by
      change v.1 = pureZeroCoefficient d 0 at hv
      rw [hv]
      rfl
    exact v.2 hh
  | inr v =>
    intro hv
    have hh : v.succ = 0 := congrArg Sigma.fst hv
    exact Fin.succ_ne_zero v hh

noncomputable def chartComplementEquiv {n : ℕ} (d : Fin (n+1) → ℕ) :
    ResultantChartVariable d ≃ {v : ResultantVNP.CoeffVar d // v ≠ pureZeroCoefficient d 0} :=
  Equiv.ofBijective (fun v => ⟨chartCoefficientIndex d v,chartCoefficientIndex_ne_zero d v⟩) (by
    constructor
    · intro a b h
      exact chartCoefficientIndex_injective d (congrArg Subtype.val h)
    · intro v
      classical
      by_cases he : v.1.2.1 = Finsupp.single 0 (d v.1.1)
      · have hv : v.1 = pureZeroCoefficient d v.1.1 := by
          exact congrArg (Sigma.mk v.1.1) (Subtype.ext he)
        have hi : v.1.1 ≠ 0 := by
          intro h0
          exact v.2 (by simpa only [h0] using hv)
        refine ⟨Sum.inr (v.1.1.pred hi),?_⟩
        apply Subtype.ext
        change pureZeroCoefficient d (v.1.1.pred hi).succ = v.1
        rw [Fin.succ_pred _ hi]
        exact hv.symm
      · exact ⟨Sum.inl ⟨v.1,he⟩,rfl⟩)

end APSCounting893.Main
end Component_10

section Component_11

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open Polynomial
namespace APSCounting893.Main

attribute [local instance] Polynomial.algebra Polynomial.isLocalization

lemma polynomial_prime_height_one_of_contract_zero {R : Type} [CommRing R] [IsDomain R]
    (P : Ideal R[X]) [P.IsPrime] (hP : P ≠ ⊥)
    (hcontract : Ideal.comap Polynomial.C P = ⊥) : P.height = 1 := by
  let K := FractionRing R
  let M : Submonoid R[X] := (nonZeroDivisors R).map Polynomial.C
  let Q : Ideal K[X] := P.map (algebraMap R[X] K[X])
  have hd : Disjoint (M : Set R[X]) (P : Set R[X]) := by
    refine Set.disjoint_left.mpr ?_
    rintro q ⟨r, hr, rfl⟩ hq
    have hr0 : r = 0 := by
      have hh : r ∈ Ideal.comap Polynomial.C P := hq
      rw [hcontract, Ideal.mem_bot] at hh
      exact hh
    exact (nonZeroDivisors.ne_zero hr) hr0
  haveI : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M K[X] P inferInstance hd
  have hinj : Function.Injective (algebraMap R[X] K[X]) :=
    Polynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K)
  have hQ : Q ≠ ⊥ := by
    intro h
    exact hP ((Ideal.map_eq_bot_iff_of_injective hinj).mp h)
  haveI : Q.IsMaximal := IsPrime.to_maximal_ideal hQ
  have hh := IsPrincipalIdealRing.height_eq_one_of_isMaximal Q (Polynomial.not_isField K)
  have he := IsLocalization.height_map_of_disjoint (S := K[X]) M P hd
  exact he.symm.trans hh

lemma polynomial_prime_principal_of_contract_zero {R : Type} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R]
    (P : Ideal R[X]) [P.IsPrime] (hcontract : Ideal.comap Polynomial.C P = ⊥) :
    P.IsPrincipal := by
  by_cases hP : P = ⊥
  · rw [hP]; infer_instance
  · exact UniqueFactorizationMonoid.isPrincipal_of_height_eq_one
      (polynomial_prime_height_one_of_contract_zero P hP hcontract)

end APSCounting893.Main
end Component_11

section Component_12

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma mv_prime_principal_of_contract_complement_zero {K σ : Type} [CommRing K] [IsDomain K] [UniqueFactorizationMonoid K]
    (v : σ) (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (hcontract : I.comap (MvPolynomial.rename (Subtype.val : {w : σ // w ≠ v} → σ)) = ⊥) :
    I.IsPrincipal := by
  classical
  let e : MvPolynomial σ K ≃ₐ[K] Polynomial (MvPolynomial {w : σ // w ≠ v} K) :=
    (MvPolynomial.renameEquiv K (Equiv.optionSubtypeNe v).symm).trans
      (MvPolynomial.optionEquivLeft K _)
  have he (p : MvPolynomial {w : σ // w ≠ v} K) :
      e (MvPolynomial.rename Subtype.val p) = Polynomial.C p := by
    have hh : e.toRingEquiv.toRingHom.comp (MvPolynomial.rename Subtype.val).toRingHom =
        (Polynomial.C : MvPolynomial {w : σ // w ≠ v} K →+* _) := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp [e]
      · intro i
        have hsome : (Equiv.optionSubtypeNe v).symm i.1 = some i := by
          apply (Equiv.optionSubtypeNe v).injective
          simp [i.property]
        simp [e,hsome]
    exact RingHom.congr_fun hh p
  let P : Ideal (Polynomial (MvPolynomial {w : σ // w ≠ v} K)) := I.comap e.symm.toRingEquiv.toRingHom
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  have hP : P.comap Polynomial.C = ⊥ := by
    ext p
    change e.symm (Polynomial.C p) ∈ I ↔ p ∈ (⊥ : Ideal _)
    have hh : e.symm (Polynomial.C p) = MvPolynomial.rename Subtype.val p := by
      apply e.injective
      rw [AlgEquiv.apply_symm_apply,he]
    rw [hh]
    exact SetLike.ext_iff.mp hcontract p
  obtain ⟨p,hgen⟩ := polynomial_prime_principal_of_contract_zero P hP
  refine ⟨e.symm p,?_⟩
  have hmap := congrArg (Ideal.map e.symm.toRingEquiv.toRingHom) hgen
  rw [Ideal.map_span,Set.image_singleton] at hmap
  have hPI : P.map e.symm.toRingEquiv.toRingHom = I :=
    Ideal.map_comap_of_surjective _ e.symm.surjective _
  rwa [hPI] at hmap

end APSCounting893.Main
end Component_12

section Component_13

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def resultantChartHom {K : Type} [CommRing K] {n : ℕ}
    (d : Fin (n+1) → ℕ) :
    MvPolynomial (ResultantVNP.CoeffVar d) K →ₐ[K] MvPolynomial (ResultantChartVariable d) K :=
  MvPolynomial.aeval (resultantChartCoefficient d)

lemma resultantChartHom_index {K : Type} [CommRing K] {n : ℕ}
    (d : Fin (n+1) → ℕ) (v : ResultantChartVariable d) :
    resultantChartHom (K := K) d (MvPolynomial.X (chartCoefficientIndex d v)) =
      Sum.elim (fun v : FreeResultantCoefficient d => MvPolynomial.X (Sum.inl v))
        (fun i : Fin n => -resultantChartRemainder d i.succ) v := by
  classical
  cases v with
  | inl v => simp [resultantChartHom,chartCoefficientIndex,resultantChartCoefficient,v.2]
  | inr v => simp [resultantChartHom,chartCoefficientIndex,pureZeroCoefficient,resultantChartCoefficient]

lemma resultantChartHom_kernel_nonzero_principal {K : Type} [CommRing K] [IsDomain K] [UniqueFactorizationMonoid K] [CharZero K] {n : ℕ}
    (d : Fin (n+1) → ℕ) (hd : ∀ i, 0 < d i) :
    let I := RingHom.ker (resultantChartHom (K := K) d).toRingHom
    I ≠ ⊥ ∧ I.IsPrincipal := by
  classical
  intro I
  haveI : I.IsPrime := RingHom.ker_isPrime _
  let v0 := pureZeroCoefficient d 0
  let E := chartComplementEquiv d
  have hg : AlgebraicIndependent K (fun v : {v : ResultantVNP.CoeffVar d // v ≠ v0} =>
      resultantChartHom (K := K) d (MvPolynomial.X v.1)) := by
    have h := (chart_selected_coefficients_independent (K := K) d hd).comp E.symm E.symm.injective
    convert h using 1
    funext v
    have hh := resultantChartHom_index (K := K) d (E.symm v)
    have hv : chartCoefficientIndex d (E.symm v) = v.1 :=
      congrArg Subtype.val (E.apply_symm_apply v)
    simpa only [hv,Function.comp_apply] using hh
  have hcontract : I.comap (MvPolynomial.rename (Subtype.val : {v : ResultantVNP.CoeffVar d // v ≠ v0} → _)) = ⊥ := by
    ext p
    change resultantChartHom d (MvPolynomial.rename Subtype.val p) = 0 ↔ p = 0
    change MvPolynomial.aeval (resultantChartCoefficient d) (MvPolynomial.rename Subtype.val p) = 0 ↔ p = 0
    rw [MvPolynomial.aeval_rename]
    have hfamily : resultantChartCoefficient (K := K) d ∘
        (Subtype.val : {v : ResultantVNP.CoeffVar d // v ≠ v0} → _) =
        (fun v => resultantChartHom (K := K) d (MvPolynomial.X v.1)) := by
      funext v
      exact (MvPolynomial.aeval_X (R := K) (resultantChartCoefficient (K := K) d) v.1).symm
    rw [hfamily]
    constructor
    · exact hg.eq_zero_of_aeval_eq_zero p
    · rintro rfl; exact map_zero _
  refine ⟨?_,mv_prime_principal_of_contract_complement_zero v0 I hcontract⟩
  intro hI
  have hind : AlgebraicIndependent K (resultantChartCoefficient (K := K) d) :=
    (RingHom.injective_iff_ker_eq_bot _).mpr hI
  have hh := hind.cardinalMk_le_trdeg
  rw [MvPolynomial.trdeg_of_isDomain] at hh
  simp only [Cardinal.mk_fintype,Cardinal.lift_natCast] at hh
  have hcard : Fintype.card (ResultantVNP.CoeffVar d) ≤ Fintype.card (ResultantChartVariable d) := by
    exact_mod_cast hh
  let e : Option (ResultantChartVariable d) ≃ ResultantVNP.CoeffVar d :=
    (Equiv.optionCongr E).trans (Equiv.optionSubtypeNe v0)
  have he : Fintype.card (ResultantVNP.CoeffVar d) = Fintype.card (ResultantChartVariable d) + 1 := by
    rw [← Fintype.card_congr e,Fintype.card_option]
  omega

end APSCounting893.Main
end Component_13

section Component_14

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial TensorProduct
namespace APSCounting893.Main

lemma flat_polynomial_kernel_principal {R S σ τ : Type}
    [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (g : MvPolynomial σ S →ₐ[S] MvPolynomial τ S)
    (hcomm : ∀ p, g (MvPolynomial.map (algebraMap R S) p) =
      MvPolynomial.map (algebraMap R S) (f p))
    (r : MvPolynomial σ R) (hker : RingHom.ker f.toRingHom = Ideal.span {r}) :
    RingHom.ker g.toRingHom = Ideal.span {MvPolynomial.map (algebraMap R S) r} := by
  classical
  let Eσ := MvPolynomial.algebraTensorAlgEquiv (σ := σ) R S
  let Eτ := MvPolynomial.algebraTensorAlgEquiv (σ := τ) R S
  let F := TensorProduct.AlgebraTensorModule.lTensor S S f.toLinearMap
  have hF (z : S ⊗[R] MvPolynomial σ R) : g (Eσ z) = Eτ (F z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a p =>
      simp only [Eσ,Eτ,F,MvPolynomial.algebraTensorAlgEquiv_tmul,
        TensorProduct.AlgebraTensorModule.lTensor_tmul,AlgHom.toLinearMap_apply]
      rw [map_smul,hcomm]
    | add z w hz hw => simp only [map_add,hz,hw]
  apply le_antisymm
  · intro p hp
    have hx : Eσ.symm p ∈ LinearMap.ker F := by
      change F (Eσ.symm p) = 0
      apply Eτ.injective
      rw [map_zero,← hF,AlgEquiv.apply_symm_apply]
      exact hp
    rw [Module.Flat.ker_lTensor_eq S S f.toLinearMap] at hx
    obtain ⟨z,hz⟩ := hx
    have hzm : Eσ ((TensorProduct.AlgebraTensorModule.lTensor S S f.toLinearMap.ker.subtype) z) ∈
        Ideal.span {MvPolynomial.map (algebraMap R S) r} := by
      clear hz
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a p =>
        simp only [TensorProduct.AlgebraTensorModule.lTensor_tmul,Submodule.coe_subtype,
          MvPolynomial.algebraTensorAlgEquiv_tmul,Eσ]
        have hpI : p.1 ∈ Ideal.span {r} := hker ▸ p.2
        obtain ⟨u,hu⟩ := Ideal.mem_span_singleton.mp hpI
        rw [Algebra.smul_def]
        apply Ideal.mul_mem_left
        apply Ideal.mem_span_singleton.mpr
        refine ⟨MvPolynomial.map (algebraMap R S) u,?_⟩
        rw [hu,map_mul]
      | add z w hz hw =>
        simp only [map_add]
        exact Ideal.add_mem _ hz hw
    rw [hz,AlgEquiv.apply_symm_apply] at hzm
    exact hzm
  · apply Ideal.span_le.mpr
    intro p hp
    rcases hp with rfl
    change g (MvPolynomial.map (algebraMap R S) r) = 0
    rw [hcomm]
    have hr : r ∈ RingHom.ker f.toRingHom := hker ▸ Ideal.subset_span (Set.mem_singleton r)
    change f r = 0 at hr
    rw [hr,map_zero]

end APSCounting893.Main
end Component_14

section Component_15

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma map_resultantChartCoefficient {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) {n : ℕ} (d : Fin (n+1) → ℕ) (v : ResultantVNP.CoeffVar d) :
    MvPolynomial.map f (resultantChartCoefficient (K := R) d v) =
      resultantChartCoefficient (K := S) d v := by
  classical
  unfold resultantChartCoefficient
  split_ifs with h
  · simp only [map_neg,resultantChartRemainder,map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro e he
    split_ifs with hh
    · exact map_zero _
    · simp only [map_mul,MvPolynomial.map_X,map_prod,map_pow]
  · exact MvPolynomial.map_X _ _

lemma resultantChartHom_base_change {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) {n : ℕ} (d : Fin (n+1) → ℕ)
    (p : MvPolynomial (ResultantVNP.CoeffVar d) R) :
    resultantChartHom (K := S) d (MvPolynomial.map f p) =
      MvPolynomial.map f (resultantChartHom (K := R) d p) := by
  have hh : (resultantChartHom (K := S) d).toRingHom.comp (MvPolynomial.map f) =
      (MvPolynomial.map f).comp (resultantChartHom (K := R) d).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [resultantChartHom]
    · intro v
      rw [RingHom.comp_apply,RingHom.comp_apply,MvPolynomial.map_X]
      change MvPolynomial.aeval (R := S) (resultantChartCoefficient (K := S) d) (MvPolynomial.X v) =
        MvPolynomial.map f (MvPolynomial.aeval (R := R) (resultantChartCoefficient (K := R) d) (MvPolynomial.X v))
      rw [MvPolynomial.aeval_X,MvPolynomial.aeval_X]
      exact (map_resultantChartCoefficient f d v).symm
  exact RingHom.congr_fun hh p

lemma resultant_chart_kernel_base_change_principal {R S : Type}
    [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    {n : ℕ} (d : Fin (n+1) → ℕ) (r : MvPolynomial (ResultantVNP.CoeffVar d) R)
    (hr : RingHom.ker (resultantChartHom (K := R) d).toRingHom = Ideal.span {r}) :
    RingHom.ker (resultantChartHom (K := S) d).toRingHom =
      Ideal.span {MvPolynomial.map (algebraMap R S) r} :=
  flat_polynomial_kernel_principal _ _ (resultantChartHom_base_change (algebraMap R S) d) r hr

end APSCounting893.Main
end Component_15

section Component_16

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma universalForm_chart_eval {K : Type*} [CommRing K] {n : ℕ}
    (d : Fin (n+1) → ℕ) (c : ResultantVNP.CoeffVar d → K) (x : Fin n → K)
    (i : Fin (n+1)) :
    MvPolynomial.eval₂ (MvPolynomial.eval c) (Fin.cons 1 x) (universalForm (K := K) d i) =
      c (pureZeroCoefficient d i) + MvPolynomial.eval (Sum.elim (fun v : FreeResultantCoefficient d => c v.1) x)
        (resultantChartRemainder (K := K) d i) := by
  classical
  let e0 : {e : Fin (n+1) →₀ ℕ // ∑ j, e j = d i} :=
    ⟨Finsupp.single 0 (d i),by simp⟩
  have hp (e : {e : Fin (n+1) →₀ ℕ // ∑ j, e j = d i}) :
      e.1.prod (fun j k => (Fin.cons (1 : K) x : Fin (n+1) → K) j ^ k) = ∏ j : Fin n, x j ^ e.1 j.succ := by
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),Fin.prod_univ_succ]
    simp
  simp only [universalForm,MvPolynomial.eval₂_sum,MvPolynomial.eval₂_monomial,MvPolynomial.eval_X]
  simp_rw [hp]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e0)]
  have he0 : c ⟨i,e0⟩ * ∏ j : Fin n, x j ^ e0.1 j.succ = c (pureZeroCoefficient d i) := by
    simp [e0,pureZeroCoefficient]
  rw [he0]
  congr 1
  unfold resultantChartRemainder
  rw [map_sum,← Finset.add_sum_erase _ _ (Finset.mem_univ e0)]
  simp only [e0,dif_pos,map_zero,zero_add]
  apply Finset.sum_congr rfl
  intro e he
  have hn : e.1 ≠ Finsupp.single 0 (d i) := by
    intro hh
    exact (Finset.ne_of_mem_erase he) (Subtype.ext hh)
  simp [hn]

lemma resultant_chart_covers_unit_coordinate {K : Type*} [CommRing K] {n : ℕ}
    (d : Fin (n+1) → ℕ) (c : ResultantVNP.CoeffVar d → K) (x : Fin n → K)
    (hroot : ∀ i, MvPolynomial.eval₂ (MvPolynomial.eval c) (Fin.cons 1 x) (universalForm (K := K) d i) = 0) :
    ∀ v : ResultantVNP.CoeffVar d,
      MvPolynomial.eval (Sum.elim (fun v : FreeResultantCoefficient d => c v.1) x)
        (resultantChartCoefficient (K := K) d v) = c v := by
  classical
  intro v
  have hr := hroot v.1
  rw [universalForm_chart_eval] at hr
  unfold resultantChartCoefficient
  split_ifs with he
  · have hv : v = pureZeroCoefficient d v.1 :=
      congrArg (Sigma.mk v.1) (Subtype.ext he)
    rw [map_neg]
    rw [eq_comm,eq_neg_iff_add_eq_zero]
    rw [congrArg c hv]
    exact hr
  · simp

end APSCounting893.Main
end Component_16

section Component_17

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma eval_homogenize_monomial {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (f : R →+* K) (z : Fin (n + 1) → K) (e : Fin n →₀ ℕ) (c : R) (d : ℕ) :
    MvPolynomial.eval₂ f z (MvPolynomial.monomial
      (Finsupp.single 0 (d - e.sum (fun _ k => k)) + e.mapDomain Fin.succ) c) =
    f c * z 0 ^ (d - e.sum (fun _ k => k)) * e.prod (fun i k => z i.succ ^ k) := by
  classical
  rw [MvPolynomial.eval₂_monomial]
  rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  rw [Finsupp.prod_single_index (h := fun i k => z i ^ k) (pow_zero (z 0))]
  rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  ring

lemma finsupp_prod_scaled {K : Type} [Field K] {n : ℕ}
    (e : Fin n →₀ ℕ) (a : K) (x : Fin n → K) :
    e.prod (fun i k => (a * x i) ^ k) =
      a ^ e.sum (fun _ k => k) * e.prod (fun i k => x i ^ k) := by
  classical
  rw [e.prod_fintype _ (fun _ => pow_zero _), e.prod_fintype _ (fun _ => pow_zero _),
    e.sum_fintype _ (fun _ => rfl)]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

lemma eval_homogenize_scaled {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (f : R →+* K) (p : MvPolynomial (Fin n) R) (d : ℕ) (hd : p.totalDegree ≤ d)
    (a : K) (x : Fin n → K) :
    MvPolynomial.eval₂ f (Fin.cases a (fun i => a * x i)) (homogenizeAll d p) =
      a ^ d * MvPolynomial.eval₂ f x p := by
  classical
  rw [homogenizeAll, MvPolynomial.eval₂_sum]
  conv_rhs => rw [MvPolynomial.eval₂_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [eval_homogenize_monomial]
  simp only [Fin.cases_zero, Fin.cases_succ]
  rw [finsupp_prod_scaled]
  have hedeg : e.sum (fun _ k => k) ≤ d := (MvPolynomial.le_totalDegree he).trans hd
  have hpow : a ^ (d - e.sum (fun _ k => k)) * a ^ e.sum (fun _ k => k) = a ^ d := by
    rw [← pow_add, Nat.sub_add_cancel hedeg]
  calc
    f (p.coeff e) * a ^ (d - e.sum (fun _ k => k)) *
        (a ^ e.sum (fun _ k => k) * e.prod (fun i k => x i ^ k)) =
      (a ^ (d - e.sum (fun _ k => k)) * a ^ e.sum (fun _ k => k)) *
        (f (p.coeff e) * e.prod (fun i k => x i ^ k)) := by ring
    _ = _ := by rw [hpow]; rfl

lemma eval_homogenize_dehomogenize {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (f : R →+* K) (p : MvPolynomial (Fin n) R) (d : ℕ) (hd : p.totalDegree ≤ d)
    (z : Fin (n + 1) → K) (hz : z 0 ≠ 0) :
    MvPolynomial.eval₂ f z (homogenizeAll d p) =
      z 0 ^ d * MvPolynomial.eval₂ f (fun i => z i.succ / z 0) p := by
  have heq : Fin.cases (z 0) (fun i => z 0 * (z i.succ / z 0)) = z := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    simp [hz, mul_div_cancel₀, mul_comm]
  simpa only [heq] using eval_homogenize_scaled f p d hd (z 0) (fun i => z i.succ / z 0)

end APSCounting893.Main
end Component_17

section Component_18

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma projectiveRepresentative_rescaling {K : Type} [Field K] {n : ℕ}
    (z : Fin n → K) (hz : z ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ projectiveRepresentative z = a • z := by
  classical
  have hS : (Finset.univ.filter (fun i : Fin n => z i ≠ 0)).Nonempty := by
    by_contra h
    apply hz
    funext i
    by_contra hi
    exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let j := (Finset.univ.filter (fun i : Fin n => z i ≠ 0)).min' hS
  have hj : z j ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem _ hS)).2
  refine ⟨(z j)⁻¹, inv_ne_zero hj, ?_⟩
  rw [projectiveRepresentative, dif_pos hS]
  funext i
  simp only [div_eq_mul_inv, Pi.smul_apply, smul_eq_mul]
  exact mul_comm _ _

lemma projectiveRepresentative_ne_zero {K : Type} [Field K] {n : ℕ}
    (z : Fin n → K) (hz : z ≠ 0) : projectiveRepresentative z ≠ 0 := by
  obtain ⟨a, ha, he⟩ := projectiveRepresentative_rescaling z hz
  rw [he]
  exact smul_ne_zero ha hz

lemma homogenizeAll_homogeneous {R : Type} [CommRing R] {n : ℕ}
    (p : MvPolynomial (Fin n) R) (d : ℕ) (hd : p.totalDegree ≤ d) :
    (homogenizeAll d p).IsHomogeneous d := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro e he
  apply MvPolynomial.isHomogeneous_monomial
  rw [map_add, Finsupp.degree_single, Finsupp.degree_mapDomain, Finsupp.degree_eq_sum]
  have hsum : (∑ i : Fin n, e i) = e.sum (fun _ k => k) :=
    (e.sum_fintype (fun _ k => k) (fun _ => rfl)).symm
  rw [hsum]
  exact Nat.sub_add_cancel ((MvPolynomial.le_totalDegree he).trans hd)

lemma homogeneous_eval₂_scaled {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (p : MvPolynomial (Fin n) R) (d : ℕ) (hp : p.IsHomogeneous d)
    (f : R →+* K) (a : K) (z : Fin n → K) :
    MvPolynomial.eval₂ f (fun i => a * z i) p = a ^ d * MvPolynomial.eval₂ f z p := by
  classical
  conv_lhs => rw [MvPolynomial.eval₂_eq]
  conv_rhs => rw [MvPolynomial.eval₂_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  change f (p.coeff e) * e.prod (fun i k => (a * z i) ^ k) =
    a ^ d * (f (p.coeff e) * e.prod (fun i k => z i ^ k))
  rw [finsupp_prod_scaled]
  have hd := hp.degree_eq_sum_deg_support he
  change d = e.sum (fun _ k => k) at hd
  rw [← hd]
  ring

lemma homogeneous_root_projectiveRepresentative {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (p : MvPolynomial (Fin n) R) (d : ℕ) (hp : p.IsHomogeneous d)
    (f : R →+* K) (z : Fin n → K) (hz : z ≠ 0) (hroot : MvPolynomial.eval₂ f z p = 0) :
    MvPolynomial.eval₂ f (projectiveRepresentative z) p = 0 := by
  obtain ⟨a, ha, he⟩ := projectiveRepresentative_rescaling z hz
  rw [he]
  change MvPolynomial.eval₂ f (fun i => a * z i) p = 0
  rw [homogeneous_eval₂_scaled p d hp f a z, hroot, mul_zero]

end APSCounting893.Main
end Component_18

section Component_19

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma chart_kernel_vanishes_unit_root {K : Type} [Field K] {n : ℕ}
    (d : Fin (n+1) → ℕ) (q : MvPolynomial (ResultantVNP.CoeffVar d) K)
    (hq : MvPolynomial.eval₂ MvPolynomial.C (resultantChartCoefficient (K := K) d) q = 0)
    (c : ResultantVNP.CoeffVar d → K) (x : Fin n → K)
    (hroot : ∀ i, MvPolynomial.eval₂ (MvPolynomial.eval c) (Fin.cons 1 x) (universalForm (K := K) d i) = 0) :
    MvPolynomial.eval c q = 0 := by
  classical
  let b : ResultantChartVariable d → K := Sum.elim (fun v : FreeResultantCoefficient d => c v.1) x
  have hh : (MvPolynomial.eval b).comp
      (MvPolynomial.eval₂Hom MvPolynomial.C (resultantChartCoefficient (K := K) d)) = MvPolynomial.eval c := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro v
      simp only [RingHom.comp_apply,MvPolynomial.eval₂Hom_X',MvPolynomial.eval_X]
      exact resultant_chart_covers_unit_coordinate d c x hroot v
  have he := congrArg (MvPolynomial.eval b) hq
  change ((MvPolynomial.eval b).comp (MvPolynomial.eval₂Hom MvPolynomial.C (resultantChartCoefficient d))) q = 0 at he
  rwa [hh] at he

lemma chart_kernel_vanishes_nonzero_coordinate_root {K : Type} [Field K] {n : ℕ}
    (d : Fin (n+1) → ℕ) (q : MvPolynomial (ResultantVNP.CoeffVar d) K)
    (hq : MvPolynomial.eval₂ MvPolynomial.C (resultantChartCoefficient (K := K) d) q = 0)
    (c : ResultantVNP.CoeffVar d → K) (x : Fin (n+1) → K) (hx : x 0 ≠ 0)
    (hroot : ∀ i, MvPolynomial.eval₂ (MvPolynomial.eval c) x (universalForm (K := K) d i) = 0) :
    MvPolynomial.eval c q = 0 := by
  let y : Fin n → K := fun j => (x 0)⁻¹ * x j.succ
  apply chart_kernel_vanishes_unit_root d q hq c y
  intro i
  have hy : (Fin.cons 1 y : Fin (n+1) → K) = fun j => (x 0)⁻¹ * x j := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [hx]
    · rfl
  rw [hy,homogeneous_eval₂_scaled _ _ (universalForm_homogeneous d i),hroot i,mul_zero]

end APSCounting893.Main
end Component_19

section Component_20

set_option autoImplicit false
namespace APSCounting893.Main

lemma polynomial_zero_of_eval_zero_off_zero {K : Type*} [Field K] [Infinite K]
    (p : Polynomial K) (hp : ∀ s : K, s ≠ 0 → p.eval s = 0) : p = 0 := by
  have hh : Polynomial.X * p = 0 := Polynomial.zero_of_eval_zero _ (by
    intro s
    by_cases hs : s = 0
    · simp [hs]
    · simp [hp s hs])
  exact (mul_eq_zero.mp hh).resolve_left Polynomial.X_ne_zero

end APSCounting893.Main
end Component_20

section Component_21

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def projectiveRootPath {K : Type} [Field K] {n : ℕ}
    (x : Fin (n+1) → K) : Fin (n+1) → Polynomial K :=
  fun k => Polynomial.C (x k) + if k = 0 then Polynomial.X else 0

noncomputable def rootPathRemainder {K : Type} [Field K] {n : ℕ}
    (d : Fin (n+1) → ℕ) (c : ResultantVNP.CoeffVar d → K)
    (x : Fin (n+1) → K) (j i : Fin (n+1)) : Polynomial K :=
  ∑ e : {e : Fin (n+1) →₀ ℕ // ∑ k, e k = d i},
    if e.1 = Finsupp.single j (d i) then 0 else
      Polynomial.C (c ⟨i,e⟩) * e.1.prod (fun k l => projectiveRootPath x k ^ l)

noncomputable def rootPathCoefficient {K : Type} [Field K] {n : ℕ}
    (d : Fin (n+1) → ℕ) (c : ResultantVNP.CoeffVar d → K)
    (x : Fin (n+1) → K) (j : Fin (n+1)) (v : ResultantVNP.CoeffVar d) : Polynomial K :=
  if v.2.1 = Finsupp.single j (d v.1) then
    -rootPathRemainder d c x j v.1 * Polynomial.C ((x j ^ d v.1)⁻¹)
  else Polynomial.C (c v)

lemma rootPath_satisfies_forms {K : Type} [Field K] {n : ℕ}
    (d : Fin (n+1) → ℕ) (c : ResultantVNP.CoeffVar d → K)
    (x : Fin (n+1) → K) (j : Fin (n+1)) (hj : j ≠ 0) (hx : x j ≠ 0)
    (i : Fin (n+1)) :
    MvPolynomial.eval₂
      (MvPolynomial.eval₂Hom Polynomial.C (rootPathCoefficient d c x j))
      (projectiveRootPath x) (universalForm (K := K) d i) = 0 := by
  classical
  let ej : {e : Fin (n+1) →₀ ℕ // ∑ k, e k = d i} :=
    ⟨Finsupp.single j (d i),by simp⟩
  simp only [universalForm,MvPolynomial.eval₂_sum,MvPolynomial.eval₂_monomial,
    MvPolynomial.eval₂Hom_X']
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ej)]
  have heval : ej.1.prod (fun k l => projectiveRootPath x k ^ l) = Polynomial.C (x j ^ d i) := by
    simp [ej,projectiveRootPath,hj]
  rw [heval]
  rw [show rootPathCoefficient d c x j ⟨i,ej⟩ =
      -rootPathRemainder d c x j i * Polynomial.C ((x j ^ d i)⁻¹) by
    simp [rootPathCoefficient,ej]]
  rw [mul_assoc,← map_mul,inv_mul_cancel₀ (pow_ne_zero _ hx),map_one,mul_one]
  have hr : rootPathRemainder d c x j i =
      ∑ e ∈ Finset.univ.erase ej, rootPathCoefficient d c x j ⟨i,e⟩ *
        e.1.prod (fun k l => projectiveRootPath x k ^ l) := by
    unfold rootPathRemainder
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ej)]
    simp only [ej,eq_self_iff_true,ite_true,zero_add]
    apply Finset.sum_congr rfl
    intro e he
    have hn : e.1 ≠ Finsupp.single j (d i) := by
      intro h
      exact (Finset.ne_of_mem_erase he) (Subtype.ext h)
    simp [hn,rootPathCoefficient]
  rw [hr,neg_add_cancel]

end APSCounting893.Main
end Component_21

section Component_22

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma universalForm_rootPath_constant_term {K : Type} [Field K] {n : ℕ}
    (d : Fin (n+1) → ℕ) (c : ResultantVNP.CoeffVar d → K)
    (x : Fin (n+1) → K) (j i : Fin (n+1)) :
    MvPolynomial.eval₂ (MvPolynomial.eval c) x (universalForm (K := K) d i) =
      c ⟨i,⟨Finsupp.single j (d i),by simp⟩⟩ * x j ^ d i +
        Polynomial.eval 0 (rootPathRemainder d c x j i) := by
  classical
  let ej : {e : Fin (n+1) →₀ ℕ // ∑ k, e k = d i} :=
    ⟨Finsupp.single j (d i),by simp⟩
  simp only [universalForm,MvPolynomial.eval₂_sum,MvPolynomial.eval₂_monomial,MvPolynomial.eval_X]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ej)]
  have heval : ej.1.prod (fun k l => x k ^ l) = x j ^ d i := by simp [ej]
  rw [heval]
  congr 1
  unfold rootPathRemainder
  rw [Polynomial.eval_finsetSum,← Finset.add_sum_erase _ _ (Finset.mem_univ ej)]
  simp only [ej,eq_self_iff_true,ite_true,Polynomial.eval_zero,zero_add]
  apply Finset.sum_congr rfl
  intro e he
  have hn : e.1 ≠ Finsupp.single j (d i) := by
    intro h
    exact (Finset.ne_of_mem_erase he) (Subtype.ext h)
  simp [hn,Finsupp.prod,projectiveRootPath,Polynomial.eval_prod,apply_ite]

lemma rootPathCoefficient_at_zero {K : Type} [Field K] {n : ℕ}
    (d : Fin (n+1) → ℕ) (c : ResultantVNP.CoeffVar d → K)
    (x : Fin (n+1) → K) (j : Fin (n+1)) (hx : x j ≠ 0)
    (hroot : ∀ i, MvPolynomial.eval₂ (MvPolynomial.eval c) x (universalForm (K := K) d i) = 0) :
    ∀ v, Polynomial.eval 0 (rootPathCoefficient d c x j v) = c v := by
  classical
  intro v
  unfold rootPathCoefficient
  split_ifs with he
  · have hr := hroot v.1
    rw [universalForm_rootPath_constant_term d c x j v.1] at hr
    have hv : v = ⟨v.1,⟨Finsupp.single j (d v.1),by simp⟩⟩ :=
      congrArg (Sigma.mk v.1) (Subtype.ext he)
    have hc := congrArg c hv
    have hneg : -Polynomial.eval 0 (rootPathRemainder d c x j v.1) = c v * x j ^ d v.1 := by
      rw [hc]
      linear_combination -hr
    rw [Polynomial.eval_mul,Polynomial.eval_neg,Polynomial.eval_C,hneg,mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hx),mul_one]
  · exact Polynomial.eval_C

end APSCounting893.Main
end Component_22

section Component_23

set_option autoImplicit false
set_option maxHeartbeats 4000000
open MvPolynomial
namespace APSCounting893.Main

lemma polynomial_eval_mv_substitution {K σ : Type} [CommRing K]
    (c : σ → Polynomial K) (s : K) (q : MvPolynomial σ K) :
    Polynomial.eval s (MvPolynomial.eval₂ Polynomial.C c q) =
      MvPolynomial.eval (fun v => Polynomial.eval s (c v)) q := by
  have hh : (Polynomial.evalRingHom s).comp (MvPolynomial.eval₂Hom Polynomial.C c) =
      MvPolynomial.eval (fun v => Polynomial.eval s (c v)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro v
      simp
  exact RingHom.congr_fun hh q

lemma polynomial_eval_universal_system {K σ : Type} [CommRing K] {n : ℕ}
    (c : σ → Polynomial K) (x : Fin n → Polynomial K) (s : K)
    (U : MvPolynomial (Fin n) (MvPolynomial σ K)) :
    Polynomial.eval s (MvPolynomial.eval₂ (MvPolynomial.eval₂Hom Polynomial.C c) x U) =
      MvPolynomial.eval₂ (MvPolynomial.eval (fun v => Polynomial.eval s (c v)))
        (fun j => Polynomial.eval s (x j)) U := by
  have hco : (Polynomial.evalRingHom s).comp (MvPolynomial.eval₂Hom Polynomial.C c) =
      MvPolynomial.eval (fun v => Polynomial.eval s (c v)) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro v; simp
  have hh := MvPolynomial.eval₂_comp_left (Polynomial.evalRingHom s)
    (MvPolynomial.eval₂Hom Polynomial.C c) x U
  rw [hco] at hh
  exact hh

end APSCounting893.Main
end Component_23

section Component_24

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma chart_kernel_vanishes_all_projective_roots {K : Type} [Field K] [Infinite K] {n : ℕ}
    (d : Fin (n+1) → ℕ) (q : MvPolynomial (ResultantVNP.CoeffVar d) K)
    (hq : MvPolynomial.eval₂ MvPolynomial.C (resultantChartCoefficient (K := K) d) q = 0)
    (c : ResultantVNP.CoeffVar d → K) (x : Fin (n+1) → K) (hx : x ≠ 0)
    (hroot : ∀ i, MvPolynomial.eval₂ (MvPolynomial.eval c) x (universalForm (K := K) d i) = 0) :
    MvPolynomial.eval c q = 0 := by
  classical
  by_cases hx0 : x 0 ≠ 0
  · exact chart_kernel_vanishes_nonzero_coordinate_root d q hq c x hx0 hroot
  have hx0 : x 0 = 0 := not_ne_iff.mp hx0
  obtain ⟨j,hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  have hj0 : j ≠ 0 := by intro h; exact hj (h ▸ hx0)
  let cp := rootPathCoefficient d c x j
  let xp := projectiveRootPath x
  let p : Polynomial K := MvPolynomial.eval₂ Polynomial.C cp q
  have hp : p = 0 := polynomial_zero_of_eval_zero_off_zero p (by
    intro s hs
    rw [polynomial_eval_mv_substitution]
    let cs : ResultantVNP.CoeffVar d → K := fun v => Polynomial.eval s (cp v)
    let xs : Fin (n+1) → K := fun k => Polynomial.eval s (xp k)
    apply chart_kernel_vanishes_nonzero_coordinate_root d q hq cs xs
    · simpa [xs,xp,projectiveRootPath,hx0] using hs
    · intro i
      have hh := congrArg (Polynomial.eval s) (rootPath_satisfies_forms d c x j hj0 hj i)
      rw [Polynomial.eval_zero,polynomial_eval_universal_system] at hh
      exact hh)
  have hzero := congrArg (Polynomial.eval 0) hp
  rw [Polynomial.eval_zero,polynomial_eval_mv_substitution] at hzero
  have hcp : (fun v => Polynomial.eval 0 (cp v)) = c := funext (rootPathCoefficient_at_zero d c x j hj hroot)
  rwa [hcp] at hzero

end APSCounting893.Main
end Component_24

section Component_25

set_option autoImplicit false
set_option maxHeartbeats 4000000
open MvPolynomial
namespace APSCounting893.Main

lemma eval_mv_substitution {K σ τ : Type} [CommRing K]
    (c : σ → MvPolynomial τ K) (b : τ → K) (q : MvPolynomial σ K) :
    MvPolynomial.eval b (MvPolynomial.eval₂ MvPolynomial.C c q) =
      MvPolynomial.eval (fun v => MvPolynomial.eval b (c v)) q := by
  have hh : (MvPolynomial.eval b).comp (MvPolynomial.eval₂Hom MvPolynomial.C c) =
      MvPolynomial.eval (fun v => MvPolynomial.eval b (c v)) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro v; simp
  exact RingHom.congr_fun hh q

lemma eval_universal_system {K σ τ : Type} [CommRing K] {n : ℕ}
    (c : σ → MvPolynomial τ K) (x : Fin n → MvPolynomial τ K) (b : τ → K)
    (U : MvPolynomial (Fin n) (MvPolynomial σ K)) :
    MvPolynomial.eval b (MvPolynomial.eval₂ (MvPolynomial.eval₂Hom MvPolynomial.C c) x U) =
      MvPolynomial.eval₂ (MvPolynomial.eval (fun v => MvPolynomial.eval b (c v)))
        (fun j => MvPolynomial.eval b (x j)) U := by
  have hco : (MvPolynomial.eval b).comp (MvPolynomial.eval₂Hom MvPolynomial.C c) =
      MvPolynomial.eval (fun v => MvPolynomial.eval b (c v)) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro v; simp
  have hh := MvPolynomial.eval₂_comp_left (MvPolynomial.eval b)
    (MvPolynomial.eval₂Hom MvPolynomial.C c) x U
  rw [hco] at hh
  exact hh

end APSCounting893.Main
end Component_25

section Component_26

set_option autoImplicit false
set_option maxHeartbeats 4000000
open MvPolynomial
namespace APSCounting893.Main

lemma projective_root_locus_algebraic {K : Type*} [Field K] [IsAlgClosed K]
    {σ : Type*} {n m : ℕ}
    (U : Fin m → MvPolynomial (Fin n) (MvPolynomial σ K)) (d : Fin m → ℕ)
    (hU : ∀ i, (U i).IsHomogeneous (d i)) :
    let Z : Set (σ → K) := {a | ∃ x : Fin n → K, x ≠ 0 ∧
      ∀ i, MvPolynomial.eval₂ (MvPolynomial.eval a) x (U i) = 0}
    MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K Z) = Z := by
  classical
  intro Z
  apply Set.Subset.antisymm
  · intro a ha
    by_contra hz
    have hno (x : Fin n → K) (hx : ∀ i, MvPolynomial.eval₂ (MvPolynomial.eval a) x (U i) = 0) : x = 0 := by
      by_contra h
      exact hz ⟨x,h,hx⟩
    obtain ⟨q,hqa,hq⟩ := no_projective_root_polynomial_certificate U d hU a hno
    have hmem : q ∈ MvPolynomial.vanishingIdeal K Z := by
      intro b hb
      simpa only [MvPolynomial.aeval_eq_eval] using hq b hb
    have hh := ha q hmem
    rw [MvPolynomial.aeval_eq_eval,hqa] at hh
    exact one_ne_zero hh
  · exact MvPolynomial.zeroLocus_vanishingIdeal_le _

end APSCounting893.Main
end Component_26

section Component_27

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma projective_root_vanishing_ideal_eq_chart_kernel {K : Type} [Field K] [Infinite K] {n : ℕ}
    (d : Fin (n+1) → ℕ) :
    let Z : Set (ResultantVNP.CoeffVar d → K) := {c | ∃ x : Fin (n+1) → K,
      x ≠ 0 ∧ ∀ i, MvPolynomial.eval₂ (MvPolynomial.eval c) x (universalForm (K := K) d i) = 0}
    MvPolynomial.vanishingIdeal K Z = RingHom.ker (resultantChartHom (K := K) d).toRingHom := by
  classical
  intro Z
  ext q
  constructor
  · intro hq
    change resultantChartHom (K := K) d q = 0
    change MvPolynomial.eval₂ MvPolynomial.C (resultantChartCoefficient (K := K) d) q = 0
    apply MvPolynomial.funext
    intro b
    rw [eval_mv_substitution]
    let c : ResultantVNP.CoeffVar d → K := fun v => MvPolynomial.eval b (resultantChartCoefficient (K := K) d v)
    let x : Fin (n+1) → K := fun j => MvPolynomial.eval b (resultantChartRoot (K := K) d j)
    have hx : x ≠ 0 := by
      intro hh
      have hz := congrFun hh 0
      simpa [x,resultantChartRoot] using hz
    have hroot (i : Fin (n+1)) : MvPolynomial.eval₂ (MvPolynomial.eval c) x (universalForm (K := K) d i) = 0 := by
      have hh := congrArg (MvPolynomial.eval b) (resultant_chart_is_root (K := K) d i)
      rw [map_zero,eval_universal_system] at hh
      exact hh
    simpa only [MvPolynomial.aeval_eq_eval,map_zero] using hq c ⟨x,hx,hroot⟩
  · intro hq
    intro c hc
    obtain ⟨x,hx,hroot⟩ := hc
    change MvPolynomial.eval₂ MvPolynomial.C (resultantChartCoefficient (K := K) d) q = 0 at hq
    simpa only [MvPolynomial.aeval_eq_eval] using
      chart_kernel_vanishes_all_projective_roots d q hq c x hx hroot

end APSCounting893.Main
end Component_27

section Component_28

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma exists_integer_irreducible_root_equation {n : ℕ}
    (d : Fin (n+1) → ℕ) (hd : ∀ i, 0 < d i) :
    ∃ r : MvPolynomial (ResultantVNP.CoeffVar d) ℤ,
      RingHom.ker (resultantChartHom (K := ℤ) d).toRingHom = Ideal.span {r} ∧
      Irreducible (MvPolynomial.map (Int.castRingHom ℂ) r) ∧
      (∀ c : ResultantVNP.CoeffVar d → ℂ,
        MvPolynomial.eval c (MvPolynomial.map (Int.castRingHom ℂ) r) = 0 ↔
          ∃ x : Fin (n+1) → ℂ, x ≠ 0 ∧
            ∀ i, MvPolynomial.eval₂ (MvPolynomial.eval c) x (universalForm (K := ℂ) d i) = 0) := by
  classical
  obtain ⟨hI,hprincipal⟩ := resultantChartHom_kernel_nonzero_principal (K := ℤ) d hd
  obtain ⟨r,hgen⟩ := hprincipal
  change RingHom.ker (resultantChartHom (K := ℤ) d).toRingHom = Ideal.span {r} at hgen
  have hr0 : r ≠ 0 := by
    intro hr
    apply hI
    rw [hgen,hr]
    exact Submodule.span_eq_bot.mpr (by simp)
  have hbase := resultant_chart_kernel_base_change_principal (R := ℤ) (S := ℂ) d r hgen
  have hcast : algebraMap ℤ ℂ = Int.castRingHom ℂ := rfl
  rw [hcast] at hbase
  have hrC0 : MvPolynomial.map (Int.castRingHom ℂ) r ≠ 0 := by
    intro hh
    apply hr0
    exact (MvPolynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective) (hh.trans (map_zero _).symm)
  have hprime : (Ideal.span {MvPolynomial.map (Int.castRingHom ℂ) r}).IsPrime := by
    rw [← hbase]
    exact RingHom.ker_isPrime _
  have hirr := ((Ideal.span_singleton_prime hrC0).mp hprime).irreducible
  refine ⟨r,hgen,hirr,?_⟩
  have hloc := projective_root_locus_algebraic (universalForm (K := ℂ) d) d
    (universalForm_homogeneous d)
  dsimp only at hloc
  rw [projective_root_vanishing_ideal_eq_chart_kernel d,hbase] at hloc
  intro c
  have hh := Set.ext_iff.mp hloc c
  simpa only [MvPolynomial.zeroLocus_span,Set.mem_setOf_eq,Set.mem_singleton_iff,
    forall_eq,MvPolynomial.aeval_eq_eval] using hh

end APSCounting893.Main
end Component_28

section Component_29

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def diagonalCoefficient {K : Type} [CommRing K] {n : ℕ}
    (d : Fin n → ℕ) (v : ResultantVNP.CoeffVar d) : K :=
  if v.2.1 = Finsupp.single v.1 (d v.1) then 1 else 0

lemma universalForm_diagonal {K : Type} [CommRing K] {n : ℕ}
    (d : Fin n → ℕ) (i : Fin n) :
    MvPolynomial.map (MvPolynomial.eval (diagonalCoefficient (K := K) d))
      (universalForm (K := K) d i) = MvPolynomial.X i ^ d i := by
  classical
  let ei : {e : Fin n →₀ ℕ // ∑ j, e j = d i} :=
    ⟨Finsupp.single i (d i),by simp⟩
  simp only [universalForm,map_sum,MvPolynomial.map_monomial,MvPolynomial.eval_X,diagonalCoefficient]
  rw [Finset.sum_eq_single ei]
  · simp [ei,MvPolynomial.X_pow_eq_monomial]
  · intro e he hne
    have hh : e.1 ≠ Finsupp.single i (d i) := by intro h; exact hne (Subtype.ext h)
    simp [hh]
  · simp

lemma exists_integer_macaulay_certificate {n : ℕ} (d : Fin (n+1) → ℕ)
    (hd : ∀ i, 0 < d i) :
    ∃ q : MvPolynomial (ResultantVNP.CoeffVar d) ℤ,
      MvPolynomial.eval (diagonalCoefficient (K := ℤ) d) q = 1 ∧
      resultantChartHom (K := ℤ) d q = 0 := by
  classical
  let D := (∑ i, (d i - 1)) + 1
  have hi (e : DegreeMonomial (n+1) D) : ∃ i, d i ≤ e.1 i := by
    by_contra h
    push Not at h
    have hh : (∑ i, e.1 i) ≤ ∑ i, (d i - 1) :=
      Finset.sum_le_sum (fun i _ => by have := h i; omega)
    have he := e.2
    rw [Finsupp.degree_eq_sum] at he
    dsimp [D] at he
    omega
  choose idx hidx using hi
  have hle (e : DegreeMonomial (n+1) D) : Finsupp.single (idx e) (d (idx e)) ≤ e.1 :=
    Finsupp.single_le_iff.mpr (hidx e)
  have hdeg (e : DegreeMonomial (n+1) D) :
      (e.1 - Finsupp.single (idx e) (d (idx e))).degree + d (idx e) = D := by
    have hh := congrArg Finsupp.degree (tsub_add_cancel_of_le (hle e))
    rw [map_add,Finsupp.degree_single,e.2] at hh
    exact hh
  let Q (e : DegreeMonomial (n+1) D) :
      MvPolynomial (Fin (n+1)) (MvPolynomial (ResultantVNP.CoeffVar d) ℤ) :=
    MvPolynomial.monomial (e.1 - Finsupp.single (idx e) (d (idx e))) 1 * universalForm d (idx e)
  have hQ (e : DegreeMonomial (n+1) D) : (Q e).IsHomogeneous D := by
    have hh := (MvPolynomial.isHomogeneous_monomial (d := e.1 - Finsupp.single (idx e) (d (idx e))) (1 : MvPolynomial (ResultantVNP.CoeffVar d) ℤ) rfl).mul
      (universalForm_homogeneous d (idx e))
    simpa only [hdeg e] using hh
  let A : Matrix (DegreeMonomial (n+1) D) (DegreeMonomial (n+1) D)
      (MvPolynomial (ResultantVNP.CoeffVar d) ℤ) := fun e f => (Q e).coeff f.1
  have hdiag (e : DegreeMonomial (n+1) D) :
      MvPolynomial.map (MvPolynomial.eval (diagonalCoefficient (K := ℤ) d)) (Q e) =
        MvPolynomial.monomial e.1 1 := by
    simp only [Q,map_mul,MvPolynomial.map_monomial,map_one,universalForm_diagonal,
      MvPolynomial.X_pow_eq_monomial,MvPolynomial.monomial_mul,one_mul,
      tsub_add_cancel_of_le (hle e)]
  refine ⟨A.det,?_,?_⟩
  · rw [RingHom.map_det]
    have hmat : (MvPolynomial.eval (diagonalCoefficient (K := ℤ) d)).mapMatrix A = 1 := by
      ext e f
      change MvPolynomial.eval (diagonalCoefficient d) ((Q e).coeff f.1) = if e = f then 1 else 0
      have hh := congrArg (MvPolynomial.coeff f.1) (hdiag e)
      rw [MvPolynomial.coeff_map,MvPolynomial.coeff_monomial] at hh
      simpa only [Subtype.val_inj] using hh
    rw [hmat,Matrix.det_one]
  · let φ := (resultantChartHom (K := ℤ) d).toRingHom
    let x := resultantChartRoot (K := ℤ) d
    let v : DegreeMonomial (n+1) D → MvPolynomial (ResultantChartVariable d) ℤ :=
      fun e => ∏ j : Fin (n+1), x j ^ e.1 j
    have hvec : (φ.mapMatrix A).mulVec v = 0 := by
      funext e
      change (∑ f : DegreeMonomial (n+1) D,
        φ ((Q e).coeff f.1) * ∏ j : Fin (n+1), x j ^ f.1 j) = 0
      rw [← eval₂_homogeneous_sum _ _ _ (hQ e)]
      change MvPolynomial.eval₂ φ x
        (MvPolynomial.monomial (e.1 - Finsupp.single (idx e) (d (idx e))) 1 * universalForm d (idx e)) = 0
      rw [MvPolynomial.eval₂_mul]
      have hh := resultant_chart_is_root (K := ℤ) d (idx e)
      change MvPolynomial.eval₂ φ x (universalForm d (idx e)) = 0 at hh
      rw [hh,mul_zero]
    by_contra hh
    have hdet : (φ.mapMatrix A).det ≠ 0 := by rw [← RingHom.map_det]; exact hh
    have hv := Matrix.eq_zero_of_mulVec_eq_zero hdet hvec
    let e0 : DegreeMonomial (n+1) D := ⟨Finsupp.single 0 D,by simp⟩
    have he := congrFun hv e0
    have hval : v e0 = 1 := by simp [v,e0,x,resultantChartRoot,Finsupp.single_apply]
    rw [hval] at he
    exact one_ne_zero he

end APSCounting893.Main
end Component_29

section Component_30

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma form_eq_specialized_universal {n : ℕ} (d : Fin n → ℕ)
    (c : ResultantVNP.CoeffVar d → ℂ) (i : Fin n) :
    ResultantVNP.form d c i = MvPolynomial.map (MvPolynomial.eval c) (universalForm (K := ℂ) d i) := by
  classical
  simp only [ResultantVNP.form,universalForm,map_sum,MvPolynomial.map_monomial,MvPolynomial.eval_X]

lemma exists_normalized_multivariate_resultant {n : ℕ} (d : Fin (n+1) → ℕ)
    (hd : ∀ i, 0 < d i) :
    ∃ R : MvPolynomial (ResultantVNP.CoeffVar d) ℤ, ResultantVNP.IsMultivariateResultant d R := by
  classical
  obtain ⟨r,hrker,hirr,hroot⟩ := exists_integer_irreducible_root_equation d hd
  obtain ⟨q,hdiag,hqker⟩ := exists_integer_macaulay_certificate d hd
  have hqr : q ∈ Ideal.span {r} := by
    rw [← hrker]
    exact hqker
  obtain ⟨h,hqh⟩ := Ideal.mem_span_singleton.mp hqr
  have hunit : MvPolynomial.eval (diagonalCoefficient (K := ℤ) d) r *
      MvPolynomial.eval (diagonalCoefficient (K := ℤ) d) h = 1 := by
    rw [← map_mul,← hqh]
    exact hdiag
  have hcriterion : ∀ c : ResultantVNP.CoeffVar d → ℂ,
      MvPolynomial.eval c (MvPolynomial.map (Int.castRingHom ℂ) r) = 0 ↔
        ∃ x : Fin (n+1) → ℂ, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (ResultantVNP.form d c i) = 0 := by
    intro c
    rw [hroot c]
    apply exists_congr
    intro x
    apply and_congr_right
    intro hx
    apply forall_congr'
    intro i
    rw [form_eq_specialized_universal,MvPolynomial.eval_map]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hunit with hplus | hminus
  · refine ⟨r,hcriterion,?_,hirr⟩
    exact hplus
  · refine ⟨-r,?_,?_,?_⟩
    · intro c
      simpa only [map_neg,neg_eq_zero] using hcriterion c
    · change MvPolynomial.eval (diagonalCoefficient (K := ℤ) d) (-r) = 1
      rw [map_neg,hminus,neg_neg]
    · rw [map_neg]
      have hass : Associated (MvPolynomial.map (Int.castRingHom ℂ) r)
          (-MvPolynomial.map (Int.castRingHom ℂ) r) := (Associated.refl _).neg_right
      exact hass.irreducible_iff.mp hirr

end APSCounting893.Main
end Component_30

section Component_31

set_option autoImplicit false
namespace APSCounting893.Main

lemma universalResultant_specification {n : ℕ} (d : Fin (n+1) → ℕ)
    (hd : ∀ i, 0 < d i) : ResultantVNP.IsMultivariateResultant d (universalResultant d) :=
  Classical.epsilon_spec (exists_normalized_multivariate_resultant d hd)

end APSCounting893.Main
end Component_31

section Component_32

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma normalized_resultant_generates_integer_kernel {n : ℕ} (d : Fin (n+1) → ℕ)
    (hd : ∀ i, 0 < d i) (R : MvPolynomial (ResultantVNP.CoeffVar d) ℤ)
    (hR : ResultantVNP.IsMultivariateResultant d R) :
    RingHom.ker (resultantChartHom (K := ℤ) d).toRingHom = Ideal.span {R} := by
  classical
  obtain ⟨r,hrker,hirr,hroot⟩ := exists_integer_irreducible_root_equation d hd
  let RC := MvPolynomial.map (Int.castRingHom ℂ) R
  have hRC : RC ∈ RingHom.ker (resultantChartHom (K := ℂ) d).toRingHom := by
    rw [← projective_root_vanishing_ideal_eq_chart_kernel d]
    intro c hc
    obtain ⟨x,hx,hroots⟩ := hc
    have he : ∀ i, MvPolynomial.eval x (ResultantVNP.form d c i) = 0 := by
      intro i
      rw [form_eq_specialized_universal,MvPolynomial.eval_map]
      exact hroots i
    simpa only [MvPolynomial.aeval_eq_eval] using (hR.1 c).mpr ⟨x,hx,he⟩
  have hRker : R ∈ RingHom.ker (resultantChartHom (K := ℤ) d).toRingHom := by
    change resultantChartHom (K := ℤ) d R = 0
    have hh : MvPolynomial.map (Int.castRingHom ℂ) (resultantChartHom (K := ℤ) d R) = 0 := by
      rw [← resultantChartHom_base_change]
      exact hRC
    exact (MvPolynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective) (hh.trans (map_zero _).symm)
  rw [hrker,Ideal.mem_span_singleton] at hRker
  obtain ⟨h,hRh⟩ := hRker
  have heC : RC = MvPolynomial.map (Int.castRingHom ℂ) r * MvPolynomial.map (Int.castRingHom ℂ) h := by
    dsimp only [RC]
    rw [hRh,map_mul]
  have huC : IsUnit (MvPolynomial.map (Int.castRingHom ℂ) h) :=
    ((hR.2.2).isUnit_or_isUnit heC).resolve_left hirr.not_isUnit
  have hdeg := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp huC).2
  have hcC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg
  have hc : h = MvPolynomial.C (h.coeff 0) := by
    apply MvPolynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective
    rw [MvPolynomial.map_C]
    simpa only [MvPolynomial.coeff_map] using hcC
  have he : MvPolynomial.eval (diagonalCoefficient (K := ℤ) d) r * h.coeff 0 = 1 := by
    have hh := hR.2.1
    change MvPolynomial.eval (diagonalCoefficient (K := ℤ) d) R = 1 at hh
    rw [hRh,hc,map_mul,MvPolynomial.eval_C] at hh
    exact hh
  have hu : IsUnit h := by
    rw [hc]
    exact (IsUnit.of_mul_eq_one (MvPolynomial.eval (diagonalCoefficient (K := ℤ) d) r)
      (by simpa only [mul_comm] using he)).map MvPolynomial.C
  rw [hrker,hRh,Ideal.span_singleton_mul_right_unit hu]

lemma normalized_resultant_root_criterion_over_field {K : Type} [Field K] [IsAlgClosed K]
    [CharZero K] {n : ℕ} (d : Fin (n+1) → ℕ) (hd : ∀ i, 0 < d i)
    (R : MvPolynomial (ResultantVNP.CoeffVar d) ℤ) (hR : ResultantVNP.IsMultivariateResultant d R)
    (c : ResultantVNP.CoeffVar d → K) :
    MvPolynomial.eval c (MvPolynomial.map (Int.castRingHom K) R) = 0 ↔
      ∃ x : Fin (n+1) → K, x ≠ 0 ∧
        ∀ i, MvPolynomial.eval₂ (MvPolynomial.eval c) x (universalForm (K := K) d i) = 0 := by
  have hgen := normalized_resultant_generates_integer_kernel d hd R hR
  have hbase := resultant_chart_kernel_base_change_principal (R := ℤ) (S := K) d R hgen
  change RingHom.ker (resultantChartHom (K := K) d).toRingHom = Ideal.span {MvPolynomial.map (Int.castRingHom K) R} at hbase
  have hloc := projective_root_locus_algebraic (universalForm (K := K) d) d (universalForm_homogeneous d)
  dsimp only at hloc
  rw [projective_root_vanishing_ideal_eq_chart_kernel d,hbase] at hloc
  have hh := Set.ext_iff.mp hloc c
  simpa only [MvPolynomial.zeroLocus_span,Set.mem_setOf_eq,Set.mem_singleton_iff,
    forall_eq,MvPolynomial.aeval_eq_eval] using hh

end APSCounting893.Main
end Component_32

section Component_33

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma specialize_universalForm_of_homogeneous {K : Type} [CommRing K] {n : ℕ}
    (d : Fin n → ℕ) (G : Fin n → MvPolynomial (Fin n) K)
    (hG : ∀ i, (G i).IsHomogeneous (d i)) (i : Fin n) :
    MvPolynomial.map (MvPolynomial.eval (fun v : ResultantVNP.CoeffVar d => (G v.1).coeff v.2.1))
      (universalForm (K := K) d i) = G i := by
  classical
  apply MvPolynomial.ext
  intro e
  simp only [universalForm,map_sum,MvPolynomial.map_monomial,MvPolynomial.eval_X,MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial]
  by_cases he : e.degree = d i
  · let e' : {a : Fin n →₀ ℕ // ∑ j, a j = d i} := ⟨e,by simpa only [Finsupp.degree_eq_sum] using he⟩
    rw [Finset.sum_eq_single e']
    · simp [e']
    · intro a ha hne
      have h : a.1 ≠ e := by intro h; exact hne (Subtype.ext h)
      simp [h]
    · simp
  · rw [(hG i).coeff_eq_zero he]
    apply Finset.sum_eq_zero
    intro a ha
    have h : a.1 ≠ e := by
      intro h
      exact he (by simpa only [h,Finsupp.degree_eq_sum] using a.2)
    simp [h]

lemma homogeneousResultant_zero_iff {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    {n : ℕ} (d : Fin (n+1) → ℕ) (hd : ∀ i, 0 < d i)
    (G : Fin (n+1) → MvPolynomial (Fin (n+1)) K) (hG : ∀ i, (G i).IsHomogeneous (d i)) :
    homogeneousResultant d G = 0 ↔
      ∃ x : Fin (n+1) → K, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (G i) = 0 := by
  let c : ResultantVNP.CoeffVar d → K := fun v => (G v.1).coeff v.2.1
  have hh := normalized_resultant_root_criterion_over_field d hd (universalResultant d)
    (universalResultant_specification d hd) c
  have heval : MvPolynomial.eval c (MvPolynomial.map (Int.castRingHom K) (universalResultant d)) =
      homogeneousResultant d G := by
    rw [MvPolynomial.eval_map]
    rfl
  rw [heval] at hh
  convert hh using 1
  apply exists_congr
  intro x
  apply and_congr_right
  intro hx
  apply forall_congr'
  intro i
  rw [← MvPolynomial.eval_map,specialize_universalForm_of_homogeneous d G hG i]

end APSCounting893.Main
end Component_33

section Component_34
set_option autoImplicit false
open APSCounting893.Main
theorem solution
    {n : ℕ} (d : Fin (n+1) → ℕ) (hd : ∀ i, 0 < d i) :
    (∃ R : MvPolynomial (ResultantVNP.CoeffVar d) ℤ, ResultantVNP.IsMultivariateResultant d R) ∧
    (∀ (R : MvPolynomial (ResultantVNP.CoeffVar d) ℤ) (hR : ResultantVNP.IsMultivariateResultant d R)
      (K : Type) [Field K] [IsAlgClosed K] [CharZero K]
      (G : Fin (n+1) → MvPolynomial (Fin (n+1)) K) (hG : ∀ i, (G i).IsHomogeneous (d i)),
      MvPolynomial.eval₂ (Int.castRingHom K)
        (fun v : ResultantVNP.CoeffVar d => (G v.1).coeff v.2.1) R = 0 ↔
        ∃ x : Fin (n+1) → K, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (G i) = 0) := by
  refine ⟨exists_normalized_multivariate_resultant d hd, ?_⟩
  intro R hR K instF instA instC G hG
  let c : ResultantVNP.CoeffVar d → K := fun v => (G v.1).coeff v.2.1
  have hh := normalized_resultant_root_criterion_over_field d hd R hR c
  rw [MvPolynomial.eval_map] at hh
  convert hh using 1
  apply exists_congr
  intro x
  apply and_congr_right
  intro hx
  apply forall_congr'
  intro i
  rw [← MvPolynomial.eval_map,specialize_universalForm_of_homogeneous d G hG i]
end Component_34

open APSCounting893.Main

