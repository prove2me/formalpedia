-- Prove2me | Definitions.Def_RHT1000_Support_20261118_B004
-- name    : RHT1000_Support_20261118_B004
-- status  : Definition
-- author  : @bueno_ricardo
-- created : 2026-11-18T16:32:30.214403+00:00
-- url     : https://prove2.me/theorems/58f6d341-00e9-45c3-bc2f-6e268660d542
-- title:
--   Suporte completo para T1000 — bloco 4 de 10
-- statement:
--   Definições e lemas auxiliares completos para a prova finita T1000. Este bloco não afirma sozinho a conclusão T1000 nem RH. A divisão reduz o tempo de compilação sem substituir demonstrações por hipóteses.
-- source:
--   Código adaptado de Salvatore Mercuri e Bhavik Mehta, smmercuri/zeta, tag v1-1e8 (3dab648), com dependências e avisos de autoria preservados. Fonte histórica integral T1000: https://axle.axiommath.ai/check#r=d2dcb520-c50a-44dc-a527-de0f7a51b892 . Reorganização em módulos ordinários para compatibilidade com Prove2Me; atribuição da adaptação: projeto Desenvolvimento RH, Ricardo Marangoni Brandão Bueno.

import Definitions.Def_RHT1000_Support_20261118_B003
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
section CertificatePort42
public section
noncomputable section
open scoped BigOperators
open Set
namespace Complex
def weierstrassFactor (m : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * exp (partialLogSum m z)
@[simp]
lemma weierstrassFactor_zero (z : ℂ) : weierstrassFactor 0 z = 1 - z := by
  simp [weierstrassFactor]
@[simp]
lemma weierstrassFactor_at_zero (m : ℕ) : weierstrassFactor m 0 = 1 := by
  simp [weierstrassFactor, partialLogSum_at_zero]
@[simp]
lemma weierstrassFactor_at_one (m : ℕ) : weierstrassFactor m 1 = 0 := by
  simp [weierstrassFactor]
lemma differentiable_weierstrassFactor (m : ℕ) :
    Differentiable ℂ (fun z : ℂ => weierstrassFactor m z) := by
  simpa [weierstrassFactor] using!
    ((differentiable_const (c := (1 : ℂ))).sub differentiable_id).mul
      (differentiable_exp.comp (differentiable_partialLogSum m))
lemma hasDerivAt_weierstrassFactor_at_one (m : ℕ) :
    HasDerivAt (weierstrassFactor m) (-Complex.exp (partialLogSum m 1)) 1 := by
  have hsub : HasDerivAt (fun z : ℂ => 1 - z) (-1) 1 := by
    simpa using! (hasDerivAt_const (1 : ℂ) (c := (1 : ℂ))).sub (hasDerivAt_id 1)
  have hexp :
      HasDerivAt (fun z : ℂ => Complex.exp (partialLogSum m z))
        ((∑ j ∈ Finset.range m, (1 : ℂ) ^ j) * Complex.exp (partialLogSum m 1)) 1 := by
    simpa [mul_comm] using!
      (Complex.hasDerivAt_exp (partialLogSum m 1)).comp 1 (hasDerivAt_partialLogSum m 1)
  simpa [weierstrassFactor] using! hsub.mul hexp
@[simp]
lemma deriv_weierstrassFactor_at_one (m : ℕ) :
    deriv (weierstrassFactor m) 1 = -Complex.exp (partialLogSum m 1) :=
  (hasDerivAt_weierstrassFactor_at_one m).deriv
lemma hasDerivAt_weierstrassFactor_div_at_self (m : ℕ) {a : ℂ} (ha : a ≠ 0) :
    HasDerivAt (fun z : ℂ ↦ weierstrassFactor m (z / a))
      ((-Complex.exp (partialLogSum m 1)) / a) a := by
  have hcomp :
      HasDerivAt ((weierstrassFactor m) ∘ fun z : ℂ ↦ z / a)
        ((-Complex.exp (partialLogSum m 1)) * (1 / a)) a :=
    HasDerivAt.comp (x := a) (h := fun z : ℂ ↦ z / a) (h₂ := weierstrassFactor m)
      (by simpa [ha] using hasDerivAt_weierstrassFactor_at_one m)
      ((hasDerivAt_id a).div_const a)
  simpa [Function.comp, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using! hcomp
@[simp]
lemma deriv_weierstrassFactor_div_at_self (m : ℕ) {a : ℂ} (ha : a ≠ 0) :
    deriv (fun z : ℂ ↦ weierstrassFactor m (z / a)) a =
      (-Complex.exp (partialLogSum m 1)) / a :=
  (hasDerivAt_weierstrassFactor_div_at_self m ha).deriv
lemma weierstrassFactor_eq_exp_neg_tail (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) (hz1 : z ≠ 1) :
    weierstrassFactor m z = exp (-logTail m z) := by
  unfold weierstrassFactor
  have hz_ne_1 : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
  rw [← exp_log hz_ne_1, ← Complex.exp_add]
  have hsum : log (1 - z) + partialLogSum m z = -logTail m z := by
    have hdecomp := neg_log_one_sub_eq_partialLogSum_add_logTail hz m
    calc
      log (1 - z) + partialLogSum m z
          = log (1 - z) + (partialLogSum m z + logTail m z) - logTail m z := by ring
      _ = log (1 - z) + (-log (1 - z)) - logTail m z := by rw [hdecomp]
      _ = -logTail m z := by ring
  simp [hsum]
theorem weierstrassFactor_sub_one_pow_bound {m : ℕ} {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖weierstrassFactor m z - 1‖ ≤ 4 * ‖z‖ ^ (m + 1) := by
  by_cases hm : m = 0
  · subst hm
    have hmain : ‖(1 - z) - 1‖ ≤ 4 * ‖z‖ ^ 1 := by
      have h : (1 - z) - 1 = -z := by ring
      calc
        ‖(1 - z) - 1‖ = ‖-z‖ := by simp [h]
        _ = ‖z‖ := norm_neg z
        _ = ‖z‖ ^ 1 := by simp
        _ ≤ 4 * ‖z‖ ^ 1 := by nlinarith [pow_nonneg (norm_nonneg z) 1]
    simpa [weierstrassFactor] using hmain
  · have hz_lt : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
    by_cases hz1 : z = 1
    · exfalso; rw [hz1] at hz; norm_num at hz
    have h_eq : weierstrassFactor m z = exp (-logTail m z) :=
      weierstrassFactor_eq_exp_neg_tail m hz_lt hz1
    rw [h_eq]
    have h_tail_bound := norm_logTail_le_two_mul_norm_pow hz_lt hz m
    have hw_le_one : ‖-logTail m z‖ ≤ 1 := by
      simp only [norm_neg]
      have : ‖logTail m z‖ ≤ 1 := by
        have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
        have h2 : 2 ≤ m + 1 := by
          exact Nat.succ_le_succ (Nat.succ_le_iff.2 hm_pos)
        have hpow : (‖z‖ ^ (m + 1)) ≤ (‖z‖ ^ 2) := by
          have hz1' : ‖z‖ ≤ 1 := by nlinarith [hz]
          have hz0' : 0 ≤ ‖z‖ := norm_nonneg z
          exact pow_le_pow_of_le_one hz0' hz1' h2
        have hmul : 2 * ‖z‖ ^ (m + 1) ≤ 2 * ‖z‖ ^ 2 := by gcongr
        have hsq : 2 * ‖z‖ ^ 2 ≤ 1 := by
          have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
          have hz_sq : ‖z‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ hz0 hz 2
          nlinarith
        exact (h_tail_bound.trans hmul).trans hsq
      linarith
    have h_exp_sub_one : ‖exp (-logTail m z) - 1‖ ≤ 2 * ‖-logTail m z‖ :=
      Complex.norm_exp_sub_one_le hw_le_one
    simp only [norm_neg] at h_exp_sub_one
    calc
      ‖exp (-logTail m z) - 1‖ ≤ 2 * ‖logTail m z‖ := h_exp_sub_one
      _ ≤ 2 * (2 * ‖z‖ ^ (m + 1)) := by gcongr
      _ = 4 * ‖z‖ ^ (m + 1) := by ring
private lemma eventually_le_norm_div_two_of_summable_inv_pow {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    ∀ R ≥ 0, ∀ᶠ n in Filter.atTop, R ≤ ‖a n‖ / 2 := by
  intro R hR
  by_cases hR0 : R = 0
  · subst hR0
    exact Filter.Eventually.of_forall fun _ => by positivity
  have hRpos : 0 < R := lt_of_le_of_ne hR (by simpa [eq_comm] using hR0)
  have htend : Filter.Tendsto (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1)) Filter.atTop (nhds (0 : ℝ)) := by
    simpa [Nat.cofinite_eq_atTop] using h_sum.tendsto_cofinite_zero
  have hεpos : 0 < (1 / (2 * R) : ℝ) ^ (m + 1) := by
    have : 0 < (1 / (2 * R) : ℝ) := by
      have : 0 < (2 * R : ℝ) := by positivity
      exact one_div_pos.mpr this
    exact pow_pos this _
  filter_upwards [htend.eventually (eventually_lt_nhds hεpos)] with n hn
  by_contra h
  have hlt : ‖a n‖ / 2 < R := lt_of_not_ge h
  have hle : ‖a n‖ ≤ 2 * R := by nlinarith
  have hanorm_pos : 0 < ‖a n‖ := norm_pos_iff.mpr (h_nonzero n)
  have hinv : (1 / (2 * R : ℝ)) ≤ ‖a n‖⁻¹ := by
    simpa [one_div] using (one_div_le_one_div_of_le hanorm_pos hle)
  have hpow :
      (1 / (2 * R : ℝ)) ^ (m + 1) ≤ ‖a n‖⁻¹ ^ (m + 1) :=
    pow_le_pow_left₀ (by positivity) hinv _
  exact (not_lt_of_ge hpow) hn
private lemma summable_scaled_bound_of_summable_inv_pow {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) :
    ∀ R ≥ 0, Summable (fun n : ℕ => 4 * R ^ (m + 1) / ‖a n‖ ^ (m + 1)) := by
  intro R _hR
  simpa [div_eq_mul_inv, inv_pow, mul_assoc, mul_left_comm, mul_comm] using
    h_sum.mul_left (4 * R ^ (m + 1))
lemma continuousOn_weierstrassFactor_div (m : ℕ) (a : ℂ) (s : Set ℂ) :
    ContinuousOn (fun z : ℂ ↦ weierstrassFactor m (z / a)) s := by
  simpa using! (differentiable_weierstrassFactor m).continuous.continuousOn.comp
    (continuous_id.div_const a).continuousOn (mapsTo_univ (fun z : ℂ ↦ z / a) s)
lemma norm_weierstrassFactor_div_sub_one_le_pow_div (m : ℕ) {a z : ℂ}
    (hza : ‖z‖ ≤ ‖a‖ / 2) :
    ‖weierstrassFactor m (z / a) - 1‖ ≤ 4 * ‖z‖ ^ (m + 1) / ‖a‖ ^ (m + 1) := by
  by_cases ha : a = 0
  · have hz : z = 0 := by
      apply norm_eq_zero.mp
      rw [ha] at hza
      simpa using hza
    subst z
    simp [ha]
  · have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
    have hza' : ‖z / a‖ ≤ 1 / 2 := by
      rw [Complex.norm_div, div_le_iff₀ ha']
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hza
    have hbase := weierstrassFactor_sub_one_pow_bound (m := m) (z := z / a) hza'
    calc
      ‖weierstrassFactor m (z / a) - 1‖ ≤ ‖z‖ ^ (m + 1) / ‖a‖ ^ (m + 1) * 4 := by
        simpa [Complex.norm_div, div_pow, mul_comm, mul_left_comm, mul_assoc] using hbase
      _ = 4 * ‖z‖ ^ (m + 1) / ‖a‖ ^ (m + 1) := by ring
lemma hasProdUniformlyOn_weierstrassFactor_div_of_bound {K : Set ℂ} (hK : IsCompact K)
    {m : ℕ → ℕ} {a : ℕ → ℂ} {R : ℝ}
    (hR : ∀ z ∈ K, ‖z‖ ≤ R) (hsmall : ∀ᶠ n in Filter.atTop, R ≤ ‖a n‖ / 2)
    (hsumm : Summable (fun n : ℕ ↦ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1))) :
    HasProdUniformlyOn (fun n z ↦ weierstrassFactor (m n) (z / a n))
      (fun z ↦ ∏' n, weierstrassFactor (m n) (z / a n)) K := by
  have hbound :
      ∀ᶠ n in Filter.atTop,
        ∀ z ∈ K,
          ‖weierstrassFactor (m n) (z / a n) - 1‖ ≤ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1) := by
    filter_upwards [hsmall] with n hn z hz
    refine (norm_weierstrassFactor_div_sub_one_le_pow_div (m := m n) ?_).trans ?_
    · exact (hR z hz).trans hn
    · have hpow : ‖z‖ ^ (m n + 1) ≤ R ^ (m n + 1) :=
        pow_le_pow_left₀ (norm_nonneg z) (hR z hz) (m n + 1)
      refine div_le_div_of_nonneg_right ?_ (pow_nonneg (norm_nonneg (a n)) _)
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hcts :
      ∀ n, ContinuousOn (fun z ↦ weierstrassFactor (m n) (z / a n) - 1) K := by
    intro n
    exact (continuousOn_weierstrassFactor_div (m n) (a n) K).fun_sub continuousOn_const
  simpa using hsumm.hasProdUniformlyOn_nat_one_add (K := K)
    (f := fun n z ↦ weierstrassFactor (m n) (z / a n) - 1) hK hbound hcts
lemma hasProdLocallyUniformlyOn_weierstrassFactor_div {s : Set ℂ} (hs : IsOpen s)
    {m : ℕ → ℕ} {a : ℕ → ℂ}
    (hsmall : ∀ R ≥ 0, ∀ᶠ n in Filter.atTop, R ≤ ‖a n‖ / 2)
    (hsumm : ∀ R ≥ 0, Summable (fun n : ℕ ↦ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1))) :
    HasProdLocallyUniformlyOn (fun n z ↦ weierstrassFactor (m n) (z / a n))
      (fun z ↦ ∏' n, weierstrassFactor (m n) (z / a n)) s := by
  apply hasProdLocallyUniformlyOn_of_forall_compact hs
  intro K hKs hK
  obtain ⟨R, hR⟩ : ∃ R, ∀ z ∈ K, ‖z‖ ≤ R := by
    by_cases hKe : K.Nonempty
    · obtain ⟨z, hzK, hzmax⟩ := hK.exists_isMaxOn hKe continuous_norm.continuousOn
      exact ⟨‖z‖, fun w hw ↦ (isMaxOn_iff.mp hzmax) w hw⟩
    · exact ⟨0, fun z hz ↦ False.elim <| hKe ⟨z, hz⟩⟩
  let R' := max R 0
  have hR'0 : 0 ≤ R' := le_max_right _ _
  have hR' : ∀ z ∈ K, ‖z‖ ≤ R' := by
    intro z hz
    exact (hR z hz).trans (le_max_left _ _)
  exact hasProdUniformlyOn_weierstrassFactor_div_of_bound hK hR'
    (hsmall R' hR'0) (hsumm R' hR'0)
lemma hasProdLocallyUniformlyOn_weierstrassFactor_div_of_summable_inv_pow {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    HasProdLocallyUniformlyOn (fun n z ↦ weierstrassFactor m (z / a n))
      (fun z ↦ ∏' n, weierstrassFactor m (z / a n)) Set.univ := by
  simpa using
    hasProdLocallyUniformlyOn_weierstrassFactor_div (s := (Set.univ : Set ℂ)) isOpen_univ
      (m := fun _ => m) (a := a)
      (eventually_le_norm_div_two_of_summable_inv_pow h_sum h_nonzero)
      (summable_scaled_bound_of_summable_inv_pow h_sum)
end Complex
end
end
end CertificatePort42

section CertificatePort43
section
noncomputable section
open Filter Topology
namespace Complex
def canonicalProduct (m : ℕ) (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∏' n : ℕ, weierstrassFactor m (z / a n)
@[simp] theorem canonicalProduct_def (m : ℕ) (a : ℕ → ℂ) (z : ℂ) :
    canonicalProduct m a z = ∏' n : ℕ, weierstrassFactor m (z / a n) :=
  rfl
theorem hasProdLocallyUniformlyOn_canonicalProduct {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    HasProdLocallyUniformlyOn (fun n z ↦ weierstrassFactor m (z / a n))
      (canonicalProduct m a) Set.univ := by
  simpa [canonicalProduct] using!
    hasProdLocallyUniformlyOn_weierstrassFactor_div_of_summable_inv_pow
      (m := m) (a := a) h_sum h_nonzero
theorem multipliableLocallyUniformlyOn_canonicalProduct {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    MultipliableLocallyUniformlyOn (fun n z ↦ weierstrassFactor m (z / a n))
      (Set.univ : Set ℂ) := by
  simpa using
    (hasProdLocallyUniformlyOn_canonicalProduct h_sum h_nonzero).multipliableLocallyUniformlyOn
@[simp]
theorem canonicalProduct_apply_eq_zero {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) (n : ℕ) :
    canonicalProduct m a (a n) = 0 := by
  let f : ℕ → ℂ := fun k ↦ weierstrassFactor m (a n / a k)
  have hmult : Multipliable f :=
    (multipliableLocallyUniformlyOn_canonicalProduct h_sum h_nonzero).multipliable (by simp)
  have htend :
      Tendsto (fun N : ℕ ↦ ∏ k ∈ Finset.range N, f k) Filter.atTop
        (𝓝 (canonicalProduct m a (a n))) := by
    simpa [f, canonicalProduct] using hmult.hasProd.tendsto_prod_nat
  have hzero :
      (fun N : ℕ ↦ ∏ k ∈ Finset.range N, f k) =ᶠ[Filter.atTop] fun _ ↦ (0 : ℂ) := by
    refine Filter.eventually_atTop.2 ⟨n + 1, fun N hN ↦ ?_⟩
    have hnN : n ∈ Finset.range N := Finset.mem_range.mpr <| lt_of_lt_of_le (Nat.lt_succ_self n) hN
    apply Finset.prod_eq_zero hnN
    simp [f, h_nonzero n, weierstrassFactor_at_one]
  exact tendsto_nhds_unique_of_eventuallyEq htend tendsto_const_nhds hzero
end Complex
end
end
end CertificatePort43

section CertificatePort44
section
open Filter Topology Set
namespace MeromorphicOn
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U K : Set 𝕜} {z : 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
lemma divisor_support_inter_compact_finite (f : 𝕜 → E) {U K : Set 𝕜}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    (K ∩ (MeromorphicOn.divisor f U).support).Finite := by
  classical
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  have hloc :
      ∀ x ∈ K, ∃ V : Set 𝕜, V ∈ 𝓝 x ∧ Set.Finite (V ∩ D.support) := by
    intro x hxK
    rcases D.supportLocallyFiniteWithinDomain x (hKU hxK) with ⟨V, hV, hfin⟩
    exact ⟨V, hV, hfin⟩
  choose V hVnhds hVfin using hloc
  rcases hK.elim_nhds_subcover' (U := fun x hx => V x hx) (hU := fun x hx => hVnhds x hx) with
    ⟨t, ht⟩
  have hsub :
      K ∩ D.support ⊆ ⋃ x ∈ t, (V (x : 𝕜) x.2 ∩ D.support) := by
    intro y hy
    rcases hy with ⟨hyK, hyS⟩
    have hycov : y ∈ ⋃ x ∈ t, V (x : 𝕜) x.2 := ht hyK
    rcases Set.mem_iUnion.1 hycov with ⟨x, hycov'⟩
    rcases Set.mem_iUnion.1 hycov' with ⟨hxT, hyV⟩
    refine Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ?_⟩
    exact ⟨hxT, ⟨hyV, hyS⟩⟩
  have hfinU : Set.Finite (⋃ x ∈ t, (V (x : 𝕜) x.2 ∩ D.support)) := by
    classical
    refine (t.finite_toSet).biUnion ?_
    intro x hx
    simpa using (hVfin (x : 𝕜) x.2)
  exact hfinU.subset hsub
end MeromorphicOn
end
end CertificatePort44

section CertificatePort45
section
open Set
namespace Complex.Hadamard
def divisorZeroIndex (f : ℂ → ℂ) (U : Set ℂ) : Type :=
  Σ z : ℂ, Fin (Int.toNat (MeromorphicOn.divisor f U z))
abbrev divisorZeroIndex₀ (f : ℂ → ℂ) (U : Set ℂ) : Type :=
  {p : divisorZeroIndex f U // p.1 ≠ 0}
abbrev divisorZeroIndex₀_val {f : ℂ → ℂ} {U : Set ℂ} (p : divisorZeroIndex₀ f U) : ℂ :=
  p.1.1
@[simp]
lemma divisorZeroIndex₀_val_ne_zero {f : ℂ → ℂ} {U : Set ℂ} (p : divisorZeroIndex₀ f U) :
    divisorZeroIndex₀_val p ≠ 0 := p.2
@[simp]
lemma divisorZeroIndex₀_val_mem_divisor_support {f : ℂ → ℂ} {U : Set ℂ}
    (p : divisorZeroIndex₀ f U) :
    MeromorphicOn.divisor f U (divisorZeroIndex₀_val p) ≠ 0 := by
  have hn :
      Int.toNat (MeromorphicOn.divisor f U (divisorZeroIndex₀_val p)) ≠ 0 := by
    intro h0
    have q0 : Fin 0 := by
      simpa [divisorZeroIndex₀_val, h0] using p.1.2
    exact Fin.elim0 q0
  intro hdiv
  have : Int.toNat (MeromorphicOn.divisor f U (divisorZeroIndex₀_val p)) = 0 := by
    simp [hdiv]
  exact hn this
noncomputable def divisorCanonicalProduct (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ) (z : ℂ) : ℂ :=
  ∏' p : divisorZeroIndex₀ f U, weierstrassFactor m (z / divisorZeroIndex₀_val p)
@[simp]
lemma divisorCanonicalProduct_zero (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ) :
    divisorCanonicalProduct m f U 0 = 1 := by
  simp [divisorCanonicalProduct]
end Complex.Hadamard
end
end CertificatePort45

section CertificatePort46
section
namespace Complex
section UniformMul
end UniformMul
end Complex
end
end CertificatePort46

section CertificatePort47
section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set
namespace Complex.Hadamard
lemma finite_divisorZeroIndex₀_subtype_norm_le {f : ℂ → ℂ} {U : Set ℂ} (B : ℝ)
    (hBU : Metric.closedBall (0 : ℂ) B ⊆ U) :
    Finite {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ B} := by
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  have hK : IsCompact (Metric.closedBall (0 : ℂ) B) := isCompact_closedBall _ _
  have hpts0 : ((Metric.closedBall (0 : ℂ) B) ∩ D.support).Finite :=
    MeromorphicOn.divisor_support_inter_compact_finite (f := f) (U := U)
      (K := Metric.closedBall (0 : ℂ) B) hK hBU
  set pts : Set ℂ := ((Metric.closedBall (0 : ℂ) B) ∩ D.support) \ {0}
  have hpts : pts.Finite := hpts0.sdiff
  let : Fintype pts := hpts.fintype
  let T : Type := Σ z : pts, Fin (Int.toNat (D z.1))
  have : Finite T := by infer_instance
  let F :
      {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ B} → T := fun p =>
    ⟨⟨divisorZeroIndex₀_val p.1, by
        have hball : divisorZeroIndex₀_val p.1 ∈ Metric.closedBall (0 : ℂ) B := by
          simpa [Metric.mem_closedBall, dist_zero_right] using p.2
        have hsupport : divisorZeroIndex₀_val p.1 ∈ D.support := by
          have hne_toNat :
              Int.toNat (MeromorphicOn.divisor f U (divisorZeroIndex₀_val p.1)) ≠ 0 := by
            intro h0
            have hpfin :
                Fin (Int.toNat (MeromorphicOn.divisor f U (divisorZeroIndex₀_val p.1))) := by
              simpa [D] using p.1.1.2
            have : Fin 0 := by simpa [h0] using hpfin
            exact Fin.elim0 this
          have hne_D : D (divisorZeroIndex₀_val p.1) ≠ 0 := by
            intro hD0
            apply hne_toNat
            simp [D, hD0]
          simp [D, Function.locallyFinsuppWithin.support, Function.support]
        have hne0 : divisorZeroIndex₀_val p.1 ≠ 0 := divisorZeroIndex₀_val_ne_zero p.1
        exact ⟨⟨hball, hsupport⟩, by simp [Set.mem_singleton_iff]⟩⟩,
      p.1.1.2⟩
  refine Finite.of_injective F ?_
  intro p q hpq
  apply Subtype.ext
  apply Subtype.ext
  have h' := (Sigma.mk.inj_iff.1 hpq)
  have hz : divisorZeroIndex₀_val p.1 = divisorZeroIndex₀_val q.1 := congrArg Subtype.val h'.1
  apply (Sigma.mk.inj_iff).2
  refine ⟨hz, ?_⟩
  exact h'.2
lemma divisorZeroIndex₀_norm_le_finite {f : ℂ → ℂ} {U : Set ℂ} (B : ℝ)
    (hBU : Metric.closedBall (0 : ℂ) B ⊆ U) :
    ({p : divisorZeroIndex₀ f U | ‖divisorZeroIndex₀_val p‖ ≤ B} : Set _).Finite := by
  let s : Set (divisorZeroIndex₀ f U) := {p | ‖divisorZeroIndex₀_val p‖ ≤ B}
  have : Finite (↥s) :=
    finite_divisorZeroIndex₀_subtype_norm_le (f := f) (U := U) B hBU
  exact Set.toFinite s
end Complex.Hadamard
end
end CertificatePort47

section CertificatePort48
section
open Set
namespace Complex.Hadamard
end Complex.Hadamard
end
end CertificatePort48

section CertificatePort49
section
noncomputable section
open Set
open scoped Topology BigOperators
namespace Complex.Hadamard
theorem divisorZeroIndex₀_fiber_finite (f : ℂ → ℂ) (z₀ : ℂ) :
    ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | divisorZeroIndex₀_val p = z₀} :
      Set _).Finite := by
  have hsub :
      ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | divisorZeroIndex₀_val p = z₀} : Set _)
        ⊆ ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ ‖z₀‖} :
          Set _) := by
    intro p hp
    have : divisorZeroIndex₀_val p = z₀ := hp
    simp [this]
  have hfin :
      ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ ‖z₀‖} :
        Set _).Finite := by
    have : Metric.closedBall (0 : ℂ) ‖z₀‖ ⊆ (Set.univ : Set ℂ) := by simp
    simpa using (divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ))
      (B := ‖z₀‖) this)
  exact hfin.subset hsub
def divisorZeroIndex₀_fiberFinset (f : ℂ → ℂ) (z₀ : ℂ) :
    Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) :=
  (divisorZeroIndex₀_fiber_finite (f := f) z₀).toFinset
@[simp]
lemma mem_divisorZeroIndex₀_fiberFinset (f : ℂ → ℂ) (z₀ : ℂ)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀ ↔ divisorZeroIndex₀_val p = z₀ := by
  simp [divisorZeroIndex₀_fiberFinset]
end Complex.Hadamard
end
end
end CertificatePort49

section CertificatePort50
section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set
namespace Complex.Hadamard
noncomputable def divisorComplementFactor
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) : ℂ := by
  classical
  exact if p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀ then (1 : ℂ)
    else weierstrassFactor m (z / divisorZeroIndex₀_val p)
@[simp]
theorem divisorComplementFactor_eq_one_of_mem
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ)
    (hp : p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀) :
    divisorComplementFactor m f z₀ p z = 1 := by
  classical
  simp [divisorComplementFactor, hp]
@[simp]
theorem divisorComplementFactor_eq_weierstrassFactor_of_not_mem
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ)
    (hp : p ∉ divisorZeroIndex₀_fiberFinset (f := f) z₀) :
    divisorComplementFactor m f z₀ p z =
      weierstrassFactor m (z / divisorZeroIndex₀_val p) := by
  classical
  simp [divisorComplementFactor, hp]
noncomputable def divisorPartialProduct (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) : ℂ :=
  ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p)
@[simp]
lemma divisorPartialProduct_def (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) :
    divisorPartialProduct m f s z = ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p) :=
  rfl
noncomputable def divisorComplementPartialProduct
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) : ℂ :=
  ∏ p ∈ s, divisorComplementFactor m f z₀ p z
@[simp]
lemma divisorComplementPartialProduct_def
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) :
    divisorComplementPartialProduct m f z₀ s z =
      ∏ p ∈ s, if divisorZeroIndex₀_val p = z₀ then (1 : ℂ)
        else weierstrassFactor m (z / divisorZeroIndex₀_val p) := by
  simp [divisorComplementPartialProduct, divisorComplementFactor,
    mem_divisorZeroIndex₀_fiberFinset]
noncomputable def divisorComplementCanonicalProduct
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) (z : ℂ) : ℂ :=
  ∏' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), divisorComplementFactor m f z₀ p z
end Complex.Hadamard
end
end CertificatePort50

section CertificatePort51
section
noncomputable section
open Complex Filter Function Finset Topology
open scoped Topology BigOperators
open Set
namespace Complex.Hadamard
end Complex.Hadamard
end
end
end CertificatePort51

section CertificatePort52
section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set
namespace Complex.Hadamard
open Filter
end Complex.Hadamard
end
end CertificatePort52

section CertificatePort53
section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set
namespace Complex.Hadamard
end Complex.Hadamard
end
end CertificatePort53

section CertificatePort54
section
namespace Complex.Hadamard
open scoped Topology
open Set
end Hadamard
end Complex
end
end CertificatePort54

section CertificatePort55
section
open Set
open scoped ENNReal
namespace Metric
variable {X : Type*} [PseudoMetricSpace X]
def annulusIoo (x : X) (r R : ℝ) : Set X := (fun y : X ↦ dist y x) ⁻¹' Ioo r R
def annulusIoc (x : X) (r R : ℝ) : Set X := (fun y : X ↦ dist y x) ⁻¹' Ioc r R
def annulusIco (x : X) (r R : ℝ) : Set X := (fun y : X ↦ dist y x) ⁻¹' Ico r R
def annulusIcc (x : X) (r R : ℝ) : Set X := (fun y : X ↦ dist y x) ⁻¹' Icc r R
def annulusIoi (x : X) (r : ℝ) : Set X := (fun y : X ↦ dist y x) ⁻¹' Ioi r
def annulusIci (x : X) (r : ℝ) : Set X := (fun y : X ↦ dist y x) ⁻¹' Ici r
variable {x : X} {r R : ℝ}
@[simp] lemma annulusIoo_eq_empty {x : X} {r R : ℝ} (h : R ≤ r) : annulusIoo x r R = ∅ := by
  simp [annulusIoo, Ioo_eq_empty_of_le h]
@[simp] lemma annulusIoc_eq_empty {x : X} {r R : ℝ} (h : R ≤ r) : annulusIoc x r R = ∅ := by
  simp [annulusIoc, Ioc_eq_empty_of_le h]
@[simp] lemma annulusIco_eq_empty {x : X} {r R : ℝ} (h : R ≤ r) : annulusIco x r R = ∅ := by
  simp [annulusIco, Ico_eq_empty_of_le h]
@[simp] lemma annulusIcc_eq_empty {x : X} {r R : ℝ} (h : R < r) : annulusIcc x r R = ∅ := by
  simp [annulusIcc, Icc_eq_empty_of_lt h]
@[gcongr]
lemma annulusIoo_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    annulusIoo x r₁ R₁ ⊆ annulusIoo x r₂ R₂ := by
  intro y hy
  exact ⟨lt_of_le_of_lt hr hy.1, lt_of_lt_of_le hy.2 hR⟩
@[gcongr]
lemma annulusIoc_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    annulusIoc x r₁ R₁ ⊆ annulusIoc x r₂ R₂ := by
  intro y hy
  exact ⟨lt_of_le_of_lt hr hy.1, hy.2.trans hR⟩
@[gcongr]
lemma annulusIco_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    annulusIco x r₁ R₁ ⊆ annulusIco x r₂ R₂ := by
  intro y hy
  exact ⟨hr.trans hy.1, lt_of_lt_of_le hy.2 hR⟩
@[gcongr]
lemma annulusIcc_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    annulusIcc x r₁ R₁ ⊆ annulusIcc x r₂ R₂ := by
  intro y hy
  exact ⟨hr.trans hy.1, hy.2.trans hR⟩
@[simp]
lemma annulusIoc_union_annulusIoo {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' < R) :
    annulusIoc x r r' ∪ annulusIoo x r' R = annulusIoo x r R := by
  simpa [annulusIoc, annulusIoo, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ioc_union_Ioo_eq_Ioo h₁ h₂)
@[simp]
lemma annulusIoc_union_annulusIoc {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' ≤ R) :
    annulusIoc x r r' ∪ annulusIoc x r' R = annulusIoc x r R := by
  simpa [annulusIoc, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ioc_union_Ioc_eq_Ioc h₁ h₂)
@[simp]
lemma annulusIoo_union_annulusIco {x : X} {r r' R : ℝ} (h₁ : r < r') (h₂ : r' ≤ R) :
    annulusIoo x r r' ∪ annulusIco x r' R = annulusIoo x r R := by
  simpa [annulusIoo, annulusIco, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ioo_union_Ico_eq_Ioo h₁ h₂)
@[simp]
lemma annulusIoo_union_annulusIcc {x : X} {r r' R : ℝ} (h₁ : r < r') (h₂ : r' ≤ R) :
    annulusIoo x r r' ∪ annulusIcc x r' R = annulusIoc x r R := by
  simpa [annulusIoo, annulusIcc, annulusIoc, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ioo_union_Icc_eq_Ioc h₁ h₂)
@[simp]
lemma annulusIcc_union_annulusIoo {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' < R) :
    annulusIcc x r r' ∪ annulusIoo x r' R = annulusIco x r R := by
  simpa [annulusIcc, annulusIoo, annulusIco, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Icc_union_Ioo_eq_Ico h₁ h₂)
@[simp]
lemma annulusIcc_union_annulusIoc {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' ≤ R) :
    annulusIcc x r r' ∪ annulusIoc x r' R = annulusIcc x r R := by
  simpa [annulusIcc, annulusIoc, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Icc_union_Ioc_eq_Icc h₁ h₂)
@[simp]
lemma annulusIco_union_annulusIco {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' ≤ R) :
    annulusIco x r r' ∪ annulusIco x r' R = annulusIco x r R := by
  simpa [annulusIco, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ico_union_Ico_eq_Ico h₁ h₂)
@[simp]
lemma annulusIco_union_annulusIcc {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' ≤ R) :
    annulusIco x r r' ∪ annulusIcc x r' R = annulusIcc x r R := by
  simpa [annulusIco, annulusIcc, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ico_union_Icc_eq_Icc h₁ h₂)
@[simp]
lemma annulusIoc_union_annulusIoi {x : X} {r R : ℝ} (h : r ≤ R) :
    annulusIoc x r R ∪ annulusIoi x R = annulusIoi x r := by
  simpa [annulusIoc, annulusIoi, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ioc_union_Ioi_eq_Ioi h)
@[simp]
lemma annulusIoo_union_annulusIci {x : X} {r R : ℝ} (h : r < R) :
    annulusIoo x r R ∪ annulusIci x R = annulusIoi x r := by
  simpa [annulusIoo, annulusIci, annulusIoi, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ioo_union_Ici_eq_Ioi h)
@[simp]
lemma annulusIcc_union_annulusIoi {x : X} {r R : ℝ} (h : r ≤ R) :
    annulusIcc x r R ∪ annulusIoi x R = annulusIci x r := by
  simpa [annulusIcc, annulusIoi, annulusIci, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Icc_union_Ioi_eq_Ici h)
@[simp]
lemma annulusIco_union_annulusIci {x : X} {r R : ℝ} (h : r ≤ R) :
    annulusIco x r R ∪ annulusIci x R = annulusIci x r := by
  simpa [annulusIco, annulusIci, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ico_union_Ici_eq_Ici h)
open scoped Function
variable {ι : Type*} [LinearOrder ι] [SuccOrder ι]
end Metric
namespace Metric
variable {X : Type*} [PseudoEMetricSpace X]
def eannulusIoo (x : X) (r R : ℝ≥0∞) : Set X := (fun y : X ↦ edist y x) ⁻¹' Ioo r R
def eannulusIoc (x : X) (r R : ℝ≥0∞) : Set X := (fun y : X ↦ edist y x) ⁻¹' Ioc r R
def eannulusIco (x : X) (r R : ℝ≥0∞) : Set X := (fun y : X ↦ edist y x) ⁻¹' Ico r R
def eannulusIcc (x : X) (r R : ℝ≥0∞) : Set X := (fun y : X ↦ edist y x) ⁻¹' Icc r R
def eannulusIoi (x : X) (r : ℝ≥0∞) : Set X := (fun y : X ↦ edist y x) ⁻¹' Ioi r
def eannulusIci (x : X) (r : ℝ≥0∞) : Set X := (fun y : X ↦ edist y x) ⁻¹' Ici r
@[simp] lemma eannulusIoo_eq_preimage (x : X) (r R : ℝ≥0∞) :
    eannulusIoo x r R = (fun y : X ↦ edist y x) ⁻¹' Ioo r R := rfl
@[simp] lemma eannulusIoc_eq_preimage (x : X) (r R : ℝ≥0∞) :
    eannulusIoc x r R = (fun y : X ↦ edist y x) ⁻¹' Ioc r R := rfl
@[simp] lemma eannulusIco_eq_preimage (x : X) (r R : ℝ≥0∞) :
    eannulusIco x r R = (fun y : X ↦ edist y x) ⁻¹' Ico r R := rfl
@[simp] lemma eannulusIcc_eq_preimage (x : X) (r R : ℝ≥0∞) :
    eannulusIcc x r R = (fun y : X ↦ edist y x) ⁻¹' Icc r R := rfl
@[simp] lemma eannulusIoi_eq_preimage (x : X) (r : ℝ≥0∞) :
    eannulusIoi x r = (fun y : X ↦ edist y x) ⁻¹' Ioi r := rfl
@[simp] lemma eannulusIci_eq_preimage (x : X) (r : ℝ≥0∞) :
    eannulusIci x r = (fun y : X ↦ edist y x) ⁻¹' Ici r := rfl
@[gcongr]
lemma eannulusIoo_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ≥0∞} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    eannulusIoo x r₁ R₁ ⊆ eannulusIoo x r₂ R₂ := by
  intro y hy
  exact ⟨lt_of_le_of_lt hr hy.1, lt_of_lt_of_le hy.2 hR⟩
@[gcongr]
lemma eannulusIoc_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ≥0∞} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    eannulusIoc x r₁ R₁ ⊆ eannulusIoc x r₂ R₂ := by
  intro y hy; exact ⟨lt_of_le_of_lt hr hy.1, hy.2.trans hR⟩
@[gcongr]
lemma eannulusIco_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ≥0∞} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    eannulusIco x r₁ R₁ ⊆ eannulusIco x r₂ R₂ := by
  intro y hy; exact ⟨hr.trans hy.1, lt_of_lt_of_le hy.2 hR⟩
@[gcongr]
lemma eannulusIcc_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ≥0∞} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    eannulusIcc x r₁ R₁ ⊆ eannulusIcc x r₂ R₂ := by
  intro y hy; exact ⟨hr.trans hy.1, hy.2.trans hR⟩
open scoped Function
variable {ι : Type*} [LinearOrder ι] [SuccOrder ι]
end Metric
namespace Metric
variable {X : Type*} [PseudoMetricSpace X]
variable {x : X} {r R : ℝ}
end Metric
end
end CertificatePort55

section CertificatePort56
section
namespace Complex.Hadamard
open Filter Topology Set Complex
open scoped BigOperators Topology
noncomputable def hadamardDenom (m : ℕ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  z ^ (analyticOrderNatAt f 0) * divisorCanonicalProduct m f (Set.univ : Set ℂ) z
noncomputable def centeredHadamardDenom (m : ℕ) (c : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (z - c) ^ (analyticOrderNatAt f c) *
    divisorCanonicalProduct m (fun w : ℂ => f (w + c)) (Set.univ : Set ℂ) (z - c)
noncomputable def centeredHadamardQuotient (m : ℕ) (c : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z / centeredHadamardDenom m c f z
@[simp]
theorem centeredHadamardDenom_center_eq_one {m : ℕ} {c : ℂ} {f : ℂ → ℂ}
    (h : analyticOrderNatAt f c = 0) :
    centeredHadamardDenom m c f c = 1 := by
  simp [centeredHadamardDenom, h, sub_self, divisorCanonicalProduct_zero, pow_zero]
@[simp]
theorem centeredHadamardDenom_center_eq_zero {m : ℕ} {c : ℂ} {f : ℂ → ℂ}
    (h : analyticOrderNatAt f c ≠ 0) : centeredHadamardDenom m c f c = 0 := by
  have hn : 0 < analyticOrderNatAt f c := by
    exact Nat.pos_of_ne_zero h
  simp [centeredHadamardDenom, sub_self, zero_pow hn.ne']
end Complex.Hadamard
end
end CertificatePort56

section CertificatePort57
section
open Filter Function MeromorphicOn Metric Real Set
namespace Function.locallyFinsuppWithin
variable {E : Type*} [NormedAddCommGroup E]
noncomputable def massClosedBall₀ {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (D : locallyFinsupp E ℤ) (R : ℝ) : ℝ := by
  classical
  exact
    (((finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).toFinset).filter
      (fun z => z ≠ (0 : E))).sum fun z => (D z : ℝ)
end Function.locallyFinsuppWithin
namespace Function.locallyFinsuppWithin
end Function.locallyFinsuppWithin
end
end CertificatePort57

section CertificatePort58
section
namespace Real
end Real
end
end CertificatePort58

section CertificatePort59
section
namespace Real
end Real
end
end CertificatePort59

section CertificatePort60
section
namespace Real
variable {α E : Type*} [SeminormedAddCommGroup E]
variable {F : Type*} [NormedAddCommGroup F]
open Metric Complex
end Real
end
end CertificatePort60

section CertificatePort61
section
open Filter Function MeromorphicOn Metric Real Set
namespace Function.locallyFinsuppWithin
variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
end Function.locallyFinsuppWithin
end
end CertificatePort61

section CertificatePort62
section
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
theorem Differentiable.divisor_nonneg {f : ℂ → E} (hf : Differentiable ℂ f) :
    0 ≤ MeromorphicOn.divisor f (univ : Set ℂ) :=
  MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hf.differentiableOn.analyticOnNhd isOpen_univ)
end
end CertificatePort62

section CertificatePort63
section
noncomputable section
open scoped BigOperators
open Filter
namespace Real
end Real
end
end
end CertificatePort63

section CertificatePort64
section
noncomputable section
open Filter Topology Set Complex
open scoped BigOperators Topology
namespace Complex.Hadamard
open scoped Real
noncomputable def divisorMassClosedBall₀ (f : ℂ → ℂ) (R : ℝ) : ℝ :=
  Function.locallyFinsuppWithin.massClosedBall₀ (MeromorphicOn.divisor f (Set.univ : Set ℂ)) R
open scoped BigOperators
end Complex.Hadamard
end
end
end CertificatePort64

section CertificatePort65
section
open Real Complex Function
namespace Backlund
noncomputable def zetaSurrogate (s : ℂ) : ℂ :=
  if s = 1 then 1 else (s - 1) * riemannZeta s
end Backlund
end
end CertificatePort65

section CertificatePort66
section
noncomputable section
namespace Kadiri
open Complex Filter
abbrev NontrivialZeros : Set ℂ :=
  riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ)
def riemannZetaConjZeroSource : Prop :=
  ∀ z : ℂ, riemannZeta z = 0 → riemannZeta ((starRingEnd ℂ) z) = 0
def positiveHeightNontrivialZeroEquivZeroesRect (T : ℝ) :
    {rho : NontrivialZeros // 0 < (rho : ℂ).im ∧ (rho : ℂ).im < T} ≃
      riemannZeta.zeroes_rect (.Ioo 0 1) (.Ioo 0 T) where
  toFun rho :=
    ⟨(rho : ℂ),
      rho.1.property.1,
      by exact ⟨rho.2.1, rho.2.2⟩,
      rho.1.property.2.2⟩
  invFun rho :=
    ⟨⟨(rho : ℂ),
        rho.property.1,
        Set.mem_univ _,
        rho.property.2.2⟩,
      by exact ⟨rho.property.2.1.1, rho.property.2.1.2⟩⟩
  left_inv rho := by
    ext
    rfl
  right_inv rho := by
    ext
    rfl
lemma zeroes_rect_Ioo_critical_positive_height_finite (T : ℝ) :
    (riemannZeta.zeroes_rect (.Ioo 0 1) (.Ioo 0 T)).Finite := by
  rw [riemannZeta.zeroes_rect_eq]
  let S : Set ℂ := (Complex.re ⁻¹' Set.Icc (0 : ℝ) 1) ∩
    (Complex.im ⁻¹' Set.Icc (0 : ℝ) T)
  have hS : IsCompact S := by
    exact Complex.equivRealProdCLM.toHomeomorph.isClosedEmbedding.isCompact_preimage
      (isCompact_Icc.prod isCompact_Icc)
  refine (riemannZeta.zeroes_on_Compact_finite' (S := S) hS).subset ?_
  intro z hz
  rcases hz with ⟨⟨hre, him⟩, hzeta⟩
  exact ⟨⟨Set.Ioo_subset_Icc_self hre, Set.Ioo_subset_Icc_self him⟩, hzeta⟩
lemma positiveHeightZero_ne_one {T : ℝ}
    (rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    (rho : ℂ) ≠ 1 := by
  intro h
  have him : (rho : ℂ).im ∈ Set.Ioo (0 : ℝ) T := rho.property.2.1
  rw [h] at him
  norm_num at him
lemma riemannZeta_analyticAt_positiveHeightZero {T : ℝ}
    (rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    AnalyticAt ℂ riemannZeta (rho : ℂ) := by
  exact riemannZeta_analyticOn_compl_one (rho : ℂ)
    (by simpa [Set.mem_compl_iff] using positiveHeightZero_ne_one rho)
lemma riemannZeta_positiveHeightZero_zero {T : ℝ}
    (rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    riemannZeta (rho : ℂ) = 0 := by
  exact rho.property.2.2
lemma riemannZeta_eventually_ne_zero_punctured_positiveHeightZero {T : ℝ}
    (rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    ∀ᶠ z in nhdsWithin (rho : ℂ) ({(rho : ℂ)}ᶜ), riemannZeta z ≠ 0 := by
  have hmem_compl_one : (rho : ℂ) ∈ ({1} : Set ℂ)ᶜ := by
    simpa [Set.mem_compl_iff] using positiveHeightZero_ne_one rho
  have hdisj : Disjoint (nhdsWithin (rho : ℂ) ({(rho : ℂ)}ᶜ))
      (𝓟 (({1} : Set ℂ)ᶜ \ riemannZeta.zeroesᶜ)) := by
    exact (mem_codiscreteWithin.mp riemannZeta.zeroes_codiscreteWithin_compl_one)
      (rho : ℂ) hmem_compl_one
  have hnot_zeroes : (({1} : Set ℂ)ᶜ \ riemannZeta.zeroesᶜ)ᶜ ∈
      nhdsWithin (rho : ℂ) ({(rho : ℂ)}ᶜ) :=
    Filter.disjoint_principal_right.mp hdisj
  have heventually_compl_one : ∀ᶠ z in nhdsWithin (rho : ℂ) ({(rho : ℂ)}ᶜ),
      z ∈ ({1} : Set ℂ)ᶜ := by
    exact nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hmem_compl_one)
  filter_upwards [hnot_zeroes, heventually_compl_one] with z hznot hz_compl_one hzero
  have hz_zero : z ∈ riemannZeta.zeroes := by
    simpa [riemannZeta.zeroes] using hzero
  exact hznot ⟨hz_compl_one, by simpa using hz_zero⟩
lemma riemannZeta_meromorphicOrderAt_ne_top_positiveHeightZero {T : ℝ}
    (rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    meromorphicOrderAt riemannZeta (rho : ℂ) ≠ ⊤ := by
  have han := riemannZeta_analyticAt_positiveHeightZero rho
  exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero han.meromorphicAt).2
    (riemannZeta_eventually_ne_zero_punctured_positiveHeightZero rho)
lemma riemannZeta_order_pos_positiveHeightZero {T : ℝ}
    (rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    0 < riemannZeta.order (rho : ℂ) := by
  have han := riemannZeta_analyticAt_positiveHeightZero rho
  have hzero := riemannZeta_positiveHeightZero_zero rho
  have horder_ne_top := riemannZeta_meromorphicOrderAt_ne_top_positiveHeightZero rho
  have hanOrder_ne_zero : analyticOrderAt riemannZeta (rho : ℂ) ≠ 0 := by
    intro h
    exact (han.analyticOrderAt_eq_zero.mp h) hzero
  unfold riemannZeta.order
  cases hO : analyticOrderAt riemannZeta (rho : ℂ) with
  | top =>
      exfalso
      exact horder_ne_top (by simp [han.meromorphicOrderAt_eq, hO])
  | coe n =>
      have hn_pos : 0 < n := by
        exact Nat.pos_of_ne_zero (by
          intro hn
          exact hanOrder_ne_zero (by simp [hO, hn]))
      rw [han.meromorphicOrderAt_eq, hO, ENat.map_natCast, WithTop.untopD_coe]
      exact_mod_cast hn_pos
lemma riemannZeta_one_le_order_positiveHeightZero {T : ℝ}
    (rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    (1 : ℤ) ≤ riemannZeta.order (rho : ℂ) := by
  exact_mod_cast riemannZeta_order_pos_positiveHeightZero rho
lemma riemannZeta_one_sub_ne_zero_of_one_le_re {w : ℂ}
    (hw_re : 1 ≤ w.re) (hcos : Complex.cos (↑Real.pi * w / 2) ≠ 0) :
    riemannZeta (1 - w) ≠ 0 := by
  have hw_neg_nat : ∀ n : ℕ, w ≠ -↑n := by
    intro n hn
    have hre' : w.re = -(n : ℝ) := by rw [hn]; simp
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [hre'] at hw_re; linarith
  have hw_ne_one : w ≠ 1 := by
    rintro rfl
    refine hcos ?_
    have h2 : (↑Real.pi * (1 : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [h2, ← Complex.ofReal_cos, Real.cos_pi_div_two, Complex.ofReal_zero]
  have hpow : (2 * ↑Real.pi : ℂ) ^ (-w) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]; left
    norm_num [Complex.ofReal_ne_zero, Real.pi_ne_zero]
  have hGamma : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hw_neg_nat
  have hzeta_w : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hw_re
  have hfe := riemannZeta_one_sub (s := w) hw_neg_nat hw_ne_one
  rw [hfe]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpow) hGamma) hcos) hzeta_w
lemma riemannZeta_ne_zero_of_re_nonpos_im_ne_zero {z : ℂ}
    (hre : z.re ≤ 0) (him : z.im ≠ 0) : riemannZeta z ≠ 0 := by
  set w : ℂ := 1 - z with hw
  have hw_im : w.im ≠ 0 := by rw [hw]; simp [him]
  have hw_re : 1 ≤ w.re := by rw [hw]; simp; linarith
  have hcos : Complex.cos (↑Real.pi * w / 2) ≠ 0 := by
    rw [Complex.cos_ne_zero_iff]
    intro k hk
    have hleft : (↑Real.pi * w / 2).im ≠ 0 := by
      rw [show (↑Real.pi * w / 2).im = Real.pi * w.im / 2 by
        simp [div_eq_mul_inv, mul_assoc]]
      exact div_ne_zero (mul_ne_zero Real.pi_ne_zero hw_im) two_ne_zero
    have hright : (((2 * (k : ℂ) + 1) * (Real.pi : ℂ) / 2).im) = 0 := by
      simp [div_eq_mul_inv, mul_assoc]
    exact hleft (by rw [hk, hright])
  have hres := riemannZeta_one_sub_ne_zero_of_one_le_re hw_re hcos
  rwa [show (1 : ℂ) - w = z by rw [hw]; ring] at hres
lemma positiveHeightZero_re_mem_Ioo {T : ℝ}
    (rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    (rho : ℂ).re ∈ Set.Ioo (0 : ℝ) 1 := by
  have him_pos : 0 < (rho : ℂ).im := rho.property.2.1.1
  have hzeta : riemannZeta (rho : ℂ) = 0 := rho.property.2.2
  have hnot_re_nonpos : ¬ (rho : ℂ).re ≤ 0 := by
    intro hre
    exact (riemannZeta_ne_zero_of_re_nonpos_im_ne_zero hre him_pos.ne') hzeta
  have hre_pos : 0 < (rho : ℂ).re := lt_of_not_ge hnot_re_nonpos
  have hnot_re_one_le : ¬ 1 ≤ (rho : ℂ).re := by
    intro hre
    exact (riemannZeta_ne_zero_of_one_le_re hre) hzeta
  have hre_lt_one : (rho : ℂ).re < 1 := lt_of_not_ge hnot_re_one_le
  exact ⟨hre_pos, hre_lt_one⟩
lemma zeroes_rect_univ_positive_height_finite (T : ℝ) :
    (riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)).Finite := by
  have hsub :
      riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T) ⊆
        riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.Ioo 0 T) := by
    intro z hz
    exact ⟨positiveHeightZero_re_mem_Ioo ⟨z, hz⟩, hz.2.1, hz.2.2⟩
  exact (zeroes_rect_Ioo_critical_positive_height_finite T).subset hsub
abbrev ZeroHeightNontrivialZeros : Type :=
  {rho : NontrivialZeros // (rho : ℂ).im = 0}
def zeroHeightNontrivialZeroEquivZeroesRectZero :
    ZeroHeightNontrivialZeros ≃
      riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.Icc 0 0) where
  toFun rho :=
    ⟨(rho : ℂ),
      rho.1.property.1,
      by simp [rho.2],
      rho.1.property.2.2⟩
  invFun rho :=
    ⟨⟨(rho : ℂ),
        rho.property.1,
        Set.mem_univ _,
        rho.property.2.2⟩,
      by exact le_antisymm rho.property.2.1.2 rho.property.2.1.1⟩
  left_inv rho := by
    ext
    rfl
  right_inv rho := by
    ext
    rfl
def zeroSquareTail (a : ℂ) (rho : NontrivialZeros) : ℝ :=
  (‖a - (rho : ℂ)‖)⁻¹ ^ (2 : ℕ)
def zeroSquareTailSummable (a : ℂ) : Prop :=
  Summable (fun rho : NontrivialZeros ↦ zeroSquareTail a rho)
def zeroImagSquareTail (rho : NontrivialZeros) : ℝ :=
  |(rho : ℂ).im|⁻¹ ^ (2 : ℕ)
def zeroImagSquareTailSummable : Prop :=
  Summable (fun rho : NontrivialZeros ↦ zeroImagSquareTail rho)
def zeroHeightDyadicShell (k : ℕ) (rho : NontrivialZeros) : Prop :=
  (2 : ℝ) ^ k ≤ |(rho : ℂ).im| ∧ |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)
def zeroImagDyadicShellSummableSource : Prop :=
  Summable
    (fun p : Sigma (fun k : ℕ =>
        {rho : NontrivialZeros // zeroHeightDyadicShell k rho}) =>
      zeroImagSquareTail p.2.1)
def zeroHeightDyadicShellMass (k : ℕ) : ℝ :=
  ∑' rho : {rho : NontrivialZeros // zeroHeightDyadicShell k rho},
    zeroImagSquareTail rho.1
def zeroImagDyadicShellCountBoundSource : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
    (Nat.card {rho : NontrivialZeros // zeroHeightDyadicShell k rho} : ℝ) ≤
      C * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k)
def zeroImagDyadicCumulativeCountBoundSource : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
    (Nat.card {rho : NontrivialZeros //
        |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)} : ℝ) ≤
      C * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k)
def zetaCountingMainTerm (T : ℝ) : ℝ :=
  T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8
def zetaCountingBacklundMajorant (b₁ b₂ b₃ T : ℝ) : ℝ :=
  |zetaCountingMainTerm T| + riemannZeta.RvM b₁ b₂ b₃ T
def zetaCountingDyadicMajorant (b₁ b₂ b₃ : ℝ) (k : ℕ) : ℝ :=
  zetaCountingBacklundMajorant b₁ b₂ b₃ ((2 : ℝ) ^ (k + 1))
def zetaCountingMainTermDyadicGrowthSource : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
    |zetaCountingMainTerm ((2 : ℝ) ^ (k + 1))| ≤
      C * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k)
def zetaCountingDyadicMajorantGrowthSource : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
    zetaCountingDyadicMajorant 0.137 0.443 6.1 k ≤
      C * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k)
def zeroImagDyadicCumulativeCountByNSource : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ k : ℕ,
    (Nat.card {rho : NontrivialZeros //
        |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)} : ℝ) ≤
      A * |riemannZeta.N ((2 : ℝ) ^ (k + 1))|
def zeroImagDyadicCumulativeCountByNWithZeroHeightSource : Prop :=
  ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧ ∀ k : ℕ,
    (Nat.card {rho : NontrivialZeros //
        |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)} : ℝ) ≤
      A * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| + D
def zeroImagDyadicAbsToPositiveCountSource : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ k : ℕ,
    (Nat.card {rho : NontrivialZeros //
        |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)} : ℝ) ≤
      A * (Nat.card {rho : NontrivialZeros //
        0 < (rho : ℂ).im ∧ (rho : ℂ).im < (2 : ℝ) ^ (k + 1)} : ℝ)
def zeroImagDyadicAbsToPositiveCountWithZeroHeightSource : Prop :=
  ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧ ∀ k : ℕ,
    (Nat.card {rho : NontrivialZeros //
        |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)} : ℝ) ≤
      A * (Nat.card {rho : NontrivialZeros //
        0 < (rho : ℂ).im ∧ (rho : ℂ).im < (2 : ℝ) ^ (k + 1)} : ℝ) + D
def zeroImagDyadicNPrimeToNSource : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ,
    |riemannZeta.N' 0 ((2 : ℝ) ^ (k + 1))| ≤
      B * |riemannZeta.N ((2 : ℝ) ^ (k + 1))|
def zeroImagDyadicNOrderSummableSource : Prop :=
  ∀ k : ℕ,
    Summable (fun rho : riemannZeta.zeroes_rect (.univ : Set ℝ)
        (.Ioo 0 ((2 : ℝ) ^ (k + 1))) =>
      (riemannZeta.order (rho : ℂ) : ℝ))
def zeroImagDyadicShellMassBoundSource : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
    zeroHeightDyadicShellMass k ≤ C * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ)⁻¹) ^ k
def highZeroToDyadicShell (rho : {rho : NontrivialZeros // 1 ≤ |(rho : ℂ).im|}) :
    Sigma (fun k : ℕ => {rho : NontrivialZeros // zeroHeightDyadicShell k rho}) :=
  let hnear := exists_nat_pow_near
    (x := |((rho.1 : ℂ).im)|) (y := (2 : ℝ)) rho.2 (by norm_num)
  ⟨hnear.choose, ⟨rho.1, hnear.choose_spec⟩⟩
def dyadicShellToCumulative (k : ℕ) :
    {rho : NontrivialZeros // zeroHeightDyadicShell k rho} →
      {rho : NontrivialZeros // |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)} :=
  fun rho => ⟨rho.1, rho.2.2⟩
noncomputable def weightedZeroHeightBucket : ℝ :=
  ∑' ρ : ZeroHeightNontrivialZeros,
    ((riemannZeta.order ((ρ : NontrivialZeros) : ℂ) : ℤ) : ℝ)
end Kadiri
end
end
end CertificatePort66

section CertificatePort67
section
open Complex
theorem riemannZeta_re_mem_Ioo_of_eq_zero_of_im_ne_zero {s : ℂ}
    (hz : riemannZeta s = 0) (him : s.im ≠ 0) : s.re ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨not_le.mp fun h ↦ Kadiri.riemannZeta_ne_zero_of_re_nonpos_im_ne_zero h him hz,
    not_le.mp fun h ↦ riemannZeta_ne_zero_of_one_le_re h hz⟩
theorem riemannZeta.N_eq_tsum_riemannXi_order (T : ℝ) :
    riemannZeta.N T =
      ∑' ρ : {z : ℂ // riemannXi z = 0 ∧ z.re ∈ Set.Ioo (0 : ℝ) 1 ∧ z.im ∈ Set.Ioo (0 : ℝ) T},
        (((meromorphicOrderAt riemannXi (ρ : ℂ)).untopD 0 : ℤ) : ℝ) := by
  have hset : riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 T) =
      {z : ℂ | riemannXi z = 0 ∧ z.re ∈ Set.Ioo (0 : ℝ) 1 ∧ z.im ∈ Set.Ioo (0 : ℝ) T} := by
    ext z
    constructor
    · rintro ⟨-, hzim, hzero⟩
      have hre := riemannZeta_re_mem_Ioo_of_eq_zero_of_im_ne_zero hzero hzim.1.ne'
      obtain ⟨hre0, hre1⟩ := Set.mem_Ioo.mp hre
      exact ⟨(riemannXi_eq_zero_iff hre0 hre1).mpr hzero, hre, hzim⟩
    · rintro ⟨hxi, hre, hzim⟩
      obtain ⟨hre0, hre1⟩ := Set.mem_Ioo.mp hre
      exact ⟨Set.mem_univ _, hzim, (riemannXi_eq_zero_iff hre0 hre1).mp hxi⟩
  calc riemannZeta.N T
      = ∑' ρ : ↥(riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 T)),
          (((meromorphicOrderAt riemannXi (ρ : ℂ)).untopD 0 : ℤ) : ℝ) := by
        simp only [riemannZeta.N, riemannZeta.zeroes_sum]
        refine tsum_congr fun ρ ↦ ?_
        obtain ⟨-, hzim, hzero⟩ := ρ.property
        obtain ⟨hre0, hre1⟩ := Set.mem_Ioo.mp
          (riemannZeta_re_mem_Ioo_of_eq_zero_of_im_ne_zero hzero hzim.1.ne')
        simp only [one_mul, riemannZeta.order,
          meromorphicOrderAt_riemannXi_eq_riemannZeta hre0 hre1]
    _ = _ := (Equiv.setCongr hset).tsum_eq
        (fun ρ ↦ (((meromorphicOrderAt riemannXi (ρ : ℂ)).untopD 0 : ℤ) : ℝ))
private theorem eq_ofReal_re_add_I_mul {T : ℝ} {z : ℂ} (hz : z.im = T) :
    z = (↑z.re : ℂ) + Complex.I * (T : ℂ) := by
  apply Complex.ext <;> simp [hz]
theorem riemannZeta_ne_zero_of_forall_re_mem_Ico {T : ℝ} (hT : 0 < T)
    (h : ∀ σ : ℝ, σ ∈ Set.Ico (1 / 2 : ℝ) 1 →
      riemannZeta ((σ : ℂ) + Complex.I * (T : ℂ)) ≠ 0) :
    ∀ s : ℂ, s.im = T → riemannZeta s ≠ 0 := by
  intro s hs hz0
  have him : s.im ≠ 0 := by rw [hs]; exact hT.ne'
  obtain ⟨hre0, hre1⟩ := Set.mem_Ioo.mp (riemannZeta_re_mem_Ioo_of_eq_zero_of_im_ne_zero hz0 him)
  have hxi : riemannXi s = 0 := (riemannXi_eq_zero_iff hre0 hre1).mpr hz0
  rcases le_or_gt (1 / 2 : ℝ) s.re with hge | hlt
  ·
    apply h s.re ⟨hge, hre1⟩
    rw [← eq_ofReal_re_add_I_mul hs]; exact hz0
  ·
    set w : ℂ := 1 - starRingEnd ℂ s with hw
    have hxi_w : riemannXi w = 0 := by
      rw [hw, riemannXi_one_sub, riemannXi_conj, hxi, map_zero]
    have hw_re : w.re = 1 - s.re := by simp [hw]
    have hw_im : w.im = T := by rw [hw]; simp [hs]
    apply h w.re ⟨by rw [hw_re]; linarith, by rw [hw_re]; linarith⟩
    rw [← eq_ofReal_re_add_I_mul hw_im]
    exact (riemannXi_eq_zero_iff (by rw [hw_re]; linarith) (by rw [hw_re]; linarith)).mp hxi_w
end
end CertificatePort67

section CertificatePort68
section
open Complex Set
theorem riemannXi_re_mem_Ioo_of_eq_zero {s : ℂ} (hs : riemannXi s = 0) :
    s.re ∈ Set.Ioo (0 : ℝ) 1 := by
  have hge : ∀ z : ℂ, 1 ≤ z.re → riemannXi z ≠ 0 := by
    intro z hz hzero
    have hz0 : z ≠ 0 := by rintro rfl; rw [Complex.zero_re] at hz; norm_num at hz
    have hz1 : z ≠ 1 := by rintro rfl; rw [riemannXi_one] at hzero; norm_num at hzero
    have hΓ : Complex.Gammaℝ z ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
    rw [riemannXi_eq_prefactor_mul hz0 hz1 hΓ] at hzero
    exact mul_ne_zero (prefactor_ne_zero_of hz0 hz1 hΓ)
      (riemannZeta_ne_zero_of_one_le_re hz) hzero
  refine ⟨?_, ?_⟩
  · by_contra h
    rw [not_lt] at h
    have h1 : 1 ≤ (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    exact hge (1 - s) h1 (by rw [riemannXi_one_sub]; exact hs)
  · by_contra h
    rw [not_lt] at h
    exact hge s h hs
theorem riemannZeta_eq_zero_of_riemannXi_eq_zero {s : ℂ} (hs : riemannXi s = 0) :
    riemannZeta s = 0 :=
  have h := riemannXi_re_mem_Ioo_of_eq_zero hs
  (riemannXi_eq_zero_iff h.1 h.2).mp hs
theorem riemannXi_ne_zero_of_im_eq_zero {z : ℂ} (hz : z.im = 0) : riemannXi z ≠ 0 := by
  intro hξ
  obtain ⟨hr0, hr1⟩ := riemannXi_re_mem_Ioo_of_eq_zero hξ
  have hz' : z = (↑z.re : ℂ) := by apply Complex.ext <;> simp [hz]
  rw [hz'] at hξ
  exact riemannXi_ofReal_ne_zero_of_mem_Icc ⟨by linarith, by linarith⟩ hξ
private theorem argVariation_riemannXi_seg (z₀ z₁ : ℂ)
    (hre : ∀ u ∈ Set.Icc (0 : ℝ) 1, 0 < (lineSeg z₀ z₁ u).re)
    (hne1 : ∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg z₀ z₁ u ≠ 1)
    (hζ : ∀ u ∈ Set.Icc (0 : ℝ) 1, riemannZeta (lineSeg z₀ z₁ u) ≠ 0) :
    argVariation 0 1 (fun u ↦ riemannXi (lineSeg z₀ z₁ u))
      = argVariation 0 1
          (fun u ↦ (1 / 2 : ℂ) * (lineSeg z₀ z₁ u * (lineSeg z₀ z₁ u - 1)))
        + argVariation 0 1 (fun u ↦ Complex.Gammaℝ (lineSeg z₀ z₁ u))
        + argVariation 0 1 (fun u ↦ riemannZeta (lineSeg z₀ z₁ u)) := by
  have hsne : ∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg z₀ z₁ u ≠ 0 := by
    intro u hu heq; simpa [heq] using hre u hu
  have hPcont : ContinuousOn
      (fun u ↦ (1 / 2 : ℂ) * (lineSeg z₀ z₁ u * (lineSeg z₀ z₁ u - 1))) (Set.Icc 0 1) :=
    (continuous_const.mul ((continuous_lineSeg z₀ z₁).mul
      ((continuous_lineSeg z₀ z₁).sub continuous_const))).continuousOn
  have hGcont : ContinuousOn (fun u ↦ Complex.Gammaℝ (lineSeg z₀ z₁ u)) (Set.Icc 0 1) := by
    intro u hu
    exact ContinuousAt.comp_continuousWithinAt (g := Complex.Gammaℝ) (f := lineSeg z₀ z₁)
      (Complex.analyticAt_Gammaℝ (hre u hu)).continuousAt
      (continuous_lineSeg z₀ z₁).continuousWithinAt
  have hZcont : ContinuousOn (fun u ↦ riemannZeta (lineSeg z₀ z₁ u)) (Set.Icc 0 1) := by
    intro u hu
    exact ContinuousAt.comp_continuousWithinAt (g := riemannZeta) (f := lineSeg z₀ z₁)
      (differentiableAt_riemannZeta (hne1 u hu)).continuousAt
      (continuous_lineSeg z₀ z₁).continuousWithinAt
  have hPne : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      (1 / 2 : ℂ) * (lineSeg z₀ z₁ u * (lineSeg z₀ z₁ u - 1)) ≠ 0 := fun u hu ↦
    mul_ne_zero (one_div_ne_zero two_ne_zero)
      (mul_ne_zero (hsne u hu) (sub_ne_zero.mpr (hne1 u hu)))
  have hGne : ∀ u ∈ Set.Icc (0 : ℝ) 1, Complex.Gammaℝ (lineSeg z₀ z₁ u) ≠ 0 :=
    fun u hu ↦ Complex.Gammaℝ_ne_zero_of_re_pos (hre u hu)
  have hEq : Set.EqOn (fun u ↦ riemannXi (lineSeg z₀ z₁ u))
      (((fun u ↦ (1 / 2 : ℂ) * (lineSeg z₀ z₁ u * (lineSeg z₀ z₁ u - 1)))
        * (fun u ↦ Complex.Gammaℝ (lineSeg z₀ z₁ u)))
        * (fun u ↦ riemannZeta (lineSeg z₀ z₁ u))) (Set.Icc 0 1) := by
    intro u hu
    change riemannXi (lineSeg z₀ z₁ u) = _
    rw [riemannXi_eq_prefactor_mul (hsne u hu) (hne1 u hu)
      (Complex.Gammaℝ_ne_zero_of_re_pos (hre u hu))]
    simp only [Pi.mul_apply]
  rw [argVariation_congr zero_le_one hEq,
    argVariation_mul zero_le_one (hPcont.mul hGcont)
      (fun u hu ↦ mul_ne_zero (hPne u hu) (hGne u hu)) hZcont hζ,
    argVariation_mul zero_le_one hPcont hPne hGcont hGne]
private theorem rectangle_corner_eq (T : ℝ) :
    (2 + I * (T : ℂ)).re = 2 ∧ (2 + I * (T : ℂ)).im = T
      ∧ (-1 : ℂ).re = -1 ∧ (-1 : ℂ).im = 0 :=
  ⟨by simp, by simp, by norm_num, by norm_num⟩
private theorem riemannXi_ne_zero_of_mem_rectangleBorder {T : ℝ}
    (hT' : ∀ s : ℂ, s.im = T → riemannZeta s ≠ 0) {ρ : ℂ}
    (hρ : ρ ∈ RectangleBorder (-1) (2 + I * (T : ℂ))) : riemannXi ρ ≠ 0 := by
  intro hξ
  obtain ⟨hr0, hr1⟩ := riemannXi_re_mem_Ioo_of_eq_zero hξ
  obtain ⟨hwre, hwim, hm1re, hm1im⟩ := rectangle_corner_eq T
  simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm, Set.mem_singleton_iff,
    hwre, hwim, hm1re, hm1im] at hρ
  rcases hρ with ((⟨_, him⟩ | ⟨hre, _⟩) | ⟨_, him⟩) | ⟨hre, _⟩
  ·
    exact riemannXi_ne_zero_of_im_eq_zero him hξ
  ·
    rw [hre] at hr0; norm_num at hr0
  ·
    exact hT' ρ him (riemannZeta_eq_zero_of_riemannXi_eq_zero hξ)
  ·
    rw [hre] at hr1; norm_num at hr1
theorem riemannZeta.N_eq {T : ℝ} (hT : 0 < T)
    (hT' : ∀ s : ℂ, s.im = T → riemannZeta s ≠ 0) :
    riemannZeta.N T = riemannSiegelTheta T / Real.pi + 1 + argZeta T := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  obtain ⟨hwre, hwim, hm1re, hm1im⟩ := rectangle_corner_eq T
  have hle_re : (-1 : ℂ).re ≤ (2 + I * (T : ℂ)).re := by rw [hm1re, hwre]; norm_num
  have hle_im : (-1 : ℂ).im ≤ (2 + I * (T : ℂ)).im := by rw [hm1im, hwim]; exact hT.le
  have hRS : (Rectangle (-1) (2 + I * (T : ℂ)) ∩ {ρ : ℂ | riemannXi ρ = 0})
      = {z : ℂ | riemannXi z = 0 ∧ z.re ∈ Set.Ioo (0 : ℝ) 1
          ∧ z.im ∈ Set.Ioo (0 : ℝ) T} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hzR, hξ⟩
      obtain ⟨hr0, hr1⟩ := riemannXi_re_mem_Ioo_of_eq_zero hξ
      rw [mem_Rect hle_re hle_im,
        hm1re, hm1im, hwre, hwim] at hzR
      obtain ⟨_, _, hzim0, hzimT⟩ := hzR
      exact ⟨hξ, ⟨hr0, hr1⟩,
        hzim0.lt_of_ne fun heq ↦ riemannXi_ne_zero_of_im_eq_zero heq.symm hξ,
        hzimT.lt_of_ne fun heq ↦ hT' z heq (riemannZeta_eq_zero_of_riemannXi_eq_zero hξ)⟩
    · rintro ⟨hξ, ⟨hr0, hr1⟩, hi0, hiT⟩
      refine ⟨?_, hξ⟩
      rw [mem_Rect hle_re hle_im,
        hm1re, hm1im, hwre, hwim]
      exact ⟨by linarith, by linarith, hi0.le, hiT.le⟩
  have hfin : (Rectangle (-1) (2 + I * (T : ℂ)) ∩ {ρ : ℂ | riemannXi ρ = 0}).Finite := by
    have hcompact : IsCompact (Rectangle (-1) (2 + I * (T : ℂ))) :=
      isCompact_uIcc.reProdIm isCompact_uIcc
    refine (riemannZeta.zeroes_on_Compact_finite' hcompact).subset ?_
    rintro z ⟨hzR, hξ⟩
    exact ⟨hzR, riemannZeta_eq_zero_of_riemannXi_eq_zero hξ⟩
  have hap : (∑ ρ ∈ hfin.toFinset, (((meromorphicOrderAt riemannXi ρ).untopD 0 : ℤ) : ℝ))
      = 1 / (2 * Real.pi) * rectangleArgVariation riemannXi (-1) (2 + I * (T : ℂ)) := by
    refine rectangle_zero_count_eq_argVariation (z := (-1 : ℂ)) (w := 2 + I * (T : ℂ))
      (z₀ := (2 : ℂ)) analyticOnNhd_riemannXi
      isConnected_univ (Set.mem_univ _) ?_ (Set.subset_univ _) hle_re hle_im
      (fun ρ hρ ↦ riemannXi_ne_zero_of_mem_rectangleBorder hT' hρ) hfin
    have h2 := riemannXi_ofReal_ne_zero_of_mem_Icc (σ := 2) ⟨by norm_num, le_refl _⟩
    simpa using h2
  have hbridge : (∑' ρ : {z : ℂ // riemannXi z = 0 ∧ z.re ∈ Set.Ioo (0 : ℝ) 1
        ∧ z.im ∈ Set.Ioo (0 : ℝ) T},
      (((meromorphicOrderAt riemannXi (ρ : ℂ)).untopD 0 : ℤ) : ℝ))
      = ∑ ρ ∈ hfin.toFinset, (((meromorphicOrderAt riemannXi ρ).untopD 0 : ℤ) : ℝ) := by
    rw [← Finset.tsum_subtype' hfin.toFinset
        (fun ρ ↦ (((meromorphicOrderAt riemannXi ρ).untopD 0 : ℤ) : ℝ)), hfin.coe_toFinset]
    exact (Equiv.setCongr hRS.symm).tsum_eq
      (fun ρ ↦ (((meromorphicOrderAt riemannXi (ρ : ℂ)).untopD 0 : ℤ) : ℝ))
  have hhalf := argVariation_riemannXi_rectangle_eq_two_mul hT hT'
  have h2re : (2 : ℂ).re = 2 := by norm_num
  have hc2re : (1 / 2 + I * (T : ℂ)).re = 1 / 2 := by simp
  have hc2im : (1 / 2 + I * (T : ℂ)).im = T := by simp
  have hcontour : argVariationContourL riemannXi T
      = argVariationContourL (fun s ↦ (1 / 2 : ℂ) * (s * (s - 1))) T
        + argVariationContourL Complex.Gammaℝ T + argVariationContourL riemannZeta T := by
    have hseg1 := argVariation_riemannXi_seg 2 (2 + I * (T : ℂ))
      (fun u _ ↦ by rw [lineSeg_re, h2re, hwre]; norm_num)
      (fun u _ heq ↦ by
        have := congrArg Complex.re heq
        rw [lineSeg_re, h2re, hwre, Complex.one_re] at this; norm_num at this)
      (fun u _ ↦ riemannZeta_ne_zero_of_one_le_re (by rw [lineSeg_re, h2re, hwre]; norm_num))
    have hseg2 := argVariation_riemannXi_seg (2 + I * (T : ℂ)) (1 / 2 + I * (T : ℂ))
      (fun u hu ↦ by rw [lineSeg_re, hwre, hc2re]; nlinarith [hu.1, hu.2])
      (fun u _ heq ↦ by
        have := congrArg Complex.im heq
        rw [lineSeg_im, hwim, hc2im, Complex.one_im] at this
        simp only [sub_self, mul_zero, add_zero] at this; exact hT.ne' this)
      (fun u _ ↦ hT' _ (by rw [lineSeg_im, hwim, hc2im]; ring))
    simp only [argVariationContourL]
    rw [hseg1, hseg2]; ring
  rw [argVariation_poly_L hT, argVariation_GammaPi_L hT] at hcontour
  have hZval : argVariationContourL riemannZeta T = Real.pi * argZeta T := by
    rw [argZeta]; field_simp
  rw [riemannZeta.N_eq_tsum_riemannXi_order, hbridge, hap, hhalf, hcontour, hZval]
  field_simp
  ring
theorem riemannZeta.N_eq_of_forall_re_mem_Ico {T : ℝ} (hT : 0 < T)
    (h : ∀ σ : ℝ, σ ∈ Set.Ico (1 / 2 : ℝ) 1 →
      riemannZeta ((σ : ℂ) + Complex.I * (T : ℂ)) ≠ 0) :
    riemannZeta.N T = riemannSiegelTheta T / Real.pi + 1 + argZeta T :=
  riemannZeta.N_eq hT (riemannZeta_ne_zero_of_forall_re_mem_Ico hT h)
end
end CertificatePort68

section CertificatePort69
section
open Complex Filter Topology Function Set
open Complex.Stirling
open scoped Real
instance : Countable RiemannXiZerosIndex := by
  have : Countable ↥(MeromorphicOn.divisor riemannXi ⊤).support :=
    ((HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
      (MeromorphicOn.divisor riemannXi ⊤).discreteSupport).to_subtype
  infer_instance
theorem AnalyticAt.conj_conj {g : ℂ → ℂ} {u : ℂ}
    (hg : AnalyticAt ℂ g (starRingEnd ℂ u)) :
    AnalyticAt ℂ (fun w ↦ starRingEnd ℂ (g (starRingEnd ℂ w))) u := by
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [Complex.continuous_conj.continuousAt.eventually
    (hg.eventually_analyticAt.mono fun y hy ↦ hy.differentiableAt)] with w hw
  simpa [Function.comp_def] using hw.conj_conj
private theorem analyticAt_riemannXi (w : ℂ) : AnalyticAt ℂ riemannXi w :=
  differentiable_riemannXi.analyticAt w
private theorem analyticOrderAt_riemannXi_ne_top (w : ℂ) :
    analyticOrderAt riemannXi w ≠ ⊤ := by
  rw [ne_eq, AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero w analyticAt_riemannXi]
  intro h
  simpa [riemannXi_zero] using congrFun h 0
theorem analyticOrderAt_riemannXi_conj (z : ℂ) :
    analyticOrderAt riemannXi (starRingEnd ℂ z) = analyticOrderAt riemannXi z := by
  set N := analyticOrderNatAt riemannXi z
  obtain ⟨g, hg, hg0, hfac⟩ :=
    (analyticAt_riemannXi z).analyticOrderAt_ne_top.mp (analyticOrderAt_riemannXi_ne_top z)
  have hgconj : AnalyticAt ℂ (fun u ↦ starRingEnd ℂ (g (starRingEnd ℂ u))) (starRingEnd ℂ z) :=
    AnalyticAt.conj_conj (u := starRingEnd ℂ z) (by rw [Complex.conj_conj]; exact hg)
  have hval : (fun u ↦ starRingEnd ℂ (g (starRingEnd ℂ u))) (starRingEnd ℂ z) ≠ 0 := by
    simp only [Complex.conj_conj]
    exact fun h ↦ hg0 (by simpa using congrArg (starRingEnd ℂ) h)
  have hfac2 : riemannXi =ᶠ[𝓝 (starRingEnd ℂ z)]
      fun u ↦ (u - starRingEnd ℂ z) ^ N • (starRingEnd ℂ (g (starRingEnd ℂ u))) := by
    have hc : ContinuousAt (starRingEnd ℂ) (starRingEnd ℂ z) :=
      Complex.continuous_conj.continuousAt
    have hpull : ∀ᶠ u in 𝓝 (starRingEnd ℂ z),
        riemannXi (starRingEnd ℂ u) = (starRingEnd ℂ u - z) ^ N • g (starRingEnd ℂ u) := by
      have hbase : ∀ᶠ y in 𝓝 (starRingEnd ℂ (starRingEnd ℂ z)),
          riemannXi y = (y - z) ^ N • g y := by rw [Complex.conj_conj]; exact hfac
      exact hc.eventually hbase
    filter_upwards [hpull] with u hu
    have h2 := congrArg (starRingEnd ℂ) hu
    simp only [smul_eq_mul, map_mul, map_pow, map_sub, riemannXi_conj, Complex.conj_conj] at h2
    simpa only [smul_eq_mul] using h2
  have hcz : analyticOrderNatAt riemannXi (starRingEnd ℂ z) = N := by
    rw [(analyticAt_riemannXi (starRingEnd ℂ z)).analyticOrderNatAt_eq_iff
      (analyticOrderAt_riemannXi_ne_top _)]
    exact ⟨_, hgconj, hval, hfac2⟩
  rw [← Nat.cast_analyticOrderNatAt (analyticOrderAt_riemannXi_ne_top (starRingEnd ℂ z)),
    ← Nat.cast_analyticOrderNatAt (analyticOrderAt_riemannXi_ne_top z), hcz]
theorem analyticOrderAt_riemannXi_one_sub (z : ℂ) :
    analyticOrderAt riemannXi (1 - z) = analyticOrderAt riemannXi z := by
  have hcomp : analyticOrderAt (riemannXi ∘ fun w ↦ 1 - w) z
      = analyticOrderAt riemannXi ((fun w ↦ 1 - w) z) := by
    refine analyticOrderAt_comp_of_deriv_ne_zero (analyticAt_const.sub analyticAt_id) ?_
    have hd : deriv (fun w : ℂ ↦ 1 - w) z = -1 := ((hasDerivAt_id z).const_sub (1 : ℂ)).deriv
    rw [hd]; exact neg_ne_zero.mpr one_ne_zero
  have hfun : (riemannXi ∘ fun w ↦ 1 - w) = riemannXi := by
    funext w; simp only [comp_apply, riemannXi_one_sub]
  rw [hfun] at hcomp
  exact hcomp.symm
theorem analyticOrderAt_riemannXi_one_sub_conj (z : ℂ) :
    analyticOrderAt riemannXi (1 - starRingEnd ℂ z) = analyticOrderAt riemannXi z := by
  rw [analyticOrderAt_riemannXi_one_sub, analyticOrderAt_riemannXi_conj]
theorem divisor_riemannXi_one_sub_conj (z : ℂ) :
    MeromorphicOn.divisor riemannXi ⊤ (1 - starRingEnd ℂ z)
      = MeromorphicOn.divisor riemannXi ⊤ z := by
  have hf : AnalyticOnNhd ℂ riemannXi ⊤ := analyticOnNhd_riemannXi
  rw [divisor_eq_analyticOrderNatAt hf, divisor_eq_analyticOrderNatAt hf]
  simp only [analyticOrderNatAt, analyticOrderAt_riemannXi_one_sub_conj]
theorem exists_equiv_riemannXiZeros_one_sub_conj :
    ∃ e : RiemannXiZerosIndex ≃ RiemannXiZerosIndex,
      ∀ i, riemannXiZeros (e i) = 1 - starRingEnd ℂ (riemannXiZeros i) := by
  let F : (MeromorphicOn.divisor riemannXi ⊤).support →
      (MeromorphicOn.divisor riemannXi ⊤).support :=
    fun a ↦ ⟨1 - starRingEnd ℂ (a : ℂ), by
      rw [mem_support, divisor_riemannXi_one_sub_conj]
      exact mem_support.mp a.2⟩
  have hFinv : Involutive F := by
    intro a
    apply Subtype.ext
    change 1 - starRingEnd ℂ (1 - starRingEnd ℂ (a : ℂ)) = (a : ℂ)
    simp only [map_sub, map_one, Complex.conj_conj]; ring
  let eSupp := hFinv.toPerm F
  have hfib : ∀ a : (MeromorphicOn.divisor riemannXi ⊤).support,
      (MeromorphicOn.divisor riemannXi ⊤ (a : ℂ)).toNat
        = (MeromorphicOn.divisor riemannXi ⊤ (eSupp a : ℂ)).toNat := by
    intro a
    change (MeromorphicOn.divisor riemannXi ⊤ (a : ℂ)).toNat
      = (MeromorphicOn.divisor riemannXi ⊤ (1 - starRingEnd ℂ (a : ℂ))).toNat
    rw [divisor_riemannXi_one_sub_conj]
  refine ⟨Equiv.sigmaCongr eSupp (fun a ↦ finCongr (hfib a)), ?_⟩
  rintro ⟨a, k⟩
  rfl
theorem tsum_riemannXiZeros_one_sub_conj {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    (g : ℂ → M) :
    ∑' i, g (riemannXiZeros i) = ∑' i, g (1 - starRingEnd ℂ (riemannXiZeros i)) := by
  obtain ⟨e, hval⟩ := exists_equiv_riemannXiZeros_one_sub_conj
  calc ∑' i, g (riemannXiZeros i)
      = ∑' i, g (riemannXiZeros (e i)) := (e.tsum_eq (fun i ↦ g (riemannXiZeros i))).symm
    _ = ∑' i, g (1 - starRingEnd ℂ (riemannXiZeros i)) := by simp_rw [hval]
theorem summable_riemannXiZeros_one_sub_conj_iff {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    (g : ℂ → M) :
    Summable (fun i ↦ g (1 - starRingEnd ℂ (riemannXiZeros i)))
      ↔ Summable (fun i ↦ g (riemannXiZeros i)) := by
  obtain ⟨e, hval⟩ := exists_equiv_riemannXiZeros_one_sub_conj
  have hcomp : (fun i ↦ g (1 - starRingEnd ℂ (riemannXiZeros i)))
      = (fun j ↦ g (riemannXiZeros j)) ∘ e := by
    ext i; simp only [Function.comp_apply, hval i]
  rw [hcomp, Equiv.summable_iff]
theorem riemannXi_riemannXiZeros_eq_zero (i : RiemannXiZerosIndex) :
    riemannXi (riemannXiZeros i) = 0 := by
  have hf : AnalyticOnNhd ℂ riemannXi ⊤ := analyticOnNhd_riemannXi
  have hmem : MeromorphicOn.divisor riemannXi ⊤ (riemannXiZeros i) ≠ 0 := by
    have := i.1.2; rwa [Function.mem_support] at this
  rw [divisor_eq_analyticOrderNatAt hf] at hmem
  have hnat : analyticOrderNatAt riemannXi (riemannXiZeros i) ≠ 0 := by
    intro h; rw [h] at hmem; simp at hmem
  have hAt : AnalyticAt ℂ riemannXi (riemannXiZeros i) := differentiable_riemannXi.analyticAt _
  rw [← hAt.analyticOrderAt_ne_zero]
  intro hz
  exact hnat (by simp [analyticOrderNatAt, hz])
theorem riemannXiZeros_re_pos (i : RiemannXiZerosIndex) : 0 < (riemannXiZeros i).re :=
  (riemannXi_re_mem_Ioo_of_eq_zero (riemannXi_riemannXiZeros_eq_zero i)).1
theorem riemannXiZeros_re_lt_one (i : RiemannXiZerosIndex) : (riemannXiZeros i).re < 1 :=
  (riemannXi_re_mem_Ioo_of_eq_zero (riemannXi_riemannXiZeros_eq_zero i)).2
private lemma abs_re_inv_le_norm_sq {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    |(ρ⁻¹).re| ≤ ‖ρ⁻¹‖ ^ 2 := by
  have hne : ρ ≠ 0 := fun h ↦ by rw [h] at h0; simp at h0
  have hns : 0 < Complex.normSq ρ := Complex.normSq_pos.mpr hne
  have hsq : ‖ρ⁻¹‖ ^ 2 = (Complex.normSq ρ)⁻¹ := by rw [norm_inv, inv_pow, Complex.sq_norm]
  rw [Complex.inv_re, hsq, abs_div, abs_of_pos h0, abs_of_pos hns, div_le_iff₀ hns,
    inv_mul_cancel₀ (ne_of_gt hns)]
  exact h1.le
theorem summable_re_inv_riemannXiZeros :
    Summable fun i ↦ ((riemannXiZeros i)⁻¹).re := by
  refine Summable.of_norm_bounded summable_inv_norm_sq_riemannXiZeros (fun i ↦ ?_)
  rw [Real.norm_eq_abs]
  exact abs_re_inv_le_norm_sq (riemannXiZeros_re_pos i) (riemannXiZeros_re_lt_one i)
private lemma log_norm_one_sub_div {ρ : ℂ} (hρ : ρ ≠ 0) {w : ℂ} (hw : w ≠ ρ) :
    Real.log ‖1 - w / ρ‖ = Real.log ‖w - ρ‖ - Real.log ‖ρ‖ := by
  have hh : (1 : ℂ) - w / ρ = (ρ - w) / ρ := by rw [sub_div, div_self hρ]
  rw [hh, norm_div, Real.log_div (norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun h ↦ hw h.symm))
    (norm_ne_zero_iff.mpr hρ), norm_sub_rev]
noncomputable def shiftLogIntegrand (t d : ℝ) (ρ : ℂ) (x : ℝ) : ℝ :=
    Real.log ‖(1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ) - ρ‖
      - Real.log ‖(1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I - ρ‖
noncomputable def shiftLogIntegral (t d : ℝ) (ρ : ℂ) : ℝ :=
    ∫ x in (0 : ℝ)..d, shiftLogIntegrand t d ρ x
private lemma abs_log_norm_one_sub_add_re_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    |Real.log ‖1 - z‖ + z.re| ≤ ‖z‖ ^ 2 := by
  have h : Real.log ‖1 - z‖ + z.re = (Complex.log (1 - z) + z).re := by
    rw [Complex.add_re, Complex.log_re]
  rw [h]
  exact (Complex.abs_re_le_norm _).trans (Complex.norm_log_one_sub_add_self_le hz)
private lemma abs_log_norm_one_sub_div_add_re_le {z ρ : ℂ} {C : ℝ} (hz : ‖z‖ ≤ C)
    (hsmall : C * ‖ρ⁻¹‖ ≤ 1 / 2) :
    |Real.log ‖1 - z / ρ‖ + (z / ρ).re| ≤ C ^ 2 * ‖ρ⁻¹‖ ^ 2 := by
  have hle : ‖z / ρ‖ ≤ C * ‖ρ⁻¹‖ := by
    rw [norm_div, norm_inv, div_eq_mul_inv]; gcongr
  calc |Real.log ‖1 - z / ρ‖ + (z / ρ).re| ≤ ‖z / ρ‖ ^ 2 :=
        abs_log_norm_one_sub_add_re_le (hle.trans hsmall)
    _ ≤ (C * ‖ρ⁻¹‖) ^ 2 := by gcongr
    _ = C ^ 2 * ‖ρ⁻¹‖ ^ 2 := by ring
private lemma sub_ne_zero_of_im_eq {z c : ℂ} {t : ℝ} (hz : z.im = t) (hc : c.im ≠ t) :
    z - c ≠ 0 := fun h ↦ hc (by
  have := congrArg Complex.im h
  rw [Complex.sub_im, hz, Complex.zero_im, sub_eq_zero] at this
  exact this.symm)
private lemma complex_line_im (a b : ℝ) : ((1 / 2 : ℂ) + (a : ℂ) + (b : ℂ) * I).im = b := by
  simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
private lemma complex_line_re (a b : ℝ) :
    ((1 / 2 : ℂ) + (a : ℂ) + (b : ℂ) * I).re = 1 / 2 + a := by
  simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
private lemma complex_line_add_im (a b c : ℝ) :
    ((1 / 2 : ℂ) + (a : ℂ) + (b : ℂ) * I + (c : ℂ)).im = b := by
  rw [Complex.add_im, complex_line_im, Complex.ofReal_im, add_zero]
private lemma shiftLogIntegrand_eq {ρ : ℂ} (hρ : ρ ≠ 0) (t d x : ℝ)
    (h1 : (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ) ≠ ρ)
    (h2 : (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I ≠ ρ) :
    shiftLogIntegrand t d ρ x
      = ((Real.log ‖1 - ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ)) / ρ‖
            + (((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ)) / ρ).re)
          - (Real.log ‖1 - ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I) / ρ‖
            + (((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I) / ρ).re))
        - d * (ρ⁻¹).re := by
  have ere : (((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ)) / ρ).re
      - (((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I) / ρ).re = d * (ρ⁻¹).re := by
    rw [← Complex.sub_re,
      show ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ)) / ρ
          - ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I) / ρ = (d : ℂ) * ρ⁻¹ by
        rw [div_sub_div_same,
          show (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ)
              - ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I) = (d : ℂ) by ring,
          div_eq_mul_inv],
      Complex.re_ofReal_mul]
  unfold shiftLogIntegrand
  rw [log_norm_one_sub_div hρ h1, log_norm_one_sub_div hρ h2]
  linear_combination -ere
private lemma continuous_shiftLogIntegrand {ρ : ℂ} (t d : ℝ) (hρt : ρ.im ≠ t) :
    Continuous (shiftLogIntegrand t d ρ) := by
  unfold shiftLogIntegrand
  refine Continuous.sub (Continuous.log (by fun_prop) (fun x ↦ ?_))
    (Continuous.log (by fun_prop) (fun x ↦ ?_))
  · rw [norm_ne_zero_iff]
    exact sub_ne_zero_of_im_eq (z := (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ))
      (complex_line_add_im x t d) hρt
  · rw [norm_ne_zero_iff]
    exact sub_ne_zero_of_im_eq (z := (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I)
      (complex_line_im x t) hρt
private lemma bookerIntegrand_eq_shiftLog (ρ : ℂ) (t d x : ℝ) (hρt : ρ.im ≠ t) :
    Real.log ‖((x : ℂ) + (d : ℂ) + (ρ - (1 / 2 + (t : ℂ) * I)))
        * ((x : ℂ) + (d : ℂ) - (starRingEnd ℂ) (ρ - (1 / 2 + (t : ℂ) * I)))
        / (((x : ℂ) + (ρ - (1 / 2 + (t : ℂ) * I)))
            * ((x : ℂ) - (starRingEnd ℂ) (ρ - (1 / 2 + (t : ℂ) * I))))‖
      = shiftLogIntegrand t d ρ x + shiftLogIntegrand t d (1 - (starRingEnd ℂ) ρ) x := by
  have hc1 : (x : ℂ) + (d : ℂ) + (ρ - (1 / 2 + (t : ℂ) * I))
      = (starRingEnd ℂ)
        ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ) - (1 - (starRingEnd ℂ) ρ)) := by
    apply Complex.ext <;> simp <;> ring
  have hc2 : (x : ℂ) + (d : ℂ) - (starRingEnd ℂ) (ρ - (1 / 2 + (t : ℂ) * I))
      = (starRingEnd ℂ) ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ) - ρ) := by
    apply Complex.ext <;> simp; ring
  have hc3 : (x : ℂ) + (ρ - (1 / 2 + (t : ℂ) * I))
      = (starRingEnd ℂ) ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I - (1 - (starRingEnd ℂ) ρ)) := by
    apply Complex.ext <;> simp <;> ring
  have hc4 : (x : ℂ) - (starRingEnd ℂ) (ρ - (1 / 2 + (t : ℂ) * I))
      = (starRingEnd ℂ) ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I - ρ) := by
    apply Complex.ext <;> simp; ring
  have him : ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I).im = t := complex_line_im x t
  have himd : ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ)).im = t := complex_line_add_im x t d
  have hρstar : (1 - (starRingEnd ℂ) ρ).im ≠ t := by
    simpa [Complex.sub_im, Complex.one_im, Complex.conj_im] using hρt
  have hA1 := sub_ne_zero_of_im_eq himd hρstar
  have hA2 := sub_ne_zero_of_im_eq himd hρt
  have hA3 := sub_ne_zero_of_im_eq him hρstar
  have hA4 := sub_ne_zero_of_im_eq him hρt
  rw [norm_div, norm_mul, norm_mul, hc1, hc2, hc3, hc4, Complex.norm_conj, Complex.norm_conj,
    Complex.norm_conj, Complex.norm_conj,
    Real.log_div (mul_ne_zero (norm_ne_zero_iff.mpr hA1) (norm_ne_zero_iff.mpr hA2))
      (mul_ne_zero (norm_ne_zero_iff.mpr hA3) (norm_ne_zero_iff.mpr hA4)),
    Real.log_mul (norm_ne_zero_iff.mpr hA1) (norm_ne_zero_iff.mpr hA2),
    Real.log_mul (norm_ne_zero_iff.mpr hA3) (norm_ne_zero_iff.mpr hA4)]
  unfold shiftLogIntegrand
  ring
private lemma shiftLogIntegral_add_le_of {ρ : ℂ} (t : ℝ) {d : ℝ} (hd : 1 / 2 < d)
    (hρt : ρ.im ≠ t) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {c : ℝ} (hc : 2 ≤ c) :
    shiftLogIntegral t d ρ + shiftLogIntegral t d (1 - (starRingEnd ℂ) ρ)
      ≤ c * d ^ 2 * ((((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - ρ)⁻¹).re
          + (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - (1 - (starRingEnd ℂ) ρ))⁻¹).re) := by
  have hwre : |(ρ - (1 / 2 + (t : ℂ) * I)).re| ≤ 1 / 2 := by
    rw [show (ρ - (1 / 2 + (t : ℂ) * I)).re = ρ.re - 1 / 2 by simp]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hwim : (ρ - (1 / 2 + (t : ℂ) * I)).im ≠ 0 := by
    rw [show (ρ - (1 / 2 + (t : ℂ) * I)).im = ρ.im - t by simp]
    exact sub_ne_zero.mpr hρt
  have hbk := bookerPairIntegral_le_of hd hwre hwim hc
  have hresPlus : (1 / ((d : ℂ) + (ρ - (1 / 2 + (t : ℂ) * I)))).re
      = (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - (1 - (starRingEnd ℂ) ρ))⁻¹).re := by
    have hc : (d : ℂ) + (ρ - (1 / 2 + (t : ℂ) * I))
        = (starRingEnd ℂ) ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - (1 - (starRingEnd ℂ) ρ)) := by
      apply Complex.ext <;> simp <;> ring
    rw [one_div, hc, ← map_inv₀, Complex.conj_re]
  have hresMinus : (1 / ((d : ℂ) - (starRingEnd ℂ) (ρ - (1 / 2 + (t : ℂ) * I)))).re
      = (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - ρ)⁻¹).re := by
    have hc : (d : ℂ) - (starRingEnd ℂ) (ρ - (1 / 2 + (t : ℂ) * I))
        = (starRingEnd ℂ) ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - ρ) := by
      apply Complex.ext <;> simp; ring
    rw [one_div, hc, ← map_inv₀, Complex.conj_re]
  have hI1 : IntervalIntegrable (shiftLogIntegrand t d ρ) MeasureTheory.volume 0 d :=
    (continuous_shiftLogIntegrand t d hρt).intervalIntegrable 0 d
  have hI2 : IntervalIntegrable (shiftLogIntegrand t d (1 - (starRingEnd ℂ) ρ))
      MeasureTheory.volume 0 d := by
    refine (continuous_shiftLogIntegrand t d ?_).intervalIntegrable 0 d
    simp only [Complex.sub_im, Complex.one_im, Complex.conj_im, zero_sub, neg_neg]
    exact hρt
  have hLHS : bookerPairIntegral d (ρ - (1 / 2 + (t : ℂ) * I))
      = shiftLogIntegral t d ρ + shiftLogIntegral t d (1 - (starRingEnd ℂ) ρ) := by
    rw [bookerPairIntegral, shiftLogIntegral, shiftLogIntegral,
      ← intervalIntegral.integral_add hI1 hI2]
    exact intervalIntegral.integral_congr (fun x _ ↦ bookerIntegrand_eq_shiftLog ρ t d x hρt)
  have hRHS : (1 / ((d : ℂ) + (ρ - (1 / 2 + (t : ℂ) * I)))
        + 1 / ((d : ℂ) - (starRingEnd ℂ) (ρ - (1 / 2 + (t : ℂ) * I)))).re
      = (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - ρ)⁻¹).re
          + (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - (1 - (starRingEnd ℂ) ρ))⁻¹).re := by
    rw [Complex.add_re, hresPlus, hresMinus]; ring
  rw [hLHS, hRHS] at hbk
  exact hbk
lemma Complex.norm_complex_line_le (a b : ℝ) :
    ‖(1 / 2 : ℂ) + (a : ℂ) + (b : ℂ) * I‖ ≤ 1 / 2 + |a| + |b| := by
  have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by rw [norm_div, norm_one, Complex.norm_ofNat]
  calc ‖(1 / 2 : ℂ) + (a : ℂ) + (b : ℂ) * I‖
      ≤ ‖(1 / 2 : ℂ) + (a : ℂ)‖ + ‖(b : ℂ) * I‖ := norm_add_le _ _
    _ ≤ (‖(1 / 2 : ℂ)‖ + ‖(a : ℂ)‖) + ‖(b : ℂ) * I‖ := by gcongr; exact norm_add_le _ _
    _ = 1 / 2 + |a| + |b| := by
        rw [h2, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
theorem summable_re_inv_riemannXiZeros_sub {s : ℂ} (hs : ∀ i, s ≠ riemannXiZeros i) :
    Summable (fun i ↦ ((s - riemannXiZeros i)⁻¹).re) := by
  have h2 : Summable (fun i ↦ (1 / (s - riemannXiZeros i) + 1 / riemannXiZeros i).re) :=
    (summable_partial_fraction hs).map (Complex.reCLM : ℂ →L[ℝ] ℝ).toAddMonoidHom
      Complex.continuous_re
  refine (h2.sub summable_re_inv_riemannXiZeros).congr (fun i ↦ ?_)
  rw [Complex.add_re, one_div, one_div, add_sub_cancel_right]
theorem exists_forall_riemannXiZeros_im_ne :
    ∃ t₀ : ℝ, ∀ i, (riemannXiZeros i).im ≠ t₀ := by
  have hcount : (Set.range (fun i ↦ (riemannXiZeros i).im)).Countable := Set.countable_range _
  have hne : Set.range (fun i ↦ (riemannXiZeros i).im) ≠ Set.univ := fun h ↦
    Cardinal.not_countable_real (h ▸ hcount)
  obtain ⟨t₀, ht₀⟩ := Set.nonempty_compl.mpr hne
  exact ⟨t₀, fun i h ↦ ht₀ ⟨i, h⟩⟩
theorem tsum_re_inv_riemannXiZeros_sub_critical_eq_zero {s₀ : ℂ}
    (hconj : starRingEnd ℂ s₀ = 1 - s₀) :
    ∑' i, ((s₀ - riemannXiZeros i)⁻¹).re = 0 := by
  have hgpt : ∀ z : ℂ, ((s₀ - (1 - starRingEnd ℂ z))⁻¹).re = -((s₀ - z)⁻¹).re := by
    intro z
    have hid : s₀ - (1 - starRingEnd ℂ z) = -(starRingEnd ℂ (s₀ - z)) := by
      rw [map_sub, hconj]; ring
    rw [hid, inv_neg, ← map_inv₀, Complex.neg_re, Complex.conj_re]
  have hcalc : (∑' i, ((s₀ - riemannXiZeros i)⁻¹).re)
      = - ∑' i, ((s₀ - riemannXiZeros i)⁻¹).re :=
    calc (∑' i, ((s₀ - riemannXiZeros i)⁻¹).re)
        = ∑' i, ((s₀ - (1 - starRingEnd ℂ (riemannXiZeros i)))⁻¹).re :=
          tsum_riemannXiZeros_one_sub_conj (fun z ↦ ((s₀ - z)⁻¹).re)
      _ = ∑' i, (-((s₀ - riemannXiZeros i)⁻¹).re) := by simp_rw [hgpt]
      _ = - ∑' i, ((s₀ - riemannXiZeros i)⁻¹).re := tsum_neg
  linarith
private lemma deriv_riemannXi_conj (s : ℂ) :
    deriv riemannXi (starRingEnd ℂ s) = starRingEnd ℂ (deriv riemannXi s) := by
  have hsym : starRingEnd ℂ ∘ riemannXi ∘ starRingEnd ℂ = riemannXi := by
    funext z; simp only [Function.comp_apply, riemannXi_conj, Complex.conj_conj]
  have h : starRingEnd ℂ ∘ deriv riemannXi ∘ starRingEnd ℂ = deriv riemannXi := by
    rw [← deriv_conj_conj, hsym]
  simpa using congrArg (starRingEnd ℂ) (congrFun h s)
private lemma deriv_riemannXi_one_sub (s : ℂ) :
    deriv riemannXi (1 - s) = - deriv riemannXi s := by
  have hu : HasDerivAt (fun w : ℂ ↦ 1 - w) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub (1 : ℂ)
  have hcomp : HasDerivAt (riemannXi ∘ fun w ↦ 1 - w) (deriv riemannXi (1 - s) * (-1)) s :=
    ((differentiable_riemannXi (1 - s)).hasDerivAt).comp s hu
  have hfun : (riemannXi ∘ fun w ↦ 1 - w) = riemannXi := by
    funext z; simp only [Function.comp_apply, riemannXi_one_sub]
  rw [hfun] at hcomp
  have hd : HasDerivAt riemannXi (deriv riemannXi s) s := (differentiable_riemannXi s).hasDerivAt
  linear_combination -(hcomp.unique hd)
theorem re_logDeriv_riemannXi_critical_eq_zero {s₀ : ℂ}
    (hconj : starRingEnd ℂ s₀ = 1 - s₀) :
    (logDeriv riemannXi s₀).re = 0 := by
  have ha : logDeriv riemannXi (starRingEnd ℂ s₀) = starRingEnd ℂ (logDeriv riemannXi s₀) := by
    rw [logDeriv_apply, logDeriv_apply, deriv_riemannXi_conj, riemannXi_conj, map_div₀]
  have hb : logDeriv riemannXi (1 - s₀) = - logDeriv riemannXi s₀ := by
    rw [logDeriv_apply, logDeriv_apply, deriv_riemannXi_one_sub, riemannXi_one_sub, neg_div]
  have hcomb : starRingEnd ℂ (logDeriv riemannXi s₀) = - logDeriv riemannXi s₀ := by
    rw [← ha, hconj, hb]
  have := congrArg Complex.re hcomb
  rw [Complex.conj_re, Complex.neg_re] at this
  linarith
private lemma re_tsum_partialFraction_add {s : ℂ} (hsne : ∀ i, s ≠ riemannXiZeros i)
    (hPair : Summable fun i ↦ ((s - riemannXiZeros i)⁻¹).re) :
    (∑' i, (1 / (s - riemannXiZeros i) + 1 / riemannXiZeros i)).re
      = ∑' i, ((s - riemannXiZeros i)⁻¹).re + ∑' i, ((riemannXiZeros i)⁻¹).re := by
  rw [Complex.re_tsum (summable_partial_fraction hsne),
    tsum_congr (fun i ↦ by rw [Complex.add_re, one_div, one_div]),
    hPair.tsum_add summable_re_inv_riemannXiZeros]
theorem hadamardConst_add_tsum_re_inv_riemannXiZeros_eq_zero :
    (logDeriv riemannXi 0).re + ∑' i, ((riemannXiZeros i)⁻¹).re = 0 := by
  obtain ⟨t₀, ht₀⟩ := exists_forall_riemannXiZeros_im_ne
  set s₀ : ℂ := (1 / 2 : ℂ) + (t₀ : ℂ) * I with hs₀
  have hs0im : s₀.im = t₀ := by rw [hs₀]; simp
  have hsne : ∀ i, s₀ ≠ riemannXiZeros i := fun i h ↦ ht₀ i (by rw [← h, hs0im])
  have hconj : starRingEnd ℂ s₀ = 1 - s₀ := by
    rw [hs₀]; apply Complex.ext <;> simp; ring
  have hkey := congrArg Complex.re (logDeriv_riemannXi_eq hsne)
  rw [Complex.add_re,
    re_tsum_partialFraction_add hsne (summable_re_inv_riemannXiZeros_sub hsne),
    re_logDeriv_riemannXi_critical_eq_zero hconj,
    tsum_re_inv_riemannXiZeros_sub_critical_eq_zero hconj, zero_add] at hkey
  linarith
theorem tsum_re_inv_riemannXiZeros_sub_eq {s : ℂ} (hre : 0 < s.re) (hs1 : s ≠ 1)
    (hsne : ∀ i, s ≠ riemannXiZeros i)
    (hPair : Summable (fun i ↦ ((s - riemannXiZeros i)⁻¹).re)) :
    ∑' i, ((s - riemannXiZeros i)⁻¹).re
      = (logDeriv riemannZeta s).re + (1 / s).re + (1 / (s - 1)).re
        - 1 / 2 * Real.log π + 1 / 2 * (Complex.digamma (s / 2)).re := by
  have hkey := logDeriv_riemannZeta_eq hre hs1 hsne
  have hκ := hadamardConst_add_tsum_re_inv_riemannXiZeros_eq_zero
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  have hlogpi_re : ((1 / 2 : ℂ) * (Real.log π : ℂ)).re = 1 / 2 * Real.log π := by
    rw [hhalf, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hpsi_re : ((1 / 2 : ℂ) * Complex.digamma (s / 2)).re
      = 1 / 2 * (Complex.digamma (s / 2)).re := by rw [hhalf, Complex.re_ofReal_mul]
  have hexp := congrArg Complex.re hkey
  simp only [Complex.add_re, Complex.sub_re, hlogpi_re, hpsi_re] at hexp
  rw [re_tsum_partialFraction_add hsne hPair] at hexp
  linarith [hexp, hκ]
lemma summable_pairDensity {t d : ℝ} (hd : 1 / 2 < d) :
    Summable (fun i ↦ (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - riemannXiZeros i)⁻¹).re) :=
  summable_re_inv_riemannXiZeros_sub fun i h ↦ by
    have hlt := riemannXiZeros_re_lt_one i
    rw [← h, complex_line_re d t] at hlt; linarith
lemma Real.log_add_le {u t : ℝ} (hu : 0 ≤ u) (ht : 0 < t) :
    Real.log (u + t) ≤ Real.log t + u / t := by
  have hdiv : Real.log ((t + u) / t) ≤ u / t := by
    calc Real.log ((t + u) / t)
        ≤ (t + u) / t - 1 := Real.log_le_sub_one_of_pos (div_pos (by linarith) ht)
      _ = u / t := by field_simp; ring
  rw [Real.log_div (ne_of_gt (by linarith : (0 : ℝ) < t + u)) ht.ne'] at hdiv
  rw [add_comm u t]
  linarith
lemma Complex.re_one_div_le_norm_inv (w : ℂ) : (1 / w).re ≤ ‖w‖⁻¹ := by
  rw [one_div]; exact (Complex.re_le_norm _).trans_eq (norm_inv w)
lemma shiftedLine_setup {d t : ℝ} (hdlt : 1 / 2 < d) (ht0 : 0 < t) :
    ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I).re = 1 / 2 + d ∧
      ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I).im = t ∧
      0 < ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I).re ∧
      1 < ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I).re ∧
      (1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I ≠ 1 ∧
      (∀ i, (1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I ≠ riemannXiZeros i) ∧
      1 / 2 + d ≤ ‖(1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I‖ ∧
      0 < ‖(1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I‖ ∧
      ‖(1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I‖ ≤ (1 / 2 + d) + t := by
  have hsre : ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I).re = 1 / 2 + d := complex_line_re d t
  have hsim : ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I).im = t := complex_line_im d t
  have hsnorm_lb : 1 / 2 + d ≤ ‖(1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I‖ := by
    rw [← hsre]; exact Complex.re_le_norm _
  refine ⟨hsre, hsim, ?_, ?_, ?_, ?_, hsnorm_lb, lt_of_lt_of_le (by linarith) hsnorm_lb, ?_⟩
  · rw [hsre]; linarith
  · rw [hsre]; linarith
  · intro h; rw [h] at hsim; simp at hsim; linarith
  · intro i h
    have hlt := riemannXiZeros_re_lt_one i
    rw [← h, hsre] at hlt; linarith
  · have h := Complex.norm_complex_line_le d t
    rw [abs_of_pos (by linarith : (0 : ℝ) < d), abs_of_pos ht0] at h
    linarith
private lemma abs_sub_sub_le (a b c : ℝ) : |a - b - c| ≤ |a| + |b| + |c| :=
  abs_le.mpr ⟨by linarith [neg_abs_le a, le_abs_self b, le_abs_self c],
              by linarith [le_abs_self a, neg_abs_le b, neg_abs_le c]⟩
private lemma exists_eventually_forall_norm_shiftLogIntegrand_le {t d : ℝ} (hd : 1 / 2 < d)
    (ht : ∀ i, (riemannXiZeros i).im ≠ t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in Filter.cofinite, ∀ x ∈ Set.uIoc (0 : ℝ) d,
      ‖shiftLogIntegrand t d (riemannXiZeros i) x‖ ≤ C * ‖(riemannXiZeros i)⁻¹‖ ^ 2 := by
  have hd0 : (0 : ℝ) < d := by linarith
  set C0 : ℝ := 1 / 2 + 2 * d + |t| with hC0
  have hC0pos : 0 ≤ C0 := by rw [hC0]; positivity
  have hsum2 := summable_inv_norm_sq_riemannXiZeros
  have htail : ∀ᶠ i in Filter.cofinite, ‖(riemannXiZeros i)⁻¹‖ ≤ 1 / (2 * (C0 + 1)) := by
    have hlt : (0 : ℝ) < (1 / (2 * (C0 + 1))) ^ 2 := by positivity
    filter_upwards [hsum2.tendsto_cofinite_zero.eventually (eventually_lt_nhds hlt)] with i hi
    exact (lt_of_pow_lt_pow_left₀ 2 (by positivity) hi).le
  refine ⟨2 * C0 ^ 2 + d, by positivity, ?_⟩
  filter_upwards [htail] with i hi
  set ρ := riemannXiZeros i with hρ
  have hρ0 : ρ ≠ 0 := riemannXiZeros_ne_zero i
  have hρre0 : 0 < ρ.re := riemannXiZeros_re_pos i
  have hρre1 : ρ.re < 1 := riemannXiZeros_re_lt_one i
  have hsmall : C0 * ‖ρ⁻¹‖ ≤ 1 / 2 := by
    have hstep : C0 * ‖ρ⁻¹‖ ≤ C0 * (1 / (2 * (C0 + 1))) := mul_le_mul_of_nonneg_left hi hC0pos
    have : C0 * (1 / (2 * (C0 + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith
  have hE3 : d * |(ρ⁻¹).re| ≤ d * ‖ρ⁻¹‖ ^ 2 :=
    mul_le_mul_of_nonneg_left (abs_re_inv_le_norm_sq hρre0 hρre1) hd0.le
  intro x hx
  rw [Set.uIoc_of_le hd0.le] at hx
  have hxabs : |x| ≤ d := by rw [abs_of_nonneg hx.1.le]; exact hx.2
  have hs_C0 : ‖(1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I‖ ≤ C0 := by
    have := Complex.norm_complex_line_le x t; rw [hC0]; linarith
  have hsd_C0 : ‖(1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ)‖ ≤ C0 := by
    have h1 := norm_add_le ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I) (d : ℂ)
    have h2 : ‖(d : ℂ)‖ = d := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0]
    have := Complex.norm_complex_line_le x t
    rw [hC0]; rw [h2] at h1; linarith
  have h2ne : (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I ≠ ρ := fun h ↦
    ht i (by rw [← hρ, ← h, complex_line_im x t])
  have h1ne : (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ) ≠ ρ := fun h ↦
    ht i (by rw [← hρ, ← h, complex_line_add_im x t d])
  rw [Real.norm_eq_abs, shiftLogIntegrand_eq hρ0 t d x h1ne h2ne]
  refine (abs_sub_sub_le _ _ _).trans ?_
  rw [abs_mul, abs_of_pos hd0]
  refine (add_le_add (add_le_add (abs_log_norm_one_sub_div_add_re_le (ρ := ρ) hsd_C0 hsmall)
    (abs_log_norm_one_sub_div_add_re_le (ρ := ρ) hs_C0 hsmall)) hE3).trans (le_of_eq ?_)
  ring
private lemma summable_shiftLogIntegral {t d : ℝ} (hd : 1 / 2 < d)
    (ht : ∀ i, (riemannXiZeros i).im ≠ t) :
    Summable (fun i ↦ shiftLogIntegral t d (riemannXiZeros i)) := by
  have hd0 : (0 : ℝ) < d := by linarith
  obtain ⟨C, hC0, hCb⟩ := exists_eventually_forall_norm_shiftLogIntegrand_le hd ht
  refine Summable.of_norm_bounded_eventually
    (summable_inv_norm_sq_riemannXiZeros.mul_left (C * d)) ?_
  filter_upwards [hCb] with i hi
  calc ‖shiftLogIntegral t d (riemannXiZeros i)‖
      = ‖∫ x in (0 : ℝ)..d, shiftLogIntegrand t d (riemannXiZeros i) x‖ := by rw [shiftLogIntegral]
    _ ≤ C * ‖(riemannXiZeros i)⁻¹‖ ^ 2 * |d - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hi
    _ = C * d * ‖(riemannXiZeros i)⁻¹‖ ^ 2 := by rw [sub_zero, abs_of_pos hd0]; ring
theorem tsum_shiftLogIntegral_eq_intervalIntegral_tsum {t d : ℝ} (hd : 1 / 2 < d)
    (ht : ∀ i, (riemannXiZeros i).im ≠ t) :
    ∑' i, shiftLogIntegral t d (riemannXiZeros i)
      = ∫ x in (0 : ℝ)..d, ∑' i, shiftLogIntegrand t d (riemannXiZeros i) x := by
  have hd0 : (0 : ℝ) < d := by linarith
  have hint : ∀ i, MeasureTheory.IntegrableOn
      (shiftLogIntegrand t d (riemannXiZeros i)) (Set.Ioc 0 d) := fun i ↦
    (continuous_shiftLogIntegrand t d (ht i)).integrableOn_Ioc
  obtain ⟨C, hC0, hCb⟩ := exists_eventually_forall_norm_shiftLogIntegrand_le hd ht
  have hsummint : Summable (fun i ↦
      ∫ x in Set.Ioc (0 : ℝ) d, ‖shiftLogIntegrand t d (riemannXiZeros i) x‖) := by
    refine Summable.of_norm_bounded_eventually
      (summable_inv_norm_sq_riemannXiZeros.mul_left (C * d)) ?_
    filter_upwards [hCb] with i hi
    have hnn : (0 : ℝ) ≤ ∫ x in Set.Ioc (0 : ℝ) d,
        ‖shiftLogIntegrand t d (riemannXiZeros i) x‖ :=
      MeasureTheory.integral_nonneg (fun x ↦ norm_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    calc ∫ x in Set.Ioc (0 : ℝ) d, ‖shiftLogIntegrand t d (riemannXiZeros i) x‖
        ≤ ∫ _x in Set.Ioc (0 : ℝ) d, C * ‖(riemannXiZeros i)⁻¹‖ ^ 2 := by
          refine MeasureTheory.setIntegral_mono_on (hint i).norm ?_ measurableSet_Ioc ?_
          · exact MeasureTheory.integrableOn_const
              (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
          · intro x hx
            exact hi x (by rw [Set.uIoc_of_le hd0.le]; exact hx)
      _ = C * d * ‖(riemannXiZeros i)⁻¹‖ ^ 2 := by
          rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le hd0.le, smul_eq_mul]
          ring
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (F := fun i ↦ shiftLogIntegrand t d (riemannXiZeros i))
    (μ := MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) d)) hint hsummint
  calc ∑' i, shiftLogIntegral t d (riemannXiZeros i)
      = ∑' i, ∫ x in Set.Ioc (0 : ℝ) d, shiftLogIntegrand t d (riemannXiZeros i) x := by
        refine tsum_congr (fun i ↦ ?_)
        rw [shiftLogIntegral, intervalIntegral.integral_of_le hd0.le]
    _ = ∫ x in Set.Ioc (0 : ℝ) d, ∑' i, shiftLogIntegrand t d (riemannXiZeros i) x := hswap
    _ = ∫ x in (0 : ℝ)..d, ∑' i, shiftLogIntegrand t d (riemannXiZeros i) x := by
        rw [intervalIntegral.integral_of_le hd0.le]
theorem integral_tsum_log_norm_shift_le_of {t d : ℝ} (hd : 1 / 2 < d)
    (ht : ∀ i, (riemannXiZeros i).im ≠ t) {c : ℝ} (hc : 2 ≤ c) :
    ∑' i, shiftLogIntegral t d (riemannXiZeros i)
      ≤ c * d ^ 2 * ∑' i,
          (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - riemannXiZeros i)⁻¹).re := by
  set A : ℂ := (1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I with hA
  set g : ℂ → ℝ := shiftLogIntegral t d with hg
  set f : ℂ → ℝ := fun ρ ↦ ((A - ρ)⁻¹).re with hf
  have hSg : Summable fun i ↦ g (riemannXiZeros i) := summable_shiftLogIntegral hd ht
  have hSh : Summable fun i ↦ g (1 - starRingEnd ℂ (riemannXiZeros i)) :=
    (summable_riemannXiZeros_one_sub_conj_iff g).mpr hSg
  have hSc : Summable fun i ↦ f (riemannXiZeros i) := summable_pairDensity hd
  have hSch : Summable fun i ↦ f (1 - starRingEnd ℂ (riemannXiZeros i)) :=
    (summable_riemannXiZeros_one_sub_conj_iff f).mpr hSc
  have hper : ∀ i, g (riemannXiZeros i) + g (1 - starRingEnd ℂ (riemannXiZeros i))
      ≤ c * d ^ 2 * (f (riemannXiZeros i) + f (1 - starRingEnd ℂ (riemannXiZeros i))) := fun i ↦
    shiftLogIntegral_add_le_of t hd (ht i) (riemannXiZeros_re_pos i)
      (riemannXiZeros_re_lt_one i) hc
  have hreflg := tsum_riemannXiZeros_one_sub_conj g
  have hreflc := tsum_riemannXiZeros_one_sub_conj f
  have key : 2 * ∑' i, g (riemannXiZeros i) ≤ 2 * (c * d ^ 2 * ∑' i, f (riemannXiZeros i)) :=
    calc 2 * ∑' i, g (riemannXiZeros i)
        = ∑' i, (g (riemannXiZeros i) + g (1 - starRingEnd ℂ (riemannXiZeros i))) := by
          rw [hSg.tsum_add hSh, ← hreflg]; ring
      _ ≤ ∑' i, c * d ^ 2 * (f (riemannXiZeros i) + f (1 - starRingEnd ℂ (riemannXiZeros i))) :=
          Summable.tsum_le_tsum hper (hSg.add hSh) ((hSc.add hSch).mul_left _)
      _ = 2 * (c * d ^ 2 * ∑' i, f (riemannXiZeros i)) := by
          rw [tsum_mul_left, hSc.tsum_add hSch, ← hreflc]; ring
  linarith
open scoped LSeries.notation
open ArithmeticFunction
lemma re_logDeriv_riemannZeta_le {s : ℂ} (hs : 1 < s.re) :
    (logDeriv riemannZeta s).re ≤ ∑' n, ‖LSeries.term ↗Λ s n‖ := by
  have hsum : Summable (fun n ↦ ‖LSeries.term ↗Λ s n‖) := (LSeriesSummable_vonMangoldt hs).norm
  have hlogD : logDeriv riemannZeta s = -LSeries ↗Λ s := by
    rw [logDeriv_apply, LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]; ring
  calc (logDeriv riemannZeta s).re
      ≤ ‖logDeriv riemannZeta s‖ := Complex.re_le_norm _
    _ = ‖LSeries ↗Λ s‖ := by rw [hlogD, norm_neg]
    _ ≤ ∑' n, ‖LSeries.term ↗Λ s n‖ := norm_tsum_le_tsum_norm hsum
lemma re_digamma_le {z : ℂ} (hz : 0 < z.re) {C : ℝ}
    (hC : ‖digammaRemainderIoi z 1‖ ≤ C * ‖z‖ ^ (-(1 : ℤ))) :
    (Complex.digamma z).re ≤ Real.log ‖z‖ + (1 / 2 + C) / ‖z‖ := by
  have hz0 : z ≠ 0 := Complex.ne_zero_of_re_pos hz
  have hznorm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hzne : ‖z‖ ≠ 0 := hznorm.ne'
  have hzpow : ‖z‖ ^ (-(1 : ℤ)) = (‖z‖)⁻¹ := by rw [zpow_neg, zpow_one]
  rw [hzpow] at hC
  have heq := digamma_eq_log_sub z hz 0
  rw [show (2 * 0 + 1) = 1 from rfl,
      show Finset.Icc 1 0 = (∅ : Finset ℕ) from Finset.Icc_eq_empty_of_lt (by norm_num),
      Finset.sum_empty, sub_zero] at heq
  rw [heq, Complex.sub_re, Complex.sub_re, Complex.log_re]
  have e1 : -((2 * z)⁻¹).re ≤ (2 * ‖z‖)⁻¹ := by
    have hn : ‖(2 * z)⁻¹‖ = (2 * ‖z‖)⁻¹ := by rw [norm_inv, norm_mul, Complex.norm_ofNat]
    calc -((2 * z)⁻¹).re ≤ ‖(2 * z)⁻¹‖ := (neg_le_abs _).trans (Complex.abs_re_le_norm _)
      _ = (2 * ‖z‖)⁻¹ := hn
  have e2 : -(digammaRemainderIoi z 1).re ≤ C * (‖z‖)⁻¹ :=
    le_trans ((neg_le_abs _).trans (Complex.abs_re_le_norm _)) hC
  have efr : (2 * ‖z‖)⁻¹ + C * (‖z‖)⁻¹ = (1 / 2 + C) / ‖z‖ := by field_simp
  linarith [e1, e2, efr]
end
end CertificatePort69

section CertificatePort70
section
open MeasureTheory Metric Real
open scoped ENNReal
private theorem lintegral_ofReal_inv_norm_closedBall {r : ℝ} (hr : 0 ≤ r) :
    ∫⁻ s in closedBall (0 : ℂ) r, ENNReal.ofReal ‖s‖⁻¹ = ENNReal.ofReal (2 * π * r) := by
  rw [← lintegral_indicator measurableSet_closedBall,
    ← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  have heqon : Set.EqOn
      (fun p : ℝ × ℝ ↦ ENNReal.ofReal p.1 •
        (closedBall (0 : ℂ) r).indicator (fun w ↦ ENNReal.ofReal ‖w‖⁻¹)
          (Complex.polarCoord.symm p))
      ((Set.Ioc 0 r ×ˢ Set.Ioo (-π) π).indicator (fun _ ↦ 1))
      (Set.Ioi 0 ×ˢ Set.Ioo (-π) π) := by
    rintro ⟨x, y⟩ ⟨hx : (0 : ℝ) < x, hy₁, hy₂⟩
    have hnorm : ‖(Complex.polarCoord.symm (x, y) : ℂ)‖ = x := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hx]
    by_cases h : x ≤ r <;>
      simp [-Complex.polarCoord_symm_apply, mem_closedBall, dist_zero_right, hnorm, hx, hy₁, hy₂,
        h, ENNReal.mul_inv_cancel (by simp [hx] : ENNReal.ofReal x ≠ 0) ENNReal.ofReal_ne_top]
  rw [setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) heqon,
    setLIntegral_indicator (measurableSet_Ioc.prod measurableSet_Ioo),
    Set.prod_inter_prod, Set.inter_eq_left.mpr Set.Ioc_subset_Ioi_self, Set.inter_self,
    setLIntegral_const, one_mul, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_Ioc, Real.volume_Ioo, ← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ r - 0)]
  congr 1
  ring
private theorem lintegral_ofReal_inv_norm_sub_closedBall (ρ : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    ∫⁻ s in closedBall ρ r, ENNReal.ofReal ‖s - ρ‖⁻¹ = ENNReal.ofReal (2 * π * r) := by
  rw [← lintegral_indicator measurableSet_closedBall, ← lintegral_add_right_eq_self _ ρ,
    ← lintegral_ofReal_inv_norm_closedBall hr, ← lintegral_indicator measurableSet_closedBall]
  refine lintegral_congr fun s ↦ ?_
  simp [Set.indicator, mem_closedBall, dist_eq_norm]
private theorem measurable_inv_norm_sub (ρ : ℂ) : Measurable (fun s : ℂ ↦ ‖s - ρ‖⁻¹) :=
  (continuous_norm.comp (continuous_id.sub continuous_const)).measurable.inv
theorem integrableOn_inv_norm_sub_closedBall (ρ : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    IntegrableOn (fun s : ℂ ↦ ‖s - ρ‖⁻¹) (closedBall ρ r) := by
  refine ⟨(measurable_inv_norm_sub ρ).aestronglyMeasurable, ?_⟩
  simp_rw [hasFiniteIntegral_iff_norm, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    lintegral_ofReal_inv_norm_sub_closedBall ρ hr]
  exact ENNReal.ofReal_lt_top
end
end CertificatePort70

section CertificatePort71
section
open Complex MeasureTheory Metric Set Filter Topology
private theorem analyticOnNhd_riemannZeta_ne_one :
    AnalyticOnNhd ℂ riemannZeta {s : ℂ | s ≠ 1} :=
  DifferentiableOn.analyticOnNhd
    (fun _ hs ↦ (differentiableAt_riemannZeta hs).differentiableWithinAt) isOpen_ne
private theorem analyticOnNhd_deriv_riemannZeta_ne_one :
    AnalyticOnNhd ℂ (deriv riemannZeta) {s : ℂ | s ≠ 1} :=
  fun s hs ↦ (analyticOnNhd_riemannZeta_ne_one s hs).deriv
private theorem analyticOnNhd_riemannZeta_upperHalfPlane :
    AnalyticOnNhd ℂ riemannZeta {s : ℂ | 0 < s.im} :=
  DifferentiableOn.analyticOnNhd (fun s hs ↦
    (differentiableAt_riemannZeta (by rintro rfl; simp at hs)).differentiableWithinAt)
    (isOpen_lt continuous_const continuous_im)
private theorem isConnected_upperHalfPlane : IsConnected {s : ℂ | 0 < s.im} :=
  (convex_halfSpace_im_gt 0).isConnected ⟨I, by simp⟩
private theorem im_pos_of_mem_rectangle {z w s : ℂ} (hz : 0 < z.im) (hw : 0 < w.im)
    (hs : s ∈ Rectangle z w) : 0 < s.im := by
  simp only [Rectangle, mem_reProdIm, mem_uIcc] at hs
  rcases hs.2 with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
private theorem continuous_riemannZeta_horizontal {t : ℝ} (ht : t ≠ 0) :
    Continuous (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ))) :=
  analyticOnNhd_riemannZeta_ne_one.continuousOn.comp_continuous (by fun_prop)
    (fun σ h ↦ ht (by simpa using congrArg Complex.im h))
private theorem continuous_riemannZeta_vertical {x : ℝ} (hx : x ≠ 1) :
    Continuous (fun τ : ℝ ↦ riemannZeta ((x : ℂ) + I * (τ : ℂ))) :=
  analyticOnNhd_riemannZeta_ne_one.continuousOn.comp_continuous (by fun_prop)
    (fun τ h ↦ hx (by simpa using congrArg Complex.re h))
private theorem ofReal_add_I_mul_ne_one {σ t : ℝ} (ht : t ≠ 0) :
    (σ : ℂ) + I * (t : ℂ) ≠ 1 := fun h ↦ ht (by simpa using congrArg Complex.im h)
theorem finite_riemannZeta_zeros_rectangle {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    (Rectangle z w ∩ {ρ | riemannZeta ρ = 0}).Finite :=
  finite_rectangle_inter_setOf_eq_zero analyticOnNhd_riemannZeta_upperHalfPlane
    isConnected_upperHalfPlane (fun _ hρ ↦ im_pos_of_mem_rectangle hz hw hρ) (z₀ := 2 + I) (by simp)
    (riemannZeta_ne_zero_of_one_le_re (by simp))
theorem finite_re_riemannZeta_zeros_rectangle {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    (Complex.re '' (Rectangle z w ∩ {ρ | riemannZeta ρ = 0})).Finite :=
  (finite_riemannZeta_zeros_rectangle hz hw).image _
theorem finite_im_riemannZeta_zeros_rectangle {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    (Complex.im '' (Rectangle z w ∩ {ρ | riemannZeta ρ = 0})).Finite :=
  (finite_riemannZeta_zeros_rectangle hz hw).image _
private theorem ofReal_add_I_mul_mem_rectangle {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    {σ t : ℝ} (hσ : σ ∈ Icc z.re w.re) (ht : t ∈ Icc z.im w.im) :
    ((σ : ℂ) + I * (t : ℂ)) ∈ Rectangle z w := by
  rw [Rectangle, mem_reProdIm, Set.uIcc_of_le hre, Set.uIcc_of_le him]
  exact ⟨by simpa using hσ, by simpa using ht⟩
private theorem ofReal_add_I_mul_mem_rectangle_two {t₁ t₂ σ t : ℝ} (h12 : t₁ ≤ t₂)
    (hσ : (1 / 2 : ℝ) ≤ σ) (hσ1 : σ ≤ 1) (ht : t ∈ Set.Icc t₁ t₂) :
    ((σ : ℂ) + I * (t : ℂ)) ∈ Rectangle ((1 / 2 : ℂ) + I * (t₁ : ℂ)) ((2 : ℂ) + I * (t₂ : ℂ)) :=
  ofReal_add_I_mul_mem_rectangle (by norm_num) (by simpa using h12)
    (by simp only [mem_Icc]; norm_num; constructor <;> linarith) (by simpa using ht)
private theorem re_le_one_of_riemannZeta_eq_zero {σ t : ℝ}
    (hz : riemannZeta ((σ : ℂ) + I * t) = 0) : σ ≤ 1 :=
  not_lt.mp fun h ↦ riemannZeta_ne_zero_of_one_le_re (by simpa using h.le) hz
private theorem riemannZeta_ray_ne_zero_of_not_mem_im_zeros {t₁ t₂ : ℝ} (h12 : t₁ ≤ t₂) {t : ℝ}
    (ht : t ∈ Set.Icc t₁ t₂)
    (htbad : t ∉ Complex.im '' (Rectangle ((1 / 2 : ℂ) + I * (t₁ : ℂ)) ((2 : ℂ) + I * (t₂ : ℂ))
      ∩ {ρ | riemannZeta ρ = 0})) :
    ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0 := fun σ hσ hzero ↦
  htbad ⟨(σ : ℂ) + I * (t : ℂ),
    ⟨ofReal_add_I_mul_mem_rectangle_two h12 hσ (re_le_one_of_riemannZeta_eq_zero hzero) ht,
      hzero⟩, by simp⟩
private theorem not_eventually_riemannZeta_eq_zero {x : ℂ} (hx : 0 < x.im) :
    ¬ ∀ᶠ z in 𝓝 x, riemannZeta z = 0 := fun hev ↦
  riemannZeta_ne_zero_of_one_le_re (s := 2 + I) (by simp)
    (analyticOnNhd_riemannZeta_upperHalfPlane.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isConnected_upperHalfPlane.isPreconnected hx hev (by simp))
private theorem integrableOn_const_div_sub_closedBall (c ρ : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    IntegrableOn (fun s : ℂ ↦ c / (s - ρ)) (closedBall ρ r) := by
  refine Integrable.mono' ((integrableOn_inv_norm_sub_closedBall ρ hr).const_mul ‖c‖)
    (measurable_const.div (measurable_id.sub measurable_const)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun s ↦ ?_)
  rw [norm_div, div_eq_mul_inv]
private theorem exists_integrableOn_logDeriv_riemannZeta_closedBall {x : ℂ} (hx : 0 < x.im) :
    ∃ r > 0, IntegrableOn (logDeriv riemannZeta) (closedBall x r) := by
  have hax : AnalyticAt ℂ riemannZeta x :=
    analyticOnNhd_riemannZeta_ne_one x (by rintro rfl; simp at hx)
  by_cases hzero : riemannZeta x = 0
  ·
    obtain ⟨n, g, -, -, -, hlogg, heq⟩ :=
      meromorphicOrderAt_eq_residue_logDeriv hax (not_eventually_riemannZeta_eq_zero hx)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
      ((eventually_nhdsWithin_iff.mp heq).and hlogg.eventually_analyticAt)
    have hlt : ∀ {z : ℂ}, z ∈ closedBall x (ε / 2) → dist z x < ε := fun {z} hz ↦
      lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith)
    refine ⟨ε / 2, half_pos hε, Integrable.congr
      ((integrableOn_const_div_sub_closedBall (n : ℂ) x (half_pos hε).le).add
        (ContinuousOn.integrableOn_compact (isCompact_closedBall x (ε / 2))
          fun _ hz ↦ (hball (hlt hz)).2.continuousAt.continuousWithinAt)) ?_⟩
    filter_upwards [ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton x)),
      ae_restrict_mem measurableSet_closedBall] with z hzne hzmem
    exact ((hball (hlt hzmem)).1 hzne).symm
  ·
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
      (hax.eventually_analyticAt.and (hax.continuousAt.eventually_ne hzero))
    refine ⟨ε / 2, half_pos hε, ContinuousOn.integrableOn_compact
      (isCompact_closedBall x (ε / 2)) fun z hz ↦ ?_⟩
    obtain ⟨haz, hzne⟩ := hball (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith))
    exact (haz.deriv.div haz hzne).continuousAt.continuousWithinAt
theorem integrableOn_logDeriv_riemannZeta_rectangle {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    IntegrableOn (logDeriv riemannZeta) (Rectangle z w) := by
  refine LocallyIntegrableOn.integrableOn_isCompact ?_ (isCompact_uIcc.reProdIm isCompact_uIcc)
  intro x hx
  obtain ⟨r, hr, hint⟩ :=
    exists_integrableOn_logDeriv_riemannZeta_closedBall (im_pos_of_mem_rectangle hz hw hx)
  exact ⟨closedBall x r, nhdsWithin_le_nhds (closedBall_mem_nhds x hr), hint⟩
theorem log_norm_riemannZeta_sub_eq_neg_im_integral {σ t₁ t₂ : ℝ} (h12 : t₁ ≤ t₂) (ht1 : 0 < t₁)
    (hne : ∀ t ∈ Icc t₁ t₂, riemannZeta ((σ : ℂ) + I * t) ≠ 0) :
    Real.log ‖riemannZeta ((σ : ℂ) + I * t₂)‖ - Real.log ‖riemannZeta ((σ : ℂ) + I * t₁)‖
      = -(∫ t in t₁..t₂, logDeriv riemannZeta ((σ : ℂ) + I * t)).im := by
  have hpathcont : Continuous (fun t : ℝ ↦ (σ : ℂ) + I * t) := by fun_prop
  have hmaps : MapsTo (fun t : ℝ ↦ (σ : ℂ) + I * t) (Icc t₁ t₂) {s : ℂ | s ≠ 1} :=
    fun t ht ↦ ofReal_add_I_mul_ne_one (ht1.trans_le ht.1).ne'
  have hderiv : ∀ t ∈ Ioo t₁ t₂,
      HasDerivAt (fun t : ℝ ↦ riemannZeta ((σ : ℂ) + I * t))
        (deriv riemannZeta ((σ : ℂ) + I * t) * I) t := fun t ht ↦
    ((analyticOnNhd_riemannZeta_ne_one _
      (ofReal_add_I_mul_ne_one (ht1.trans_le ht.1.le).ne')).differentiableAt.hasDerivAt).comp t
      (by simpa using ((ofRealCLM.hasDerivAt (x := t)).const_mul I).const_add (σ : ℂ))
  have hφcont : ContinuousOn (fun t : ℝ ↦ riemannZeta ((σ : ℂ) + I * t)) (Icc t₁ t₂) :=
    analyticOnNhd_riemannZeta_ne_one.continuousOn.comp hpathcont.continuousOn hmaps
  have heq : (fun t : ℝ ↦ deriv riemannZeta ((σ : ℂ) + I * t) * I / riemannZeta ((σ : ℂ) + I * t))
      = fun t : ℝ ↦ logDeriv riemannZeta ((σ : ℂ) + I * t) * I :=
    funext fun t ↦ by rw [logDeriv_apply, mul_div_right_comm]
  have h := re_integral_div_eq_log_norm_sub h12 hφcont hne hderiv
    (((analyticOnNhd_deriv_riemannZeta_ne_one.continuousOn.comp hpathcont.continuousOn hmaps).mul
      continuousOn_const).div hφcont hne)
  rw [heq, intervalIntegral.integral_mul_const, mul_I_re] at h
  linarith
theorem argVariation_riemannZeta_horizontal_eq_im_integral {a X t : ℝ} (hX : a ≤ X) (ht : t ≠ 0)
    (hne : ∀ σ ∈ Icc a X, riemannZeta ((σ : ℂ) + I * t) ≠ 0) :
    argVariation a X (fun σ ↦ riemannZeta ((σ : ℂ) + I * t))
      = (∫ σ in a..X, logDeriv riemannZeta ((σ : ℂ) + I * t)).im := by
  have hφcont : ContinuousOn (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * t)) (Icc a X) :=
    (continuous_riemannZeta_horizontal ht).continuousOn
  have hdcont : Continuous (fun σ : ℝ ↦ deriv riemannZeta ((σ : ℂ) + I * t)) :=
    analyticOnNhd_deriv_riemannZeta_ne_one.continuousOn.comp_continuous (by fun_prop)
      (fun _ ↦ ofReal_add_I_mul_ne_one ht)
  have hderiv : ∀ σ ∈ Ioo a X,
      HasDerivAt (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * t))
        (deriv riemannZeta ((σ : ℂ) + I * t)) σ := fun σ _ ↦ by
    have h1 : HasDerivAt (fun σ : ℝ ↦ (σ : ℂ) + I * t) 1 σ := by
      simpa using (ofRealCLM.hasDerivAt (x := σ)).add_const (I * (t : ℂ))
    have hd := ((analyticOnNhd_riemannZeta_ne_one _
      (ofReal_add_I_mul_ne_one ht)).differentiableAt.hasDerivAt).comp σ h1
    rw [mul_one] at hd; exact hd
  rw [argVariation_eq_im_integral hX hφcont hne hderiv (hdcont.continuousOn.div hφcont hne)]
  simp only [logDeriv_apply]
theorem tendsto_argVariation_riemannZeta_vertical_atTop {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun X : ℝ ↦ argVariation 0 t (fun τ : ℝ ↦ riemannZeta ((X : ℂ) + I * (τ : ℂ))))
      atTop (𝓝 0) := by
  have key : Tendsto (fun X : ℝ ↦ (riemannZeta ((X : ℂ) + I * (t : ℂ))).arg
      - (riemannZeta ((X : ℂ) + I * ((0 : ℝ) : ℂ))).arg) atTop (𝓝 0) := by
    simpa using (tendsto_arg_riemannZeta_atTop t).sub (tendsto_arg_riemannZeta_atTop 0)
  refine key.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with X hX
  rw [argVariation_eq_arg_sub_arg ht
    (continuous_riemannZeta_vertical (by linarith)).continuousOn
    (fun τ _ ↦ riemannZeta_mem_slitPlane_of_two_le_re (by simpa using hX))]
private theorem arg_riemannZeta_ofReal_eq_zero {σ : ℝ} (hσ : 2 ≤ σ) :
    (riemannZeta (σ : ℂ)).arg = 0 := by
  have hterm : ∀ n : ℕ, (1 : ℂ) / ((n : ℂ) + 1) ^ (σ : ℂ)
      = (((1 / ((n : ℝ) + 1) ^ σ : ℝ)) : ℂ) := fun n ↦ by
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_cpow (by positivity)]
    push_cast; ring
  have him : (riemannZeta (σ : ℂ)).im = 0 := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using (by linarith : (1 : ℝ) < σ)),
      tsum_congr hterm, ← Complex.ofReal_tsum, Complex.ofReal_im]
  have hsp := Complex.mem_slitPlane_iff.mp
    (riemannZeta_mem_slitPlane_of_two_le_re (s := (σ : ℂ)) (by simpa using hσ))
  exact Complex.arg_eq_zero_iff.mpr ⟨hsp.elim le_of_lt (absurd him), him⟩
private theorem mem_Icc_affine {a b u : ℝ} (hab : a ≤ b) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    a + u * (b - a) ∈ Set.Icc a b :=
  Set.uIcc_of_le hab ▸ add_mul_sub_mem_uIcc hu
private theorem argVariation_riemannZeta_lineSeg_comp {a b : ℝ} (hab : a ≤ b) {P Q : ℂ}
    {g : ℝ → ℂ} (hg : ∀ u : ℝ, lineSeg P Q u = g (a + u * (b - a)))
    (hcont : ContinuousOn (fun x : ℝ ↦ riemannZeta (g x)) (Set.Icc a b))
    (hne : ∀ x ∈ Set.Icc a b, riemannZeta (g x) ≠ 0) :
    argVariation 0 1 (fun u ↦ riemannZeta (lineSeg P Q u))
      = argVariation a b (fun x : ℝ ↦ riemannZeta (g x)) := by
  rw [show (fun u : ℝ ↦ riemannZeta (lineSeg P Q u))
      = fun u : ℝ ↦ (fun x : ℝ ↦ riemannZeta (g x)) (a + u * (b - a)) from
    funext fun u ↦ by rw [hg u]]
  exact argVariation_comp hab zero_le_one (by fun_prop) (fun u hu ↦ mem_Icc_affine hab hu)
    (by ring) (by ring) hcont hne
private theorem argVariation_riemannZeta_lineSeg_symm {z₀ z₁ : ℂ}
    (hcont : ContinuousOn (fun u : ℝ ↦ riemannZeta (lineSeg z₀ z₁ u)) (Set.Icc (0 : ℝ) 1))
    (hne : ∀ u ∈ Set.Icc (0 : ℝ) 1, riemannZeta (lineSeg z₀ z₁ u) ≠ 0) :
    argVariation 0 1 (fun u ↦ riemannZeta (lineSeg z₁ z₀ u))
      = - argVariation 0 1 (fun u ↦ riemannZeta (lineSeg z₀ z₁ u)) := by
  have hfun : (fun u : ℝ ↦ riemannZeta (lineSeg z₁ z₀ u))
      = (fun u : ℝ ↦ (fun v : ℝ ↦ riemannZeta (lineSeg z₀ z₁ v)) (0 + 1 - u)) := by
    funext u; simp only; congr 1; simp only [lineSeg]; push_cast; ring
  rw [hfun]
  exact argVariation_reverse zero_le_one hcont hne
private theorem argVariation_riemannZeta_lineSeg_horizontal_rev {a b t : ℝ} (hab : a ≤ b)
    (ht : t ≠ 0) (hrowcont : Continuous fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ)))
    (hne : ∀ σ ∈ Set.Icc a b, riemannZeta ((σ : ℂ) + I * (t : ℂ)) ≠ 0) :
    argVariation 0 1
        (fun u ↦ riemannZeta (lineSeg ((b : ℂ) + I * (t : ℂ)) ((a : ℂ) + I * (t : ℂ)) u))
      = - argVariation a b (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ))) := by
  have heq : ∀ u : ℝ, lineSeg ((a : ℂ) + I * (t : ℂ)) ((b : ℂ) + I * (t : ℂ)) u
      = (((a + u * (b - a) : ℝ)) : ℂ) + I * (t : ℂ) := fun u ↦ by
    simp only [lineSeg]; push_cast; ring
  have hcont : ContinuousOn
      (fun u : ℝ ↦ riemannZeta (lineSeg ((a : ℂ) + I * (t : ℂ)) ((b : ℂ) + I * (t : ℂ)) u))
      (Set.Icc 0 1) :=
    analyticOnNhd_riemannZeta_ne_one.continuousOn.comp (continuous_lineSeg _ _).continuousOn
      (fun u _ ↦ by rw [heq u]; exact ofReal_add_I_mul_ne_one ht)
  have hne01 : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      riemannZeta (lineSeg ((a : ℂ) + I * (t : ℂ)) ((b : ℂ) + I * (t : ℂ)) u) ≠ 0 := fun u hu ↦ by
    rw [heq u]; exact hne _ (mem_Icc_affine hab hu)
  rw [argVariation_riemannZeta_lineSeg_symm hcont hne01,
    argVariation_riemannZeta_lineSeg_comp (g := fun σ : ℝ ↦ (σ : ℂ) + I * (t : ℂ)) hab heq
      hrowcont.continuousOn hne]
private theorem argVariation_riemannZeta_lineSeg_of_two_le_re {z₀ z₁ : ℂ}
    (h : ∀ u ∈ Set.Icc (0 : ℝ) 1, 2 ≤ (lineSeg z₀ z₁ u).re) :
    argVariation 0 1 (fun u ↦ riemannZeta (lineSeg z₀ z₁ u))
      = (riemannZeta z₁).arg - (riemannZeta z₀).arg := by
  have hcont : ContinuousOn (fun u : ℝ ↦ riemannZeta (lineSeg z₀ z₁ u)) (Set.Icc 0 1) :=
    analyticOnNhd_riemannZeta_ne_one.continuousOn.comp (continuous_lineSeg _ _).continuousOn
      fun u hu h1 ↦ by simpa [h1] using h u hu
  rw [argVariation_eq_arg_sub_arg zero_le_one hcont
    fun u hu ↦ riemannZeta_mem_slitPlane_of_two_le_re (h u hu), lineSeg_one, lineSeg_zero]
theorem tendsto_argVariation_riemannZeta_horizontal_atTop {t : ℝ} (ht : 0 < t)
    (hne : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * (t : ℂ)) ≠ 0) :
    Tendsto (fun X : ℝ ↦ argVariation (1 / 2) X
        (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ))))
      atTop (𝓝 (-(Real.pi * argZeta t))) := by
  have hrowcont : Continuous (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ))) :=
    continuous_riemannZeta_horizontal ht.ne'
  have hpi : Real.pi * argZeta t = argVariationContourL riemannZeta t := by
    rw [argZeta, ← mul_assoc, mul_one_div, div_self Real.pi_ne_zero, one_mul]
  have hlim := (tendsto_argVariation_riemannZeta_vertical_atTop ht.le).sub_const
    (Real.pi * argZeta t)
  rw [zero_sub] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with X hX
  have hzero :
      argVariation 0 1 (fun u ↦ riemannZeta (lineSeg (2 : ℂ) (X : ℂ) u))
        + argVariation 0 1 (fun u ↦ riemannZeta (lineSeg (X : ℂ) ((X : ℂ) + I * (t : ℂ)) u))
        + argVariation 0 1 (fun u ↦
            riemannZeta (lineSeg ((X : ℂ) + I * (t : ℂ)) ((2 : ℂ) + I * (t : ℂ)) u))
        + argVariation 0 1 (fun u ↦
            riemannZeta (lineSeg ((2 : ℂ) + I * (t : ℂ)) (2 : ℂ) u)) = 0 := by
    have hsub : Rectangle (2 : ℂ) ((X : ℂ) + I * (t : ℂ)) ⊆ {s : ℂ | 1 < s.re} := fun ρ hρ ↦ by
      simp only [Rectangle, mem_reProdIm, mem_uIcc, show (2 : ℂ).re = 2 from by norm_num,
        show ((X : ℂ) + I * (t : ℂ)).re = X from by simp] at hρ
      rcases hρ.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact Set.mem_ofPred.mpr (by linarith)
    have hz0 := rectangleArgVariation_eq_zero_of_analyticOnNhd
      (fun s hs ↦ analyticOnNhd_riemannZeta_ne_one s (by rintro rfl; simp at hs))
      (fun _ hs ↦ riemannZeta_ne_zero_of_one_le_re hs.le) hsub
    rw [rectangleArgVariation] at hz0
    simpa [Complex.re_add_im, mul_comm] using hz0
  have hEb : argVariation 0 1 (fun u ↦ riemannZeta (lineSeg (2 : ℂ) (X : ℂ) u)) = 0 := by
    rw [argVariation_riemannZeta_lineSeg_of_two_le_re (fun u hu ↦ by
        simp only [lineSeg_re, Complex.re_ofNat, Complex.ofReal_re]
        nlinarith [mul_nonneg hu.1 (by linarith : (0 : ℝ) ≤ X - 2)]),
      arg_riemannZeta_ofReal_eq_zero hX,
      show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_num,
      arg_riemannZeta_ofReal_eq_zero (le_refl 2), sub_self]
  have hEr0 :
      argVariation 0 1 (fun u ↦ riemannZeta (lineSeg (X : ℂ) ((X : ℂ) + I * (t : ℂ)) u))
      = argVariation 0 t (fun τ : ℝ ↦ riemannZeta ((X : ℂ) + I * (τ : ℂ))) :=
    argVariation_riemannZeta_lineSeg_comp (g := fun τ : ℝ ↦ (X : ℂ) + I * (τ : ℂ)) ht.le
      (fun u ↦ by simp only [lineSeg]; push_cast; ring)
      (continuous_riemannZeta_vertical (by rintro rfl; norm_num at hX)).continuousOn
      (fun τ _ ↦ riemannZeta_ne_zero_of_one_le_re (by simpa using (by linarith : (1 : ℝ) ≤ X)))
  have hEt0 :
      argVariation 0 1
          (fun u ↦ riemannZeta (lineSeg ((X : ℂ) + I * (t : ℂ)) ((2 : ℂ) + I * (t : ℂ)) u))
      = - argVariation 2 X (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ))) := by
    rw [show ((2 : ℂ) + I * (t : ℂ)) = (((2 : ℝ) : ℂ) + I * (t : ℂ)) from by norm_num]
    exact argVariation_riemannZeta_lineSeg_horizontal_rev hX ht.ne' hrowcont
      (fun σ hσ ↦ hne σ (by linarith [hσ.1]))
  have hEl0 :
      argVariation 0 1 (fun u ↦ riemannZeta (lineSeg ((2 : ℂ) + I * (t : ℂ)) (2 : ℂ) u))
      = - argVariation 0 1
          (fun u ↦ riemannZeta (lineSeg (2 : ℂ) ((2 : ℂ) + I * (t : ℂ)) u)) := by
    rw [argVariation_riemannZeta_lineSeg_of_two_le_re (fun u _ ↦ by norm_num [lineSeg_re]),
      argVariation_riemannZeta_lineSeg_of_two_le_re (fun u _ ↦ by norm_num [lineSeg_re]), neg_sub]
  have hAsplit : argVariation (1 / 2) X (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ)))
      = argVariation (1 / 2) 2 (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ)))
        + argVariation 2 X (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ))) :=
    argVariation_trans (by norm_num) hX hrowcont.continuousOn
      (fun σ hσ ↦ hne σ (by linarith [hσ.1]))
  have hAlow :
      argVariation 0 1
          (fun u ↦
            riemannZeta (lineSeg ((2 : ℂ) + I * (t : ℂ)) ((1 / 2 : ℂ) + I * (t : ℂ)) u))
      = - argVariation (1 / 2) 2 (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ))) := by
    rw [show ((2 : ℂ) + I * (t : ℂ)) = (((2 : ℝ) : ℂ) + I * (t : ℂ)) from by norm_num,
      show ((1 / 2 : ℂ) + I * (t : ℂ)) = (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) from by norm_num]
    exact argVariation_riemannZeta_lineSeg_horizontal_rev (by norm_num) ht.ne' hrowcont
      (fun σ hσ ↦ hne σ (by linarith [hσ.1]))
  rw [hEb, hEr0, hEt0, hEl0] at hzero
  rw [hpi, argVariationContourL]
  linarith [hzero, hAsplit, hAlow]
private theorem abs_arg_le_arcsin_of_norm_sub_one_le {w : ℂ} {δ : ℝ}
    (hw : ‖w - 1‖ ≤ δ) (hδ : δ < 1) : |w.arg| ≤ Real.arcsin δ := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hw
  have hre1 : |(w - 1).re| ≤ δ := (Complex.abs_re_le_norm _).trans hw
  rw [Complex.sub_re, Complex.one_re, abs_le] at hre1
  have hre : 0 < w.re := by linarith [hre1.1]
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr (by rintro rfl; simp at hre)
  have e3 : (w.re - 1) ^ 2 + w.im ^ 2 ≤ δ ^ 2 := by
    have he : ‖w - 1‖ ^ 2 = (w.re - 1) ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.one_re, Complex.one_im]; ring
    linarith [pow_le_pow_left₀ (norm_nonneg _) hw 2, he]
  have e1 : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h1d : (0 : ℝ) ≤ 1 - δ ^ 2 := by nlinarith [hδ0, hδ]
  have habs : -(δ * ‖w‖) ≤ w.im ∧ w.im ≤ δ * ‖w‖ :=
    abs_le_of_sq_le_sq' (by
      rw [mul_pow, e1]
      nlinarith [e3, h1d, sq_nonneg (w.re - 1 + δ ^ 2), mul_nonneg h1d
        (by nlinarith [e3] : (0 : ℝ) ≤ δ ^ 2 - (w.re - 1) ^ 2 - w.im ^ 2)]) (by positivity)
  rw [Complex.arg_of_re_nonneg hre.le, abs_le, ← Real.arcsin_neg]
  exact ⟨Real.arcsin_le_arcsin (by rw [le_div_iff₀ hnorm]; linarith [habs.1]),
    Real.arcsin_le_arcsin (by rw [div_le_iff₀ hnorm]; linarith [habs.2])⟩
private theorem integrable_logDeriv_riemannZeta_box {a b c d : ℝ} (hab : a ≤ b) (hc : 0 < c)
    (hcd : c ≤ d) :
    Integrable (fun p : ℝ × ℝ ↦ logDeriv riemannZeta ((p.1 : ℂ) + I * (p.2 : ℂ)))
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c d))) := by
  have hfun : (fun p : ℝ × ℝ ↦ logDeriv riemannZeta ((p.1 : ℂ) + I * (p.2 : ℂ))) ∘
      ⇑Complex.measurableEquivRealProd = logDeriv riemannZeta := funext fun z ↦ by
    simp only [Function.comp_apply, Complex.measurableEquivRealProd_apply]
    rw [mul_comm I (z.im : ℂ), Complex.re_add_im]
  have hset : Complex.measurableEquivRealProd ⁻¹' (Set.Icc a b ×ˢ Set.Icc c d)
      = Rectangle ((a : ℂ) + I * (c : ℂ)) ((b : ℂ) + I * (d : ℂ)) := by
    ext z
    simp [Rectangle, Complex.mem_reProdIm, Set.uIcc_of_le hab, Set.uIcc_of_le hcd,
      and_and_and_comm]
  rw [Measure.prod_restrict]
  change IntegrableOn (fun p : ℝ × ℝ ↦ logDeriv riemannZeta ((p.1 : ℂ) + I * (p.2 : ℂ)))
    (Set.Icc a b ×ˢ Set.Icc c d) volume
  rw [← Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
        Complex.measurableEquivRealProd.measurableEmbedding, hfun, hset]
  exact integrableOn_logDeriv_riemannZeta_rectangle (by simpa using hc)
    (by simpa using hc.trans_le hcd)
theorem abs_argVariation_riemannZeta_horizontal_le {X t : ℝ} (hX : 2 ≤ X) (ht : t ≠ 0)
    (hne : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0) :
    |argVariation (1 / 2) X (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * t))|
      ≤ 2 * Real.arcsin (Real.pi ^ 2 / 6 - 1)
        + ∫ σ in (1 / 2 : ℝ)..2, ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := by
  have hrowcont : Continuous (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * t)) :=
    continuous_riemannZeta_horizontal ht
  have hhead : |argVariation (1 / 2) 2 (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * t))|
      ≤ ∫ σ in (1 / 2 : ℝ)..2, ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := by
    rw [argVariation_riemannZeta_horizontal_eq_im_integral (by norm_num) ht
      (fun σ hσ ↦ hne σ hσ.1)]
    exact (Complex.abs_im_le_norm _).trans
      (intervalIntegral.norm_integral_le_integral_norm (by norm_num))
  have htail : |argVariation 2 X (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * t))|
      ≤ 2 * Real.arcsin (Real.pi ^ 2 / 6 - 1) := by
    have hb : ∀ σ : ℝ, 2 ≤ σ →
        |(riemannZeta ((σ : ℂ) + I * t)).arg| ≤ Real.arcsin (Real.pi ^ 2 / 6 - 1) :=
      fun σ hσ ↦ abs_arg_le_arcsin_of_norm_sub_one_le
        (norm_riemannZeta_sub_one_le_of_two_le_re (by simpa using hσ))
        (by nlinarith [Real.pi_lt_d2, Real.pi_pos])
    rw [argVariation_eq_arg_sub_arg hX hrowcont.continuousOn (fun σ hσ ↦
      riemannZeta_mem_slitPlane_of_two_le_re (by simpa using hσ.1))]
    exact (abs_sub _ _).trans (by linarith [hb X (by linarith), hb 2 le_rfl])
  rw [argVariation_trans (by norm_num) hX hrowcont.continuousOn (fun σ hσ ↦ hne σ hσ.1)]
  exact (abs_add_le _ _).trans (by linarith [hhead, htail])
theorem integrableOn_argVariation_riemannZeta_horizontal_bound {t₁ t₂ : ℝ} (ht1 : 0 < t₁)
    (h12 : t₁ ≤ t₂) :
    IntegrableOn (fun t : ℝ ↦ 2 * Real.arcsin (Real.pi ^ 2 / 6 - 1)
      + ∫ σ in (1 / 2 : ℝ)..2, ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖) (Icc t₁ t₂) := by
  have hbox := integrable_logDeriv_riemannZeta_box (by norm_num : (1 / 2 : ℝ) ≤ 2) ht1 h12
  refine continuous_const.continuousOn.integrableOn_Icc.add
    ((hbox.swap.integral_norm_prod_left).congr (Filter.Eventually.of_forall fun t ↦ ?_))
  simp only [Function.comp_apply, Prod.swap_prod_mk,
    intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2),
    MeasureTheory.integral_Icc_eq_integral_Ioc]
private theorem tendsto_im_integral_logDeriv_row_atTop {t : ℝ} (ht : 0 < t)
    (hray : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0) :
    Tendsto (fun X : ℝ ↦ (∫ σ in (1 / 2 : ℝ)..X, logDeriv riemannZeta ((σ : ℂ) + I * t)).im)
      atTop (𝓝 (-(Real.pi * argZeta t))) := by
  refine (tendsto_argVariation_riemannZeta_horizontal_atTop ht hray).congr' ?_
  filter_upwards [eventually_ge_atTop (1 / 2 : ℝ)] with X hX
  exact argVariation_riemannZeta_horizontal_eq_im_integral hX ht.ne' fun σ hσ ↦ hray σ hσ.1
private theorem abs_im_integral_logDeriv_row_le {X t : ℝ} (hX : 2 ≤ X) (ht : t ≠ 0)
    (hray : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0) :
    |(∫ σ in (1 / 2 : ℝ)..X, logDeriv riemannZeta ((σ : ℂ) + I * t)).im|
      ≤ 2 * Real.arcsin (Real.pi ^ 2 / 6 - 1)
        + ∫ σ in (1 / 2 : ℝ)..2, ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := by
  rw [← argVariation_riemannZeta_horizontal_eq_im_integral (by linarith) ht
    fun σ hσ ↦ hray σ hσ.1]
  exact abs_argVariation_riemannZeta_horizontal_le hX ht hray
private theorem integrable_integral_logDeriv_riemannZeta_row {t₁ t₂ : ℝ} (ht1 : 0 < t₁)
    (h12 : t₁ ≤ t₂) {X : ℝ} (hX : (1 / 2 : ℝ) ≤ X) :
    Integrable (fun t : ℝ ↦ ∫ σ in (1 / 2 : ℝ)..X, logDeriv riemannZeta ((σ : ℂ) + I * t))
      (volume.restrict (Set.Icc t₁ t₂)) := by
  have hbox := integrable_logDeriv_riemannZeta_box hX ht1 h12
  refine (hbox.swap.integral_prod_left).congr (Filter.Eventually.of_forall fun t ↦ ?_)
  simp only [Function.comp_apply, Prod.swap_prod_mk, intervalIntegral.integral_of_le hX,
    MeasureTheory.integral_Icc_eq_integral_Ioc]
private theorem integrable_integral_logDeriv_riemannZeta_col {t₁ t₂ : ℝ} (ht1 : 0 < t₁)
    (h12 : t₁ ≤ t₂) {X : ℝ} (hX : (1 / 2 : ℝ) ≤ X) :
    Integrable (fun σ : ℝ ↦ ∫ t in t₁..t₂, logDeriv riemannZeta ((σ : ℂ) + I * t))
      (volume.restrict (Set.Icc (1 / 2 : ℝ) X)) := by
  have hbox := integrable_logDeriv_riemannZeta_box hX ht1 h12
  refine (hbox.integral_prod_left).congr (Filter.Eventually.of_forall fun σ ↦ ?_)
  simp only [intervalIntegral.integral_of_le h12, MeasureTheory.integral_Icc_eq_integral_Ioc]
private theorem intervalIntegral_im {a b : ℝ} (hab : a ≤ b) {F : ℝ → ℂ}
    (hF : Integrable F (volume.restrict (Icc a b))) :
    (∫ x in a..b, (F x).im) = (∫ x in a..b, F x).im := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  exact integral_im (hF.mono_measure (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl))
private theorem intervalIntegral₂_eq_setIntegral₂ {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (F : ℝ → ℝ → ℂ) :
    (∫ x in a..b, ∫ y in c..d, F x y) = ∫ x in Icc a b, ∫ y in Icc c d, F x y := by
  rw [intervalIntegral.integral_of_le hab, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact setIntegral_congr_fun measurableSet_Icc fun x _ ↦ by
    rw [intervalIntegral.integral_of_le hcd, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
private theorem integral_log_norm_riemannZeta_sub_eq {t₁ t₂ : ℝ} (ht1 : 0 < t₁) (h12 : t₁ ≤ t₂)
    {X : ℝ} (hX : (1 / 2 : ℝ) ≤ X) :
    (∫ σ in (1 / 2 : ℝ)..X,
        (Real.log ‖riemannZeta ((σ : ℂ) + I * t₂)‖
          - Real.log ‖riemannZeta ((σ : ℂ) + I * t₁)‖))
      = -∫ t in t₁..t₂,
          (∫ σ in (1 / 2 : ℝ)..X, logDeriv riemannZeta ((σ : ℂ) + I * t)).im := by
  have hcongr : (∫ σ in (1 / 2 : ℝ)..X,
        (Real.log ‖riemannZeta ((σ : ℂ) + I * t₂)‖
          - Real.log ‖riemannZeta ((σ : ℂ) + I * t₁)‖))
      = ∫ σ in (1 / 2 : ℝ)..X,
          -(∫ t in t₁..t₂, logDeriv riemannZeta ((σ : ℂ) + I * t)).im := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [compl_mem_ae_iff.mpr ((finite_re_riemannZeta_zeros_rectangle
      (z := (1 / 2 : ℂ) + I * (t₁ : ℂ)) (w := (X : ℂ) + I * (t₂ : ℂ)) (by simpa using ht1)
      (by simpa using ht1.trans_le h12)).measure_zero volume)] with σ hσ hσI
    rw [Set.uIoc_of_le hX] at hσI
    refine log_norm_riemannZeta_sub_eq_neg_im_integral h12 ht1 fun t ht hzero ↦
      hσ ⟨(σ : ℂ) + I * (t : ℂ), ⟨ofReal_add_I_mul_mem_rectangle (by simpa using hX)
        (by simpa using h12) (by simpa using (⟨hσI.1.le, hσI.2⟩ : σ ∈ Icc (1 / 2 : ℝ) X))
        (by simpa using ht), hzero⟩, by simp⟩
  have hpullσ := intervalIntegral_im hX (integrable_integral_logDeriv_riemannZeta_col ht1 h12 hX)
  have hpullt := intervalIntegral_im h12 (integrable_integral_logDeriv_riemannZeta_row ht1 h12 hX)
  have hswap : (∫ σ in (1 / 2 : ℝ)..X, ∫ t in t₁..t₂, logDeriv riemannZeta ((σ : ℂ) + I * t))
      = ∫ t in t₁..t₂, ∫ σ in (1 / 2 : ℝ)..X, logDeriv riemannZeta ((σ : ℂ) + I * t) := by
    rw [intervalIntegral₂_eq_setIntegral₂ hX h12, intervalIntegral₂_eq_setIntegral₂ h12 hX]
    exact integral_integral_swap (integrable_logDeriv_riemannZeta_box hX ht1 h12)
  rw [hcongr, intervalIntegral.integral_neg]
  congr 1
  rw [hpullσ, hswap, ← hpullt]
private theorem ae_not_mem_im_riemannZeta_zeros {t₁ t₂ : ℝ} (ht1 : 0 < t₁) (ht2 : 0 < t₂) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      t ∉ Complex.im '' (Rectangle ((1 / 2 : ℂ) + I * (t₁ : ℂ)) ((2 : ℂ) + I * (t₂ : ℂ))
        ∩ {ρ | riemannZeta ρ = 0}) :=
  compl_mem_ae_iff.mpr ((finite_im_riemannZeta_zeros_rectangle (by simpa using ht1)
    (by simpa using ht2)).measure_zero volume)
private theorem pos_and_ray_ne_zero_of_not_mem_im_zeros {t₁ t₂ : ℝ} (ht1 : 0 < t₁) (h12 : t₁ ≤ t₂)
    {t : ℝ} (htI : t ∈ Set.uIoc t₁ t₂)
    (htbad : t ∉ Complex.im '' (Rectangle ((1 / 2 : ℂ) + I * (t₁ : ℂ)) ((2 : ℂ) + I * (t₂ : ℂ))
      ∩ {ρ | riemannZeta ρ = 0})) :
    0 < t ∧ ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0 := by
  rw [Set.uIoc_of_le h12] at htI
  have htIcc : t ∈ Set.Icc t₁ t₂ := Set.Ioc_subset_Icc_self htI
  exact ⟨by linarith [htIcc.1], riemannZeta_ray_ne_zero_of_not_mem_im_zeros h12 htIcc htbad⟩
private theorem aestronglyMeasurable_im_integral_row {t₁ t₂ : ℝ} (ht1 : 0 < t₁) (h12 : t₁ ≤ t₂)
    {X : ℝ} (hX : (1 / 2 : ℝ) ≤ X) :
    AEStronglyMeasurable
      (fun t : ℝ ↦ (∫ σ in (1 / 2 : ℝ)..X, logDeriv riemannZeta ((σ : ℂ) + I * t)).im)
      ((volume : Measure ℝ).restrict (Set.uIoc t₁ t₂)) :=
  ((integrable_integral_logDeriv_riemannZeta_row ht1 h12 hX).im).aestronglyMeasurable.mono_measure
    (Measure.restrict_mono (Set.uIoc_of_le h12 ▸ Set.Ioc_subset_Icc_self) le_rfl)
theorem intervalIntegrable_argZeta {t₁ t₂ : ℝ} (ht1 : 0 < t₁) (h12 : t₁ ≤ t₂) :
    IntervalIntegrable argZeta volume t₁ t₂ := by
  have ht2 : 0 < t₂ := lt_of_lt_of_le ht1 h12
  have h0T := ae_not_mem_im_riemannZeta_zeros ht1 ht2
  set bound : ℝ → ℝ := fun t ↦ 2 * Real.arcsin (Real.pi ^ 2 / 6 - 1)
      + ∫ σ in (1 / 2 : ℝ)..2, ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖
  set F : ℕ → ℝ → ℝ := fun n t ↦
    (∫ σ in (1 / 2 : ℝ)..((n : ℝ) + 1), logDeriv riemannZeta ((σ : ℂ) + I * t)).im
  have hFmeas : ∀ n, AEStronglyMeasurable (F n)
      ((volume : Measure ℝ).restrict (Set.uIoc t₁ t₂)) := fun n ↦
    aestronglyMeasurable_im_integral_row ht1 h12
      (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc t₁ t₂ →
      Tendsto (fun n : ℕ ↦ F n t) atTop (𝓝 (-(Real.pi * argZeta t)))
        ∧ ‖-(Real.pi * argZeta t)‖ ≤ bound t := by
    filter_upwards [h0T] with t htbad htI
    obtain ⟨htpos, hray⟩ := pos_and_ray_ne_zero_of_not_mem_im_zeros ht1 h12 htI htbad
    have htend : Tendsto (fun n : ℕ ↦ F n t) atTop (𝓝 (-(Real.pi * argZeta t))) :=
      (tendsto_im_integral_logDeriv_row_atTop htpos hray).comp
        (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
    refine ⟨htend, le_of_tendsto htend.norm ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Real.norm_eq_abs]
    exact abs_im_integral_logDeriv_row_le
      (by exact_mod_cast Nat.add_one_le_iff.mpr (by lia)) htpos.ne' hray
  have hmeas : AEStronglyMeasurable (fun t ↦ -(Real.pi * argZeta t))
      ((volume : Measure ℝ).restrict (Set.uIoc t₁ t₂)) := by
    refine aestronglyMeasurable_of_tendsto_ae atTop hFmeas ?_
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hae] with t ht htI using (ht htI).1
  have hbound_int : IntegrableOn bound (Set.uIoc t₁ t₂) volume :=
    Set.uIoc_of_le h12 ▸ (integrableOn_argVariation_riemannZeta_horizontal_bound ht1
      h12).mono_set Set.Ioc_subset_Icc_self
  have hdom : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.uIoc t₁ t₂)),
      ‖-(Real.pi * argZeta t)‖ ≤ bound t := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hae] with t ht htI using (ht htI).2
  have hfun : (fun t ↦ -(1 / Real.pi) * -(Real.pi * argZeta t)) = argZeta := funext fun t ↦ by
    rw [neg_mul_neg, ← mul_assoc, one_div_mul_cancel Real.pi_ne_zero, one_mul]
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h12, ← Set.uIoc_of_le h12]
  exact hfun ▸ (Integrable.mono' hbound_int hmeas hdom).const_mul (-(1 / Real.pi))
theorem finite_setOf_riemannZeta_zero_ray_Icc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    {t : ℝ | (∃ σ : ℝ, (1 / 2 : ℝ) ≤ σ ∧ riemannZeta ((σ : ℂ) + I * t) = 0)
      ∧ t ∈ Set.Icc a b}.Finite := by
  have hb : (0 : ℝ) < b := lt_of_lt_of_le ha hab
  refine Set.Finite.subset (finite_im_riemannZeta_zeros_rectangle
    (show (0 : ℝ) < ((1 / 2 : ℂ) + I * (a : ℂ)).im by simpa using ha)
    (show (0 : ℝ) < ((2 : ℂ) + I * (b : ℂ)).im by simpa using hb)) ?_
  rintro t ⟨⟨σ, hσ, hz⟩, htab⟩
  exact ⟨(σ : ℂ) + I * (t : ℂ), ⟨ofReal_add_I_mul_mem_rectangle_two hab hσ
    (re_le_one_of_riemannZeta_eq_zero hz) htab, hz⟩, by simp⟩
theorem pi_mul_integral_argZeta_eq_sub {t₁ t₂ : ℝ} (h12 : t₁ < t₂) (ht1 : 0 < t₁)
    (hne1 : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₁) ≠ 0)
    (hne2 : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₂) ≠ 0) :
    Real.pi * ∫ t in t₁..t₂, argZeta t
      = logNormZetaIntegral t₂ - logNormZetaIntegral t₁ := by
  have h12' : t₁ ≤ t₂ := h12.le
  have ht2 : 0 < t₂ := lt_trans ht1 h12
  have htr : ∀ t : ℝ, t ≠ 0 → (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0) →
      Tendsto (fun X : ℝ ↦ ∫ σ in (1 / 2 : ℝ)..X, Real.log ‖riemannZeta ((σ : ℂ) + I * t)‖)
        atTop (𝓝 (logNormZetaIntegral t)) := fun t ht hne ↦ by
    simpa [logNormZetaIntegral] using intervalIntegral_tendsto_integral_Ioi (1 / 2)
      (integrableOn_log_norm_riemannZeta_Ioi ht hne) tendsto_id
  have hii : ∀ t : ℝ, t ≠ 0 → (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0) →
      ∀ X : ℝ, (1 / 2 : ℝ) ≤ X → IntervalIntegrable
        (fun σ : ℝ ↦ Real.log ‖riemannZeta ((σ : ℂ) + I * t)‖) volume (1 / 2) X :=
    fun t ht hne X hX ↦ (intervalIntegrable_iff_integrableOn_Ioc_of_le hX).mpr
      ((integrableOn_log_norm_riemannZeta_Ioi ht hne).mono_set Set.Ioc_subset_Ioi_self)
  have hDtend : Tendsto (fun X : ℝ ↦ ∫ σ in (1 / 2 : ℝ)..X,
        (Real.log ‖riemannZeta ((σ : ℂ) + I * t₂)‖
          - Real.log ‖riemannZeta ((σ : ℂ) + I * t₁)‖)) atTop
      (𝓝 (logNormZetaIntegral t₂ - logNormZetaIntegral t₁)) := by
    refine ((htr t₂ ht2.ne' hne2).sub (htr t₁ ht1.ne' hne1)).congr' ?_
    filter_upwards [eventually_ge_atTop (1 / 2 : ℝ)] with X hX
    rw [intervalIntegral.integral_sub (hii t₂ ht2.ne' hne2 X hX) (hii t₁ ht1.ne' hne1 X hX)]
  have h0T := ae_not_mem_im_riemannZeta_zeros ht1 ht2
  have hDCT : Tendsto (fun X : ℝ ↦ ∫ t in t₁..t₂,
        (∫ σ in (1 / 2 : ℝ)..X, logDeriv riemannZeta ((σ : ℂ) + I * t)).im) atTop
      (𝓝 (∫ t in t₁..t₂, -(Real.pi * argZeta t))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun t ↦ 2 * Real.arcsin (Real.pi ^ 2 / 6 - 1)
        + ∫ σ in (1 / 2 : ℝ)..2, ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖) ?_ ?_ ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 / 2 : ℝ)] with X hX
      exact aestronglyMeasurable_im_integral_row ht1 h12' hX
    · filter_upwards [eventually_ge_atTop (2 : ℝ)] with X hX
      filter_upwards [h0T] with t htbad htI
      obtain ⟨htpos, hray⟩ := pos_and_ray_ne_zero_of_not_mem_im_zeros ht1 h12' htI htbad
      rw [Real.norm_eq_abs]
      exact abs_im_integral_logDeriv_row_le hX htpos.ne' hray
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h12').mpr
        ((integrableOn_argVariation_riemannZeta_horizontal_bound ht1 h12').mono_set
          Set.Ioc_subset_Icc_self)
    · filter_upwards [h0T] with t htbad htI
      obtain ⟨htpos, hray⟩ := pos_and_ray_ne_zero_of_not_mem_im_zeros ht1 h12' htI htbad
      exact tendsto_im_integral_logDeriv_row_atTop htpos hray
  have huniq : logNormZetaIntegral t₂ - logNormZetaIntegral t₁
      = -∫ t in t₁..t₂, -(Real.pi * argZeta t) :=
    tendsto_nhds_unique (hDtend.congr' (by
      filter_upwards [eventually_ge_atTop (1 / 2 : ℝ)] with X hX
      exact integral_log_norm_riemannZeta_sub_eq ht1 h12' hX)) hDCT.neg
  rw [huniq, intervalIntegral.integral_neg, neg_neg, intervalIntegral.integral_const_mul]
end
end CertificatePort71

section CertificatePort72
section
open Complex Filter Topology MeasureTheory Set
theorem Real.sum_range_rpow_neg_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.range (N + 1), (n : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (1 - σ) / (1 - σ) + 1 := by
  have h1mσ : 0 < 1 - σ := by linarith
  have hcmp := (Real.antitoneOn_rpow_neg_Icc (a := 1) (b := 1 + (↑(N - 1) : ℝ)) hσ0.le
    one_pos).sum_le_integral
  have hcast : (1 : ℝ) + (↑(N - 1) : ℝ) = (N : ℝ) := by
    rw [Nat.cast_sub hN]; push_cast; ring
  rw [hcast] at hcmp
  have hint : ∫ x in (1 : ℝ)..(N : ℝ), x ^ (-σ) = ((N : ℝ) ^ (1 - σ) - 1) / (1 - σ) := by
    rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < -σ)), Real.one_rpow,
      show -σ + 1 = 1 - σ by ring]
  rw [hint] at hcmp
  rw [Finset.sum_range_succ', Nat.cast_zero, Real.zero_rpow (neg_ne_zero.mpr hσ0.ne'), add_zero]
  have inner : ∑ i ∈ Finset.range N, ((↑(i + 1) : ℝ)) ^ (-σ)
      = (∑ i ∈ Finset.range (N - 1), ((1 : ℝ) + ↑(i + 1)) ^ (-σ)) + 1 := by
    conv_lhs => rw [show N = (N - 1) + 1 by lia]
    rw [Finset.sum_range_succ']
    congr 1
    · refine Finset.sum_congr rfl (fun i _ ↦ ?_)
      congr 1; push_cast; ring
    · norm_num
  rw [inner]
  calc (∑ i ∈ Finset.range (N - 1), ((1 : ℝ) + ↑(i + 1)) ^ (-σ)) + 1
      ≤ ((N : ℝ) ^ (1 - σ) - 1) / (1 - σ) + 1 := by linarith [hcmp]
    _ ≤ (N : ℝ) ^ (1 - σ) / (1 - σ) + 1 := by gcongr; linarith
private theorem add_mul_I_ne_one {σ t : ℝ} (ht : t ≠ 0) : (σ : ℂ) + (t : ℂ) * I ≠ 1 :=
  fun h ↦ ht (by simpa using congrArg Complex.im h)
private theorem abs_floor_bundle {t : ℝ} (ht : 3 < |t|) :
    0 < |t| ∧ 0 < ⌊|t|⌋₊ ∧ (⌊|t|⌋₊ : ℝ) ≤ |t| :=
  have htpos : (0 : ℝ) < |t| := by linarith
  ⟨htpos, Nat.floor_pos.mpr (by linarith), Nat.floor_le htpos.le⟩
private theorem norm_sum_one_div_cpow_le {σ t : ℝ} (hσ : σ ∈ Ioo (1 / 2 : ℝ) 1) (ht : 3 < |t|) :
    ‖∑ n ∈ Finset.range (⌊|t|⌋₊ + 1), 1 / (n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I)‖
      ≤ |t| ^ (1 - σ) / (1 - σ) + |t| ^ (1 - σ) := by
  have σpos : 0 < σ := by linarith [hσ.1]
  have h1mσ : 0 < 1 - σ := by linarith [hσ.2]
  obtain ⟨htpos, Npos, N_le_t⟩ := abs_floor_bundle ht
  have hre : 0 < ((σ : ℂ) + (t : ℂ) * I).re := by
    rw [show ((σ : ℂ) + (t : ℂ) * I).re = σ by simp]; exact σpos
  have hs_ne : (σ : ℂ) + (t : ℂ) * I ≠ 0 := fun h ↦ by rw [h] at hre; simp at hre
  have hsum_norm : ‖∑ n ∈ Finset.range (⌊|t|⌋₊ + 1), 1 / (n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I)‖
      ≤ ∑ n ∈ Finset.range (⌊|t|⌋₊ + 1), (n : ℝ) ^ (-σ) := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun n _ ↦ ?_))
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [Nat.cast_zero]
      rw [Complex.zero_cpow hs_ne, div_zero, norm_zero, Real.zero_rpow (neg_ne_zero.mpr σpos.ne')]
    · rw [norm_div, norm_one, norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
        show ((σ : ℂ) + (t : ℂ) * I).re = σ by simp, one_div, Real.rpow_neg (Nat.cast_nonneg n)]
  refine hsum_norm.trans ((Real.sum_range_rpow_neg_le σpos hσ.2 Npos).trans ?_)
  have hdiv : (⌊|t|⌋₊ : ℝ) ^ (1 - σ) / (1 - σ) ≤ |t| ^ (1 - σ) / (1 - σ) := by gcongr
  have h1L : (1 : ℝ) ≤ |t| ^ (1 - σ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ |t|) h1mσ.le
  linarith
private theorem norm_neg_cpow_one_sub_div_le {σ t : ℝ} (hσ : σ ∈ Ioo (1 / 2 : ℝ) 1)
    (ht : 3 < |t|) :
    ‖-(⌊|t|⌋₊ : ℂ) ^ (1 - ((σ : ℂ) + (t : ℂ) * I)) / (1 - ((σ : ℂ) + (t : ℂ) * I))‖
      ≤ |t| ^ (1 - σ) * 2 := by
  obtain ⟨htpos, Npos, N_le_t⟩ := abs_floor_bundle ht
  rw [norm_div, norm_neg, norm_natCast_cpow_of_pos Npos,
    show ((1 : ℂ) - ((σ : ℂ) + (t : ℂ) * I)).re = 1 - σ by simp]
  exact (UpperBnd_aux6 ht ⟨hσ.1, by linarith [hσ.2]⟩ (add_mul_I_ne_one (abs_pos.mp htpos))
    Npos N_le_t).1
private theorem norm_neg_cpow_neg_div_two_le {σ t : ℝ} (hσ : σ ∈ Ioo (1 / 2 : ℝ) 1)
    (ht : 3 < |t|) :
    ‖-(⌊|t|⌋₊ : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) / 2‖ ≤ |t| ^ (1 - σ) := by
  obtain ⟨htpos, Npos, N_le_t⟩ := abs_floor_bundle ht
  rw [norm_div, norm_neg, norm_natCast_cpow_of_pos Npos, RCLike.norm_ofNat,
    show (-((σ : ℂ) + (t : ℂ) * I)).re = -σ by simp]
  exact (UpperBnd_aux6 ht ⟨hσ.1, by linarith [hσ.2]⟩ (add_mul_I_ne_one (abs_pos.mp htpos))
    Npos N_le_t).2.1
private theorem norm_riemannZeta0_tail_le {σ t : ℝ} (hσ : σ ∈ Ioo (1 / 2 : ℝ) 1) (ht : 3 < |t|) :
    ‖((σ : ℂ) + (t : ℂ) * I) * ∫ x in Ioi (⌊|t|⌋₊ : ℝ),
        (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (((σ : ℂ) + (t : ℂ) * I) + 1)‖ ≤ 16 * |t| ^ (1 - σ) := by
  have σpos : 0 < σ := by linarith [hσ.1]
  have hσ2 : σ ≤ 2 := by linarith [hσ.2]
  obtain ⟨htpos, Npos, N_le_t⟩ := abs_floor_bundle ht
  have hpow : |t| * |t| ^ (-σ) = |t| ^ (1 - σ) := by
    rw [show (1 - σ : ℝ) = 1 + (-σ) by ring, Real.rpow_add htpos, Real.rpow_one]
  refine (ZetaBnd_aux1 ⌊|t|⌋₊ Npos ⟨σpos, hσ2⟩ (by linarith : (2 : ℝ) ≤ |t|)).trans ?_
  rw [mul_div_assoc]
  refine (mul_le_mul_of_nonneg_left
    (UpperBnd_aux6 ht ⟨hσ.1, hσ2⟩ (add_mul_I_ne_one (abs_pos.mp htpos)) Npos N_le_t).2.2
    (by positivity)).trans (le_of_eq ?_)
  rw [show |t| ^ (1 - σ) = |t| * |t| ^ (-σ) from hpow.symm]; ring
theorem norm_riemannZeta_le_of_mem_strip {σ t : ℝ} (hσ : σ ∈ Ioo (1 / 2 : ℝ) 1) (ht : 3 < |t|) :
    ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ ≤ 11 / (1 - σ) * |t| ^ (1 - σ) := by
  rw [mul_comm Complex.I (t : ℂ)]
  have h1mσ : 0 < 1 - σ := by linarith [hσ.2]
  have σpos : 0 < σ := by linarith [hσ.1]
  obtain ⟨htpos, Npos, -⟩ := abs_floor_bundle ht
  have hre : 0 < ((σ : ℂ) + (t : ℂ) * I).re := by
    rw [show ((σ : ℂ) + (t : ℂ) * I).re = σ by simp]; exact σpos
  have hL : (0 : ℝ) < |t| ^ (1 - σ) := Real.rpow_pos_of_pos htpos _
  rw [← Zeta0EqZeta Npos hre (add_mul_I_ne_one (abs_pos.mp htpos))]
  refine le_trans (norm_add₄_le ..) ?_
  refine le_trans (add_le_add (add_le_add (add_le_add (norm_sum_one_div_cpow_le hσ ht)
    (norm_neg_cpow_one_sub_div_le hσ ht)) (norm_neg_cpow_neg_div_two_le hσ ht))
    (norm_riemannZeta0_tail_le hσ ht)) ?_
  have hscalar : 1 / (1 - σ) + 20 ≤ 11 / (1 - σ) := by
    rw [← sub_nonneg, show 11 / (1 - σ) - (1 / (1 - σ) + 20) = (20 * σ - 10) / (1 - σ) by
      field_simp; ring]
    exact div_nonneg (by linarith [hσ.1]) h1mσ.le
  calc |t| ^ (1 - σ) / (1 - σ) + |t| ^ (1 - σ) + |t| ^ (1 - σ) * 2 + |t| ^ (1 - σ)
        + 16 * |t| ^ (1 - σ)
      = (1 / (1 - σ) + 20) * |t| ^ (1 - σ) := by ring
    _ ≤ 11 / (1 - σ) * |t| ^ (1 - σ) := mul_le_mul_of_nonneg_right hscalar hL.le
private theorem intervalIntegrable_log_one_sub :
    IntervalIntegrable (fun σ : ℝ ↦ Real.log (1 - σ)) volume (1 / 2) 1 := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := (1 / 2 : ℝ)) (b := 0)).comp_sub_left 1
  norm_num at h; exact h
private theorem intervalIntegrable_log_sub_one :
    IntervalIntegrable (fun σ : ℝ ↦ Real.log (σ - 1)) volume 1 2 := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := 1)).comp_sub_right 1
  norm_num at h; exact h
private theorem integral_strip_majorant (L : ℝ) :
    ∫ σ in (1 / 2 : ℝ)..1, (Real.log 11 + (1 - σ) * L - Real.log (1 - σ))
      = 1 / 2 * Real.log 11 + L / 8 + (1 / 2 * Real.log 2 + 1 / 2) := by
  have ii_const : IntervalIntegrable (fun _ : ℝ ↦ Real.log 11) volume (1 / 2) 1 :=
    intervalIntegrable_const
  have ii_lin : IntervalIntegrable (fun σ : ℝ ↦ (1 - σ) * L) volume (1 / 2) 1 :=
    Continuous.intervalIntegrable (by fun_prop) (1 / 2) 1
  have ii_log := intervalIntegrable_log_one_sub
  have hlin : ∫ σ in (1 / 2 : ℝ)..1, (1 - σ) * L = L / 8 := by
    rw [intervalIntegral.integral_mul_const]
    have hone : ∫ σ in (1 / 2 : ℝ)..1, (1 - σ) = 1 / 8 := by
      rw [intervalIntegral.integral_comp_sub_left (fun x ↦ x) 1, integral_id]
      norm_num
    rw [hone]; ring
  have hlog : ∫ σ in (1 / 2 : ℝ)..1, Real.log (1 - σ) = -(1 / 2 * Real.log 2) - 1 / 2 := by
    rw [intervalIntegral.integral_comp_sub_left (fun x ↦ Real.log x) 1, integral_log]
    rw [show (1 : ℝ) - 1 = 0 by norm_num, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
      Real.log_div one_ne_zero two_ne_zero, Real.log_one]
    simp
  rw [intervalIntegral.integral_sub (ii_const.add ii_lin) ii_log,
    intervalIntegral.integral_add ii_const ii_lin, intervalIntegral.integral_const, hlin, hlog]
  simp only [smul_eq_mul]
  ring
theorem norm_riemannZeta_le_div_sub_one {σ t : ℝ} (hσ : 1 < σ) :
    ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ ≤ σ / (σ - 1) := by
  have hσ1 : (0 : ℝ) < σ - 1 := by linarith
  set s : ℂ := (σ : ℂ) + Complex.I * t with hs
  have hsre : s.re = σ := by simp [hs]
  have htail : ‖riemannZeta s - 1‖ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ := by
    have h := norm_riemannZeta_sub_one_le (s := s) (by rw [hsre]; exact hσ)
    rwa [hsre] at h
  have hsum := Real.tsum_one_div_nat_add_two_rpow_le_inv_sub_one hσ
  have hnorm := norm_le_insert (1 : ℂ) (riemannZeta s)
  rw [norm_one, norm_sub_rev] at hnorm
  refine (by linarith [htail, hsum] : ‖riemannZeta s‖ ≤ 1 + 1 / (σ - 1)).trans (le_of_eq ?_)
  rw [eq_div_iff hσ1.ne']; field_simp; ring
private theorem integral_log_sub_log_sub_one :
    ∫ σ in (1 : ℝ)..2, (Real.log σ - Real.log (σ - 1)) = 2 * Real.log 2 := by
  have iiA : IntervalIntegrable (fun σ : ℝ ↦ Real.log σ) volume 1 2 :=
    intervalIntegral.intervalIntegrable_log'
  rw [intervalIntegral.integral_sub iiA intervalIntegrable_log_sub_one]
  have hA : ∫ σ in (1 : ℝ)..2, Real.log σ = 2 * Real.log 2 - 1 := by
    rw [integral_log, Real.log_one]; ring
  have hB : ∫ σ in (1 : ℝ)..2, Real.log (σ - 1) = -1 := by
    rw [intervalIntegral.integral_comp_sub_right (fun x ↦ Real.log x) 1]
    norm_num [integral_log, Real.log_one]
  rw [hA, hB]; ring
private theorem integrableOn_log_norm_riemannZeta_subset {t : ℝ} {S : Set ℝ} (ht : t ≠ 0)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0)
    (hS : S ⊆ Ioi (1 / 2 : ℝ)) :
    IntegrableOn (fun σ : ℝ ↦ Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) S :=
  (integrableOn_log_norm_riemannZeta_Ioi ht hzero).mono_set hS
private theorem logNormZetaIntegral_eq_add {t : ℝ} (ht : t ≠ 0)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    logNormZetaIntegral t
      = (∫ σ in Ioc (1 / 2 : ℝ) 1, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
        + (∫ σ in Ioc (1 : ℝ) 2, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
        + (∫ σ in Ioc (2 : ℝ) 4, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
        + ∫ σ in Ioi (4 : ℝ), Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ := by
  have ig : ∀ {S : Set ℝ}, S ⊆ Ioi (1 / 2 : ℝ) →
      IntegrableOn (fun σ : ℝ ↦ Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) S :=
    fun hS ↦ integrableOn_log_norm_riemannZeta_subset ht hzero hS
  have ig_a := ig (S := Ioc (1 / 2 : ℝ) 1) Ioc_subset_Ioi_self
  have ig_Ioi1 := ig (S := Ioi (1 : ℝ)) (Ioi_subset_Ioi (by norm_num))
  have ig_Ioi2 := ig (S := Ioi (2 : ℝ)) (Ioi_subset_Ioi (by norm_num))
  have ig_b := ig (S := Ioc (1 : ℝ) 2) (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by norm_num)))
  have ig_c := ig (S := Ioc (2 : ℝ) 4) (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by norm_num)))
  have ig_d := ig (S := Ioi (4 : ℝ)) (Ioi_subset_Ioi (by norm_num))
  rw [logNormZetaIntegral, ← Ioc_union_Ioi_eq_Ioi (show (1 / 2 : ℝ) ≤ 1 by norm_num),
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi ig_a ig_Ioi1,
    ← Ioc_union_Ioi_eq_Ioi (show (1 : ℝ) ≤ 2 by norm_num),
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi ig_b ig_Ioi2,
    ← Ioc_union_Ioi_eq_Ioi (show (2 : ℝ) ≤ 4 by norm_num),
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi ig_c ig_d]
  ring
private theorem integral_log_norm_riemannZeta_Ioc_half_one_le {t : ℝ} (ht : 3 < t)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    (∫ σ in Ioc (1 / 2 : ℝ) 1, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ≤ 1 / 2 * Real.log 11 + Real.log t / 8 + (1 / 2 * Real.log 2 + 1 / 2) := by
  have htpos : 0 < t := by linarith
  have ht3 : 3 < |t| := by rwa [abs_of_pos htpos]
  have hpos : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → 0 < ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ :=
    fun σ hσ ↦ norm_pos_iff.mpr (hzero σ hσ)
  have ig_a := integrableOn_log_norm_riemannZeta_subset (S := Ioc (1 / 2 : ℝ) 1) htpos.ne' hzero
    Ioc_subset_Ioi_self
  have hmaj : IntegrableOn
      (fun σ : ℝ ↦ Real.log 11 + (1 - σ) * Real.log t - Real.log (1 - σ))
      (Ioc (1 / 2 : ℝ) 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    exact ((intervalIntegrable_const).add
      (Continuous.intervalIntegrable (by fun_prop) (1 / 2) 1)).sub intervalIntegrable_log_one_sub
  calc (∫ σ in Ioc (1 / 2 : ℝ) 1, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ≤ ∫ σ in Ioc (1 / 2 : ℝ) 1, (Real.log 11 + (1 - σ) * Real.log t - Real.log (1 - σ)) := by
        refine setIntegral_mono_on_ae ig_a hmaj measurableSet_Ioc ?_
        have hne1 : ∀ᵐ σ : ℝ, σ ≠ 1 := by rw [ae_iff]; simp
        filter_upwards [hne1] with σ hσ1 hσmem
        have hσIoo : σ ∈ Ioo (1 / 2 : ℝ) 1 := ⟨hσmem.1, lt_of_le_of_ne hσmem.2 hσ1⟩
        have h1mσ : 0 < 1 - σ := by linarith [hσIoo.2]
        have hstrip := norm_riemannZeta_le_of_mem_strip hσIoo ht3
        rw [abs_of_pos htpos] at hstrip
        have hzpos := hpos σ (le_of_lt hσmem.1)
        have hlogexp : Real.log (11 / (1 - σ) * t ^ (1 - σ))
            = Real.log 11 - Real.log (1 - σ) + (1 - σ) * Real.log t := by
          rw [Real.log_mul (ne_of_gt (div_pos (by norm_num) h1mσ))
              (ne_of_gt (Real.rpow_pos_of_pos htpos _)),
            Real.log_div (by norm_num) (ne_of_gt h1mσ), Real.log_rpow htpos]
        calc Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖
            ≤ Real.log (11 / (1 - σ) * t ^ (1 - σ)) := Real.log_le_log hzpos hstrip
          _ = Real.log 11 + (1 - σ) * Real.log t - Real.log (1 - σ) := by rw [hlogexp]; ring
    _ = ∫ σ in (1 / 2 : ℝ)..1, (Real.log 11 + (1 - σ) * Real.log t - Real.log (1 - σ)) :=
        (intervalIntegral.integral_of_le (by norm_num)).symm
    _ = 1 / 2 * Real.log 11 + Real.log t / 8 + (1 / 2 * Real.log 2 + 1 / 2) :=
        integral_strip_majorant _
private theorem integral_log_norm_riemannZeta_Ioc_two_four_le {t : ℝ} (ht : t ≠ 0)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    (∫ σ in Ioc (2 : ℝ) 4, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ≤ 2 * Real.log (Real.pi ^ 2 / 6) := by
  have hpos : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → 0 < ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ :=
    fun σ hσ ↦ norm_pos_iff.mpr (hzero σ hσ)
  have ig_c := integrableOn_log_norm_riemannZeta_subset (S := Ioc (2 : ℝ) 4) ht hzero
    (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by norm_num)))
  have ig_m3 : IntegrableOn (fun _ : ℝ ↦ Real.log (Real.pi ^ 2 / 6)) (Ioc (2 : ℝ) 4) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (2 : ℝ) ≤ 4)]
    exact intervalIntegrable_const
  calc (∫ σ in Ioc (2 : ℝ) 4, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ≤ ∫ σ in Ioc (2 : ℝ) 4, Real.log (Real.pi ^ 2 / 6) := by
        refine setIntegral_mono_on ig_c ig_m3 measurableSet_Ioc ?_
        intro σ hσmem
        have hre : ((σ : ℂ) + Complex.I * t).re = σ := by simp
        have hb := norm_riemannZeta_sub_one_le_of_two_le_re
          (s := (σ : ℂ) + Complex.I * t) (by rw [hre]; linarith [hσmem.1])
        have hzle : ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ ≤ Real.pi ^ 2 / 6 := by
          have h := norm_sub_norm_le (riemannZeta ((σ : ℂ) + Complex.I * t)) 1
          rw [norm_one] at h
          linarith
        have hzpos := hpos σ (by linarith [hσmem.1])
        exact Real.log_le_log hzpos hzle
    _ = 2 * Real.log (Real.pi ^ 2 / 6) := by
        rw [← intervalIntegral.integral_of_le (by norm_num : (2 : ℝ) ≤ 4),
          intervalIntegral.integral_const]; norm_num
private theorem integral_log_norm_riemannZeta_Ioi_four_le {t : ℝ} (ht : t ≠ 0)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    (∫ σ in Ioi (4 : ℝ), Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ≤ ∫ σ in Ioi (4 : ℝ), 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have ig_d := integrableOn_log_norm_riemannZeta_subset (S := Ioi (4 : ℝ)) ht hzero
    (Ioi_subset_Ioi (by norm_num))
  have ig_maj : IntegrableOn
      (fun σ : ℝ ↦ 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ))) (Ioi (4 : ℝ)) :=
    (Real.integrableOn_exp_neg_mul_Ioi hl2 4).const_mul _
  refine setIntegral_mono_on ig_d ig_maj measurableSet_Ioi ?_
  intro σ hσmem
  calc Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖
      ≤ |Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖| := le_abs_self _
    _ ≤ 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ)) :=
        abs_log_norm_riemannZeta_le_exp (le_of_lt hσmem)
theorem logNormZetaIntegral_le_of_middle {M₂ β₂ : ℝ} {t : ℝ} (ht : 168 * Real.pi ≤ t)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0)
    (hmid : (∫ σ in Ioc (1 : ℝ) 2, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
        ≤ M₂ + β₂ * Real.log t) :
    logNormZetaIntegral t ≤
      (1 / 2 * Real.log 11 + (1 / 2 * Real.log 2 + 1 / 2) + M₂
        + (2 * Real.log (Real.pi ^ 2 / 6)
          + ∫ σ in Ioi (4 : ℝ), 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ))))
        + (1 / 8 + β₂) * Real.log t := by
  have htpos : 0 < t := by nlinarith [Real.pi_pos]
  have ht3 : 3 < t := by nlinarith [Real.pi_gt_three]
  rw [logNormZetaIntegral_eq_add htpos.ne' hzero]
  linarith [integral_log_norm_riemannZeta_Ioc_half_one_le ht3 hzero, hmid,
    integral_log_norm_riemannZeta_Ioc_two_four_le htpos.ne' hzero,
    integral_log_norm_riemannZeta_Ioi_four_le htpos.ne' hzero]
theorem logNormZetaIntegral_le_elem {t : ℝ} (ht : 168 * Real.pi ≤ t)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    logNormZetaIntegral t ≤
      (1 / 2 * Real.log 11 + (1 / 2 * Real.log 2 + 1 / 2) + 2 * Real.log 2
        + (2 * Real.log (Real.pi ^ 2 / 6)
          + ∫ σ in Ioi (4 : ℝ), 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ))))
        + 1 / 8 * Real.log t := by
  have htpos : 0 < t := by nlinarith [Real.pi_pos]
  have ig_b := integrableOn_log_norm_riemannZeta_subset (S := Ioc (1 : ℝ) 2) htpos.ne' hzero
    (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by norm_num)))
  have hmid : (∫ σ in Ioc (1 : ℝ) 2, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ≤ 2 * Real.log 2 + 0 * Real.log t := by
    have hmaj : IntegrableOn (fun σ : ℝ ↦ Real.log σ - Real.log (σ - 1)) (Ioc (1 : ℝ) 2) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
      exact intervalIntegral.intervalIntegrable_log'.sub intervalIntegrable_log_sub_one
    calc (∫ σ in Ioc (1 : ℝ) 2, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
        ≤ ∫ σ in Ioc (1 : ℝ) 2, (Real.log σ - Real.log (σ - 1)) := by
          refine setIntegral_mono_on ig_b hmaj measurableSet_Ioc (fun σ hσmem ↦ ?_)
          have hσ1 : 1 < σ := hσmem.1
          have hre : ((σ : ℂ) + Complex.I * t).re = σ := by simp
          have hzpos : 0 < ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ :=
            norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re (by rw [hre]; exact hσ1.le))
          have hζle := norm_riemannZeta_le_div_sub_one (t := t) hσ1
          calc Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖
              ≤ Real.log (σ / (σ - 1)) := Real.log_le_log hzpos hζle
            _ = Real.log σ - Real.log (σ - 1) := Real.log_div (by linarith) (by linarith)
      _ = ∫ σ in (1 : ℝ)..2, (Real.log σ - Real.log (σ - 1)) :=
          (intervalIntegral.integral_of_le (by norm_num)).symm
      _ = 2 * Real.log 2 := integral_log_sub_log_sub_one
      _ = 2 * Real.log 2 + 0 * Real.log t := by ring
  linarith [logNormZetaIntegral_le_of_middle ht hzero hmid]
private theorem integral_exp_tail_eq :
    (∫ σ in Ioi (4 : ℝ), 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ)))
      = (Real.pi ^ 2 / 6 - 1) / (2 * Real.log 2) := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have key : (∫ σ in Ioi (4 : ℝ), 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ)))
      = 8 * (Real.pi ^ 2 / 6 - 1) * ∫ σ in Ioi (4 : ℝ), Real.exp ((-Real.log 2) * σ) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun σ _ ↦ ?_)
    simp only [neg_mul]
  rw [key, integral_exp_mul_Ioi (by linarith : -Real.log 2 < 0) 4]
  have hexp : Real.exp ((-Real.log 2) * 4) = 1 / 16 := by
    rw [show (-Real.log 2) * 4 = -(4 * Real.log 2) by ring, Real.exp_neg,
      show (4 : ℝ) * Real.log 2 = Real.log (2 ^ 4) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity)]
    norm_num
  rw [hexp]; field_simp; ring
private theorem pi_sq_lt_d4 : Real.pi ^ 2 < 9.8697 := by
  nlinarith [Real.pi_lt_d6, Real.pi_pos]
private theorem log_eleven_le : Real.log 11 ≤ 3 * Real.log 2 + 3 / 8 := by
  have he : Real.log 11 = Real.log (2 ^ 3) + Real.log (11 / 8) := by
    rw [← Real.log_mul (by positivity) (by norm_num)]; norm_num
  rw [he, Real.log_pow]
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 11 / 8 by norm_num)
  push_cast; linarith
private theorem log_pi_sq_div_six_lt : Real.log (Real.pi ^ 2 / 6) < 1 / 2 := by
  rw [Real.log_lt_iff_lt_exp (by positivity)]
  have hsq : (Real.pi ^ 2 / 6) ^ 2 < Real.exp (1 / 2) ^ 2 := by
    have h1 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [pow_two, ← Real.exp_add]; norm_num
    rw [h1]; nlinarith [pi_sq_lt_d4, Real.exp_one_gt_d9]
  exact lt_of_pow_lt_pow_left₀ 2 (Real.exp_pos _).le hsq
private theorem exp_tail_lt_half : (Real.pi ^ 2 / 6 - 1) / (2 * Real.log 2) < 1 / 2 := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [pi_sq_lt_d4, Real.log_two_gt_d9]
theorem logNormZetaIntegral_le_five {t : ℝ} (ht : 168 * Real.pi ≤ t)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    logNormZetaIntegral t ≤ 5 + 1 / 8 * Real.log t := by
  refine (logNormZetaIntegral_le_elem ht hzero).trans ?_
  rw [integral_exp_tail_eq]
  linarith [log_eleven_le, log_pi_sq_div_six_lt, exp_tail_lt_half, Real.log_two_lt_d9]
end
end CertificatePort72


