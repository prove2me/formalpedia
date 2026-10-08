-- Prove2me | solution 1 for ArtinPrimitiveRoots.harmonic_mass
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T11:47:35.566473+00:00
-- url     : https://prove2.me/submissions/e66100b7-28d7-4eb1-a042-af3d775b2c1c

import Mathlib
import Definitions.Def_ArtinSieve
import Theorems.Thm_ArtinPrimitiveRoots_mertens_prime_reciprocals

/-!
# Harmonic mass (OpenAI, "Primitive roots for every admissible integer base", Lemma 12.2)

Group integers are parametrised by their set `T` of prime factors (a subset of the finite set of
group primes) and the cofactor, a `T`-factored number; the Euler product of Mathlib evaluates
each fibre.  The mark depends only on `T`, and splits as a product over the (disjoint) groups,
which gives the exact derivative formula.  The tail bound is Rankin's trick with
`s = L^{-a_K}`, and the predecessor mass `A_r` is at most `2x/r`.
-/

namespace ArtinPrimitiveRoots

namespace HarmonicMassSol

open Real Finset Filter Topology


lemma fiber_hasSum (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) {σ : ℝ} (hσ : 0 < σ) :
    HasSum (fun r : ℕ => if 0 < r ∧ r.primeFactors = T then (((r : ℝ) ^ σ)⁻¹) else 0)
      (∏ p ∈ T, ((p : ℝ) ^ σ - 1)⁻¹) := by
  set P : ℕ := ∏ p ∈ T, p with hP
  have hPpos : 0 < P := Finset.prod_pos fun p hp => (hT p hp).pos
  have hPf : P.primeFactors = T := Nat.primeFactors_prod hT
  let g : Nat.factoredNumbers T → ℕ := fun m => P * m.1
  have hg : Function.Injective g := by
    intro m n h
    exact Subtype.ext (Nat.eq_of_mul_eq_mul_left hPpos h)
  have hrange : ∀ r ∉ Set.range g,
      (if 0 < r ∧ r.primeFactors = T then (((r : ℝ) ^ σ)⁻¹) else 0) = 0 := by
    intro r hr
    rw [if_neg]
    rintro ⟨hr0, hrT⟩
    apply hr
    have hd : P ∣ r := by rw [hP, ← hrT]; exact Nat.prod_primeFactors_dvd r
    obtain ⟨m, rfl⟩ := hd
    have hm : m ≠ 0 := by rintro rfl; simp at hr0
    refine ⟨⟨m, hm, fun p hp => ?_⟩, rfl⟩
    rw [← hrT, Nat.mem_primeFactors]
    exact ⟨Nat.prime_of_mem_primeFactorsList hp, Dvd.dvd.mul_left (Nat.dvd_of_mem_primeFactorsList hp) _,
      hr0.ne'⟩
  rw [← hg.hasSum_iff hrange]
  -- Euler product
  have hf1 : ((((1 : ℕ) : ℝ) ^ σ)⁻¹) = 1 := by simp
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n →
      ((((m * n : ℕ) : ℝ) ^ σ)⁻¹) = (((m : ℝ) ^ σ)⁻¹) * (((n : ℝ) ^ σ)⁻¹) := by
    intro m n _
    rw [Nat.cast_mul, mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), mul_inv]
  have hgeom : ∀ {p : ℕ}, p.Prime → ∀ n : ℕ, ((((p ^ n : ℕ) : ℝ) ^ σ)⁻¹) = (((p : ℝ) ^ σ)⁻¹) ^ n := by
    intro p _ n
    rw [Nat.cast_pow, ← rpow_natCast, ← rpow_mul (Nat.cast_nonneg _), mul_comm, rpow_mul (Nat.cast_nonneg _),
      rpow_natCast, inv_pow]
  have hlt : ∀ {p : ℕ}, p.Prime → ((p : ℝ) ^ σ)⁻¹ < 1 := by
    intro p hp
    apply inv_lt_one_of_one_lt₀
    exact one_lt_rpow (by exact_mod_cast hp.one_lt) hσ
  have hpos : ∀ {p : ℕ}, p.Prime → 0 ≤ ((p : ℝ) ^ σ)⁻¹ := fun _ => by positivity
  have hsum : ∀ {p : ℕ}, p.Prime →
      Summable (fun n : ℕ => ‖((((p ^ n : ℕ) : ℝ) ^ σ)⁻¹)‖) := by
    intro p hp
    simp_rw [hgeom hp, norm_pow, Real.norm_of_nonneg (hpos hp)]
    exact summable_geometric_of_lt_one (hpos hp) (hlt hp)
  have key := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := fun n : ℕ => (((n : ℝ) ^ σ)⁻¹)) hf1 hmul hsum T).2
  have hfilt : T.filter Nat.Prime = T := Finset.filter_true_of_mem hT
  rw [hfilt] at key
  have key2 := key.mul_left (((P : ℝ) ^ σ)⁻¹)
  have hv : ∏ p ∈ T, ((p : ℝ) ^ σ - 1)⁻¹ = ((P : ℝ) ^ σ)⁻¹ * ∏ p ∈ T, ∑' n : ℕ, ((((p ^ n : ℕ) : ℝ) ^ σ)⁻¹) := by
    rw [hP, Nat.cast_prod, ← Real.finsetProd_rpow _ _ (fun _ _ => Nat.cast_nonneg _), ← Finset.prod_inv_distrib,
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hpp := hT p hp
    rw [funext (hgeom hpp), tsum_geometric_of_lt_one (hpos hpp) (hlt hpp)]
    have h1 : 1 < (p : ℝ) ^ σ := one_lt_rpow (by exact_mod_cast hpp.one_lt) hσ
    field_simp
  have hf : (fun r : ℕ => if 0 < r ∧ r.primeFactors = T then (((r : ℝ) ^ σ)⁻¹) else 0) ∘ g =
      fun m => ((P : ℝ) ^ σ)⁻¹ * (((m.1 : ℕ) : ℝ) ^ σ)⁻¹ := by
    funext m
    have hm := m.2
    have hm0 : m.1 ≠ 0 := hm.1
    have hpf : (P * m.1).primeFactors = T := by
      rw [Nat.primeFactors_mul hPpos.ne' hm0, hPf]
      apply Finset.union_eq_left.2
      intro p hp
      exact hm.2 p (Nat.mem_primeFactors_iff_mem_primeFactorsList.1 hp)
    simp only [Function.comp_apply, g]
    rw [if_pos ⟨Nat.mul_pos hPpos (Nat.pos_of_ne_zero hm0), hpf⟩, Nat.cast_mul,
      mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), mul_inv]
  rw [hf, hv]
  exact key2

lemma core_hasSum (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {σ : ℝ} (hσ : 0 < σ) (F : Finset ℕ → ℝ) :
    HasSum (fun r : ℕ => if 0 < r ∧ r.primeFactors ⊆ S then F r.primeFactors * ((r : ℝ) ^ σ)⁻¹ else 0)
      (∑ T ∈ S.powerset, F T * ∏ p ∈ T, ((p : ℝ) ^ σ - 1)⁻¹) := by
  have h := hasSum_sum (fun T hT => (fiber_hasSum T (fun p hp => hS p (Finset.mem_powerset.1 hT hp)) hσ).mul_left (F T))
  have hfun : (fun r : ℕ => if 0 < r ∧ r.primeFactors ⊆ S then F r.primeFactors * ((r : ℝ) ^ σ)⁻¹ else 0)
      = fun r : ℕ => ∑ T ∈ S.powerset,
          F T * (if 0 < r ∧ r.primeFactors = T then (((r : ℝ) ^ σ)⁻¹) else 0) := by
    funext r
    by_cases hr : 0 < r ∧ r.primeFactors ⊆ S
    · rw [if_pos hr, Finset.sum_eq_single r.primeFactors]
      · rw [if_pos ⟨hr.1, rfl⟩]
      · intro T _ hT
        rw [if_neg (fun h => hT h.2.symm), mul_zero]
      · intro h; exact absurd (Finset.mem_powerset.2 hr.2) h
    · rw [if_neg hr]
      symm
      apply Finset.sum_eq_zero
      intro T hT
      rw [if_neg, mul_zero]
      rintro ⟨h1, h2⟩
      exact hr ⟨h1, h2 ▸ Finset.mem_powerset.1 hT⟩
  rw [hfun]; exact h

lemma hasDerivAt_powerset (P : Finset ℕ) (w : ℕ → ℝ) {q : ℝ} (hq : q ≠ 0) :
    HasDerivAt (fun t => ∏ p ∈ P, (1 + t * w p))
      (∑ U ∈ P.powerset, (U.card : ℝ) * q ^ ((U.card : ℤ) - 1) * ∏ p ∈ U, w p) q := by
  induction P using Finset.induction with
  | empty => simp [hasDerivAt_const]
  | insert a P ha ih =>
    have h1 : HasDerivAt (fun t => 1 + t * w a) (w a) q := by
      simpa using ((hasDerivAt_id q).mul_const (w a)).const_add 1
    have h2 : HasDerivAt (fun t => (1 + t * w a) * ∏ p ∈ P, (1 + t * w p)) _ q := h1.mul ih
    simp only [Finset.prod_insert ha]
    refine h2.congr_deriv ?_
    rw [Finset.sum_powerset_insert ha]
    have hE : ∏ p ∈ P, (1 + q * w p) = ∑ U ∈ P.powerset, q ^ U.card * ∏ p ∈ U, w p := by
      rw [Finset.prod_one_add]
      apply Finset.sum_congr rfl
      intro U _
      rw [Finset.prod_mul_distrib, Finset.prod_const]
    rw [hE, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro U hU
    have haU : a ∉ U := fun h => ha (Finset.mem_powerset.1 hU h)
    rw [Finset.card_insert_of_notMem haU, Finset.prod_insert haU]
    push_cast
    have : q ^ (((U.card : ℤ) + 1) - 1) = q ^ U.card := by simp
    rw [this]
    rcases Nat.eq_zero_or_pos U.card with h0 | hpos
    · simp [h0]
    · have : q ^ U.card = q * q ^ ((U.card : ℤ) - 1) := by
        rw [← zpow_one_add₀ hq]; simp
      rw [this]; ring

lemma prodsplit {K : ℕ} (P : Fin K → Finset ℕ) (hP : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (ψ : Fin K → Finset ℕ → ℝ) :
    ∑ T ∈ (Finset.univ.biUnion P).powerset, ∏ i, ψ i ((P i).filter (· ∈ T)) =
      ∏ i, ∑ U ∈ (P i).powerset, ψ i U := by
  rw [Finset.prod_univ_sum]
  apply Finset.sum_nbij' (fun T => fun i => (P i).filter (· ∈ T)) (fun f => Finset.univ.biUnion f)
  · intro T _
    rw [Fintype.mem_piFinset]
    intro i; exact Finset.mem_powerset.2 (Finset.filter_subset _ _)
  · intro f hf
    rw [Fintype.mem_piFinset] at hf
    rw [Finset.mem_powerset]
    intro p hp
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hp ⊢
    obtain ⟨i, hi⟩ := hp
    exact ⟨i, Finset.mem_powerset.1 (hf i) hi⟩
  · intro T hT
    rw [Finset.mem_powerset] at hT
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨i, _, h⟩; exact h
    · intro h
      have := hT h
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at this
      obtain ⟨i, hi⟩ := this
      exact ⟨i, hi, h⟩
  · intro f hf
    rw [Fintype.mem_piFinset] at hf
    funext i
    ext p
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hpi, j, hj⟩
      by_cases hij : i = j
      · exact hij ▸ hj
      · exact absurd (Finset.mem_powerset.1 (hf j) hj) (Finset.disjoint_left.1 (hP i j hij) hpi)
    · intro h; exact ⟨Finset.mem_powerset.1 (hf i) h, i, h⟩
  · intro T _
    rfl


lemma mem_primeGroup {x a : ℝ} {p : ℕ} :
    p ∈ primeGroup x a ↔ p.Prime ∧ exp (log x ^ a) ≤ p ∧ (p : ℝ) ≤ exp (2 * log x ^ a) := by
  unfold primeGroup
  rw [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, Nat.le_floor_iff (exp_pos _).le]
  tauto

lemma tendsto_Y {a : ℝ} (ha : 0 < a) : Tendsto (fun x : ℝ => exp (log x ^ a)) atTop atTop :=
  tendsto_exp_atTop.comp ((tendsto_rpow_atTop ha).comp tendsto_log_atTop)

lemma V_bounds {a : ℝ} (ha : 0 < a) :
    ∀ᶠ x in atTop, 1 / 4 ≤ groupReciprocalSum x a ∧ groupReciprocalSum x a ≤ 3 := by
  have h1 := (mertens_prime_reciprocals 1 2 one_pos one_lt_two).comp (tendsto_Y ha)
  have h2 := (mertens_prime_reciprocals (1/2) 2 (by norm_num) (by norm_num)).comp (tendsto_Y ha)
  have l2 : (1:ℝ)/4 < log (2/1) := by
    have := Real.log_two_gt_d9; norm_num; linarith
  have l4 : log (2/(1/2)) < (3:ℝ) := by
    have : log (2/(1/2) : ℝ) = 2 * log 2 := by
      rw [show (2:ℝ)/(1/2) = 2^2 by norm_num, Real.log_pow]; norm_num
    rw [this]; linarith [Real.log_two_lt_d9]
  filter_upwards [h1.eventually (lt_mem_nhds l2), h2.eventually (gt_mem_nhds l4),
    eventually_gt_atTop 1] with x hx1 hx2 hx
  simp only [Function.comp_apply] at hx1 hx2
  set y := exp (log x ^ a) with hy
  have hL : 0 < log x := log_pos hx
  have hy1 : 1 < y := by have := exp_lt_exp.2 (rpow_pos_of_pos hL a); rwa [exp_zero] at this
  have hy2 : y ^ (2:ℝ) = exp (2 * log x ^ a) := by rw [hy, ← exp_mul, mul_comm]
  have hyh : y ^ (1/2:ℝ) < y := by
    conv_rhs => rw [← rpow_one y]
    exact rpow_lt_rpow_of_exponent_lt hy1 (by norm_num)
  rw [hy2, rpow_one] at hx1
  rw [hy2] at hx2
  unfold groupReciprocalSum
  constructor
  · refine hx1.le.trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity))
    intro p hp
    unfold primeGroup
    simp only [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1, hp.2.2.le⟩
  · refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)) hx2.le
    intro p hp
    unfold primeGroup at hp
    simp only [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1, hyh.trans_le hp.2.2⟩

lemma group_large {a : ℝ} (ha : 0 < a) : ∀ᶠ x in atTop, ∀ p ∈ primeGroup x a, (15:ℝ) ≤ p := by
  filter_upwards [(tendsto_Y ha).eventually_ge_atTop 15] with x hx p hp
  exact hx.trans (mem_primeGroup.1 hp).2.1

lemma group_disj {a b : ℝ} (hab : a < b) :
    ∀ᶠ x in atTop, Disjoint (primeGroup x a) (primeGroup x b) := by
  have h := ((tendsto_rpow_atTop (sub_pos.2 hab)).comp tendsto_log_atTop).eventually_gt_atTop 2
  filter_upwards [h, eventually_gt_atTop 1] with x hx hx1
  simp only [Function.comp_apply] at hx
  have hL : 0 < log x := log_pos hx1
  have hlt : 2 * log x ^ a < log x ^ b := by
    have : log x ^ b = log x ^ a * log x ^ (b - a) := by
      rw [← rpow_add hL]; ring_nf
    rw [this]
    have := rpow_pos_of_pos hL a
    nlinarith
  rw [Finset.disjoint_left]
  intro p hpa hpb
  have h1 := (mem_primeGroup.1 hpa).2.2
  have h2 := (mem_primeGroup.1 hpb).2.1
  have := exp_lt_exp.2 hlt
  linarith

/-! ## Main algebra -/

lemma zpow_sum' {ι : Type*} (s : Finset ι) {q : ℝ} (hq : q ≠ 0) (e : ι → ℤ) :
    q ^ (∑ i ∈ s, e i) = ∏ i ∈ s, q ^ (e i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, zpow_add₀ hq, ih]

/-- The per-group factor of the mark. -/
noncomputable def psi (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (i : Fin K) (U : Finset ℕ) : ℝ :=
  (U.card : ℝ) * (1 / 2 : ℝ) ^ ((U.card : ℤ) - 1) / groupReciprocalSum x (a i)

/-- The mark as a function of the set of prime factors. -/
noncomputable def Fm (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (T : Finset ℕ) : ℝ :=
  ∏ i, psi x a i ((primeGroup x (a i)).filter (· ∈ T))

lemma mark_eq (x : ℝ) {K : ℕ} (a : Fin K → ℝ) {r : ℕ} (hr : 0 < r) :
    mark (1 / 2) x a r = Fm x a r.primeFactors := by
  have hfil : ∀ i, (primeGroup x (a i)).filter (· ∣ r) = (primeGroup x (a i)).filter (· ∈ r.primeFactors) := by
    intro i
    apply Finset.filter_congr
    intro p hp
    rw [Nat.mem_primeFactors]
    exact ⟨fun h => ⟨(mem_primeGroup.1 hp).1, h, hr.ne'⟩, fun h => h.2.1⟩
  unfold mark markOmega groupOmega Fm psi
  simp_rw [hfil]
  have hK : ((∑ i : Fin K, ((primeGroup x (a i)).filter (· ∈ r.primeFactors)).card : ℕ) : ℤ) - (K : ℤ)
      = ∑ i : Fin K, (((((primeGroup x (a i)).filter (· ∈ r.primeFactors)).card : ℕ) : ℤ) - 1) := by
    rw [Finset.sum_sub_distrib]; simp
  rw [hK, zpow_sum' _ (by norm_num), ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  ring

lemma harmonic_hasSum (x : ℝ) {K : ℕ} (a : Fin K → ℝ) {σ : ℝ} (hσ : 0 < σ) :
    HasSum (fun r : ℕ => if 0 < r ∧ r.primeFactors ⊆ groupPrimes x a then
        mark (1 / 2) x a r * ((r : ℝ) ^ σ)⁻¹ else 0)
      (∑ T ∈ (groupPrimes x a).powerset, Fm x a T * ∏ p ∈ T, ((p : ℝ) ^ σ - 1)⁻¹) := by
  have hS : ∀ p ∈ groupPrimes x a, p.Prime := by
    intro p hp
    unfold groupPrimes at hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨i, _, hi⟩ := hp
    exact (mem_primeGroup.1 hi).1
  have h := core_hasSum _ hS hσ (Fm x a)
  have hfun : (fun r : ℕ => if 0 < r ∧ r.primeFactors ⊆ groupPrimes x a then
        mark (1 / 2) x a r * ((r : ℝ) ^ σ)⁻¹ else 0) =
      (fun r : ℕ => if 0 < r ∧ r.primeFactors ⊆ groupPrimes x a then
        Fm x a r.primeFactors * ((r : ℝ) ^ σ)⁻¹ else 0) := by
    funext r
    split_ifs with hr
    · rw [mark_eq x a hr.1]
    · rfl
  rw [hfun]; exact h

lemma harmonicMass_eq_tsum (x : ℝ) {K : ℕ} (a : Fin K → ℝ) :
    harmonicMass x a = ∑' r : ℕ, (if 0 < r ∧ r.primeFactors ⊆ groupPrimes x a then
        mark (1 / 2) x a r * ((r : ℝ) ^ (1:ℝ))⁻¹ else 0) := by
  unfold harmonicMass
  refine (_root_.tsum_subtype {r : ℕ | IsGroupInteger x a r}
    (fun r : ℕ => mark (1 / 2) x a r / (r : ℝ))).trans ?_
  congr 1
  funext r
  by_cases h : 0 < r ∧ r.primeFactors ⊆ groupPrimes x a
  · rw [Set.indicator_of_mem (show r ∈ {r | IsGroupInteger x a r} from h), if_pos h, rpow_one,
      div_eq_mul_inv]
  · rw [Set.indicator_of_notMem (show r ∉ {r | IsGroupInteger x a r} from h), if_neg h]

lemma groupPrimes_eq (x : ℝ) {K : ℕ} (a : Fin K → ℝ) :
    groupPrimes x a = Finset.univ.biUnion (fun i => primeGroup x (a i)) := rfl

lemma finite_identity (x : ℝ) {K : ℕ} (a : Fin K → ℝ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j))) (w : ℕ → ℝ) :
    ∑ T ∈ (groupPrimes x a).powerset, Fm x a T * ∏ p ∈ T, w p =
      ∏ i, (∑ U ∈ (primeGroup x (a i)).powerset,
        (U.card : ℝ) * (1 / 2 : ℝ) ^ ((U.card : ℤ) - 1) * ∏ p ∈ U, w p) /
          groupReciprocalSum x (a i) := by
  have h := prodsplit (fun i => primeGroup x (a i)) hdisj (fun i U => psi x a i U * ∏ p ∈ U, w p)
  rw [groupPrimes_eq]
  have hl : ∀ T ∈ (Finset.univ.biUnion (fun i => primeGroup x (a i))).powerset,
      Fm x a T * ∏ p ∈ T, w p =
        ∏ i, psi x a i ((primeGroup x (a i)).filter (· ∈ T)) *
          ∏ p ∈ (primeGroup x (a i)).filter (· ∈ T), w p := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    rw [Finset.prod_mul_distrib, Fm]
    congr 1
    have hTe : T = Finset.univ.biUnion (fun i => (primeGroup x (a i)).filter (· ∈ T)) := by
      ext p
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
      constructor
      · intro hp
        have := hT hp
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at this
        obtain ⟨i, hi⟩ := this
        exact ⟨i, hi, hp⟩
      · rintro ⟨i, _, h⟩; exact h
    conv_lhs => rw [hTe]
    rw [Finset.prod_biUnion]
    intro i _ j _ hij
    exact Finset.disjoint_filter_filter (hdisj i j hij)
  rw [Finset.sum_congr rfl hl, h]
  apply Finset.prod_congr rfl
  intro i _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro U _
  unfold psi
  ring

lemma identity1 (x : ℝ) {K : ℕ} (a : Fin K → ℝ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j))) :
    harmonicMass x a = ∏ i, deriv (fun t : ℝ => ∏ p ∈ primeGroup x (a i), (1 + t / ((p : ℝ) - 1))) (1 / 2) /
      groupReciprocalSum x (a i) := by
  rw [harmonicMass_eq_tsum, (harmonic_hasSum x a one_pos).tsum_eq, finite_identity x a hdisj]
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  have hd := hasDerivAt_powerset (primeGroup x (a i)) (fun p => ((p : ℝ) - 1)⁻¹) (q := 1 / 2) (by norm_num)
  simp only [div_eq_mul_inv (_ : ℝ) ((_ : ℝ) - 1)]
  rw [hd.deriv]
  simp only [rpow_one]

lemma deriv_eq (P : Finset ℕ) (hP : ∀ p ∈ P, (2 : ℝ) ≤ p) :
    deriv (fun t : ℝ => ∏ p ∈ P, (1 + t / ((p : ℝ) - 1))) (1 / 2) =
      (∏ p ∈ P, (1 + (1 / 2) / ((p : ℝ) - 1))) * ∑ p ∈ P, 1 / ((p : ℝ) - 1 + 1 / 2) := by
  classical
  have hd := HasDerivAt.fun_finsetProd (u := P) (f := fun p t => 1 + t / ((p : ℝ) - 1))
    (f' := fun p => 1 / ((p : ℝ) - 1)) (x := 1 / 2)
    (fun p _ => by simpa using ((hasDerivAt_id (1 / 2 : ℝ)).div_const ((p : ℝ) - 1)).const_add 1)
  rw [hd.deriv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.mul_prod_erase P _ hp, smul_eq_mul]
  have h1 : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith [hP p hp]
  field_simp

lemma factor_bounds (P : Finset ℕ) (hP : ∀ p ∈ P, (2 : ℝ) ≤ p) (hV : 0 < ∑ p ∈ P, 1 / (p : ℝ)) :
    1 ≤ (∏ p ∈ P, (1 + (1 / 2) / ((p : ℝ) - 1))) * (∑ p ∈ P, 1 / ((p : ℝ) - 1 + 1 / 2)) /
        ∑ p ∈ P, 1 / (p : ℝ) ∧
      (∏ p ∈ P, (1 + (1 / 2) / ((p : ℝ) - 1))) * (∑ p ∈ P, 1 / ((p : ℝ) - 1 + 1 / 2)) /
        ∑ p ∈ P, 1 / (p : ℝ) ≤ 2 * exp (∑ p ∈ P, 1 / (p : ℝ)) := by
  have hE1 : 1 ≤ ∏ p ∈ P, (1 + (1 / 2) / ((p : ℝ) - 1)) := by
    have := Finset.prod_le_prod (s := P) (f := fun _ => (1 : ℝ))
      (g := fun p : ℕ => 1 + (1 / 2) / ((p : ℝ) - 1)) (fun _ _ => zero_le_one)
      (fun p hp => by
        have := hP p hp
        have : (0:ℝ) < (p:ℝ) - 1 := by linarith
        have : 0 ≤ (1/2) / ((p:ℝ) - 1) := by positivity
        show (1:ℝ) ≤ _
        linarith)
    simpa using this
  have hE2 : ∏ p ∈ P, (1 + (1 / 2) / ((p : ℝ) - 1)) ≤ exp (∑ p ∈ P, 1 / (p : ℝ)) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp; have := hP p hp; have : (0:ℝ) < (p:ℝ) - 1 := by linarith
      positivity
    · intro p hp
      have h2 := hP p hp
      have h3 : (1 / 2) / ((p : ℝ) - 1) ≤ 1 / p := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith
      have := add_one_le_exp (1 / (p : ℝ))
      linarith
  have hS1 : ∑ p ∈ P, 1 / (p : ℝ) ≤ ∑ p ∈ P, 1 / ((p : ℝ) - 1 + 1 / 2) := by
    apply Finset.sum_le_sum
    intro p hp; have := hP p hp
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hS2 : ∑ p ∈ P, 1 / ((p : ℝ) - 1 + 1 / 2) ≤ 2 * ∑ p ∈ P, 1 / (p : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp; have := hP p hp
    rw [mul_one_div, div_le_div_iff₀ (by linarith) (by linarith)]; linarith
  have hEpos : 0 ≤ ∏ p ∈ P, (1 + (1 / 2) / ((p : ℝ) - 1)) := by linarith
  constructor
  · rw [le_div_iff₀ hV, one_mul]
    nlinarith
  · rw [div_le_iff₀ hV]
    have := exp_pos (∑ p ∈ P, 1 / (p : ℝ))
    nlinarith

lemma mark_nonneg (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (hV : ∀ i, 0 ≤ groupReciprocalSum x (a i)) (r : ℕ) :
    0 ≤ mark (1 / 2) x a r := by
  unfold mark
  apply mul_nonneg (by positivity)
  apply Finset.prod_nonneg
  intro i _
  exact div_nonneg (Nat.cast_nonneg _) (hV i)

lemma half_pow_le (n : ℕ) : (n : ℝ) * (1 / 2 : ℝ) ^ ((n : ℤ) - 1) ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by push_cast; ring
    rw [this, zpow_natCast, one_div_pow]
    have hm : ((m : ℝ) + 1) ≤ 2 ^ m := by
      have := Nat.lt_two_pow_self (n := m)
      exact_mod_cast this
    rw [← div_eq_mul_one_div, div_le_one (by positivity)]
    push_cast; linarith

lemma Fm_bounds (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (hV : ∀ i, 1 / 4 ≤ groupReciprocalSum x (a i))
    (T : Finset ℕ) : 0 ≤ Fm x a T ∧ Fm x a T ≤ 4 ^ K := by
  have hpsi : ∀ i U, 0 ≤ psi x a i U ∧ psi x a i U ≤ 4 := by
    intro i U
    have hVi := hV i
    have hVp : 0 < groupReciprocalSum x (a i) := by linarith
    unfold psi
    constructor
    · positivity
    · rw [div_le_iff₀ hVp]
      have := half_pow_le U.card
      nlinarith
  unfold Fm
  constructor
  · exact Finset.prod_nonneg fun i _ => (hpsi i _).1
  · have := Finset.prod_le_prod (s := Finset.univ) (fun i _ => (hpsi i _).1) (fun i _ => (hpsi i
      ((primeGroup x (a i)).filter (· ∈ T))).2)
    simpa using this

lemma exp_two_lt : exp (2 : ℝ) < 7.4 := by
  have h := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  have : exp (2 : ℝ) = exp 1 * exp 1 := by rw [← exp_add]; norm_num
  rw [this]; nlinarith

lemma g_bound {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {iK : Fin K} (hmax : ∀ i, a i ≤ a iK)
    (hL : 1 < log x) (h15 : ∀ i, ∀ p ∈ primeGroup x (a i), (15 : ℝ) ≤ p)
    {p : ℕ} (hp : p ∈ groupPrimes x a) :
    0 ≤ ((p : ℝ) ^ (1 - (log x ^ a iK)⁻¹) - 1)⁻¹ ∧
      ((p : ℝ) ^ (1 - (log x ^ a iK)⁻¹) - 1)⁻¹ ≤ 2 * exp 2 / p := by
  rw [groupPrimes_eq, Finset.mem_biUnion] at hp
  obtain ⟨i, _, hi⟩ := hp
  have hp15 := h15 i p hi
  have hpos : (0 : ℝ) < p := by linarith
  have hup := (mem_primeGroup.1 hi).2.2
  have hLpos : 0 < log x := by linarith
  have hLa : 0 < log x ^ a iK := rpow_pos_of_pos hLpos _
  have hlogp : log p ≤ 2 * log x ^ a iK := by
    have h1 : log p ≤ 2 * log x ^ a i := (Real.log_le_iff_le_exp hpos).2 hup
    have h2 : log x ^ a i ≤ log x ^ a iK := rpow_le_rpow_of_exponent_le hL.le (hmax i)
    linarith
  set s := (log x ^ a iK)⁻¹ with hs
  have hps : (p : ℝ) ^ s ≤ exp 2 := by
    rw [rpow_def_of_pos hpos]
    apply exp_le_exp.2
    rw [hs, ← div_eq_mul_inv, div_le_iff₀ hLa]
    exact hlogp
  have hps0 : 0 < (p : ℝ) ^ s := rpow_pos_of_pos hpos s
  have hσ : (p : ℝ) ^ (1 - s) = p / p ^ s := by rw [rpow_sub hpos, rpow_one]
  have he := exp_two_lt
  have he0 := exp_pos (2 : ℝ)
  have hlow : p / (2 * exp 2) ≤ (p : ℝ) ^ (1 - s) - 1 := by
    rw [hσ]
    have : p / exp 2 ≤ p / p ^ s := div_le_div_of_nonneg_left hpos.le hps0 hps
    have : p / (2 * exp 2) = p / exp 2 - p / (2 * exp 2) := by field_simp; ring
    have : 1 ≤ p / (2 * exp 2) := by rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  have hlp : 0 < p / (2 * exp 2) := by positivity
  constructor
  · exact inv_nonneg.2 (hlp.le.trans hlow)
  · calc ((p : ℝ) ^ (1 - s) - 1)⁻¹ ≤ (p / (2 * exp 2))⁻¹ := inv_anti₀ hlp hlow
      _ = 2 * exp 2 / p := by rw [inv_div]

lemma Hv_bound {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {iK : Fin K} (hmax : ∀ i, a i ≤ a iK)
    (hL : 1 < log x)
    (hdisj : ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)))
    (hV : ∀ i, 1 / 4 ≤ groupReciprocalSum x (a i) ∧ groupReciprocalSum x (a i) ≤ 3)
    (h15 : ∀ i, ∀ p ∈ primeGroup x (a i), (15 : ℝ) ≤ p) :
    ∑ T ∈ (groupPrimes x a).powerset,
        Fm x a T * ∏ p ∈ T, ((p : ℝ) ^ (1 - (log x ^ a iK)⁻¹) - 1)⁻¹ ≤
      4 ^ K * exp (2 * exp 2 * (3 * K)) := by
  set c := 2 * exp 2 with hc
  have hc0 : 0 ≤ c := by positivity
  calc ∑ T ∈ (groupPrimes x a).powerset,
        Fm x a T * ∏ p ∈ T, ((p : ℝ) ^ (1 - (log x ^ a iK)⁻¹) - 1)⁻¹
      ≤ ∑ T ∈ (groupPrimes x a).powerset, 4 ^ K * ∏ p ∈ T, (c / p) := by
        apply Finset.sum_le_sum
        intro T hT
        have hTS := Finset.mem_powerset.1 hT
        have hF := Fm_bounds x a (fun i => (hV i).1) T
        apply mul_le_mul hF.2 _ (Finset.prod_nonneg fun p hp => (g_bound hmax hL h15 (hTS hp)).1)
          (by positivity)
        exact Finset.prod_le_prod (fun p hp => (g_bound hmax hL h15 (hTS hp)).1)
          (fun p hp => (g_bound hmax hL h15 (hTS hp)).2)
    _ = 4 ^ K * ∏ p ∈ groupPrimes x a, (1 + c / p) := by
        rw [← Finset.mul_sum, Finset.prod_one_add]
    _ ≤ 4 ^ K * exp (∑ p ∈ groupPrimes x a, c / p) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [Real.exp_sum]
        apply Finset.prod_le_prod
        · intro p _; positivity
        · intro p _; have := add_one_le_exp (c / p); linarith
    _ ≤ 4 ^ K * exp (2 * exp 2 * (3 * K)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply exp_le_exp.2
        simp_rw [div_eq_mul_one_div c]
        rw [← Finset.mul_sum, ← hc, groupPrimes_eq, Finset.sum_biUnion (fun i _ j _ hij => hdisj i j hij)]
        apply mul_le_mul_of_nonneg_left _ hc0
        have : ∀ i, ∑ p ∈ primeGroup x (a i), 1 / (p : ℝ) ≤ 3 := fun i => (hV i).2
        calc ∑ i, ∑ p ∈ primeGroup x (a i), 1 / (p : ℝ) ≤ ∑ _i : Fin K, (3 : ℝ) :=
              Finset.sum_le_sum fun i _ => this i
          _ = 3 * K := by simp; ring

lemma tail_bound {x ε : ℝ} {K : ℕ} {a : Fin K → ℝ} {iK : Fin K} (hmax : ∀ i, a i ≤ a iK)
    (hapos : 0 < a iK) (hε : 0 < ε) (hx : 0 < x) (hL : 1 < log x)
    (hdisj : ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)))
    (hV : ∀ i, 1 / 4 ≤ groupReciprocalSum x (a i) ∧ groupReciprocalSum x (a i) ≤ 3)
    (h15 : ∀ i, ∀ p ∈ primeGroup x (a i), (15 : ℝ) ≤ p) :
    Summable (fun r : {r : ℕ // IsGroupInteger x a r ∧ x ^ ε < r} => mark (1 / 2) x a r / (r : ℝ)) ∧
    ∑' r : {r : ℕ // IsGroupInteger x a r ∧ x ^ ε < r}, mark (1 / 2) x a r / (r : ℝ) ≤
      4 ^ K * exp (2 * exp 2 * (3 * K)) * exp (-ε * log x ^ (1 - a iK)) := by
  have hLpos : 0 < log x := by linarith
  have hLa : 1 < log x ^ a iK := one_lt_rpow hL hapos
  set s := (log x ^ a iK)⁻¹ with hs
  have hs0 : 0 < s := inv_pos.2 (by linarith)
  have hs1 : s < 1 := inv_lt_one_of_one_lt₀ hLa
  have hσ : 0 < 1 - s := by linarith
  have hH := harmonic_hasSum x a hσ
  have hVnn : ∀ i, 0 ≤ groupReciprocalSum x (a i) := fun i => by linarith [(hV i).1]
  set E := exp (-ε * log x ^ (1 - a iK)) with hE
  have hHnn : ∀ r : ℕ, 0 ≤ (if 0 < r ∧ r.primeFactors ⊆ groupPrimes x a then
        mark (1 / 2) x a r * ((r : ℝ) ^ (1 - s))⁻¹ else 0) := by
    intro r
    split_ifs
    · exact mul_nonneg (mark_nonneg x a hVnn r) (by positivity)
    · exact le_rfl
  have hpt : ∀ r : {r : ℕ // IsGroupInteger x a r ∧ x ^ ε < r},
      mark (1 / 2) x a r / (r : ℝ) ≤ E * (if 0 < r.1 ∧ r.1.primeFactors ⊆ groupPrimes x a then
        mark (1 / 2) x a r.1 * ((r.1 : ℝ) ^ (1 - s))⁻¹ else 0) := by
    rintro ⟨r, ⟨hr0, hrS⟩, hxr⟩
    simp only
    rw [if_pos ⟨hr0, hrS⟩]
    have hrpos : (0 : ℝ) < r := by exact_mod_cast hr0
    have hsplit : (r : ℝ)⁻¹ = ((r : ℝ) ^ (1 - s))⁻¹ * ((r : ℝ) ^ s)⁻¹ := by
      rw [← mul_inv, ← rpow_add hrpos]; simp
    have hxe : 0 < x ^ ε := rpow_pos_of_pos hx ε
    have h1 : (x ^ ε) ^ s < (r : ℝ) ^ s := rpow_lt_rpow hxe.le hxr hs0
    have h2 : (x ^ ε) ^ s = exp (ε * log x ^ (1 - a iK)) := by
      rw [← rpow_mul hx.le, rpow_def_of_pos hx, rpow_sub hLpos, rpow_one, hs]
      congr 1
      field_simp
    have hE' : ((r : ℝ) ^ s)⁻¹ ≤ E := by
      rw [hE, neg_mul, exp_neg, ← h2]
      exact inv_anti₀ (by positivity) h1.le
    rw [div_eq_mul_inv, hsplit]
    have hm := mark_nonneg x a hVnn r
    have : 0 ≤ ((r : ℝ) ^ (1 - s))⁻¹ := by positivity
    calc mark (1 / 2) x a r * (((r : ℝ) ^ (1 - s))⁻¹ * ((r : ℝ) ^ s)⁻¹)
        = ((r : ℝ) ^ s)⁻¹ * (mark (1 / 2) x a r * ((r : ℝ) ^ (1 - s))⁻¹) := by ring
      _ ≤ E * (mark (1 / 2) x a r * ((r : ℝ) ^ (1 - s))⁻¹) :=
        mul_le_mul_of_nonneg_right hE' (mul_nonneg hm this)
  have hg := (hH.summable.comp_injective (Subtype.val_injective
    (p := fun r : ℕ => IsGroupInteger x a r ∧ x ^ ε < r))).mul_left E
  have hfnn : ∀ r : {r : ℕ // IsGroupInteger x a r ∧ x ^ ε < r}, 0 ≤ mark (1 / 2) x a r / (r : ℝ) :=
    fun r => div_nonneg (mark_nonneg x a hVnn r) (Nat.cast_nonneg _)
  have hf := Summable.of_nonneg_of_le hfnn hpt hg
  refine ⟨hf, ?_⟩
  calc ∑' r : {r : ℕ // IsGroupInteger x a r ∧ x ^ ε < r}, mark (1 / 2) x a r / (r : ℝ)
      ≤ ∑' r : {r : ℕ // IsGroupInteger x a r ∧ x ^ ε < r},
          E * (if 0 < r.1 ∧ r.1.primeFactors ⊆ groupPrimes x a then
            mark (1 / 2) x a r.1 * ((r.1 : ℝ) ^ (1 - s))⁻¹ else 0) := hf.tsum_le_tsum hpt hg
    _ = E * ∑' r : {r : ℕ // IsGroupInteger x a r ∧ x ^ ε < r},
          (if 0 < r.1 ∧ r.1.primeFactors ⊆ groupPrimes x a then
            mark (1 / 2) x a r.1 * ((r.1 : ℝ) ^ (1 - s))⁻¹ else 0) := tsum_mul_left
    _ ≤ E * ∑' r : ℕ, (if 0 < r ∧ r.primeFactors ⊆ groupPrimes x a then
            mark (1 / 2) x a r * ((r : ℝ) ^ (1 - s))⁻¹ else 0) :=
        mul_le_mul_of_nonneg_left (tsum_comp_le_tsum_of_inj hH.summable hHnn Subtype.val_injective)
          (exp_pos _).le
    _ ≤ E * (4 ^ K * exp (2 * exp 2 * (3 * K))) := by
        rw [hH.tsum_eq]
        exact mul_le_mul_of_nonneg_left (Hv_bound hmax hL hdisj hV h15) (exp_pos _).le
    _ = 4 ^ K * exp (2 * exp 2 * (3 * K)) * E := by ring

lemma predMass_bounds (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (hΨ1 : ∀ y, Ψ y ≤ 1) {x : ℝ} (hx : 0 < x) (hc : 1 ≤ c) {r : ℕ}
    (hr : 0 < r) :
    0 ≤ predecessorMass M c u Ψ x r ∧ predecessorMass M c u Ψ x r ≤ 2 * x / r := by
  unfold predecessorMass predecessorMassDvd
  set N := ⌈2 * x / r⌉₊ with hN
  let g : ℕ → ℝ := fun Q => if Q ∈ Finset.Ico 1 N then 1 else 0
  have hg : Summable g := summable_of_ne_finset_zero (s := Finset.Ico 1 N) (fun b hb => if_neg hb)
  have hgnn : ∀ Q, 0 ≤ g Q := fun Q => by simp only [g]; split_ifs <;> norm_num
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hpt : ∀ Q : {Q : ℕ // Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧
      ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M] ∧ 1 ∣ c * r * Q + 1},
      Ψ (((c * r * Q.1 + 1 : ℕ) : ℝ) / x) ≤ g Q.1 := by
    intro Q
    by_cases h0 : Ψ (((c * r * Q.1 + 1 : ℕ) : ℝ) / x) = 0
    · rw [h0]; exact hgnn _
    have hmem := hΨs (subset_tsupport _ h0)
    have hQ1 : 1 ≤ Q.1 := Q.2.1.one_lt.le
    have h2 := hmem.2
    rw [div_lt_iff₀ hx] at h2
    push_cast at h2
    have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
    have hlt : (Q.1 : ℝ) < 2 * x / r := by
      rw [lt_div_iff₀ hrpos]
      have := mul_nonneg (mul_nonneg (sub_nonneg.2 hc') hrpos.le) (Nat.cast_nonneg (α := ℝ) Q.1)
      nlinarith
    have hQN : Q.1 < N := Nat.lt_ceil.2 hlt
    have : Q.1 ∈ Finset.Ico 1 N := Finset.mem_Ico.2 ⟨hQ1, hQN⟩
    simp only [g, if_pos this]
    exact hΨ1 _
  have hg' := hg.comp_injective (Subtype.val_injective (p := fun Q : ℕ => Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧
      ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M] ∧ 1 ∣ c * r * Q + 1))
  have hf := Summable.of_nonneg_of_le (fun Q => hΨ0 _) hpt hg'
  refine ⟨tsum_nonneg fun Q => hΨ0 _, ?_⟩
  refine (hf.tsum_le_tsum hpt hg').trans ((tsum_comp_le_tsum_of_inj hg hgnn Subtype.val_injective).trans ?_)
  rw [tsum_eq_sum (s := Finset.Ico 1 N) (fun b hb => if_neg hb)]
  have : ∑ b ∈ Finset.Ico 1 N, g b = ∑ b ∈ Finset.Ico 1 N, (1 : ℝ) :=
    Finset.sum_congr rfl fun b hb => if_pos hb
  rw [this, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
  have hNlt : (N : ℝ) < 2 * x / r + 1 := Nat.ceil_lt_add_one (by positivity)
  rcases Nat.eq_zero_or_pos N with h | h
  · rw [h]; simp; positivity
  · rw [Nat.cast_sub h]; push_cast; linarith


end HarmonicMassSol

end ArtinPrimitiveRoots

open ArtinPrimitiveRoots ArtinPrimitiveRoots.HarmonicMassSol Real Finset Filter Topology in

theorem solution (M c : ℕ) (u : ℤ) (hM : 0 < M) (h8 : 8 ∣ M) (hc : c = 2 ∨ c = 4)
    (hu : IsCoprime u M) (hcu : (c : ℤ) ∣ u - 1) (hcop : IsCoprime ((u - 1) / c) ((M : ℤ) / c))
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (hΨ1 : ∀ y, Ψ y ≤ 1) (hΨi : 0 < ∫ y, Ψ y) (K : ℕ) (hK : 1 ≤ K) :
    ∃ C : ℝ, ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∀ ε : ℝ, 0 < ε → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
        harmonicMass x a =
          ∏ i, deriv (fun t : ℝ => ∏ p ∈ primeGroup x (a i), (1 + t / ((p : ℝ) - 1))) (1 / 2) /
            groupReciprocalSum x (a i) ∧
        harmonicMass x a =
          ∏ i, ((∏ p ∈ primeGroup x (a i), (1 + (1 / 2) / ((p : ℝ) - 1))) /
              groupReciprocalSum x (a i) *
            ∑ p ∈ primeGroup x (a i), 1 / ((p : ℝ) - 1 + 1 / 2)) ∧
        1 ≤ harmonicMass x a ∧ harmonicMass x a ≤ C ∧
        ∑' r : {r : ℕ // IsGroupInteger x a r ∧ x ^ ε < r}, mark (1 / 2) x a r / (r : ℝ) ≤
          C * exp (-ε * log x ^ (1 - a ⟨K - 1, by omega⟩)) ∧
        ∑' r : {r : ℕ // IsGroupInteger x a r ∧ x ^ ε < r},
            mark (1 / 2) x a r * predecessorMass M c u Ψ x r ≤
          C * (x * exp (-ε * log x ^ (1 - a ⟨K - 1, by omega⟩))) := by
  set C2 : ℝ := 4 ^ K * exp (2 * exp 2 * (3 * K)) with hC2
  set C1 : ℝ := (2 * exp 3) ^ K with hC1
  have hC2nn : 0 ≤ C2 := by positivity
  have hC1nn : 0 ≤ C1 := by positivity
  refine ⟨C1 + 2 * C2, ?_⟩
  intro a ha hrange ε hε
  set iK : Fin K := ⟨K - 1, by omega⟩ with hiK
  have hmax : ∀ i, a i ≤ a iK := fun i => ha.monotone (by rw [Fin.le_def]; simp [iK]; omega)
  have hapos : ∀ i, 0 < a i := fun i => by linarith [(hrange i).1]
  have hev : ∀ᶠ x in atTop, 0 < x ∧ 1 < log x ∧
      (∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j))) ∧
      (∀ i, 1 / 4 ≤ groupReciprocalSum x (a i) ∧ groupReciprocalSum x (a i) ≤ 3) ∧
      (∀ i, ∀ p ∈ primeGroup x (a i), (15 : ℝ) ≤ p) := by
    have hdisj : ∀ᶠ x in atTop, ∀ i j, i < j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)) := by
      rw [eventually_all]; intro i; rw [eventually_all]; intro j
      by_cases hij : i < j
      · filter_upwards [group_disj (ha hij)] with x hx _ using hx
      · exact Eventually.of_forall fun x h => absurd h hij
    filter_upwards [eventually_gt_atTop 0, tendsto_log_atTop.eventually_gt_atTop 1, hdisj,
      eventually_all.2 (fun i => V_bounds (hapos i)),
      eventually_all.2 (fun i => group_large (hapos i))] with x h1 h2 h3 h4 h5
    refine ⟨h1, h2, ?_, h4, h5⟩
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact h3 i j h
    · exact (h3 j i h).symm
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 hev
  refine ⟨x₀, fun x hx => ?_⟩
  obtain ⟨hx0, hL, hdisj, hV, h15⟩ := hx₀ x hx
  have hP2 : ∀ i, ∀ p ∈ primeGroup x (a i), (2 : ℝ) ≤ p := fun i p hp => by
    exact_mod_cast (mem_primeGroup.1 hp).1.two_le
  have hVpos : ∀ i, 0 < groupReciprocalSum x (a i) := fun i => by linarith [(hV i).1]
  have hid1 := identity1 x a hdisj
  have hid3 : harmonicMass x a = ∏ i, (∏ p ∈ primeGroup x (a i), (1 + (1 / 2) / ((p : ℝ) - 1))) *
      (∑ p ∈ primeGroup x (a i), 1 / ((p : ℝ) - 1 + 1 / 2)) / groupReciprocalSum x (a i) := by
    rw [hid1]
    apply Finset.prod_congr rfl
    intro i _
    rw [deriv_eq _ (hP2 i)]
  have hfb := fun i => factor_bounds (primeGroup x (a i)) (hP2 i) (hVpos i)
  have hVnn : ∀ i, 0 ≤ groupReciprocalSum x (a i) := fun i => (hVpos i).le
  obtain ⟨htsum, htail⟩ := tail_bound (ε := ε) hmax (hapos iK) hε hx0 hL hdisj hV h15
  set E := exp (-ε * log x ^ (1 - a iK)) with hE
  have hEpos : 0 < E := exp_pos _
  refine ⟨hid1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hid3]
    apply Finset.prod_congr rfl
    intro i _
    ring
  · rw [hid3]
    unfold groupReciprocalSum
    have := Finset.prod_le_prod (s := Finset.univ) (f := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)
      (fun i _ => (hfb i).1)
    simpa using this
  · rw [hid3]
    have := Finset.prod_le_prod (s := Finset.univ) (fun i _ => zero_le_one.trans (hfb i).1)
      (fun i _ => (hfb i).2.trans (by
        have := exp_le_exp.2 (hV i).2
        show 2 * exp (groupReciprocalSum x (a i)) ≤ 2 * exp 3
        linarith))
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    unfold groupReciprocalSum
    linarith
  · calc _ ≤ C2 * E := htail
      _ ≤ (C1 + 2 * C2) * E := mul_le_mul_of_nonneg_right (by linarith) hEpos.le
  · have hc1 : 1 ≤ c := by rcases hc with h | h <;> omega
    have hpt : ∀ r : {r : ℕ // IsGroupInteger x a r ∧ x ^ ε < r},
        mark (1 / 2) x a r * predecessorMass M c u Ψ x r ≤ (2 * x) * (mark (1 / 2) x a r / (r : ℝ)) := by
      intro r
      have hb := predMass_bounds M c u Ψ hΨs hΨ0 hΨ1 hx0 hc1 r.2.1.1
      have hm := mark_nonneg x a hVnn r
      calc mark (1 / 2) x a r * predecessorMass M c u Ψ x r ≤ mark (1 / 2) x a r * (2 * x / r) :=
            mul_le_mul_of_nonneg_left hb.2 hm
        _ = (2 * x) * (mark (1 / 2) x a r / (r : ℝ)) := by ring
    have hnn : ∀ r : {r : ℕ // IsGroupInteger x a r ∧ x ^ ε < r},
        0 ≤ mark (1 / 2) x a r * predecessorMass M c u Ψ x r := fun r =>
      mul_nonneg (mark_nonneg x a hVnn r) (predMass_bounds M c u Ψ hΨs hΨ0 hΨ1 hx0 hc1 r.2.1.1).1
    have hg := htsum.mul_left (2 * x)
    have hf := Summable.of_nonneg_of_le hnn hpt hg
    calc _ ≤ ∑' r : {r : ℕ // IsGroupInteger x a r ∧ x ^ ε < r},
            (2 * x) * (mark (1 / 2) x a r / (r : ℝ)) := hf.tsum_le_tsum hpt hg
      _ = (2 * x) * ∑' r : {r : ℕ // IsGroupInteger x a r ∧ x ^ ε < r},
            mark (1 / 2) x a r / (r : ℝ) := tsum_mul_left
      _ ≤ (2 * x) * (C2 * E) := mul_le_mul_of_nonneg_left htail (by linarith)
      _ ≤ (C1 + 2 * C2) * (x * E) := by nlinarith [mul_pos hx0 hEpos]


