-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FiniteTorsOfFiniteTorsion
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FiniteTorsOfFiniteTorsion
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T23:19:54.150828+00:00
-- url     : https://prove2.me/theorems/efa871d5-08f1-49a6-bc51-73c26fb1ac26
-- title:
--   Finite Tors Of Finite Torsion
-- statement:
--   Definitions and structural lemmas for Finite Tors Of Finite Torsion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FiniteTorsOfFiniteTorsion.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_FormalChartAtZero
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_FormalGroupTorsionCharts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvBasicNEvalSubCoeffMem
import Theorems.Thm_GlobalTheory_evBasic_exists_pow
import Theorems.Thm_GlobalTheory_evBasic_map_tEval
import Theorems.Thm_GlobalTheory_evBasic_nEval_eq_tEval
import Theorems.Thm_GlobalTheory_evBasic_nEval_sub_coeff_mem
import Theorems.Thm_GlobalTheory_evBasic_tEval_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing TensorProduct ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Be2 GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts
namespace GlobalTheory.ChartCompare
variable {R₀ : Type} [CommRing R₀]
section Eval
open MvPowerSeries
variable {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  {S : Type} [CommRing S] [Algebra R₀ S]
theorem nEval_eq_evalNil (f : MvPowerSeries σ R₀) (a : σ → S) (ha : ∀ i, IsNilpotent (a i)) :
    nEval f a = evalNil f a ha := by
  obtain ⟨N, -, hN⟩ := evBasic_exists_pow a ha
  have ht : ∀ e : σ → ℕ, evalTerm f a (Finsupp.equivFunOnFinite.symm e) =
      algebraMap R₀ S (coeff (Finsupp.equivFunOnFinite.symm e) f) * ∏ i, a i ^ e i := fun e => by
    unfold evalTerm
    rw [Finsupp.prod_fintype _ _ (by simp), Algebra.smul_def]
    rfl
  rw [evBasic_nEval_eq_tEval f a N hN, evBasic_tEval_eq_sum, evalNil_eq_finsum,
    ← finsum_comp_equiv (Finsupp.equivFunOnFinite (α := σ) (M := ℕ)).symm,
    finsum_eq_sum_of_support_subset (s := Fintype.piFinset fun _ : σ => Finset.range N)]
  · exact Finset.sum_congr rfl fun e _ => (ht e).symm
  · intro e he
    by_contra hc
    apply he
    rw [Finset.mem_coe, Fintype.mem_piFinset] at hc
    push Not at hc
    obtain ⟨i, hi⟩ := hc
    have hi' : N ≤ e i := by simpa using hi
    show evalTerm f a _ = 0
    rw [ht, Finset.prod_eq_zero (f := fun i => a i ^ e i) (Finset.mem_univ i)
      (pow_eq_zero_of_le hi' (hN i)), mul_zero]
open IsLocalRing TensorProduct in
variable {R₀ : Type} [CommRing R₀] in
open MvPowerSeries in
variable {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  {S : Type} [CommRing S] [Algebra R₀ S] in
theorem _root_.GlobalTheory.ChartCompare.hasSubst_C (a : σ → S) (ha : ∀ i, IsNilpotent (a i)) :
    HasSubst (fun i => (C (a i) : MvPowerSeries Empty S)) :=
  hasSubst_of_constantCoeff_nilpotent fun i => by simpa using ha i
open IsLocalRing TensorProduct in
variable {R₀ : Type} [CommRing R₀] in
open MvPowerSeries in
variable {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  {S : Type} [CommRing S] [Algebra R₀ S] in
theorem nilpotent_eval_eq_finsum (f : MvPowerSeries σ R₀) (a : σ → S)
    (ha : ∀ i, IsNilpotent (a i)) : _root_.ReciprocityTheory.PGsh.Be2.nEval f a = ∑ᶠ d, _root_.GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts.evalTerm f a d := by
  obtain ⟨N, -, hN⟩ := _root_.GlobalTheory.evBasic_exists_pow a ha
  rw [_root_.GlobalTheory.evBasic_nEval_eq_tEval f a N hN, _root_.GlobalTheory.evBasic_tEval_eq_sum]
  have hsupp : Function.support (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts.evalTerm f a) ⊆
      (((Fintype.piFinset fun _ : σ => Finset.range N).map
        Finsupp.equivFunOnFinite.symm.toEmbedding : Finset (σ →₀ ℕ)) : Set (σ →₀ ℕ)) := by
    intro d hd
    rw [Finset.mem_coe, Finset.mem_map_equiv, Fintype.mem_piFinset]
    intro i
    simp only [Equiv.symm_symm, Finsupp.equivFunOnFinite_apply, Finset.mem_range]
    by_contra hi
    apply hd
    rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts.evalTerm, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Finset.prod_eq_zero (f := fun k => a k ^ d k) (Finset.mem_univ i)
        (pow_eq_zero_of_le (not_lt.mp hi) (hN i)),
      smul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_map]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts.evalTerm, Algebra.smul_def, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp
open IsLocalRing TensorProduct in
variable {R₀ : Type} [CommRing R₀] in
open MvPowerSeries in
variable {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  {S : Type} [CommRing S] [Algebra R₀ S] in
theorem _root_.GlobalTheory.ChartCompare.subst_C_eq (f : MvPowerSeries σ R₀) (a : σ → S)
    (ha : ∀ i, IsNilpotent (a i)) :
    subst (fun i => (C (a i) : MvPowerSeries Empty S)) f = C (_root_.ReciprocityTheory.PGsh.Be2.nEval f a) := by
  ext e
  obtain rfl : e = 0 := Subsingleton.elim _ _
  rw [coeff_subst (_root_.GlobalTheory.ChartCompare.hasSubst_C a ha), nilpotent_eval_eq_finsum f a ha,
    coeff_zero_C]
  refine finsum_congr fun d => ?_
  have hC : (d.prod fun s n => (C (a s) : MvPowerSeries Empty S) ^ n) =
      C (d.prod fun s n => a s ^ n) := by
    simp [map_finsuppProd]
  rw [hC, coeff_zero_C, _root_.GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts.evalTerm]
open IsLocalRing TensorProduct in
variable {R₀ : Type} [CommRing R₀] in
open MvPowerSeries in
variable {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  {S : Type} [CommRing S] [Algebra R₀ S] in
theorem _root_.GlobalTheory.ChartCompare.nEval_X (a : σ → S) (ha : ∀ i, IsNilpotent (a i)) (s : σ) :
    _root_.ReciprocityTheory.PGsh.Be2.nEval (X s : MvPowerSeries σ R₀) a = a s := by
  have h := congrArg (coeff 0) (_root_.GlobalTheory.ChartCompare.subst_C_eq (X s : MvPowerSeries σ R₀) a ha)
  rw [subst_X (_root_.GlobalTheory.ChartCompare.hasSubst_C a ha), coeff_zero_C, coeff_zero_C] at h
  exact h.symm
open IsLocalRing TensorProduct in
variable {R₀ : Type} [CommRing R₀] in
open MvPowerSeries in
variable {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  {S : Type} [CommRing S] [Algebra R₀ S] in
theorem _root_.GlobalTheory.ChartCompare.isNilpotent_nEval (f : MvPowerSeries σ R₀)
    (hf : constantCoeff f = 0) (a : σ → S)
    (ha : ∀ i, IsNilpotent (a i)) : IsNilpotent (_root_.ReciprocityTheory.PGsh.Be2.nEval f a) := by
  have h := _root_.GlobalTheory.evBasic_nEval_sub_coeff_mem f a ha
  rw [coeff_zero_eq_constantCoeff_apply, hf, map_zero, sub_zero] at h
  have hle : Ideal.span (Set.range a) ≤ nilradical S :=
    Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact mem_nilradical.mpr (ha i))
  exact mem_nilradical.mp (hle h)
open IsLocalRing TensorProduct in
variable {R₀ : Type} [CommRing R₀] in
open MvPowerSeries in
variable {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  {S : Type} [CommRing S] [Algebra R₀ S] in

theorem _root_.GlobalTheory.ChartCompare.nEval_subst (b : σ → MvPowerSeries τ R₀)
    (hb : ∀ s, constantCoeff (b s) = 0)
    (f : MvPowerSeries σ R₀) (a : τ → S) (ha : ∀ i, IsNilpotent (a i)) :
    _root_.ReciprocityTheory.PGsh.Be2.nEval (subst b f) a = _root_.ReciprocityTheory.PGsh.Be2.nEval f (fun s => _root_.ReciprocityTheory.PGsh.Be2.nEval (b s) a) := by
  have hbS : HasSubst b := hasSubst_of_constantCoeff_nilpotent fun s => by simp [hb s]
  have hab : ∀ s, IsNilpotent (_root_.ReciprocityTheory.PGsh.Be2.nEval (b s) a) := fun s =>
    _root_.GlobalTheory.ChartCompare.isNilpotent_nEval (b s) (hb s) a ha
  have h := _root_.GlobalTheory.ChartCompare.subst_C_eq (subst b f) a ha
  rw [subst_comp_subst_apply hbS (_root_.GlobalTheory.ChartCompare.hasSubst_C a ha)] at h
  simp_rw [_root_.GlobalTheory.ChartCompare.subst_C_eq _ a ha] at h
  rw [_root_.GlobalTheory.ChartCompare.subst_C_eq f _ hab] at h
  simpa using (congrArg (coeff 0) h).symm
omit [Fintype σ] in
theorem coeff_eq_zero_of_mem_span {N : ℕ} (f : MvPolynomial σ R₀)
    (hf : f ∈ Ideal.span (Set.range fun j : σ => (MvPolynomial.X j : MvPolynomial σ R₀) ^ N))
    (m : σ →₀ ℕ) (hm : ∀ i, m i < N) : MvPolynomial.coeff m f = 0 := by
  rw [Ideal.span, Finsupp.mem_span_range_iff_exists_finsupp] at hf
  obtain ⟨c, rfl⟩ := hf
  rw [Finsupp.sum, MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [smul_eq_mul, MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_mul_monomial', if_neg]
  intro h
  have := h j
  simp only [Finsupp.single_eq_same] at this
  exact absurd (hm j) (not_lt.mpr this)
theorem coeff_tEval_X {N : ℕ} (f : MvPowerSeries σ R₀) (m : σ →₀ ℕ) (hm : ∀ i, m i < N) :
    MvPolynomial.coeff m (tEval N f (MvPolynomial.X : σ → MvPolynomial σ R₀)) = coeff m f := by
  have h : ∀ (e : σ → ℕ) (r : R₀), algebraMap R₀ (MvPolynomial σ R₀) r *
      ∏ i, MvPolynomial.X i ^ e i = MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm e) r :=
    fun e r => by
      rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
      rfl
  rw [evBasic_tEval_eq_sum, MvPolynomial.coeff_sum, Finset.sum_eq_single (⇑m)]
  · rw [h, MvPolynomial.coeff_monomial]; simp
  · intro e _ he
    rw [h, MvPolynomial.coeff_monomial, if_neg]
    rintro rfl
    exact he rfl
  · intro hc
    exact absurd (by simpa [Fintype.mem_piFinset] using hm) hc
theorem eq_of_nEval_eq (f f' : MvPowerSeries σ R₀)
    (h : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : σ → S), (∀ i, IsNilpotent (a i)) →
      nEval f a = nEval f' a) : f = f' := by
  ext m
  set N := (∑ i, m i) + 1
  have hm : ∀ i, m i < N := fun i => Nat.lt_succ_of_le
    (Finset.single_le_sum (f := fun i => m i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  let J := Ideal.span (Set.range fun j : σ => (MvPolynomial.X j : MvPolynomial σ R₀) ^ N)
  let π := Ideal.Quotient.mkₐ R₀ J
  have hx : ∀ j, π (MvPolynomial.X j) ^ N = 0 := fun j => by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨j, rfl⟩)
  have h1 := h _ (fun j => π (MvPolynomial.X j)) fun j => ⟨N, hx j⟩
  rw [evBasic_nEval_eq_tEval _ _ N hx, evBasic_nEval_eq_tEval _ _ N hx, ← evBasic_map_tEval,
    ← evBasic_map_tEval] at h1
  have h2 := coeff_eq_zero_of_mem_span _ (Ideal.Quotient.eq.1 h1) m hm
  rwa [MvPolynomial.coeff_sub, coeff_tEval_X _ _ hm, coeff_tEval_X _ _ hm, sub_eq_zero] at h2
open IsLocalRing TensorProduct in
variable {R₀ : Type} [CommRing R₀] in
open MvPowerSeries in
variable {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  {S : Type} [CommRing S] [Algebra R₀ S] in
theorem finsupp_prod_pow_eq_toMultiset_map_prod (a : σ → S) (d : σ →₀ ℕ) :
    (d.prod fun i n => a i ^ n) = ((Finsupp.toMultiset d).map a).prod := by
  rw [Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
    Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
open IsLocalRing TensorProduct in
variable {R₀ : Type} [CommRing R₀] in
open MvPowerSeries in
variable {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  {S : Type} [CommRing S] [Algebra R₀ S] in
theorem multiset_map_prod_sub_mem_of_sub_mem (a b : σ → S) (J : Ideal S) (hJ : ∀ i, a i - b i ∈ J)
    (m : Multiset σ) : (m.map a).prod - (m.map b).prod ∈ J := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons i m ih =>
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons]
    have e : a i * (m.map a).prod - b i * (m.map b).prod =
        a i * ((m.map a).prod - (m.map b).prod) + (a i - b i) * (m.map b).prod := by ring
    rw [e]
    exact J.add_mem (J.mul_mem_left _ ih) (J.mul_mem_right _ (hJ i))
open IsLocalRing TensorProduct in
variable {R₀ : Type} [CommRing R₀] in
open MvPowerSeries in
variable {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  {S : Type} [CommRing S] [Algebra R₀ S] in
theorem multiset_map_prod_sub_mem_mul_of_two_le_card (a b : σ → S) (I J : Ideal S) (ha : ∀ i, a i ∈ I)
    (hb : ∀ i, b i ∈ I) (hJ : ∀ i, a i - b i ∈ J) (m : Multiset σ)
    (hm : 2 ≤ Multiset.card m) : (m.map a).prod - (m.map b).prod ∈ I * J := by
  obtain ⟨i, hi⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < Multiset.card m)
  obtain ⟨m', rfl⟩ := Multiset.exists_cons_of_mem hi
  rw [Multiset.card_cons] at hm
  have hB : (m'.map b).prod ∈ I := by
    obtain ⟨j, hj⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < Multiset.card m')
    obtain ⟨m'', rfl⟩ := Multiset.exists_cons_of_mem hj
    rw [Multiset.map_cons, Multiset.prod_cons]
    exact I.mul_mem_right _ (hb j)
  have e : ((i ::ₘ m').map a).prod - ((i ::ₘ m').map b).prod =
      a i * ((m'.map a).prod - (m'.map b).prod) + (m'.map b).prod * (a i - b i) := by
    simp only [Multiset.map_cons, Multiset.prod_cons]
    ring
  rw [e]
  exact add_mem (Ideal.mul_mem_mul (ha i) (multiset_map_prod_sub_mem_of_sub_mem a b J hJ _))
    (Ideal.mul_mem_mul hB (hJ i))
open IsLocalRing TensorProduct in
variable {R₀ : Type} [CommRing R₀] in
open MvPowerSeries in
variable {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  {S : Type} [CommRing S] [Algebra R₀ S] in

theorem _root_.GlobalTheory.ChartCompare.nEval_sub_mem (f : MvPowerSeries σ R₀) (a b : σ → S)
    (hna : ∀ i, IsNilpotent (a i))
    (hnb : ∀ i, IsNilpotent (b i)) (I J : Ideal S) (ha : ∀ i, a i ∈ I) (hb : ∀ i, b i ∈ I)
    (hJ : ∀ i, a i - b i ∈ J) :
    _root_.ReciprocityTheory.PGsh.Be2.nEval f a - _root_.ReciprocityTheory.PGsh.Be2.nEval f b - ∑ j, coeff (Finsupp.single j 1) f • (a j - b j) ∈ I * J := by
  set t : (σ →₀ ℕ) → S := fun d => _root_.GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts.evalTerm f a d - _root_.GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts.evalTerm f b d
    with ht
  have hfa := _root_.GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts.evalTerm_finite f a hna
  have hfb := _root_.GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts.evalTerm_finite f b hnb
  have key : _root_.ReciprocityTheory.PGsh.Be2.nEval f a - _root_.ReciprocityTheory.PGsh.Be2.nEval f b = ∑ᶠ d, t d := by
    rw [nilpotent_eval_eq_finsum f a hna, nilpotent_eval_eq_finsum f b hnb,
      finsum_sub_distrib hfa hfb]
  have lin : ∑ j, coeff (Finsupp.single j 1) f • (a j - b j) =
      ∑ᶠ d, (Set.range fun j => Finsupp.single j 1).indicator t d := by
    rw [← finsum_mem_def, finsum_mem_range (Finsupp.single_left_injective one_ne_zero),
      finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [t, _root_.GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts.evalTerm]
    rw [Finsupp.prod_single_index (h := fun i n => a i ^ n) (pow_zero _),
      Finsupp.prod_single_index (h := fun i n => b i ^ n) (pow_zero _), pow_one, pow_one, smul_sub]
  have hft : (Function.support t).Finite := (hfa.union hfb).subset (Function.support_sub _ _)
  have hfi : (Function.support ((Set.range fun j => Finsupp.single j 1).indicator t)).Finite :=
    (Set.finite_range _).subset Set.support_indicator_subset
  rw [key, lin, ← finsum_sub_distrib hft hfi]
  refine finsum_induction (fun x => x ∈ I * J) (zero_mem _) (fun _ _ => add_mem) fun d => ?_
  by_cases hd : d ∈ Set.range fun j : σ => Finsupp.single j 1
  · rw [Set.indicator_of_mem hd, sub_self]
    exact zero_mem _
  · rw [Set.indicator_of_notMem hd, sub_zero, ht]
    simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts.evalTerm, ← smul_sub, finsupp_prod_pow_eq_toMultiset_map_prod]
    rw [Algebra.smul_def]
    apply Ideal.mul_mem_left
    rcases Nat.lt_or_ge (Multiset.card (Finsupp.toMultiset d)) 2 with h | h
    · obtain h0 | h1 : Multiset.card (Finsupp.toMultiset d) = 0 ∨
          Multiset.card (Finsupp.toMultiset d) = 1 := by omega
      · rw [Multiset.card_eq_zero.mp h0]
        simp
      · obtain ⟨j, hj⟩ := Multiset.card_eq_one.mp h1
        have hdj : Finsupp.single j 1 = d := by
          rw [← Finsupp.toMultiset_toFinsupp d, hj, Multiset.toFinsupp_singleton]
        exact absurd ⟨j, hdj⟩ hd
    · exact multiset_map_prod_sub_mem_mul_of_two_le_card a b I J ha hb hJ _ h
end Eval
section Law
open MvPowerSeries
variable {g : ℕ}
structure PointLaws (F : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R₀) : Prop where
  unit : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S), (∀ i, IsNilpotent (a i)) →
    fAdd F a 0 = a
  comm : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
    (∀ i, IsNilpotent (b i)) → fAdd F a b = fAdd F b a
  assoc : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b c : Fin g → S),
    (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) → (∀ i, IsNilpotent (c i)) →
    fAdd F (fAdd F a b) c = fAdd F a (fAdd F b c)
theorem nil_elim {S : Type} [CommRing S] {a b : Fin g → S} (ha : ∀ i, IsNilpotent (a i))
    (hb : ∀ i, IsNilpotent (b i)) : ∀ s, IsNilpotent (Sum.elim a b s) := by
  rintro (i | i); exacts [ha i, hb i]
theorem nEval_subst_elim {τ S : Type} [Fintype τ] [DecidableEq τ] [CommRing S] [Algebra R₀ S]
    (F : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R₀) (u v : Fin g → MvPowerSeries τ R₀)
    (hu : ∀ s, constantCoeff (u s) = 0) (hv : ∀ s, constantCoeff (v s) = 0) (x : τ → S)
    (hx : ∀ i, IsNilpotent (x i)) (k : Fin g) :
    nEval (subst (Sum.elim u v) (F k)) x =
      fAdd F (fun b => nEval (u b) x) (fun b => nEval (v b) x) k := by
  rw [nEval_subst _ (by rintro (s | s); exacts [hu s, hv s]) _ _ hx, fAdd]
  congr 1
  funext s
  cases s <;> rfl
theorem nEval_swap {S : Type} [CommRing S] [Algebra R₀ S]
    (F : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R₀) (a b : Fin g → S) (ha : ∀ i, IsNilpotent (a i))
    (hb : ∀ i, IsNilpotent (b i)) (k : Fin g) :
    nEval ((F k).subst (fun s => (X s.swap : MvPowerSeries (Fin g ⊕ Fin g) R₀))) (Sum.elim a b) =
      fAdd F b a k := by
  rw [nEval_subst _ (by simp) _ _ (nil_elim ha hb), fAdd]
  congr 1
  funext s
  rw [nEval_X _ (nil_elim ha hb)]
  cases s <;> rfl
theorem nEval_pair {S : Type} [CommRing S] [Algebra R₀ S]
    (F : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R₀) (x : Fin 3 × Fin g → S)
    (hx : ∀ i, IsNilpotent (x i)) (i j : Fin 3) :
    (fun b => nEval ((F b).subst
      (Sum.elim (fun c => (X (i, c) : MvPowerSeries (Fin 3 × Fin g) R₀)) (fun c => X (j, c)))) x) =
      fAdd F (fun c => x (i, c)) (fun c => x (j, c)) := by
  funext b
  rw [nEval_subst_elim F _ _ (by simp) (by simp) x hx]
  simp only [nEval_X x hx]
theorem const_pair (F : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R₀)
    (hF : ∀ a, constantCoeff (F a) = 0) (i j : Fin 3) (b : Fin g) :
    constantCoeff ((F b).subst
      (Sum.elim (fun c => (X (i, c) : MvPowerSeries (Fin 3 × Fin g) R₀)) (fun c => X (j, c)))) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (by rintro (s | s) <;> simp))
    (by rintro (s | s) <;> simp) (hF b)
theorem pointLaws_of_law (L : FormalGroupLaw R₀ g) : PointLaws L.F := by
  have hassoc : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b c : Fin g → S),
      (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) → (∀ i, IsNilpotent (c i)) →
      fAdd L.F (fAdd L.F a b) c = fAdd L.F a (fAdd L.F b c) := by
    intro S _ _ a b c ha hb hc
    funext k
    let x : Fin 3 × Fin g → S := fun q => ![a, b, c] q.1 q.2
    have hx : ∀ i, IsNilpotent (x i) := by
      rintro ⟨i, j⟩
      fin_cases i
      exacts [ha j, hb j, hc j]
    have h := congrArg (fun f => nEval f x) (L.assoc k)
    beta_reduce at h
    rw [nEval_subst_elim _ _ _ (const_pair _ L.const _ _) (by simp) x hx,
      nEval_subst_elim _ _ _ (by simp) (const_pair _ L.const _ _) x hx, nEval_pair _ x hx,
      nEval_pair _ x hx] at h
    simp only [nEval_X x hx] at h
    exact h
  refine ⟨?_, ?_, hassoc⟩
  · intro S _ _ a ha
    have h0 : ∀ i, IsNilpotent ((0 : Fin g → S) i) := fun _ => IsNilpotent.zero
    have h00 : fAdd L.F (0 : Fin g → S) 0 = 0 := by
      funext k
      have := evBasic_nEval_sub_coeff_mem (L.F k) (Sum.elim (0 : Fin g → S) 0) (nil_elim h0 h0)
      rw [coeff_zero_eq_constantCoeff_apply, L.const, map_zero, sub_zero] at this
      exact (Ideal.span_le.2 (by rintro _ ⟨i | i, rfl⟩ <;> simp) :
        Ideal.span _ ≤ (⊥ : Ideal S)) this
    have h1 := hassoc S a 0 0 ha h0 h0
    rw [h00] at h1
    have hb : ∀ i, IsNilpotent (fAdd L.F a 0 i) := fun i =>
      isNilpotent_nEval _ (L.const i) _ (nil_elim ha h0)
    generalize hbdef : fAdd L.F a 0 = b at h1 hb
    let I := Ideal.span (Set.range (Sum.elim a b))
    let J := Ideal.span (Set.range (b - a))
    have hJ : J ≤ I * J := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      have h2 := nEval_sub_mem (L.F k) (Sum.elim b 0) (Sum.elim a 0) (nil_elim hb h0)
        (nil_elim ha h0) I J
        (by rintro (i | i); exacts [Ideal.subset_span ⟨Sum.inr i, rfl⟩, I.zero_mem])
        (by rintro (i | i); exacts [Ideal.subset_span ⟨Sum.inl i, rfl⟩, I.zero_mem])
        (by rintro (i | i); exacts [Ideal.subset_span ⟨i, rfl⟩, by simp])
      have e1 : nEval (L.F k) (Sum.elim b 0) = b k := congrFun h1 k
      have e2 : nEval (L.F k) (Sum.elim a 0) = b k := congrFun hbdef k
      rw [e1, e2, sub_self, zero_sub, neg_mem_iff, Fintype.sum_sum_type] at h2
      simpa [L.lin_left] using h2
    obtain ⟨n, hn⟩ : IsNilpotent I :=
      (Ideal.FG.isNilpotent_iff_le_nilradical
        (Submodule.fg_span (Set.finite_range _))).2
        (Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact nil_elim ha hb i))
    have hpow : ∀ m : ℕ, J ≤ I ^ m * J := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ, mul_assoc]; exact ih.trans (Ideal.mul_mono_right hJ)
    have h3 := hpow n
    rw [hn, zero_mul] at h3
    funext k
    exact sub_eq_zero.1 (h3 (Ideal.subset_span ⟨k, rfl⟩ : (b - a) k ∈ J))
  · intro S _ _ a b ha hb
    funext k
    rw [← nEval_swap L.F a b ha hb, L.comm]
    rfl
def lawOfPointLaws (F : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R₀) (h : PointLaws F) :
    FormalGroupLaw R₀ g :=
  have hconst : ∀ a, constantCoeff (F a) = 0 := fun k => by
    have h0 : ∀ i, IsNilpotent ((0 : Fin g → R₀) i) := fun _ => IsNilpotent.zero
    have h1 := evBasic_nEval_sub_coeff_mem (F k) (Sum.elim (0 : Fin g → R₀) 0) (nil_elim h0 h0)
    have h2 : nEval (F k) (Sum.elim (0 : Fin g → R₀) 0) = 0 := congrFun (h.unit R₀ 0 h0) k
    have h3 := (Ideal.span_le.2 (by rintro _ ⟨i | i, rfl⟩ <;> simp) :
        Ideal.span _ ≤ (⊥ : Ideal R₀)) h1
    rw [h2] at h3
    simpa using h3
  have hlin : ∀ (k : Fin g) (s : Fin g ⊕ Fin g),
      nEval (F k) (Pi.single s (DualNumber.eps : DualNumber R₀)) =
        coeff (Finsupp.single s 1) (F k) • (DualNumber.eps : DualNumber R₀) := fun k s => by
    have hm : ∀ i, (Pi.single s DualNumber.eps : _ → DualNumber R₀) i ∈
        Ideal.span {(DualNumber.eps : DualNumber R₀)} := fun i => by
      rw [Pi.single_apply]
      split_ifs
      exacts [Ideal.subset_span rfl, Ideal.zero_mem _]
    have hn : ∀ i, IsNilpotent ((Pi.single s DualNumber.eps : _ → DualNumber R₀) i) := fun i => by
      rw [Pi.single_apply]
      split_ifs
      exacts [⟨2, by rw [pow_two, DualNumber.eps_mul_eps]⟩, IsNilpotent.zero]
    have h0 : ∀ i, IsNilpotent ((0 : Fin g → DualNumber R₀) i) := fun _ => IsNilpotent.zero
    have h1 := nEval_sub_mem (F k) _ (Sum.elim (0 : Fin g → DualNumber R₀) 0) hn (nil_elim h0 h0)
      _ _ hm (by rintro (i | i) <;> simp) (by rintro (i | i) <;> simpa using hm _)
    have h2 : nEval (F k) (Sum.elim (0 : Fin g → DualNumber R₀) 0) = 0 :=
      congrFun (h.unit _ 0 h0) k
    rw [Ideal.span_singleton_mul_span_singleton, DualNumber.eps_mul_eps,
      Ideal.span_singleton_eq_bot.2 rfl, Ideal.mem_bot, h2, sub_zero, sub_eq_zero,
      Finset.sum_eq_single s (fun i _ hi => by simp [hi]) (by simp)] at h1
    simpa using h1
  have hn : ∀ b i : Fin g, IsNilpotent ((Pi.single b DualNumber.eps : _ → DualNumber R₀) i) :=
    fun b i => by
      rw [Pi.single_apply]
      split_ifs
      exacts [⟨2, by rw [pow_two, DualNumber.eps_mul_eps]⟩, IsNilpotent.zero]
  { F := F
    const := hconst
    lin_left := fun a b => by
      have h1 := hlin a (Sum.inl b)
      have h2 : (Pi.single (Sum.inl b) DualNumber.eps : Fin g ⊕ Fin g → DualNumber R₀) =
          Sum.elim (Pi.single b DualNumber.eps) 0 := by
        funext s; cases s <;> simp [Pi.single_apply]
      rw [h2] at h1
      have h3 := congrArg TrivSqZeroExt.snd ((congrFun (h.unit _ _ (hn b)) a).symm.trans h1)
      rw [Pi.single_apply] at h3
      split_ifs at h3 ⊢ <;> simpa using h3.symm
    lin_right := fun a b => by
      have h1 := hlin a (Sum.inr b)
      have h2 : (Pi.single (Sum.inr b) DualNumber.eps : Fin g ⊕ Fin g → DualNumber R₀) =
          Sum.elim (0 : Fin g → DualNumber R₀) (Pi.single b DualNumber.eps) := by
        funext s; cases s <;> simp [Pi.single_apply]
      rw [h2] at h1
      have h4 := (h.comm _ 0 _ (fun _ => IsNilpotent.zero) (hn b)).trans (h.unit _ _ (hn b))
      have h3 := congrArg TrivSqZeroExt.snd ((congrFun h4 a).symm.trans h1)
      rw [Pi.single_apply] at h3
      split_ifs at h3 ⊢ <;> simpa using h3.symm
    assoc := fun k => eq_of_nEval_eq _ _ fun S _ _ x hx => by
      rw [nEval_subst_elim _ _ _ (const_pair _ hconst _ _) (by simp) x hx,
        nEval_subst_elim _ _ _ (by simp) (const_pair _ hconst _ _) x hx, nEval_pair _ x hx,
        nEval_pair _ x hx]
      simp only [nEval_X x hx]
      exact congrFun (h.assoc S _ _ _ (fun _ => hx _) (fun _ => hx _) (fun _ => hx _)) k
    comm := fun k => eq_of_nEval_eq _ _ fun S _ _ x hx => by
      obtain ⟨a, b, rfl⟩ : ∃ a b, x = Sum.elim a b :=
        ⟨x ∘ Sum.inl, x ∘ Sum.inr, (Sum.elim_comp_inl_inr x).symm⟩
      have ha : ∀ i, IsNilpotent (a i) := fun i => hx (Sum.inl i)
      have hb : ∀ i, IsNilpotent (b i) := fun i => hx (Sum.inr i)
      rw [nEval_swap F a b ha hb, h.comm S b a hb ha]
      rfl }
def lawEquiv : FormalGroupLaw R₀ g ≃ {F : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R₀ // PointLaws F} where
  toFun L := ⟨L.F, pointLaws_of_law L⟩
  invFun F := lawOfPointLaws F.1 F.2
  left_inv _ := rfl
  right_inv _ := rfl
end Law
section Nil
variable {K : LAlg R₀}
theorem ker_eq_maximalIdeal (hK : IsField (K : Type)) {R : LAlg R₀} (ρ : LHom R K) :
    RingHom.ker ρ.1 = maximalIdeal (R : Type) := by
  ext a
  rw [RingHom.mem_ker, mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro h hu
    have := hu.map ρ.1
    rw [h] at this
    exact not_isUnit_zero this
  · intro h
    by_contra hne
    obtain ⟨b, hb⟩ := hK.mul_inv_cancel hne
    exact h (ρ.2.map_nonunit a (IsUnit.of_mul_eq_one b hb))
theorem isField_of_resAlg (R : ResAlg K) : IsField (K : Type) := by
  rw [isField_iff_maximalIdeal_eq, eq_bot_iff]
  intro x hx
  obtain ⟨a, rfl⟩ := R.res_surj x
  have ha : a ∈ maximalIdeal (R.alg : Type) := fun hu => hx (hu.map R.res.1)
  rw [← R.res_ker] at ha
  exact ha
theorem isNilOver_res (R : NilAlg K) : IsNilOver R.res :=
  ⟨R.res_surj, fun a ha => R.nil a (R.res_ker ▸ ha)⟩
def nilAlgOf (hK : IsField (K : Type)) {R : LAlg R₀} (ρ : LHom R K) (hρ : IsNilOver ρ) :
    NilAlg K where
  alg := R
  res := ρ
  res_surj := hρ.1
  res_ker := ker_eq_maximalIdeal hK ρ
  nil a ha := hρ.2 a (ker_eq_maximalIdeal hK ρ ▸ ha)
def nilEquiv (hK : IsField (K : Type)) :
    NilAlg K ≃ Σ R : LAlg R₀, {ρ : LHom R K // IsNilOver ρ} where
  toFun R := ⟨R.alg, R.res, isNilOver_res R⟩
  invFun R := nilAlgOf hK R.2.1 R.2.2
  left_inv _ := rfl
  right_inv _ := rfl
theorem sm_iff (B : BX R₀) (W : NilAlg K) : SM B K W.alg W.res ↔ LiftsFromResidue B W :=
  ⟨fun h => h.onto, fun h => ⟨isNilOver_res W, h⟩⟩
theorem exists_factor (R : ResAlg K) {S : LAlg R₀} (π : LHom R.alg S) (hπ : π.SqZero) :
    ∃ r : LHom S K, r.comp π = R.res := by
  have hle : RingHom.ker π.1 ≤ RingHom.ker R.res.1 := by
    rw [R.res_ker]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
  let r : (S : Type) →ₐ[R₀] (K : Type) := AlgHom.liftOfSurjective π.1 hπ.1 R.res.1 hle
  have hr : ∀ a, r (π.1 a) = R.res.1 a := fun a => AlgHom.liftOfSurjective_apply _ _ _ _ a
  exact ⟨⟨r, ⟨fun s hs => by
    obtain ⟨a, rfl⟩ := hπ.1 s
    have h1 : IsUnit (R.res.1 a) := by rw [← hr]; exact hs
    exact (R.res.2.map_nonunit a h1).map π.1⟩⟩, Subtype.ext (AlgHom.ext hr)⟩
end Nil
section Chart
variable {B : BX R₀} {K : LAlg R₀} {g : ℕ}
theorem elim_val {R : Type} [CommRing R] {I : Ideal R} (x y : Fin g → I) :
    (fun s => (Sum.elim x y s).1) = Sum.elim (fun k => (x k : R)) (fun k => (y k : R)) := by
  funext s; cases s <;> rfl
def chartOfCH0 (c : FormalChartAtZero B K g) : FormalChart B c.gb K where
  law := lawOfPointLaws c.F ⟨c.F_unit, c.F_comm, c.F_assoc⟩
  coord R := c.χ R.res (isNilOver_res R)
  coord_nat R S f hf x a := c.χ_nat R.res S.res _ _ f hf x a
  coord_add R x y a := by
    rw [← nEval_eq_evalNil, elim_val]
    exact congrFun (c.χ_add R.res (isNilOver_res R) x y) a
  coord_tg R S π hπ w i a := by
    obtain ⟨r, hr⟩ := exists_factor R.toResAlg π hπ
    exact c.χ_tg R.res _ π hπ r hr w i a
def ch0OfChart (hK : IsField (K : Type)) {gb : Module.Basis (Fin g) R₀ B.gg}
    (c : FormalChart B gb K) : FormalChartAtZero B K g where
  F := c.law.F
  F_unit := (pointLaws_of_law c.law).unit
  F_comm := (pointLaws_of_law c.law).comm
  F_assoc := (pointLaws_of_law c.law).assoc
  gb := gb
  χ ρ hρ := c.coord (nilAlgOf hK ρ hρ)
  χ_add ρ hρ x y := by
    funext a
    have h := c.coord_add (nilAlgOf hK ρ hρ) x y a
    rw [← nEval_eq_evalNil, elim_val] at h
    exact h
  χ_nat ρ ρ' hρ hρ' f hf x a := c.coord_nat (nilAlgOf hK ρ hρ) (nilAlgOf hK ρ' hρ') f hf x a
  χ_tg ρ hρ π hπ _ _ w i a := c.coord_tg (nilAlgOf hK ρ hρ) _ π hπ w i a
def chartEquiv (hK : IsField (K : Type)) :
    FormalChartAtZero B K g ≃ Σ gb : Module.Basis (Fin g) R₀ B.gg, FormalChart B gb K where
  toFun c := ⟨c.gb, chartOfCH0 c⟩
  invFun c := ch0OfChart hK c.2
  left_inv _ := rfl
  right_inv _ := rfl
end Chart
section Torsion
universe v
variable {B : BX R₀} {k : LAlg R₀} {p g : ℕ} {O : ResAlg k}
theorem mem_tors {R : LAlg R₀} {z : B.G R} : z ∈ Tors B p R ↔ p • z = 0 := by
  rw [← natCast_zsmul]
  exact Iff.rfl
theorem card_tors (R : LAlg R₀) : Nat.card {t : B.G R // p • t = 0} = Nat.card (Tors B p R) :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_tors.symm)
variable {C : Type v} [Field C] [Algebra (O.alg : Type) C] [IsFractionRing (O.alg : Type) C]
omit [IsFractionRing (O.alg : Type) C] in
theorem toFun_one_tmul (D : TorsionRep B p O) (f : D.total) (t : Tors B p O.alg) :
    D.toFun C (1 ⊗ₜ f) t = algebraMap (O.alg : Type) C ((D.classify t).2.1 (f (D.classify t).1)) := by
  unfold TorsionRep.toFun
  rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl
theorem classify_eq (D : TorsionRep B p O) (x : Tors B p k) (φ : LHom (D.A x).alg O.alg)
    (hφ : φ.comp (D.str x) = LHom.id _) (t : Tors B p O.alg)
    (ht : B.map φ (D.y x : B.G _) = (t : B.G O.alg)) : D.classify t = ⟨x, φ⟩ :=
  (D.universal O.alg (LHom.id _) t).unique (D.classify_spec t) ⟨hφ, ht⟩
theorem sep_of_finiteTorsion (D : FiniteTorsion B p g O C) (x : Tors B p k)
    (f : ((D.rep.A x).alg : Type))
    (hf : ∀ t, ∀ φ : LHom (D.rep.A x).alg O.alg, D.rep.classify t = ⟨x, φ⟩ → φ.1 f = 0) :
    f = 0 := by
  classical
  haveI := D.free
  have h1 : D.rep.toFun C (1 ⊗ₜ (Pi.single x f : D.rep.total)) = 0 := by
    funext t
    rw [toFun_one_tmul]
    have := hf t
    generalize D.rep.classify t = c at this
    obtain ⟨x', φ⟩ := c
    by_cases h : x' = x
    · subst h
      simp [this φ rfl]
    · simp [Pi.single_eq_of_ne h]
  have h2 : (1 : C) ⊗ₜ[(O.alg : Type)] (Pi.single x f : D.rep.total) = 0 :=
    D.generic.1 (h1.trans (map_zero _).symm)
  have h3 : (Pi.single x f : D.rep.total) = 0 :=
    Algebra.TensorProduct.includeRight_injective (A := C) (B := D.rep.total)
      (IsFractionRing.injective (O.alg : Type) C) (h2.trans (map_zero _).symm)
  simpa using congrFun h3 x
theorem finite_tors_of_finiteTorsion [Fact p.Prime] (D : FiniteTorsion B p g O C) :
    Finite (Tors B p O.alg) :=
  Nat.finite_of_card_ne_zero (D.card ▸ pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
theorem finite_index [Fact p.Prime] (D : FiniteTorsion B p g O C) : Finite (Tors B p k) := by
  haveI := finite_tors_of_finiteTorsion D
  refine Finite.of_surjective (fun t => (D.rep.classify t).1) fun x => ?_
  by_contra h
  exact one_ne_zero (sep_of_finiteTorsion D x 1 fun t φ ht => (h ⟨t, congrArg Sigma.fst ht⟩).elim)
theorem free_factor (D : FiniteTorsion B p g O C) (x : Tors B p k) :
    Module.Free (O.alg : Type) ((D.rep.A x).alg : Type) ∧
      Module.Finite (O.alg : Type) ((D.rep.A x).alg : Type) := by
  classical
  haveI := D.free
  haveI := D.finite
  haveI : Module.Finite (O.alg : Type) ((D.rep.A x).alg : Type) :=
    Module.Finite.of_surjective (LinearMap.proj (R := (O.alg : Type))
      (φ := fun x => ((D.rep.A x).alg : Type)) x) (Function.surjective_eval x)
  haveI : Module.Flat (O.alg : Type) ((D.rep.A x).alg : Type) :=
    Module.Flat.of_retract (LinearMap.single (O.alg : Type) (fun x => ((D.rep.A x).alg : Type)) x)
      (LinearMap.proj x) (by ext; simp)
  exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩
def finOfFiniteTorsion [Fact p.Prime] (D : FiniteTorsion B p g O C) : FIN B O.alg p where
  ι := Tors B p k
  fι := haveI := finite_index D; Fintype.ofFinite _
  dι := Classical.decEq _
  AAx x := (D.rep.A x).alg
  sO := D.rep.str
  free := free_factor D
  y x := D.rep.y x
  y_p x := mem_tors.1 (D.rep.y x).2
  univ S s z hz := by
    obtain ⟨c, hc, hu⟩ := D.rep.universal S s ⟨z, mem_tors.2 hz⟩
    exact ⟨c.1, c.2, hc.1, hc.2, fun j φ' h1 h2 => Sigma.ext_iff.1 (hu ⟨j, φ'⟩ ⟨h1, h2⟩)⟩
  sep x f hf := sep_of_finiteTorsion D x f fun t φ ht => hf φ (by
    have := (D.rep.classify_spec t).1
    rw [ht] at this
    exact this)
  rank := by
    haveI := finite_index D
    haveI := finite_tors_of_finiteTorsion D
    letI := Fintype.ofFinite (Tors B p k)
    letI := Fintype.ofFinite (Tors B p O.alg)
    haveI := D.free
    haveI := fun x => (free_factor D x).1
    haveI := fun x => (free_factor D x).2
    have h1 := Module.finrank_pi_fintype (O.alg : Type) (M := fun x => ((D.rep.A x).alg : Type))
    have h2 := (LinearEquiv.ofBijective (D.rep.toFun C).toLinearMap D.generic).finrank_eq
    rw [Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card] at h2
    rw [card_tors, Nat.card_eq_fintype_card, ← h2]
    exact h1.symm
namespace OfFin
variable (F : FIN B O.alg p)
theorem exists_point (i : F.ι) : ∃ φ : LHom (F.AAx i) O.alg, φ.comp (F.sO i) = LHom.id O.alg := by
  by_contra h
  exact one_ne_zero (F.sep i 1 fun φ hφ => (h ⟨φ, hφ⟩).elim)
def res (i : F.ι) : LHom (F.AAx i) k := O.res.comp (exists_point F i).choose
theorem res_comp (i : F.ι) : (res F i).comp (F.sO i) = O.res :=
  Subtype.ext (AlgHom.ext fun a => congrArg O.res.1
    (congrArg (fun f : LHom O.alg O.alg => f.1 a) (exists_point F i).choose_spec))
theorem res_unique (i : F.ι) (φ : LHom (F.AAx i) k) (hφ : φ.comp (F.sO i) = O.res) :
    φ = res F i := by
  have hk := isField_of_resAlg O
  refine Subtype.ext (AlgHom.ext fun a => ?_)
  obtain ⟨o, ho⟩ := O.res_surj ((res F i).1 a)
  have e1 : (res F i).1 ((F.sO i).1 o) = O.res.1 o :=
    congrArg (fun f : LHom O.alg k => f.1 o) (res_comp F i)
  have e2 : φ.1 ((F.sO i).1 o) = O.res.1 o := congrArg (fun f : LHom O.alg k => f.1 o) hφ
  have h1 : a - (F.sO i).1 o ∈ RingHom.ker (res F i).1 := by
    rw [RingHom.mem_ker, map_sub, e1, ho, sub_self]
  rw [ker_eq_maximalIdeal hk, ← ker_eq_maximalIdeal hk φ, RingHom.mem_ker, map_sub, e2, ho] at h1
  exact sub_eq_zero.1 h1
def factor (i : F.ι) : ResAlg k where
  alg := F.AAx i
  res := res F i
  res_surj a := by
    obtain ⟨o, rfl⟩ := O.res_surj a
    exact ⟨(F.sO i).1 o, congrArg (fun f : LHom O.alg k => f.1 o) (res_comp F i)⟩
  res_ker := ker_eq_maximalIdeal (isField_of_resAlg O) _
def red (i : F.ι) : Tors B p k :=
  ⟨B.map (res F i) (F.y i), mem_tors.2 (by rw [← map_nsmul, F.y_p, map_zero])⟩
theorem red_bijective : Function.Bijective (red F) := by
  constructor
  · intro i j h
    obtain ⟨l, φ, -, -, hu⟩ := F.univ k O.res (red F j) (mem_tors.1 (red F j).2)
    exact (hu i _ (res_comp F i) (congrArg Subtype.val h)).1.trans
      (hu j _ (res_comp F j) rfl).1.symm
  · intro x
    obtain ⟨l, φ, h1, h2, -⟩ := F.univ k O.res x (mem_tors.1 x.2)
    rw [res_unique F l φ h1] at h2
    exact ⟨l, Subtype.ext h2⟩
def index : Tors B p k ≃ F.ι := (Equiv.ofBijective _ (red_bijective F)).symm
def rep : TorsionRep B p O where
  A x := factor F (index F x)
  str x := F.sO (index F x)
  str_res x := res_comp F _
  y x := ⟨F.y (index F x), mem_tors.2 (F.y_p _)⟩
  y_res x := congrArg Subtype.val ((index F).symm_apply_apply x)
  universal S s t := by
    obtain ⟨i, φ, h1, h2, hu⟩ := F.univ S s t (mem_tors.1 t.2)
    obtain ⟨x, rfl⟩ := (index F).surjective i
    refine ⟨⟨x, φ⟩, ⟨h1, h2⟩, ?_⟩
    rintro ⟨x', φ'⟩ ⟨h1', h2'⟩
    obtain ⟨e1, e2⟩ := hu _ φ' h1' h2'
    obtain rfl := (index F).injective e1
    obtain rfl := eq_of_heq e2
    rfl
theorem free_factor (x : Tors B p k) :
    Module.Free (O.alg : Type) (((rep F).A x).alg : Type) ∧
      Module.Finite (O.alg : Type) (((rep F).A x).alg : Type) := F.free (index F x)
include F in
theorem finite_index : Finite (Tors B p k) := Finite.of_equiv _ (index F).symm
theorem free_total : Module.Free (O.alg : Type) (rep F).total :=
  haveI := finite_index F
  haveI := fun x => (free_factor F x).1
  Module.Free.pi _ _
theorem finite_total : Module.Finite (O.alg : Type) (rep F).total :=
  haveI := finite_index F
  haveI := fun x => (free_factor F x).2
  Module.Finite.pi
theorem finrank_total :
    Module.finrank (O.alg : Type) (rep F).total = Nat.card (Tors B p O.alg) := by
  haveI := finite_index F
  letI := Fintype.ofFinite (Tors B p k)
  haveI := fun x => (free_factor F x).1
  haveI := fun x => (free_factor F x).2
  rw [← card_tors, ← F.rank, ← (index F).sum_comp]
  exact Module.finrank_pi_fintype (O.alg : Type) (M := fun x => (((rep F).A x).alg : Type))
include F in
theorem finite_tors : Finite (Tors B p O.alg) := by
  haveI := free_total F
  haveI := finite_total F
  haveI : Nontrivial (rep F).total := Pi.nontrivial_at 0
  exact Nat.finite_of_card_ne_zero (finrank_total F ▸
    ((Module.finrank_pos_iff_of_free (O.alg : Type) (rep F).total).2 inferInstance).ne')
variable (C) in
theorem generic : Function.Bijective ((rep F).toFun C) := by
  haveI := free_total F
  haveI := finite_total F
  haveI := finite_tors F
  letI := Fintype.ofFinite (Tors B p O.alg)
  have hinj : Function.Injective ((rep F).toFun C) := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨f, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors (O.alg : Type))
      (TensorProduct.mk (O.alg : Type) C (rep F).total 1) z
    have hs' : algebraMap (O.alg : Type) C s • z = (1 : C) ⊗ₜ f := by
      rw [algebraMap_smul]; exact hs
    have h1 : (rep F).toFun C (1 ⊗ₜ f) = 0 := by rw [← hs', map_smul, hz, smul_zero]
    have h2 : f = 0 := by
      funext x
      refine F.sep (index F x) (f x) fun φ hφ => ?_
      have ht := classify_eq (rep F) x φ hφ
        ⟨B.map φ (F.y _), mem_tors.2 (by rw [← map_nsmul, F.y_p, map_zero])⟩ rfl
      have h3 := congrFun h1
        ⟨B.map φ (F.y _), mem_tors.2 (by rw [← map_nsmul, F.y_p, map_zero])⟩
      rw [toFun_one_tmul, ht] at h3
      exact IsFractionRing.injective (O.alg : Type) C (h3.trans (map_zero _).symm)
    rw [h2, TensorProduct.tmul_zero] at hs'
    exact (smul_eq_zero.1 hs').resolve_left
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2)
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := ((rep F).toFun C).toLinearMap) ?_).1 hinj⟩
  rw [Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card, finrank_total,
    Nat.card_eq_fintype_card]
end OfFin
def TateClauses (B : BX R₀) (p g : ℕ) (O : LAlg R₀) : Prop :=
  (∀ t : Tors B p O, ∃ τ ∈ tateModule B p O, τ 0 = (t : B.G O)) ∧
    Nat.card (Tors B p O) = p ^ (2 * g)
variable (C) in

def finiteTorsionOfFin (F : FIN B O.alg p) (h : TateClauses B p g O.alg) :
    FiniteTorsion B p g O C where
  rep := OfFin.rep F
  free := OfFin.free_total F
  finite := OfFin.finite_total F
  generic := OfFin.generic C F
  tate_surj := h.1
  card := h.2
end Torsion
section Bundle
universe v
variable {B : BX R₀} {g : ℕ} {p : ℕ} [Fact p.Prime] {k : LAlg R₀} {O : ResAlg k} {W : NilAlg k}
  {C : Type v} [Field C] [Algebra (O.alg : Type) C] [IsFractionRing (O.alg : Type) C]
variable (C) in

def chartDataOf (c : FormalChartAtZero B k g) (s : SM B k W.alg W.res) (F : FIN B O.alg p)
    (h : TateClauses B p g O.alg) : ChartData B c.gb p k O W C where
  chart := chartOfCH0 c
  smooth := (sm_iff B W).1 s
  fin := finiteTorsionOfFin C F h
end Bundle
universe v
end GlobalTheory.ChartCompare


