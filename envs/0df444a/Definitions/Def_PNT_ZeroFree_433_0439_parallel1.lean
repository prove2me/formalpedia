-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0439_parallel1
-- name    : PNT_ZeroFree_433_0439_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:18:42.959979+00:00
-- url     : https://prove2.me/theorems/ca55eedd-272f-4966-9940-91ee4aa7741b
-- title:
--   Zero-free region foundations: Detector.SelectedPrimeSums, Detector.SelectedPrimeIndexed [0439_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Detector.SelectedPrimeSums
--   - OAI.NumberTheory.DirichletL.Detector.SelectedPrimeIndexed
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/SelectedPrimeSums.lean#L11-L166
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/SelectedPrimeIndexed.lean#L10-L35

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0055
import Definitions.Def_PNT_ZeroFree_433_0058
import Definitions.Def_PNT_ZeroFree_433_0147
import Definitions.Def_PNT_ZeroFree_433_0149
import Definitions.Def_PNT_ZeroFree_433_0345_parallel1
import Definitions.Def_PNT_ZeroFree_433_0377_parallel1
import Definitions.Def_PNT_ZeroFree_433_0419_parallel1
import Definitions.Def_PNT_ZeroFree_433_0475_parallel1

/- Supporting zero-free-region lemmas, grouped by intact source scopes.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/SelectedPrimeSums.lean#L11-L166
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/SelectedPrimeIndexed.lean#L10-L35
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Detector.SelectedPrimeSums
section
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeSelectedPrimeSums
local notation "O" => ActualEisensteinCubic.O

lemma finite_ideal_count (S : Finset (Ideal O)) (H : ℝ) (hH : 0≤H)
    (hS : ∀I∈S,I≠0) (hN : ∀I∈S,(Ideal.absNorm I:ℝ)≤H) :
    (S.card:ℝ)≤128*H := by
  by_cases hh : 1≤H
  · exact DescentFiberCost.finite_ideal_count_real S H hh hS hN
  · have he : S=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro I hI
      have hp : (1:ℝ)≤Ideal.absNorm I := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hS I hI))
      have := hN I hI
      linarith
    simp only [he,Finset.card_empty,Nat.cast_zero]
    positivity

lemma ramified_card_bound (eps : ℝ) (heps : 0<eps) :
    ∃C : ℝ, 0<C ∧ ∀ (U : Ideal O), U≠0 → ∀S : Finset (Ideal O),
      ((S.filter (fun P=>P∣U)).card:ℝ)≤C*(Ideal.absNorm U:ℝ)^eps := by
  obtain ⟨C,hC,hb⟩ := IdealDivisorBound.ideal_divisor_small_power eps heps
  refine ⟨C,hC,?_⟩
  intro U hU S
  apply (show ((S.filter (fun P=>P∣U)).card:ℝ)≤(IdealMobiusDivisorSum.idealDivisors U).card from ?_).trans (hb U hU)
  exact_mod_cast Finset.card_le_card (show S.filter (fun P=>P∣U)⊆IdealMobiusDivisorSum.idealDivisors U from by
    intro P hP
    exact (IdealMobiusDivisorSum.mem_idealDivisors hU).mpr (Finset.mem_filter.mp hP).2)

def annularPower (a b r : ℝ) : ℝ := max (a^r) (b^r)

lemma annularPower_nonneg (a b r : ℝ) (ha : 0<a) : 0≤annularPower a b r :=
  (Real.rpow_nonneg ha.le _).trans (le_max_left _ _)

lemma annular_rpow (a b P q r : ℝ) (ha : 0<a) (hb : 0<b) (hP : 0<P)
    (hqa : a*P≤q) (hqb : q≤b*P) : q^r≤annularPower a b r*P^r := by
  have hq : 0<q := (mul_pos ha hP).trans_le hqa
  by_cases hr : 0≤r
  · calc
      q^r≤(b*P)^r := Real.rpow_le_rpow hq.le hqb hr
      _=b^r*P^r := Real.mul_rpow hb.le hP.le
      _≤annularPower a b r*P^r := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hP.le _)
  · calc
      q^r≤(a*P)^r := Real.rpow_le_rpow_of_nonpos (mul_pos ha hP) hqa (by linarith)
      _=a^r*P^r := Real.mul_rpow ha.le hP.le
      _≤annularPower a b r*P^r := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hP.le _)

theorem annular_slot_majorant (eps a b r d : ℝ) (heps : 0<eps)
    (ha : 0<a) (hb : 0<b) (hd : d≤1) :
    ∃C : ℝ, 0<C ∧ ∀(U : Ideal O), U≠0 → ∀P : ℝ, 1≤P →
    ∀S : Finset (Ideal O), (∀I∈S,I≠0) →
      (∀I∈S,a*P≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤b*P) →
      (∑I∈S,(Ideal.absNorm I:ℝ)^(r-1)*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1))
        ≤C*(Ideal.absNorm U:ℝ)^eps*P^r := by
  obtain ⟨D,hD,hdiv⟩ := ramified_card_bound eps heps
  let A := annularPower a b (r-1)
  let B := annularPower a b (r-1+d)
  have hA : 0≤A := annularPower_nonneg a b _ ha
  have hB : 0≤B := annularPower_nonneg a b _ ha
  refine ⟨1+128*b*A+D*B,by positivity,?_⟩
  intro U hU P hP S hS hSP
  have hP0 : 0<P := by linarith
  have hU1 : (1:ℝ)≤Ideal.absNorm U := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hU)
  have hUpow : 1≤(Ideal.absNorm U:ℝ)^eps := Real.one_le_rpow hU1 heps.le
  have hq (I : Ideal O) (hI : I∈S) : 0<(Ideal.absNorm I:ℝ) :=
    (mul_pos ha hP0).trans_le (hSP I hI).1
  have hc := finite_ideal_count S (b*P) (by positivity) hS (fun I hI=>(hSP I hI).2)
  have heP : P*P^(r-1)=P^r := by
    calc
      _=P^(1:ℝ)*P^(r-1) := by rw [Real.rpow_one]
      _=P^r := by rw [←Real.rpow_add hP0];congr 1;ring
  have hfirst : (∑I∈S,(Ideal.absNorm I:ℝ)^(r-1))≤128*b*A*P^r := by
    calc
      _≤∑_I∈S,A*P^(r-1) := Finset.sum_le_sum (fun I hI=>annular_rpow a b P _ _ ha hb hP0 (hSP I hI).1 (hSP I hI).2)
      _=(S.card:ℝ)*(A*P^(r-1)) := by simp
      _≤(128*(b*P))*(A*P^(r-1)) := mul_le_mul_of_nonneg_right hc (by positivity)
      _=128*b*A*(P*P^(r-1)) := by ring
      _=128*b*A*P^r := by rw [heP]
  have hsecond : (∑I∈S.filter (fun I=>I∣U),(Ideal.absNorm I:ℝ)^(r-1+d))≤
      D*B*(Ideal.absNorm U:ℝ)^eps*P^r := by
    have hpP : P^(r-1+d)≤P^r := Real.rpow_le_rpow_of_exponent_le hP (by linarith)
    calc
      _≤∑_I∈S.filter (fun I=>I∣U),B*P^(r-1+d) := by
        apply Finset.sum_le_sum
        intro I hI
        exact annular_rpow a b P _ _ ha hb hP0 (hSP I (Finset.mem_filter.mp hI).1).1 (hSP I (Finset.mem_filter.mp hI).1).2
      _=((S.filter (fun I=>I∣U)).card:ℝ)*(B*P^(r-1+d)) := by simp
      _≤(D*(Ideal.absNorm U:ℝ)^eps)*(B*P^r) := by
        gcongr
        exact hdiv U hU S
      _=D*B*(Ideal.absNorm U:ℝ)^eps*P^r := by ring
  have hsum : (∑I∈S,(Ideal.absNorm I:ℝ)^(r-1)*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1))≤
      (∑I∈S,(Ideal.absNorm I:ℝ)^(r-1))+
        ∑I∈S.filter (fun I=>I∣U),(Ideal.absNorm I:ℝ)^(r-1+d) := by
    rw [Finset.sum_filter,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro I hI
    split_ifs
    · rw [←Real.rpow_add (hq I hI)]
      exact le_add_of_nonneg_left (by positivity)
    · simp only [mul_one,add_zero,le_refl]
  apply hsum.trans
  have hup : 128*b*A*P^r≤128*b*A*(Ideal.absNorm U:ℝ)^eps*P^r := by
    nlinarith [mul_nonneg (show 0≤128*b*A*P^r by positivity) (show 0≤(Ideal.absNorm U:ℝ)^eps-1 by linarith)]
  nlinarith [mul_nonneg (Real.rpow_nonneg (by positivity : (0:ℝ)≤Ideal.absNorm U) eps) (Real.rpow_nonneg hP0.le r)]

theorem weighted_slot_bound (eps a b r d B K : ℝ) (heps : 0<eps)
    (ha : 0<a) (hb : 0<b) (hd : d≤1) (hB : 0≤B) (hK : 0≤K) :
    ∃C : ℝ, 0<C ∧ ∀(U : Ideal O), U≠0 → ∀P : ℝ, 1≤P →
    ∀(S : Finset (Ideal O)), (∀I∈S,I≠0) → ∀(W : ℝ→ℂ),
      Function.support W⊆Set.Icc a b → (∀y,‖W y‖≤B) →
    ∀(G : Ideal O→ℂ), (∀I∈S,‖G I‖≤K*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1)) →
    ∀z : ℂ, z.re=r →
      (∑I∈S,‖W ((Ideal.absNorm I:ℝ)/P)*(Ideal.absNorm I:ℂ)^(z-1)*G I‖)
        ≤C*(Ideal.absNorm U:ℝ)^eps*P^r := by
  obtain ⟨C,hC,hmajor⟩ := annular_slot_majorant eps a b r d heps ha hb hd
  refine ⟨(B*K+1)*C,by positivity,?_⟩
  intro U hU P hP S hS W hWS hWB G hG z hz
  have hP0 : 0<P := by linarith
  let T := S.filter (fun I=>W ((Ideal.absNorm I:ℝ)/P)≠0)
  have hTS : T⊆S := Finset.filter_subset _ _
  have hbounds (I : Ideal O) (hI : I∈T) : a*P≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤b*P := by
    have ht := hWS (show (Ideal.absNorm I:ℝ)/P∈Function.support W from (Finset.mem_filter.mp hI).2)
    exact ⟨(le_div_iff₀ hP0).mp ht.1,(div_le_iff₀ hP0).mp ht.2⟩
  have he : (∑I∈S,‖W ((Ideal.absNorm I:ℝ)/P)*(Ideal.absNorm I:ℂ)^(z-1)*G I‖)=
      ∑I∈T,‖W ((Ideal.absNorm I:ℝ)/P)*(Ideal.absNorm I:ℂ)^(z-1)*G I‖ := by
    symm
    apply Finset.sum_subset hTS
    intro I hI hn
    have hw : W ((Ideal.absNorm I:ℝ)/P)=0 := by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hI,hh⟩)
    simp only [hw,zero_mul,norm_zero]
  rw [he]
  have hpoint (I : Ideal O) (hI : I∈T) :
      ‖W ((Ideal.absNorm I:ℝ)/P)*(Ideal.absNorm I:ℂ)^(z-1)*G I‖≤
        (B*K)*((Ideal.absNorm I:ℝ)^(r-1)*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1)) := by
    have hN : (0:ℝ)<Ideal.absNorm I := (mul_pos ha hP0).trans_le (hbounds I hI).1
    have hc : ‖(Ideal.absNorm I:ℂ)^(z-1)‖=(Ideal.absNorm I:ℝ)^(r-1) := by
      simpa only [Complex.ofReal_natCast,Complex.sub_re,Complex.one_re,hz] using
        Complex.norm_cpow_eq_rpow_re_of_pos hN (z-1)
    simp only [norm_mul,hc]
    calc
      _≤B*(Ideal.absNorm I:ℝ)^(r-1)*(K*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1)) := by
        gcongr
        · exact hWB _
        · exact hG I (hTS hI)
      _=_ := by ring
  have hmain := hmajor U hU P hP T (fun I hI=>hS I (hTS hI)) hbounds
  calc
    _≤∑I∈T,(B*K)*((Ideal.absNorm I:ℝ)^(r-1)*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1)) :=
      Finset.sum_le_sum hpoint
    _=(B*K)*∑I∈T,(Ideal.absNorm I:ℝ)^(r-1)*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1) :=
      (Finset.mul_sum _ _ _).symm
    _≤(B*K)*(C*(Ideal.absNorm U:ℝ)^eps*P^r) := mul_le_mul_of_nonneg_left hmain (mul_nonneg hB hK)
    _≤((B*K+1)*C)*(Ideal.absNorm U:ℝ)^eps*P^r := by
      nlinarith [mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (by positivity : (0:ℝ)≤Ideal.absNorm U) eps))
        (Real.rpow_nonneg hP0.le r)]

end SevenEighths.ProbeSelectedPrimeSums
end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Detector.SelectedPrimeIndexed
section
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeSelectedPrimeSums
local notation "O" => ActualEisensteinCubic.O

lemma weighted_slot_bound_indexed (eps a b r d B K : ℝ) (heps : 0<eps)
    (ha : 0<a) (hb : 0<b) (hd : d≤1) (hB : 0≤B) (hK : 0≤K) :
    ∃C : ℝ, 0<C ∧ ∀{ι : Type*} (f : ι→Ideal O), Function.Injective f →
    ∀(U : Ideal O), U≠0 → ∀P : ℝ, 1≤P →
    ∀(S : Finset ι), (∀i∈S,f i≠0) → ∀(W : ℝ→ℂ),
      Function.support W⊆Set.Icc a b → (∀y,‖W y‖≤B) →
    ∀(G : ι→ℂ), (∀i∈S,‖G i‖≤K*(if f i∣U then (Ideal.absNorm (f i):ℝ)^d else 1)) →
    ∀z : ℂ, z.re=r →
      (∑i∈S,‖W ((Ideal.absNorm (f i):ℝ)/P)*(Ideal.absNorm (f i):ℂ)^(z-1)*G i‖)
        ≤C*(Ideal.absNorm U:ℝ)^eps*P^r := by
  obtain ⟨C,hC,hmain⟩ := weighted_slot_bound eps a b r d B K heps ha hb hd hB hK
  refine ⟨C,hC,?_⟩
  intro ι f hf U hU P hP S hS W hWS hWB G hG z hz
  let G' : Ideal O→ℂ := Function.extend f G (fun _=>0)
  have he (i : ι) : G' (f i)=G i := hf.extend_apply G (fun _=>0) i
  have hI (I : Ideal O) (hI : I∈S.image f) : I≠0 := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI
    exact hS i hi
  have hg (I : Ideal O) (hI : I∈S.image f) :
      ‖G' I‖≤K*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1) := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI
    rw [he]
    exact hG i hi
  have hh := hmain U hU P hP (S.image f) hI W hWS hWB G' hg z hz
  rw [Finset.sum_image hf.injOn] at hh
  simpa only [he] using hh

end SevenEighths.ProbeSelectedPrimeSums
end

end OAI

end


