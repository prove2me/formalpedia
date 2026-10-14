-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0455_parallel1
-- name    : PNT_ZeroFree_433_0455_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:24:12.190054+00:00
-- url     : https://prove2.me/theorems/945f7457-915a-4a54-b693-5eeb81812976
-- title:
--   Zero-free region foundations: Hecke.PrimeAmplitudeBins [0455_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Hecke.PrimeAmplitudeBins
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/PrimeAmplitudeBins.lean#L11-L161

import Definitions.Def_PNT_ZeroFree_433_0150
import Definitions.Def_PNT_ZeroFree_433_0292_parallel1
import Definitions.Def_PNT_ZeroFree_433_0293_parallel1
import Definitions.Def_PNT_ZeroFree_433_0294_parallel1
import Definitions.Def_PNT_ZeroFree_433_0306_parallel1
import Definitions.Def_PNT_ZeroFree_433_0326_parallel1
import Definitions.Def_PNT_ZeroFree_433_0339_parallel1
import Definitions.Def_PNT_ZeroFree_433_0366_parallel1
import Definitions.Def_PNT_ZeroFree_433_0369_parallel1
import Definitions.Def_PNT_ZeroFree_433_0377_parallel1
import Definitions.Def_PNT_ZeroFree_433_0391_parallel1
import Definitions.Def_PNT_ZeroFree_433_0439_parallel1
import Definitions.Def_PNT_ZeroFree_433_0464_parallel1
import Definitions.Def_PNT_ZeroFree_433_0480_parallel1
import Definitions.Def_PNT_ZeroFree_433_0600_parallel1
import Definitions.Def_PNT_ZeroFree_433_0616_parallel1
import Definitions.Def_PNT_ZeroFree_433_0623_parallel1

/- Supporting zero-free-region lemmas, grouped by intact source scopes.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/PrimeAmplitudeBins.lean#L11-L161
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Hecke.PrimeAmplitudeBins
section
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckePrimeAmplitudeBins

def amplitude (P cap mesh : ℝ) (Q : ℂ) : ℝ :=
  if Q=0 then 0 else min cap (max 0 (mesh*(⌊Real.log ‖Q‖/(mesh*Real.log P)⌋ : ℤ)))

theorem amplitude_bounds (P cap mesh : ℝ) (Q : ℂ) (hcap : 0≤cap) :
    0≤amplitude P cap mesh Q ∧ amplitude P cap mesh Q≤cap := by
  unfold amplitude
  split_ifs
  · exact ⟨le_rfl,hcap⟩
  · exact ⟨le_min hcap (le_max_left _ _),min_le_left _ _⟩

theorem amplitude_upper (P cap mesh : ℝ) (Q : ℂ) (hP : 1<P) (hm : 0<mesh)
    (hbound : ‖Q‖≤P^(cap+mesh)) :
    ‖Q‖≤P^(amplitude P cap mesh Q+mesh) := by
  by_cases hQ : Q=0
  · subst Q
    simp only [norm_zero,amplitude,ite_true,zero_add]
    exact Real.rpow_nonneg (by linarith) _
  have hx : 0<‖Q‖ := norm_pos_iff.mpr hQ
  have hl : 0<Real.log P := Real.log_pos hP
  have hd : 0<mesh*Real.log P := mul_pos hm hl
  let n : ℤ := ⌊Real.log ‖Q‖/(mesh*Real.log P)⌋
  by_cases hc : cap≤max 0 (mesh*(n : ℝ))
  · simpa [amplitude,hQ,n,min_eq_left hc] using hbound
  · have he : amplitude P cap mesh Q=max 0 (mesh*(n : ℝ)) := by
      simp only [amplitude,if_neg hQ]
      exact min_eq_right (le_of_not_ge hc)
    rw [he]
    apply (Real.le_rpow_iff_log_le hx (by linarith : 0<P)).mpr
    have hn : Real.log ‖Q‖/(mesh*Real.log P)<(n : ℝ)+1 := Int.lt_floor_add_one _
    have hn' := (div_lt_iff₀ hd).mp hn
    have hg := mul_le_mul_of_nonneg_right (le_max_right 0 (mesh*(n : ℝ))) hl.le
    nlinarith

theorem amplitude_lower (P cap mesh : ℝ) (Q : ℂ) (hP : 1<P) (hm : 0<mesh)
    (hg : 0<amplitude P cap mesh Q) :
    P^(amplitude P cap mesh Q)≤‖Q‖ := by
  have hQ : Q≠0 := by intro h; simp [amplitude,h] at hg
  have hx : 0<‖Q‖ := norm_pos_iff.mpr hQ
  have hl : 0<Real.log P := Real.log_pos hP
  have hd : 0<mesh*Real.log P := mul_pos hm hl
  let n : ℤ := ⌊Real.log ‖Q‖/(mesh*Real.log P)⌋
  have hpos : 0<mesh*(n : ℝ) := by
    have hmin : amplitude P cap mesh Q≤max 0 (mesh*(n : ℝ)) := by
      simp only [amplitude,if_neg hQ]
      exact min_le_right _ _
    have ht : 0<max 0 (mesh*(n : ℝ)) := hg.trans_le hmin
    exact (lt_max_iff.mp ht).resolve_left (lt_irrefl _)
  have he : amplitude P cap mesh Q=min cap (mesh*(n : ℝ)) := by
    simp only [amplitude,if_neg hQ]
    rw [max_eq_right hpos.le]
  have hn : (n : ℝ)≤Real.log ‖Q‖/(mesh*Real.log P) := Int.floor_le _
  have hn' := (le_div_iff₀ hd).mp hn
  have hb : amplitude P cap mesh Q*Real.log P≤Real.log ‖Q‖ := by
    rw [he]
    have hh := mul_le_mul_of_nonneg_right (min_le_right cap (mesh*(n : ℝ))) hl.le
    nlinarith
  have hpow : 0<P^(amplitude P cap mesh Q) := Real.rpow_pos_of_pos (by linarith) _
  apply (Real.log_le_log_iff hpow hx).mp
  rw [Real.log_rpow (by linarith : 0<P)]
  exact hb

def labels (cap mesh : ℝ) : Finset ℝ :=
  insert 0 (insert cap ((Finset.Icc (0 : ℤ) ⌈cap/mesh⌉).image (fun n : ℤ => mesh*(n : ℝ))))

theorem amplitude_mem_labels (P cap mesh : ℝ) (Q : ℂ) (hm : 0<mesh) :
    amplitude P cap mesh Q∈labels cap mesh := by
  by_cases hQ : Q=0
  · simp [amplitude,hQ,labels]
  let n : ℤ := ⌊Real.log ‖Q‖/(mesh*Real.log P)⌋
  have he : amplitude P cap mesh Q=min cap (max 0 (mesh*(n : ℝ))) := by
    simp only [amplitude,if_neg hQ]
    rfl
  rw [he]
  by_cases hc : cap≤max 0 (mesh*(n : ℝ))
  · rw [min_eq_left hc]
    simp [labels]
  rw [min_eq_right (le_of_not_ge hc)]
  by_cases hn : mesh*(n : ℝ)≤0
  · rw [max_eq_left hn]
    simp [labels]
  have hn' : 0<mesh*(n : ℝ) := lt_of_not_ge hn
  rw [max_eq_right hn'.le]
  apply Finset.mem_insert_of_mem
  apply Finset.mem_insert_of_mem
  apply Finset.mem_image.mpr
  refine ⟨n,Finset.mem_Icc.mpr ⟨?_,?_⟩,rfl⟩
  · have hh : (0 : ℝ)≤(n : ℝ) := by nlinarith
    exact_mod_cast hh
  · have hh : (n : ℝ)≤cap/mesh := by
      apply (le_div_iff₀ hm).mpr
      have hlt : max 0 (mesh*(n : ℝ))<cap := lt_of_not_ge hc
      have : mesh*(n : ℝ)≤max 0 (mesh*(n : ℝ)) := le_max_right _ _
      nlinarith
    exact_mod_cast hh.trans (Int.le_ceil _)

theorem squared_spike (U w cap mesh : ℝ) (Q : ℂ) (hU : 1<U) (hw : 0<w)
    (hm : 0<mesh) (hg : 0<amplitude (U^w) cap mesh Q) :
    U^(2*w*amplitude (U^w) cap mesh Q)≤‖Q‖^2 := by
  have hP : 1<U^w := Real.one_lt_rpow hU hw
  have hb := amplitude_lower (U^w) cap mesh Q hP hm hg
  have hs := (sq_le_sq₀ (Real.rpow_nonneg (Real.rpow_nonneg (by linarith) _) _) (norm_nonneg _)).mpr hb
  convert! hs using 1
  rw [←Real.rpow_natCast,←Real.rpow_mul (Real.rpow_nonneg (by linarith : (0 : ℝ)≤U) _),
    ←Real.rpow_mul (by linarith : (0 : ℝ)≤U)]
  congr 1
  ring

theorem product_upper {ι : Type*} (slots : Finset ι) (w : ι→ℝ) (Q : ι→ℂ)
    (U cap mesh : ℝ) (hU : 1<U) (hm : 0<mesh)
    (hw : ∀ i∈slots, 0<w i)
    (hQ : ∀ i∈slots, ‖Q i‖≤(U^(w i))^(cap+mesh)) :
    ‖∏ i∈slots, Q i‖≤U^((∑ i∈slots, w i*amplitude (U^(w i)) cap mesh (Q i))+
      mesh*(∑ i∈slots,w i)) := by
  rw [norm_prod]
  calc
    _ ≤ ∏ i∈slots, (U^(w i))^(amplitude (U^(w i)) cap mesh (Q i)+mesh) :=
      Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i hi =>
        amplitude_upper _ cap mesh (Q i) (Real.one_lt_rpow hU (hw i hi)) hm (hQ i hi))
    _ = ∏ i∈slots, U^(w i*(amplitude (U^(w i)) cap mesh (Q i)+mesh)) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact (Real.rpow_mul (by linarith : (0 : ℝ)≤U) _ _).symm
    _ = _ := by
      rw [←Real.rpow_sum_of_pos (by linarith : 0<U)]
      congr 1
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib,←Finset.sum_mul, mul_comm mesh]

theorem common_bin_selection {ι : Type*} (slots : Finset ι) (w g : ι→ℝ)
    (U δ mesh binWidth q z : ℝ) (hU : 1<U) (hδ : 0≤δ) (hmesh : 0≤mesh)
    (hbin : 0<binWidth) (hw : ∀ i∈slots, 0<w i) (hwm : ∀ i∈slots, w i≤mesh)
    (hg : ∀ i∈slots, 0≤g i ∧ g i≤δ/2)
    (hq : 0≤q) (hqδ : q≤δ/2) (hz : 0≤z)
    (hzs : z≤∑ i∈slots,w i) (hmean : q*(∑ i∈slots,w i)≤∑ i∈slots,w i*g i) :
    ∃ T : Finset ι, T⊆slots ∧ (∀ i∈T,0<g i) ∧ (∑ i∈T,w i)≤z ∧
      ∀ Q : ι→ℂ, (∀ i∈slots,amplitude (U^(w i)) (δ/2) binWidth (Q i)=g i) →
        U^(2*q*z-δ*mesh)≤‖∏ i∈T,Q i‖^2 := by
  have hm : q*(∑ i∈slots,w i)≤∑ i∈slots,w i*max (g i) 0 := by
    convert! hmean using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [max_eq_left (hg i hi).1]
  obtain ⟨T,hTs,hTp,hTw,hTb⟩ := HeckeDetectorSlotSelection.selected_product_spike
    slots w g U δ mesh q z hU.le hδ hmesh (fun i hi => (hw i hi).le) hwm
    (fun i hi => (hg i hi).2) hq hqδ hz hzs hm
  refine ⟨T,hTs,hTp,hTw,?_⟩
  intro Q hQ
  apply hTb Q
  intro i hi hgi
  rw [←hQ i hi] at hgi ⊢
  exact squared_spike U (w i) (δ/2) binWidth (Q i) hU (hw i hi) hbin hgi

end SevenEighths.HeckePrimeAmplitudeBins

end

end OAI

end


