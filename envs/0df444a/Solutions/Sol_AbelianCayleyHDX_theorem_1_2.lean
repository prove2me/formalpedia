-- Prove2me | solution 1 for AbelianCayleyHDX.theorem_1_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:23:24.611075+00:00
-- url     : https://prove2.me/submissions/6cc08219-81a0-48cc-bc39-ba42715c0cf3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AbelianCayleyHDX_lemma_2_3
import Theorems.Thm_AbelianCayleyHDX_eq_2_3_parameters
import Theorems.Thm_AbelianCayleyHDX_section_2_4_relation_complex_nonempty
import Theorems.Thm_AbelianCayleyHDX_lemma_2_1
import Theorems.Thm_AbelianCayleyHDX_lemma_2_2
import Theorems.Thm_AbelianCayleyHDX_explicit_relation_complexes
import Definitions.Def_AbelianCayleyHDX_cayleyGraph
import Definitions.Def_AbelianCayleyHDX_IsCayleyComplex
import Definitions.Def_AbelianCayleyHDX_IsTranslationInvariant
import Definitions.Def_AbelianCayleyHDX_HasLocalSpectralNorm
import Definitions.Def_AbelianCayleyHDX_IsExplicitFamily
import Definitions.Def_ReplParity_Vec

open Filter
open ReplParity (Vec)

namespace AbelianCayleyHDX.R12

/-- `n ≥ 2h·2^{t/3}` forces `n ≥ 2^{(t+1)/3}`. -/
lemma two_pow_le (h t : ℕ) (n : ℝ) (hh : 1 ≤ h)
    (hn : 2 * (h : ℝ) * (2 : ℝ) ^ ((t : ℝ) / 3) ≤ n) :
    (2 : ℝ) ^ (((t : ℝ) + 1) / 3) ≤ n := by
  have e : (2 : ℝ) ^ (((t : ℝ) + 1) / 3) = (2 : ℝ) ^ ((1 : ℝ) / 3) * (2 : ℝ) ^ ((t : ℝ) / 3) := by
    rw [← Real.rpow_add (by norm_num)]; congr 1; ring
  have h13 : (2 : ℝ) ^ ((1 : ℝ) / 3) ≤ 2 := by
    calc (2 : ℝ) ^ ((1 : ℝ) / 3) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have h2h : (2 : ℝ) ≤ 2 * (h : ℝ) := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  have hpos : 0 < (2 : ℝ) ^ ((t : ℝ) / 3) := by positivity
  rw [e]
  calc (2 : ℝ) ^ ((1 : ℝ) / 3) * (2 : ℝ) ^ ((t : ℝ) / 3) ≤ 2 * (2 : ℝ) ^ ((t : ℝ) / 3) :=
        mul_le_mul_of_nonneg_right h13 hpos.le
    _ ≤ 2 * (h : ℝ) * (2 : ℝ) ^ ((t : ℝ) / 3) := mul_le_mul_of_nonneg_right h2h hpos.le
    _ ≤ n := hn

/-- The number of columns is at most `n^{6h}`. -/
lemma M_le (h t n : ℕ) (hh : 1 ≤ h)
    (hn : 2 * (h : ℝ) * (2 : ℝ) ^ ((t : ℝ) / 3) ≤ (n : ℝ)) :
    ((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t) ≤ n ^ (6 * h) := by
  have h1 : ((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t) ≤ 2 ^ (2 * h * (t + 1)) := by
    calc ((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t) ≤ (2 ^ h) ^ 2 * (2 ^ h) ^ (2 * t) :=
          Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ = 2 ^ (2 * h * (t + 1)) := by rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
  have h2 : (2 : ℝ) ^ (2 * h * (t + 1)) ≤ (n : ℝ) ^ (6 * h) := by
    have hb := two_pow_le h t (n : ℝ) hh hn
    have hp : 0 ≤ (2 : ℝ) ^ (((t : ℝ) + 1) / 3) := by positivity
    calc (2 : ℝ) ^ (2 * h * (t + 1)) = ((2 : ℝ) ^ (((t : ℝ) + 1) / 3)) ^ (6 * h) := by
          rw [← Real.rpow_mul_natCast (by norm_num), ← Real.rpow_natCast]
          congr 1; push_cast; ring
      _ ≤ (n : ℝ) ^ (6 * h) := pow_le_pow_left₀ hp hb _
  have : ((((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t) : ℕ) : ℝ) ≤ ((n ^ (6 * h) : ℕ) : ℝ) := by
    calc ((((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t) : ℕ) : ℝ) ≤ ((2 ^ (2 * h * (t + 1)) : ℕ) : ℝ) :=
          by exact_mod_cast h1
      _ = (2 : ℝ) ^ (2 * h * (t + 1)) := by push_cast; ring
      _ ≤ (n : ℝ) ^ (6 * h) := h2
      _ = ((n ^ (6 * h) : ℕ) : ℝ) := by push_cast; ring
  exact_mod_cast this

lemma logb_le (n : ℝ) (hn : 1 ≤ n) : Real.logb 2 n ≤ 2 * n := by
  rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
  have h1 := Real.log_le_sub_one_of_pos (by linarith : 0 < n)
  have h2 := Real.log_two_gt_d9
  nlinarith

end AbelianCayleyHDX.R12

open AbelianCayleyHDX AbelianCayleyHDX.R12 in
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → ∃ Cl : ℝ, 0 < Cl ∧
      ∃ (n : ℕ → ℕ) (S : ∀ j, Finset (Vec (n j))) (T : ∀ j, Finset (Finset (Vec (n j)))),
        Tendsto n atTop atTop ∧
        (∀ j, IsCayleyComplex (S j) (T j) ∧ IsTranslationInvariant (T j) ∧
          (cayleyGraph (S j)).Connected ∧ HasLocalSpectralNorm (T j) lam ∧
          ((S j).card : ℝ) ≤ (n j : ℝ) ^ (C * Real.log (2 + 1 / lam)) ∧
          ∀ e ∈ edges (T j), (triCount (T j) e : ℝ) ≤ Cl * Real.log (n j)) ∧
        IsExplicitFamily n S T := by
  obtain ⟨-, ⟨C2, hC2, hpar⟩, hpar3⟩ := eq_2_3_parameters
  refine ⟨6 * C2, by positivity, fun lam hlam => ?_⟩
  obtain ⟨h, hq8, hqlam, -, hhC⟩ := hpar lam hlam
  have hh : 1 ≤ h := by
    rcases Nat.eq_zero_or_pos h with rfl | hpos
    · norm_num at hq8
    · exact hpos
  obtain ⟨C, hC, t, ht, R, ρ, H, hprop, Mach, p, hMach⟩ := lemma_2_3 lam hlam h hq8 hqlam
  -- the dimension `n_j = dim ker H_j`
  have hnbound : ∀ j, 2 * (h : ℝ) * (2 : ℝ) ^ ((t j : ℝ) / 3) ≤
      (Module.finrank (ZMod 2) (kerF2 (H j)) : ℝ) := fun j => (hprop j).2.2.2.1
  have hMle : ∀ j, ((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t j) ≤
      (Polynomial.X ^ (6 * h) : Polynomial ℕ).eval (Module.finrank (ZMod 2) (kerF2 (H j))) := by
    intro j
    simp only [Polynomial.eval_pow, Polynomial.eval_X]
    exact M_le h (t j) _ hh (hnbound j)
  obtain ⟨φ, hφ, hexp⟩ := explicit_relation_complexes R
    (fun j => ((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t j)) ρ H (fun j => (hprop j).2.2.1) Mach p hMach
    (Polynomial.X ^ (6 * h)) hMle
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨6 * C / Real.log 2, by positivity, fun j => Module.finrank (ZMod 2) (kerF2 (H j)),
    fun j => Finset.univ.image fun i => φ j (Pi.single i 1),
    fun j => relationComplex (H j) (φ j), ?_, fun j => ?_, hexp⟩
  · -- `n_j → ∞`
    rw [tendsto_atTop_atTop]
    intro b
    obtain ⟨i, hi⟩ := (tendsto_atTop_atTop.1 ht) (6 * b)
    refine ⟨i, fun a ha => ?_⟩
    have h1 := hi a ha
    have hn1 : (1 : ℝ) ≤ Module.finrank (ZMod 2) (kerF2 (H a)) := by
      have := hnbound a
      have : (1 : ℝ) ≤ 2 * (h : ℝ) * (2 : ℝ) ^ ((t a : ℝ) / 3) := by
        have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ ((t a : ℝ) / 3) :=
          Real.one_le_rpow (by norm_num) (by positivity)
        have h3 : (1 : ℝ) ≤ h := by exact_mod_cast hh
        nlinarith
      linarith
    have h3 := hpar3 h (t a) _ hh (hnbound a)
    have h4 := logb_le _ hn1
    have : (t a : ℝ) ≤ 6 * (Module.finrank (ZMod 2) (kerF2 (H a)) : ℝ) := by linarith
    have : t a ≤ 6 * Module.finrank (ZMod 2) (kerF2 (H a)) := by exact_mod_cast this
    omega
  -- the properties of each member
  obtain ⟨-, hρC, hgood, hnb, G, hGc, d, hGreg, hPH, hnorm⟩ := hprop j
  have hMpos : 0 < ((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t j) := by
    apply Nat.mul_pos
    · have : 8 ≤ 2 ^ h := hq8
      have : 64 ≤ (2 ^ h) ^ 2 := by nlinarith
      omega
    · positivity
  have : Nonempty (Fin (((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t j))) := ⟨⟨0, hMpos⟩⟩
  obtain ⟨hsurj, hkerφ⟩ := hφ j
  obtain ⟨hs0, hsinj, hspan, -, -, -, hCay, hTI, hcard, htri, hlinkV, hlinkW, hlinkG⟩ :=
    section_2_4_relation_complex_nonempty (H j) (ρ j) hgood (φ j) hsurj hkerφ
  set S := Finset.univ.image fun i => φ j (Pi.single i 1) with hSdef
  have hSne : S.Nonempty := hCay.2.1
  have hS0 : (0 : Vec _) ∉ S := hCay.2.2.1
  have hρpos : 0 < ρ j := hgood.2.2.1
  have hn1 : (1 : ℝ) ≤ Module.finrank (ZMod 2) (kerF2 (H j)) := by
    have : (1 : ℝ) ≤ 2 * (h : ℝ) * (2 : ℝ) ^ ((t j : ℝ) / 3) := by
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ ((t j : ℝ) / 3) :=
        Real.one_le_rpow (by norm_num) (by positivity)
      have h3 : (1 : ℝ) ≤ h := by exact_mod_cast hh
      nlinarith
    linarith
  refine ⟨hCay, hTI, ?_, ?_, ?_, ?_⟩
  · -- connectivity of the one-skeleton
    have := (lemma_2_1 S hSne hS0).2.2.2.2
    rw [this, hSdef, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact hspan
  · -- local spectral norm via Lemma 2.2
    apply lemma_2_2 (H j) (ρ j) hgood (φ j) hsurj hkerφ lam _ hnorm
    -- connectivity of the link at the identity
    rw [hlinkV]
    have hpos : ∀ a b, G.Adj a b →
        0 < linkWeight (relationComplex (H j) (φ j)) 0 (φ j (Pi.single a 1))
          (φ j (Pi.single b 1)) := by
      intro a b hab
      rw [hlinkG]
      have hd : 0 < d := by
        classical
        rw [← hGreg a]
        convert (G.degree_pos_iff_exists_adj a).2 ⟨b, hab⟩
      have e1 : ((Htilde (H j)).transpose * Htilde (H j) - (ρ j : ℝ) • (1 : Matrix _ _ ℝ)) =
          (2 * (ρ j : ℝ)) • PH (H j) (ρ j) := by
        unfold PH
        rw [smul_smul]
        have : (2 * (ρ j : ℝ)) * (1 / (2 * (ρ j : ℝ))) = 1 := by
          field_simp
        rw [this, one_smul]
      rw [e1, hPH, smul_smul, Matrix.smul_apply, SimpleGraph.adjMatrix_apply, if_pos hab]
      have : (0 : ℝ) < d := by exact_mod_cast hd
      have : (0 : ℝ) < ρ j := by exact_mod_cast hρpos
      positivity
    intro u hu v hv
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hv
    have hr := (SimpleGraph.reachable_iff_reflTransGen a b).1 (hGc.preconnected a b)
    refine Relation.ReflTransGen.lift (fun i => φ j (Pi.single i 1)) ?_ a b hr
    intro x y hxy
    exact ⟨Finset.mem_image_of_mem _ (Finset.mem_univ x),
      Finset.mem_image_of_mem _ (Finset.mem_univ y), hpos x y hxy⟩
  · -- Cayley degree
    rw [hcard, Fintype.card_fin]
    have hM := M_le h (t j) _ hh hnb
    have hexp : (6 * h : ℝ) ≤ 6 * C2 * Real.log (2 + 1 / lam) := by
      have := hhC; nlinarith
    calc ((((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t j) : ℕ) : ℝ)
        ≤ ((Module.finrank (ZMod 2) (kerF2 (H j)) ^ (6 * h) : ℕ) : ℝ) := by exact_mod_cast hM
      _ = (Module.finrank (ZMod 2) (kerF2 (H j)) : ℝ) ^ ((6 * h : ℕ) : ℝ) := by
          rw [Real.rpow_natCast]; push_cast; ring
      _ ≤ (Module.finrank (ZMod 2) (kerF2 (H j)) : ℝ) ^ (6 * C2 * Real.log (2 + 1 / lam)) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by push_cast; linarith)
  · -- triangles per edge
    intro e he
    rw [htri e he]
    have h3 := hpar3 h (t j) _ hh hnb
    rw [Real.logb] at h3
    push_cast
    have : (2 * (ρ j : ℝ)) ≤ 2 * (C * (t j : ℝ)) := by linarith
    calc 2 * (ρ j : ℝ) ≤ 2 * (C * (t j : ℝ)) := this
      _ ≤ 2 * (C * (3 * (Real.log (Module.finrank (ZMod 2) (kerF2 (H j))) / Real.log 2))) := by
          gcongr
      _ = 6 * C / Real.log 2 * Real.log (Module.finrank (ZMod 2) (kerF2 (H j))) := by ring
