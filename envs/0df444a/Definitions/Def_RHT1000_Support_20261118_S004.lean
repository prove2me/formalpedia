-- Prove2me | Definitions.Def_RHT1000_Support_20261118_S004
-- name    : RHT1000_Support_20261118_S004
-- status  : Definition
-- author  : @bueno_ricardo
-- created : 2026-11-18T19:34:44.405241+00:00
-- url     : https://prove2.me/theorems/80210729-e318-459d-ab85-8f1004114f2e
-- title:
--   Suporte completo para T1000 — bloco 9 de 10
-- statement:
--   Definições e lemas auxiliares completos para a prova finita T1000. Este bloco não afirma sozinho a conclusão T1000 nem RH. A divisão reduz o tempo de compilação sem substituir demonstrações por hipóteses.
-- source:
--   Código adaptado de Salvatore Mercuri e Bhavik Mehta, smmercuri/zeta, tag v1-1e8 (3dab648), com dependências e avisos de autoria preservados. Fonte histórica integral T1000: https://axle.axiommath.ai/check#r=d2dcb520-c50a-44dc-a527-de0f7a51b892 . Reorganização em módulos ordinários para compatibilidade com Prove2Me; atribuição da adaptação: projeto Desenvolvimento RH, Ricardo Marangoni Brandão Bueno.

import Definitions.Def_RHT1000_Support_20261118_S003
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
section CertificatePort146
section
namespace Enclosure
theorem isNear_verify_le (X q eps : ℝ) (cneg qneg : Bool) (cn cd rn rd qn qd en ed : ℕ)
    (hcert : Real.IsNear X cneg cn cd rn rd)
    (hq : q = sfrac qneg qn qd) (heps : eps = sfrac false en ed)
    (hcd : Nat.ble 1 cd) (hrd : Nat.ble 1 rd) (hqd : Nat.ble 1 qd) (hed : Nat.ble 1 ed)
    (hlo : Nat.ble ((((numPos qneg qn).mul ((ed.mul cd).mul rd)).add
              ((numNeg cneg cn).mul ((qd.mul ed).mul rd))).add
              (rn.mul ((cd.mul qd).mul ed)))
            ((((numPos cneg cn).mul ((qd.mul ed).mul rd)).add
              ((numNeg qneg qn).mul ((ed.mul cd).mul rd))).add
              (en.mul ((qd.mul cd).mul rd))))
    (hhi : Nat.ble ((((numPos cneg cn).mul ((qd.mul ed).mul rd)).add
              ((numNeg qneg qn).mul ((ed.mul cd).mul rd))).add
              (rn.mul ((cd.mul qd).mul ed)))
            ((((numPos qneg qn).mul ((ed.mul cd).mul rd)).add
              ((numNeg cneg cn).mul ((qd.mul ed).mul rd))).add
              (en.mul ((qd.mul cd).mul rd)))) :
    |X - q| ≤ eps := by
  subst hq heps
  simp only [Nat.ble_eq, Nat.add_eq, Nat.mul_eq] at hlo hhi
  have hcdR : (0:ℝ) < cd := pos_real_of_ble hcd
  have hrdR : (0:ℝ) < rd := pos_real_of_ble hrd
  have hqdR : (0:ℝ) < qd := pos_real_of_ble hqd
  have hedR : (0:ℝ) < ed := pos_real_of_ble hed
  have heps : sfrac false en ed = (en : ℝ) / ed := by simp [sfrac]
  rw [Real.IsNear, abs_le] at hcert
  have hloR : sfrac qneg qn qd - (en : ℝ) / ed ≤ sfrac cneg cn cd - (rn : ℝ) / rd := by
    rw [sfrac_eq_parts qneg qn qd, sfrac_eq_parts cneg cn cd,
      div_sub_div _ _ hqdR.ne' hedR.ne', div_sub_div _ _ hcdR.ne' hrdR.ne',
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hc : ((numPos qneg qn * (ed * cd * rd) + numNeg cneg cn * (qd * ed * rd)
                + rn * (cd * qd * ed) : ℕ) : ℝ)
            ≤ ((numPos cneg cn * (qd * ed * rd) + numNeg qneg qn * (ed * cd * rd)
                + en * (qd * cd * rd) : ℕ) : ℝ) := by exact_mod_cast hlo
    push_cast at hc ⊢; nlinarith [hc]
  have hhiR : sfrac cneg cn cd + (rn : ℝ) / rd ≤ sfrac qneg qn qd + (en : ℝ) / ed := by
    rw [sfrac_eq_parts qneg qn qd, sfrac_eq_parts cneg cn cd,
      div_add_div _ _ hcdR.ne' hrdR.ne', div_add_div _ _ hqdR.ne' hedR.ne',
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hc : ((numPos cneg cn * (qd * ed * rd) + numNeg qneg qn * (ed * cd * rd)
                + rn * (cd * qd * ed) : ℕ) : ℝ)
            ≤ ((numPos qneg qn * (ed * cd * rd) + numNeg cneg cn * (qd * ed * rd)
                + en * (qd * cd * rd) : ℕ) : ℝ) := by exact_mod_cast hhi
    push_cast at hc ⊢; nlinarith [hc]
  rw [heps, abs_le]
  exact ⟨by linarith [hcert.1, hloR], by linarith [hcert.2, hhiR]⟩
theorem isNear_verify_le_center (X q eps : ℝ) (neg : Bool) (cn cd rn rd qn qd en ed : ℕ)
    (hcert : Real.IsNear X neg cn cd rn rd)
    (hq : q = sfrac neg qn qd) (heps : eps = sfrac false en ed)
    (hcd : Nat.ble 1 cd) (hqd : Nat.ble 1 qd) (hrd : Nat.ble 1 rd) (hed : Nat.ble 1 ed)
    (hsame : (qn.mul cd).beq (cn.mul qd)) (hle : Nat.ble (rn.mul ed) (en.mul rd)) :
    |X - q| ≤ eps := by
  subst hq heps
  simp only [Nat.beq_eq, Nat.ble_eq, Nat.mul_eq] at hsame hle
  have hcdR : (0:ℝ) < cd := pos_real_of_ble hcd
  have hqdR : (0:ℝ) < qd := pos_real_of_ble hqd
  have hrdR : (0:ℝ) < rd := pos_real_of_ble hrd
  have hedR : (0:ℝ) < ed := pos_real_of_ble hed
  have hqc : (qn : ℝ) / qd = (cn : ℝ) / cd := by
    rw [div_eq_div_iff hqdR.ne' hcdR.ne']; exact_mod_cast hsame
  have hqcenter : sfrac neg qn qd = sfrac neg cn cd := by unfold sfrac; rw [hqc]
  rw [hqcenter]
  have hcert' : |X - sfrac neg cn cd| ≤ (rn : ℝ) / rd := hcert
  refine hcert'.trans ?_
  rw [show sfrac false en ed = (en : ℝ) / ed from by simp [sfrac], div_le_div_iff₀ hrdR hedR]
  exact_mod_cast hle
theorem Real.IsNear.neg_val {x : ℝ} {cn cd rn rd : ℕ}
    (h : Real.IsNear x true cn cd rn rd)
    (hcd : Nat.ble 1 cd) (hrd : Nat.ble 1 rd)
    (hlt : Nat.blt (rn.mul cd) (cn.mul rd)) : x < 0 := by
  simp only [Nat.blt_eq, Nat.mul_eq] at hlt
  have hcdR : (0:ℝ) < cd := pos_real_of_ble hcd
  have hrdR : (0:ℝ) < rd := pos_real_of_ble hrd
  have hu := h.upper
  rw [sfrac_true_div, neg_div] at hu
  have hcross : (rn : ℝ) * cd < (cn : ℝ) * rd := by exact_mod_cast hlt
  have hlt' : (rn : ℝ) / rd < (cn : ℝ) / cd := by
    rw [div_lt_div_iff₀ hrdR hcdR]
    linarith
  linarith
theorem Real.IsNear.pos_val {x : ℝ} {cn cd rn rd : ℕ}
    (h : Real.IsNear x false cn cd rn rd)
    (hcd : Nat.ble 1 cd) (hrd : Nat.ble 1 rd)
    (hlt : Nat.blt (rn.mul cd) (cn.mul rd)) : 0 < x := by
  simp only [Nat.blt_eq, Nat.mul_eq] at hlt
  have hcdR : (0:ℝ) < cd := pos_real_of_ble hcd
  have hrdR : (0:ℝ) < rd := pos_real_of_ble hrd
  have hl := h.lower
  rw [sfrac_false_div] at hl
  have hcross : (rn : ℝ) * cd < (cn : ℝ) * rd := by exact_mod_cast hlt
  have hlt' : (rn : ℝ) / rd < (cn : ℝ) / cd := by
    rw [div_lt_div_iff₀ hrdR hcdR]
    linarith
  linarith
theorem norm_gt_of_isNear {x e : ℝ} {nx ne' : Bool} {cnx cdx rnx rdx cne cde rne rde : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) (he : Real.IsNear e ne' cne cde rne rde)
    (hcdx : Nat.ble 1 cdx) (hrdx : Nat.ble 1 rdx) (hcde : Nat.ble 1 cde) (hrde : Nat.ble 1 rde)
    (h : Nat.blt ((((numPos ne' cne).mul (rde.mul (cdx.mul rdx))).add
            (rne.mul (cde.mul (cdx.mul rdx)))).add
            (rnx.mul (cde.mul (rde.mul cdx))))
          ((cnx.mul (cde.mul (rde.mul rdx))).add
            ((numNeg ne' cne).mul (rde.mul (cdx.mul rdx))))) :
    ‖x‖ > e := by
  simp only [Nat.blt_eq, Nat.mul_eq, Nat.add_eq] at h
  have hcdxR : (0:ℝ) < cdx := pos_real_of_ble hcdx
  have hrdxR : (0:ℝ) < rdx := pos_real_of_ble hrdx
  have hcdeR : (0:ℝ) < cde := pos_real_of_ble hcde
  have hrdeR : (0:ℝ) < rde := pos_real_of_ble hrde
  have habs : (cnx : ℝ) / cdx - (rnx : ℝ) / rdx ≤ |x| := by
    have h1 : |sfrac nx cnx cdx| - |x - sfrac nx cnx cdx| ≤ |x| := by
      have := abs_sub_abs_le_abs_sub (sfrac nx cnx cdx) x
      have habs2 : |sfrac nx cnx cdx - x| = |x - sfrac nx cnx cdx| := abs_sub_comm _ _
      linarith [this, habs2 ▸ this]
    rw [abs_sfrac] at h1
    have h2 : |x - sfrac nx cnx cdx| ≤ (rnx : ℝ) / rdx := hx
    linarith
  have hup := he.upper
  have hcR : ((numPos ne' cne * (rde * (cdx * rdx)) + rne * (cde * (cdx * rdx))
        + rnx * (cde * (rde * cdx)) : ℕ) : ℝ)
      < ((cnx * (cde * (rde * rdx)) + numNeg ne' cne * (rde * (cdx * rdx)) : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at hcR
  have hkey : sfrac ne' cne cde + (rne : ℝ) / rde < (cnx : ℝ) / cdx - (rnx : ℝ) / rdx := by
    rw [sfrac_eq_parts]
    rw [div_add_div _ _ hcdeR.ne' hrdeR.ne', div_sub_div _ _ hcdxR.ne' hrdxR.ne',
      div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hcR]
  rw [Real.norm_eq_abs, gt_iff_lt]
  linarith
theorem gt_of_isNear {x e : ℝ} {nx ne' : Bool} {cnx cdx rnx rdx cne cde rne rde : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) (he : Real.IsNear e ne' cne cde rne rde)
    (hcdx : Nat.ble 1 cdx) (hrdx : Nat.ble 1 rdx) (hcde : Nat.ble 1 cde) (hrde : Nat.ble 1 rde)
    (h : Nat.blt ((((numPos ne' cne).mul (rde.mul (cdx.mul rdx))).add
            (rne.mul (cde.mul (cdx.mul rdx)))).add
          (((numNeg nx cnx).mul (rdx.mul (cde.mul rde))).add
            (rnx.mul (cdx.mul (cde.mul rde)))))
          (((numPos nx cnx).mul (rdx.mul (cde.mul rde))).add
            ((numNeg ne' cne).mul (rde.mul (cdx.mul rdx))))) :
    x > e := by
  simp only [Nat.blt_eq, Nat.mul_eq, Nat.add_eq] at h
  have hcdxR : (0:ℝ) < cdx := pos_real_of_ble hcdx
  have hrdxR : (0:ℝ) < rdx := pos_real_of_ble hrdx
  have hcdeR : (0:ℝ) < cde := pos_real_of_ble hcde
  have hrdeR : (0:ℝ) < rde := pos_real_of_ble hrde
  have hlo : sfrac nx cnx cdx - (rnx : ℝ) / rdx ≤ x := by
    have h1 : |x - sfrac nx cnx cdx| ≤ (rnx : ℝ) / rdx := hx
    linarith [(abs_le.mp h1).1]
  have hup : e ≤ sfrac ne' cne cde + (rne : ℝ) / rde := he.upper
  have hcR : ((numPos ne' cne * (rde * (cdx * rdx)) + rne * (cde * (cdx * rdx))
        + (numNeg nx cnx * (rdx * (cde * rde)) + rnx * (cdx * (cde * rde))) : ℕ) : ℝ)
      < ((numPos nx cnx * (rdx * (cde * rde))
        + numNeg ne' cne * (rde * (cdx * rdx)) : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at hcR
  have hkey : sfrac ne' cne cde + (rne : ℝ) / rde < sfrac nx cnx cdx - (rnx : ℝ) / rdx := by
    rw [sfrac_eq_parts, sfrac_eq_parts,
      div_add_div _ _ hcdeR.ne' hrdeR.ne', div_sub_div _ _ hcdxR.ne' hrdxR.ne',
      div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hcR]
  linarith
end Enclosure
end
end CertificatePort146


section CertificatePort147
section
namespace Enclosure
theorem Real.IsNear.of_eq {x y : ℝ} {n : Bool} {cn cd rn rd : ℕ}
    (he : x = y) (h : Real.IsNear y n cn cd rn rd) : Real.IsNear x n cn cd rn rd := by
  rw [he]; exact h
theorem sum_Ico_consec_real (f : ℕ → ℝ) (a m b : ℕ)
    (hab : Nat.ble a m = true) (hmb : Nat.ble m b = true) :
    (∑ i ∈ Finset.Ico a b, f i) = (∑ i ∈ Finset.Ico a m, f i) + (∑ i ∈ Finset.Ico m b, f i) :=
  (Finset.sum_Ico_consecutive f (Nat.le_of_ble_eq_true hab) (Nat.le_of_ble_eq_true hmb)).symm
theorem sum_Ico_width_one_real (f : ℕ → ℝ) (a b : ℕ) (h : Nat.beq b (a.add 1) = true) :
    (∑ i ∈ Finset.Ico a b, f i) = f a := by
  have hb : b = a + 1 := Nat.eq_of_beq_eq_true h
  subst hb
  rw [Finset.sum_Ico_succ_top (Nat.le_refl a), Finset.Ico_self, Finset.sum_empty, zero_add]
theorem Real.IsNear.sum_Ico_empty (f : ℕ → ℝ) (a b : ℕ) (h : Nat.beq a b = true) :
    Real.IsNear (∑ i ∈ Finset.Ico a b, f i) false (nat_lit 0) (nat_lit 1) (nat_lit 0)
      (nat_lit 1) := by
  have hb : a = b := Nat.eq_of_beq_eq_true h
  subst hb
  rw [Finset.Ico_self, Finset.sum_empty]
  simp [Real.IsNear, sfrac]
theorem sum_range_eq_Ico_real (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, f i) = (∑ i ∈ Finset.Ico 0 n, f i) := by
  rw [Finset.range_eq_Ico]
end Enclosure
end
end CertificatePort147


section CertificatePort148
section
end
end CertificatePort148


section CertificatePort149
section
namespace BSN
open Enclosure
open _root_.Real
def argRoundOk (u v u' v' Dp D : ℕ) : Bool :=
  Nat.beq
    (Nat.add (Nat.sub (nat_lit 1) v)
    (Nat.add (Nat.sub (nat_lit 1) v')
    (Nat.add (Nat.sub (nat_lit 1) Dp)
    (Nat.add (Nat.sub (nat_lit 1) D)
    (Nat.add (Nat.sub (u'.mul v) (u.mul v'))
             (Nat.sub (Nat.add (Nat.mul (D.mul Dp) (Nat.sub (u.mul v') (u'.mul v)))
                               (Nat.mul D (v.mul v')))
                      (Nat.mul Dp (v.mul v'))))))))
    (nat_lit 0)
private theorem argRoundOk_parts {u v u' v' Dp D : ℕ} (hs : argRoundOk u v u' v' Dp D = true) :
    1 ≤ v ∧ 1 ≤ v' ∧ 1 ≤ Dp ∧ 1 ≤ D ∧ u' * v ≤ u * v' ∧
      D * Dp * (u * v' - u' * v) + D * (v * v') ≤ Dp * (v * v') := by
  simp only [argRoundOk, Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at hs
  obtain ⟨z1, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z2, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z3, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z4, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z5, z6⟩ := Nat.add_eq_zero_iff.mp hs
  exact ⟨Nat.le_of_sub_eq_zero z1, Nat.le_of_sub_eq_zero z2, Nat.le_of_sub_eq_zero z3,
    Nat.le_of_sub_eq_zero z4, Nat.le_of_sub_eq_zero z5, Nat.le_of_sub_eq_zero z6⟩
private theorem arg_round_bound {u v u' v' Dp D : ℕ}
    (hv : 1 ≤ v) (hv' : 1 ≤ v') (hDp : 1 ≤ Dp) (hD : 1 ≤ D)
    (hle : u' * v ≤ u * v')
    (hmain : D * Dp * (u * v' - u' * v) + D * (v * v') ≤ Dp * (v * v')) :
    |(u : ℝ) / v - (u' : ℝ) / v'| + 1 / Dp ≤ 1 / D := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hv'R : (0 : ℝ) < v' := by exact_mod_cast hv'
  have hDpR : (0 : ℝ) < Dp := by exact_mod_cast hDp
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hleR : ((u' : ℝ) * v) ≤ (u : ℝ) * v' := by exact_mod_cast hle
  have hnn : (0 : ℝ) ≤ (u : ℝ) * v' - (u' : ℝ) * v := by linarith
  have hsub : ((u * v' - u' * v : ℕ) : ℝ) = (u : ℝ) * v' - (u' : ℝ) * v := by
    have hle' : (u' * v : ℕ) ≤ (u * v' : ℕ) := hle
    push_cast [Nat.cast_sub hle']
    ring
  have hrw : (u : ℝ) / v - (u' : ℝ) / v' = ((u : ℝ) * v' - (u' : ℝ) * v) / (v * v') := by
    field_simp
  have habs : |(u : ℝ) / v - (u' : ℝ) / v'| = ((u : ℝ) * v' - (u' : ℝ) * v) / (v * v') := by
    rw [hrw]
    exact abs_of_nonneg (div_nonneg hnn (by positivity))
  have hmainR : (D : ℝ) * Dp * ((u : ℝ) * v' - (u' : ℝ) * v) + D * (v * v') ≤ Dp * (v * v') := by
    have hc : ((D * Dp * (u * v' - u' * v) + D * (v * v') : ℕ) : ℝ)
        ≤ ((Dp * (v * v') : ℕ) : ℝ) := by
      exact_mod_cast hmain
    push_cast [hsub] at hc
    linarith
  rw [← sub_nonneg, habs]
  have key : (1 : ℝ) / D - (((u : ℝ) * v' - (u' : ℝ) * v) / (v * v') + 1 / Dp)
      = ((Dp : ℝ) * (v * v') - ((D : ℝ) * Dp * ((u : ℝ) * v' - (u' : ℝ) * v) + D * (v * v')))
        / ((D : ℝ) * Dp * (v * v')) := by
    field_simp
  rw [key]
  exact div_nonneg (by linarith) (by positivity)
theorem cos_arg_round {n : Bool} {cn cd : ℕ} (u v u' v' Dp D : ℕ)
    (h : Real.IsNear (Real.cos ((u' : ℝ) / v')) n cn cd 1 Dp)
    (hs : argRoundOk u v u' v' Dp D = true) :
    Real.IsNear (Real.cos ((u : ℝ) / v)) n cn cd 1 D := by
  obtain ⟨hv, hv', hDp, hD, hle, hmain⟩ := argRoundOk_parts hs
  have hb := arg_round_bound hv hv' hDp hD hle hmain
  have hlip : |Real.cos ((u : ℝ) / v) - Real.cos ((u' : ℝ) / v')| ≤ |(u : ℝ) / v - (u' : ℝ) / v'| :=
    Real.abs_cos_sub_cos_le _ _
  have h' : |Real.cos ((u' : ℝ) / v') - sfrac n cn cd| ≤ (1 : ℝ) / Dp := by
    have hh := h
    simp only [Real.IsNear] at hh
    push_cast at hh
    exact hh
  have htri := abs_sub_le (Real.cos ((u : ℝ) / v)) (Real.cos ((u' : ℝ) / v')) (sfrac n cn cd)
  have hres : |Real.cos ((u : ℝ) / v) - sfrac n cn cd| ≤ ((1 : ℕ) : ℝ) / ((D : ℕ) : ℝ) := by
    push_cast
    linarith
  exact hres
theorem sin_arg_round {n : Bool} {cn cd : ℕ} (u v u' v' Dp D : ℕ)
    (h : Real.IsNear (Real.sin ((u' : ℝ) / v')) n cn cd 1 Dp)
    (hs : argRoundOk u v u' v' Dp D = true) :
    Real.IsNear (Real.sin ((u : ℝ) / v)) n cn cd 1 D := by
  obtain ⟨hv, hv', hDp, hD, hle, hmain⟩ := argRoundOk_parts hs
  have hb := arg_round_bound hv hv' hDp hD hle hmain
  have hlip : |Real.sin ((u : ℝ) / v) - Real.sin ((u' : ℝ) / v')| ≤ |(u : ℝ) / v - (u' : ℝ) / v'| :=
    Real.abs_sin_sub_sin_le _ _
  have h' : |Real.sin ((u' : ℝ) / v') - sfrac n cn cd| ≤ (1 : ℝ) / Dp := by
    have hh := h
    simp only [Real.IsNear] at hh
    push_cast at hh
    exact hh
  have htri := abs_sub_le (Real.sin ((u : ℝ) / v)) (Real.sin ((u' : ℝ) / v')) (sfrac n cn cd)
  have hres : |Real.sin ((u : ℝ) / v) - sfrac n cn cd| ≤ ((1 : ℕ) : ℝ) / ((D : ℕ) : ℝ) := by
    push_cast
    linarith
  exact hres
theorem sin_quad0 (r : ℝ) (q : ℤ) :
    Real.sin (r + (4 * (q : ℝ)) * (π / 2)) = Real.sin r := by
  have e : r + (4 * (q : ℝ)) * (π / 2) = r + (q : ℝ) * (2 * π) := by ring
  rw [e, sin_add_int_mul_two_pi]
theorem sin_quad1 (r : ℝ) (q : ℤ) :
    Real.sin (r + (4 * (q : ℝ) + 1) * (π / 2)) = Real.cos r := by
  have e : r + (4 * (q : ℝ) + 1) * (π / 2) = (r + π / 2) + (q : ℝ) * (2 * π) := by ring
  rw [e, sin_add_int_mul_two_pi, sin_add_pi_div_two]
theorem sin_quad2 (r : ℝ) (q : ℤ) :
    Real.sin (r + (4 * (q : ℝ) + 2) * (π / 2)) = -Real.sin r := by
  have e : r + (4 * (q : ℝ) + 2) * (π / 2) = (r + π) + (q : ℝ) * (2 * π) := by ring
  rw [e, sin_add_int_mul_two_pi, sin_add_pi]
theorem sin_quad3 (r : ℝ) (q : ℤ) :
    Real.sin (r + (4 * (q : ℝ) + 3) * (π / 2)) = -Real.cos r := by
  have e : r + (4 * (q : ℝ) + 3) * (π / 2) = ((r + π / 2) + π) + (q : ℝ) * (2 * π) := by ring
  rw [e, sin_add_int_mul_two_pi, sin_add_pi, sin_add_pi_div_two]
theorem sin_triple_step (θ q qnew : ℝ) (D Rho D' : ℝ)
    (hq1 : |q| ≤ 1)
    (hq : |Real.sin θ - q| ≤ 1 / D)
    (hround : |(3 * q - 4 * q ^ 3) - qnew| ≤ 1 / Rho)
    (hcomb : 15 * (1 / D) + 1 / Rho ≤ 1 / D') :
    |Real.sin (3 * θ) - qnew| ≤ 1 / D' := by
  rw [Real.sin_three_mul]
  have hs1 : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have hfirst : |3 * Real.sin θ - 4 * Real.sin θ ^ 3 - (3 * q - 4 * q ^ 3)| ≤ 15 * (1 / D) := by
    have hfac : 3 * Real.sin θ - 4 * Real.sin θ ^ 3 - (3 * q - 4 * q ^ 3)
        = (Real.sin θ - q) * (3 - 4 * (Real.sin θ ^ 2 + Real.sin θ * q + q ^ 2)) := by ring
    rw [hfac, abs_mul]
    have hsum : |Real.sin θ ^ 2 + Real.sin θ * q + q ^ 2| ≤ 3 := by
      calc |Real.sin θ ^ 2 + Real.sin θ * q + q ^ 2|
          ≤ |Real.sin θ ^ 2| + |Real.sin θ * q| + |q ^ 2| :=
            (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
        _ ≤ 1 + 1 + 1 := by
            gcongr
            · rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hs1
            · rw [abs_mul]; exact mul_le_one₀ hs1 (abs_nonneg _) hq1
            · rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hq1
        _ = 3 := by norm_num
    have hc : |3 - 4 * (Real.sin θ ^ 2 + Real.sin θ * q + q ^ 2)| ≤ 15 :=
      calc |3 - 4 * (Real.sin θ ^ 2 + Real.sin θ * q + q ^ 2)|
          ≤ |(3 : ℝ)| + |4 * (Real.sin θ ^ 2 + Real.sin θ * q + q ^ 2)| := abs_sub _ _
        _ = 3 + 4 * |Real.sin θ ^ 2 + Real.sin θ * q + q ^ 2| := by
            rw [abs_mul]; norm_num
        _ ≤ 3 + 4 * 3 := by gcongr
        _ = 15 := by norm_num
    calc |Real.sin θ - q| * |3 - 4 * (Real.sin θ ^ 2 + Real.sin θ * q + q ^ 2)|
        ≤ (1 / D) * 15 := by
          apply mul_le_mul hq hc (abs_nonneg _)
          exact le_trans (abs_nonneg _) hq
      _ = 15 * (1 / D) := by ring
  calc |3 * Real.sin θ - 4 * Real.sin θ ^ 3 - qnew|
      ≤ |3 * Real.sin θ - 4 * Real.sin θ ^ 3 - (3 * q - 4 * q ^ 3)|
          + |(3 * q - 4 * q ^ 3) - qnew| := abs_sub_le _ _ _
    _ ≤ 15 * (1 / D) + 1 / Rho := add_le_add hfirst hround
    _ ≤ 1 / D' := hcomb
theorem sin_triple_step_dyadic (nq : Bool) (cq Q : ℕ) (nq' : Bool) (cq' Q' D D' : ℕ) (θ : ℝ)
    (hQ : Nat.ble 1 Q) (hQ' : Nat.ble 1 Q') (hD : Nat.ble 1 D) (hD' : Nat.ble 1 D')
    (hq1a : (numPos nq cq).ble ((numNeg nq cq).add Q))
    (hq1b : (numNeg nq cq).ble ((numPos nq cq).add Q))
    (hround1 : (((numPos nq' cq').mul (Q.pow 3)).add
        (((((Nat.mul 3 (numNeg nq cq)).mul (Q.pow 2)).add
          (Nat.mul 4 ((numPos nq cq).pow 3))).add
          ((Nat.mul 12 (numPos nq cq)).mul ((numNeg nq cq).pow 2))).mul Q')).ble
      ((((((Nat.mul 3 (numPos nq cq)).mul (Q.pow 2)).add
        ((Nat.mul 12 ((numPos nq cq).pow 2)).mul (numNeg nq cq))).add
        (Nat.mul 4 ((numNeg nq cq).pow 3))).mul Q').add ((numNeg nq' cq').mul (Q.pow 3))))
    (hround2 : ((((((Nat.mul 3 (numPos nq cq)).mul (Q.pow 2)).add
        ((Nat.mul 12 ((numPos nq cq).pow 2)).mul (numNeg nq cq))).add
        (Nat.mul 4 ((numNeg nq cq).pow 3))).mul Q').add ((numNeg nq' cq').mul (Q.pow 3))).blt
      ((((numPos nq' cq').mul (Q.pow 3)).add (Q.pow 3)).add
        (((((Nat.mul 3 (numNeg nq cq)).mul (Q.pow 2)).add
          (Nat.mul 4 ((numPos nq cq).pow 3))).add
          ((Nat.mul 12 (numPos nq cq)).mul ((numNeg nq cq).pow 2))).mul Q')))
    (hcomb : (((Nat.mul 15 Q').add D).mul D').ble (D.mul Q'))
    (hstep : Real.IsNear (Real.sin θ) nq cq Q 1 D) :
    Real.IsNear (Real.sin (3 * θ)) nq' cq' Q' 1 D' := by
  set mp := numPos nq cq with hmp_def
  set mn := numNeg nq cq with hmn_def
  set mp' := numPos nq' cq' with hmp'_def
  set mn' := numNeg nq' cq' with hmn'_def
  rw [Real.IsNear, Nat.cast_one, sfrac_eq_parts nq cq Q, ← hmp_def, ← hmn_def] at hstep
  rw [Real.IsNear, Nat.cast_one, sfrac_eq_parts nq' cq' Q', ← hmp'_def, ← hmn'_def]
  simp only [Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq,
    Nat.pow_eq] at hq1a hq1b hround1 hround2 hcomb
  have hQr : (0 : ℝ) < Q := pos_real_of_ble hQ
  have hQ'r : (0 : ℝ) < Q' := pos_real_of_ble hQ'
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  have hD'r : (0 : ℝ) < D' := pos_real_of_ble hD'
  have hQne : (Q : ℝ) ≠ 0 := ne_of_gt hQr
  have hQ'ne : (Q' : ℝ) ≠ 0 := ne_of_gt hQ'r
  set q : ℝ := ((mp : ℝ) - mn) / Q with hq_def
  set qn : ℝ := ((mp' : ℝ) - mn') / Q' with hqn_def
  have hq1 : |q| ≤ 1 := by
    rw [hq_def, abs_div, abs_of_pos hQr, div_le_one hQr, abs_le]
    refine ⟨?_, ?_⟩
    · have : (mn : ℝ) ≤ (mp : ℝ) + Q := by exact_mod_cast hq1b
      linarith
    · have : (mp : ℝ) ≤ (mn : ℝ) + Q := by exact_mod_cast hq1a
      linarith
  have C1z : ((mp' : ℤ) * Q ^ 3 + (3 * mn * Q ^ 2 + 4 * mp ^ 3 + 12 * mp * mn ^ 2) * Q')
      ≤ ((3 * mp * Q ^ 2 + 12 * mp ^ 2 * mn + 4 * mn ^ 3) * Q' + mn' * Q ^ 3) := by
    exact_mod_cast hround1
  have C2z : ((3 * (mp : ℤ) * Q ^ 2 + 12 * mp ^ 2 * mn + 4 * mn ^ 3) * Q' + mn' * Q ^ 3)
      < ((mp' : ℤ) * Q ^ 3 + Q ^ 3 + (3 * mn * Q ^ 2 + 4 * mp ^ 3 + 12 * mp * mn ^ 2) * Q') := by
    exact_mod_cast hround2
  set M : ℤ := 3 * ((mp : ℤ) - mn) * Q ^ 2 - 4 * ((mp : ℤ) - mn) ^ 3 with hM_def
  set s' : ℤ := (mp' : ℤ) - mn' with hs'_def
  have hN0 : (0 : ℤ) ≤ M * Q' - s' * Q ^ 3 := by
    have hexp : M * (Q' : ℤ) - s' * Q ^ 3
        = ((3 * (mp : ℤ) * Q ^ 2 + 12 * mp ^ 2 * mn + 4 * mn ^ 3) * Q' + mn' * Q ^ 3)
          - ((mp' : ℤ) * Q ^ 3 + (3 * mn * Q ^ 2 + 4 * mp ^ 3 + 12 * mp * mn ^ 2) * Q') := by
      rw [hM_def, hs'_def]; ring
    rw [hexp]; linarith [C1z]
  have hN1 : M * (Q' : ℤ) - s' * Q ^ 3 < Q ^ 3 := by
    have hexp : M * (Q' : ℤ) - s' * Q ^ 3 - Q ^ 3
        = ((3 * (mp : ℤ) * Q ^ 2 + 12 * mp ^ 2 * mn + 4 * mn ^ 3) * Q' + mn' * Q ^ 3)
          - ((mp' : ℤ) * Q ^ 3 + Q ^ 3
                + (3 * mn * Q ^ 2 + 4 * mp ^ 3 + 12 * mp * mn ^ 2) * Q') := by
      rw [hM_def, hs'_def]; ring
    linarith [C2z, hexp]
  have hround : |(3 * q - 4 * q ^ 3) - qn| ≤ 1 / (Q' : ℝ) := by
    have hval : 3 * q - 4 * q ^ 3 - qn
        = ((M : ℝ) * Q' - (s' : ℝ) * Q ^ 3) / ((Q : ℝ) ^ 3 * Q') := by
      rw [hq_def, hqn_def, hM_def, hs'_def]
      push_cast
      field_simp
    rw [hval]
    have hden : (0 : ℝ) < (Q : ℝ) ^ 3 * Q' := by positivity
    have hN0r : (0 : ℝ) ≤ (M : ℝ) * Q' - (s' : ℝ) * Q ^ 3 := by exact_mod_cast hN0
    have hN1r : (M : ℝ) * Q' - (s' : ℝ) * Q ^ 3 < Q ^ 3 := by exact_mod_cast hN1
    rw [abs_of_nonneg (div_nonneg hN0r (le_of_lt hden)), div_le_div_iff₀ hden hQ'r, one_mul]
    have hmul : ((M : ℝ) * Q' - (s' : ℝ) * Q ^ 3) * Q' ≤ (Q : ℝ) ^ 3 * Q' :=
      mul_le_mul_of_nonneg_right (le_of_lt hN1r) (le_of_lt hQ'r)
    linarith [hmul]
  have hcombr : 15 * (1 / (D : ℝ)) + 1 / (Q' : ℝ) ≤ 1 / (D' : ℝ) := by
    have hlhs : 15 * (1 / (D : ℝ)) + 1 / (Q' : ℝ) = (15 * (Q' : ℝ) + D) / ((D : ℝ) * Q') := by
      field_simp
    rw [hlhs, div_le_div_iff₀ (mul_pos hDr hQ'r) hD'r, one_mul]
    have key : (15 * (Q' : ℝ) + D) * D' ≤ (D : ℝ) * Q' := by exact_mod_cast hcomb
    linarith [key]
  exact sin_triple_step θ q qn (D : ℝ) (Q' : ℝ) (D' : ℝ) hq1 hstep hround hcombr
theorem sin_triple_step_arg (a dj dj1 : ℕ) (nq : Bool) (cq Q : ℕ) (nq' : Bool) (cq' Q' D D' : ℕ)
    (hdj1 : dj1.beq (Nat.mul 3 dj))
    (hdj : Nat.ble 1 dj)
    (hQ : Nat.ble 1 Q) (hQ' : Nat.ble 1 Q') (hD : Nat.ble 1 D) (hD' : Nat.ble 1 D')
    (hq1a : (numPos nq cq).ble ((numNeg nq cq).add Q))
    (hq1b : (numNeg nq cq).ble ((numPos nq cq).add Q))
    (hround1 : (((numPos nq' cq').mul (Q.pow 3)).add
        (((((Nat.mul 3 (numNeg nq cq)).mul (Q.pow 2)).add
          (Nat.mul 4 ((numPos nq cq).pow 3))).add
          ((Nat.mul 12 (numPos nq cq)).mul ((numNeg nq cq).pow 2))).mul Q')).ble
      ((((((Nat.mul 3 (numPos nq cq)).mul (Q.pow 2)).add
        ((Nat.mul 12 ((numPos nq cq).pow 2)).mul (numNeg nq cq))).add
        (Nat.mul 4 ((numNeg nq cq).pow 3))).mul Q').add ((numNeg nq' cq').mul (Q.pow 3))))
    (hround2 : ((((((Nat.mul 3 (numPos nq cq)).mul (Q.pow 2)).add
        ((Nat.mul 12 ((numPos nq cq).pow 2)).mul (numNeg nq cq))).add
        (Nat.mul 4 ((numNeg nq cq).pow 3))).mul Q').add ((numNeg nq' cq').mul (Q.pow 3))).blt
      ((((numPos nq' cq').mul (Q.pow 3)).add (Q.pow 3)).add
        (((((Nat.mul 3 (numNeg nq cq)).mul (Q.pow 2)).add
          (Nat.mul 4 ((numPos nq cq).pow 3))).add
          ((Nat.mul 12 (numPos nq cq)).mul ((numNeg nq cq).pow 2))).mul Q')))
    (hcomb : (((Nat.mul 15 Q').add D).mul D').ble (D.mul Q'))
    (hstep : Real.IsNear (Real.sin ((a : ℝ) / (dj1 : ℝ))) nq cq Q 1 D) :
    Real.IsNear (Real.sin ((a : ℝ) / (dj : ℝ))) nq' cq' Q' 1 D' := by
  simp only [Nat.beq_eq, Nat.mul_eq] at hdj1
  subst hdj1
  have hdjpos : 0 < dj := pos_of_ble hdj
  have hdjr : (dj : ℝ) ≠ 0 := by exact_mod_cast hdjpos.ne'
  have h3 : (3 : ℝ) * ((a : ℝ) / ((3 * dj : ℕ) : ℝ)) = (a : ℝ) / (dj : ℝ) := by
    push_cast
    field_simp
  rw [Real.IsNear, ← h3, ← Real.IsNear]
  exact sin_triple_step_dyadic nq cq Q nq' cq' Q' D D' ((a : ℝ) / ((3 * dj : ℕ) : ℝ))
    hQ hQ' hD hD' hq1a hq1b hround1 hround2 hcomb hstep
theorem reduce_core_val (F r rc q B inner Dinv : ℝ) (ε : ℝ) (g : ℝ → ℝ)
    (hε : |ε| = 1)
    (hquad : F = ε * g r)
    (hlip : |g r - g rc| ≤ |r - rc|)
    (hB : |r - rc| ≤ B)
    (hinner : |g rc - q| ≤ inner)
    (htot : B + inner ≤ Dinv) :
    |F - ε * q| ≤ Dinv := by
  have h1 : |F - ε * q| ≤ |g r - g rc| + |g rc - q| := by
    rw [hquad]
    calc |ε * g r - ε * q| = |ε| * |g r - q| := by rw [← mul_sub, abs_mul]
      _ = |g r - q| := by rw [hε, one_mul]
      _ ≤ |g r - g rc| + |g rc - q| := abs_sub_le _ _ _
  calc |F - ε * q| ≤ |g r - g rc| + |g rc - q| := h1
    _ ≤ B + inner := add_le_add (hlip.trans hB) hinner
    _ ≤ Dinv := htot
theorem reduce_step_val (F x r rcv Pr val : ℝ) (k E Dp D : ℕ) (ε : ℝ) (g : ℝ → ℝ)
    (hε : |ε| = 1)
    (hquad : F = ε * g r)
    (hr : r = x - (k : ℝ) * (π / 2))
    (hlip : |g r - g rcv| ≤ |r - rcv|)
    (hrc : rcv = x - (k : ℝ) * (Pr / 2))
    (hpi : |Real.pi - Pr| ≤ 1 / (E : ℝ))
    (hinner : |g rcv - val| ≤ 1 / (Dp : ℝ))
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((k.mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble ((Nat.mul 2 E).mul Dp)) :
    |F - ε * val| ≤ 1 / (D : ℝ) := by
  simp only [Nat.ble_eq, Nat.add_eq, Nat.mul_eq] at htot
  have hEr : (0 : ℝ) < E := pos_real_of_ble hE
  have hDpr : (0 : ℝ) < Dp := pos_real_of_ble hDp
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  have hB : |r - rcv| ≤ (k : ℝ) / (2 * E) := by
    rw [hr, hrc]
    have e : (x - (k : ℝ) * (π / 2)) - (x - (k : ℝ) * (Pr / 2)) = (k : ℝ) * (Pr / 2 - π / 2) := by
      ring
    rw [e, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ))]
    have hhalf : |Pr / 2 - π / 2| ≤ 1 / (2 * E) := by
      have e2 : Pr / 2 - π / 2 = -(Real.pi - Pr) / 2 := by ring
      rw [e2, abs_div, abs_neg, abs_two]
      calc |Real.pi - Pr| / 2 ≤ (1 / (E : ℝ)) / 2 := by gcongr
        _ = 1 / (2 * E) := by ring
    calc (k : ℝ) * |Pr / 2 - π / 2| ≤ (k : ℝ) * (1 / (2 * E)) := by gcongr
      _ = (k : ℝ) / (2 * E) := by ring
  have htotR : (k : ℝ) / (2 * E) + 1 / (Dp : ℝ) ≤ 1 / (D : ℝ) := by
    have hc : ((k * D * Dp + 2 * E * D : ℕ) : ℝ) ≤ ((2 * E * Dp : ℕ) : ℝ) := by exact_mod_cast htot
    push_cast at hc
    rw [div_add_div _ _ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hc, hEr, hDpr, hDr]
  exact reduce_core_val F r rcv val ((k : ℝ) / (2 * E)) (1 / Dp) (1 / D) ε g hε hquad
    hlip hB hinner htotR
theorem reduce_quad_val (F x rcv : ℝ) (g : ℝ → ℝ) (ε : ℝ) (Pc PQ : ℕ) (ineg oneg : Bool)
    (icn Qd k E Dp D : ℕ)
    (hε : |ε| = 1)
    (hquad : F = ε * g (x - (k : ℝ) * (π / 2)))
    (hlip : ∀ a b, |g a - g b| ≤ |a - b|)
    (hsign : sfrac oneg icn Qd = ε * sfrac ineg icn Qd)
    (hrc : rcv = x - (k : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (g rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((k.mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear F oneg icn Qd 1 D := by
  rw [Real.IsNear, sfrac_false_div, Nat.cast_one] at hpi
  rw [← sfrac_false_div Pc PQ] at hpi
  rw [Real.IsNear, Nat.cast_one] at hinner
  rw [Real.IsNear, Nat.cast_one, hsign]
  exact reduce_step_val F x (x - (k : ℝ) * (π / 2)) rcv (sfrac false Pc PQ)
    (sfrac ineg icn Qd) k E Dp D ε g hε hquad rfl (hlip _ _) hrc hpi hinner hE hDp hD htot
theorem cos_quad0 (r : ℝ) (q : ℤ) :
    Real.cos (r + (4 * (q : ℝ)) * (π / 2)) = Real.cos r := by
  have e : r + (4 * (q : ℝ)) * (π / 2) = r + (q : ℝ) * (2 * π) := by ring
  rw [e, cos_add_int_mul_two_pi]
theorem cos_quad1 (r : ℝ) (q : ℤ) :
    Real.cos (r + (4 * (q : ℝ) + 1) * (π / 2)) = -Real.sin r := by
  have e : r + (4 * (q : ℝ) + 1) * (π / 2) = (r + π / 2) + (q : ℝ) * (2 * π) := by ring
  rw [e, cos_add_int_mul_two_pi, cos_add_pi_div_two]
theorem cos_quad2 (r : ℝ) (q : ℤ) :
    Real.cos (r + (4 * (q : ℝ) + 2) * (π / 2)) = -Real.cos r := by
  have e : r + (4 * (q : ℝ) + 2) * (π / 2) = (r + π) + (q : ℝ) * (2 * π) := by ring
  rw [e, cos_add_int_mul_two_pi, cos_add_pi]
theorem cos_quad3 (r : ℝ) (q : ℤ) :
    Real.cos (r + (4 * (q : ℝ) + 3) * (π / 2)) = Real.sin r := by
  have e : r + (4 * (q : ℝ) + 3) * (π / 2) = ((r + π / 2) + π) + (q : ℝ) * (2 * π) := by ring
  rw [e, cos_add_int_mul_two_pi, cos_add_pi, cos_add_pi_div_two, neg_neg]
theorem sin_reduce0 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.sin rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : ((((Nat.mul 4 qq).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.sin x) ineg icn Qd 1 D :=
  reduce_quad_val (Real.sin x) x rcv Real.sin 1 Pc PQ ineg ineg icn Qd (4 * qq) E Dp D abs_one
    (by rw [one_mul, ← sin_quad0 (x - ((4 * qq : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 1; push_cast; ring)
    Real.abs_sin_sub_sin_le (one_mul _).symm hrc hpi hinner hE hDp hD htot
theorem sin_reduce1 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq + 1 : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.cos rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((((Nat.mul 4 qq).succ).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.sin x) ineg icn Qd 1 D :=
  reduce_quad_val (Real.sin x) x rcv Real.cos 1 Pc PQ ineg ineg icn Qd (4 * qq + 1) E Dp D abs_one
    (by rw [one_mul, ← sin_quad1 (x - ((4 * qq + 1 : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 1; push_cast; ring)
    Real.abs_cos_sub_cos_le (one_mul _).symm hrc hpi hinner hE hDp hD htot
theorem sin_reduce2 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq + 2 : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.sin rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((((Nat.mul 4 qq).add 2).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.sin x) (!ineg) icn Qd 1 D :=
  reduce_quad_val (Real.sin x) x rcv Real.sin (-1) Pc PQ ineg (!ineg) icn Qd (4 * qq + 2) E Dp D
    ((abs_neg 1).trans abs_one)
    (by rw [neg_one_mul, ← sin_quad2 (x - ((4 * qq + 2 : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 1; push_cast; ring)
    Real.abs_sin_sub_sin_le ((sfrac_not ineg icn Qd).trans (neg_one_mul _).symm)
    hrc hpi hinner hE hDp hD htot
theorem sin_reduce3 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq + 3 : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.cos rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((((Nat.mul 4 qq).add 3).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.sin x) (!ineg) icn Qd 1 D :=
  reduce_quad_val (Real.sin x) x rcv Real.cos (-1) Pc PQ ineg (!ineg) icn Qd (4 * qq + 3) E Dp D
    ((abs_neg 1).trans abs_one)
    (by rw [neg_one_mul, ← sin_quad3 (x - ((4 * qq + 3 : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 1; push_cast; ring)
    Real.abs_cos_sub_cos_le ((sfrac_not ineg icn Qd).trans (neg_one_mul _).symm)
    hrc hpi hinner hE hDp hD htot
theorem cos_reduce0 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.cos rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : ((((Nat.mul 4 qq).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.cos x) ineg icn Qd 1 D :=
  reduce_quad_val (Real.cos x) x rcv Real.cos 1 Pc PQ ineg ineg icn Qd (4 * qq) E Dp D abs_one
    (by rw [one_mul, ← cos_quad0 (x - ((4 * qq : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 1; push_cast; ring)
    Real.abs_cos_sub_cos_le (one_mul _).symm hrc hpi hinner hE hDp hD htot
theorem cos_reduce1 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq + 1 : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.sin rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((((Nat.mul 4 qq).succ).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.cos x) (!ineg) icn Qd 1 D :=
  reduce_quad_val (Real.cos x) x rcv Real.sin (-1) Pc PQ ineg (!ineg) icn Qd (4 * qq + 1) E Dp D
    ((abs_neg 1).trans abs_one)
    (by rw [neg_one_mul, ← cos_quad1 (x - ((4 * qq + 1 : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 2; push_cast; ring)
    Real.abs_sin_sub_sin_le ((sfrac_not ineg icn Qd).trans (neg_one_mul _).symm)
    hrc hpi hinner hE hDp hD htot
theorem cos_reduce2 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq + 2 : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.cos rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((((Nat.mul 4 qq).add 2).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.cos x) (!ineg) icn Qd 1 D :=
  reduce_quad_val (Real.cos x) x rcv Real.cos (-1) Pc PQ ineg (!ineg) icn Qd (4 * qq + 2) E Dp D
    ((abs_neg 1).trans abs_one)
    (by rw [neg_one_mul, ← cos_quad2 (x - ((4 * qq + 2 : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 2; push_cast; ring)
    Real.abs_cos_sub_cos_le ((sfrac_not ineg icn Qd).trans (neg_one_mul _).symm)
    hrc hpi hinner hE hDp hD htot
theorem cos_reduce3 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq + 3 : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.sin rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((((Nat.mul 4 qq).add 3).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.cos x) ineg icn Qd 1 D :=
  reduce_quad_val (Real.cos x) x rcv Real.sin 1 Pc PQ ineg ineg icn Qd (4 * qq + 3) E Dp D
    abs_one
    (by rw [one_mul, ← cos_quad3 (x - ((4 * qq + 3 : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 1; push_cast; ring)
    Real.abs_sin_sub_sin_le (one_mul _).symm hrc hpi hinner hE hDp hD htot
theorem sin_reduce_arg_pos_rat (a b Pc PQ k u v : ℕ)
    (hlink : ((Nat.mul 2 a).mul PQ).beq (u.add (k.mul (b.mul Pc))))
    (hv : ((Nat.mul 2 b).mul PQ).beq v) (hQ : Nat.ble 1 PQ) (hb : Nat.ble 1 b) :
    ((u : ℝ) / (v : ℝ)) = ((a : ℝ) / (b : ℝ)) - (k : ℝ) * (sfrac false Pc PQ / 2) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq] at hlink hv
  subst hv
  rw [sfrac_false_div]
  have hQr : (0 : ℝ) < PQ := pos_real_of_ble hQ
  have hbr : (0 : ℝ) < b := pos_real_of_ble hb
  have hlinkR : (2 * a * PQ : ℝ) = (u + k * (b * Pc) : ℝ) := by exact_mod_cast hlink
  push_cast
  field_simp
  ring_nf
  linarith [hlinkR]
theorem sin_reduce_arg_pos_rat_q0 (a b Pc PQ qq u v : ℕ)
    (hlink : ((Nat.mul 2 a).mul PQ).beq (u.add ((Nat.mul 4 qq).mul (b.mul Pc))))
    (hv : ((Nat.mul 2 b).mul PQ).beq v) (hQ : Nat.ble 1 PQ) (hb : Nat.ble 1 b) :
    ((u : ℝ) / (v : ℝ)) = ((a : ℝ) / (b : ℝ)) - ((4 * qq : ℕ) : ℝ) * (sfrac false Pc PQ / 2) := by
  simpa using sin_reduce_arg_pos_rat a b Pc PQ (4 * qq) u v hlink hv hQ hb
theorem sin_reduce_arg_pos_rat_q1 (a b Pc PQ qq u v : ℕ)
    (hlink : ((Nat.mul 2 a).mul PQ).beq (u.add ((Nat.add (Nat.mul 4 qq) 1).mul (b.mul Pc))))
    (hv : ((Nat.mul 2 b).mul PQ).beq v) (hQ : Nat.ble 1 PQ) (hb : Nat.ble 1 b) :
    ((u : ℝ) / (v : ℝ)) = ((a : ℝ) / (b : ℝ))
      - ((4 * qq + 1 : ℕ) : ℝ) * (sfrac false Pc PQ / 2) := by
  simpa using sin_reduce_arg_pos_rat a b Pc PQ (4 * qq + 1) u v hlink hv hQ hb
theorem sin_reduce_arg_pos_rat_q2 (a b Pc PQ qq u v : ℕ)
    (hlink : ((Nat.mul 2 a).mul PQ).beq (u.add ((Nat.add (Nat.mul 4 qq) 2).mul (b.mul Pc))))
    (hv : ((Nat.mul 2 b).mul PQ).beq v) (hQ : Nat.ble 1 PQ) (hb : Nat.ble 1 b) :
    ((u : ℝ) / (v : ℝ)) = ((a : ℝ) / (b : ℝ))
      - ((4 * qq + 2 : ℕ) : ℝ) * (sfrac false Pc PQ / 2) := by
  simpa using sin_reduce_arg_pos_rat a b Pc PQ (4 * qq + 2) u v hlink hv hQ hb
theorem sin_reduce_arg_pos_rat_q3 (a b Pc PQ qq u v : ℕ)
    (hlink : ((Nat.mul 2 a).mul PQ).beq (u.add ((Nat.add (Nat.mul 4 qq) 3).mul (b.mul Pc))))
    (hv : ((Nat.mul 2 b).mul PQ).beq v) (hQ : Nat.ble 1 PQ) (hb : Nat.ble 1 b) :
    ((u : ℝ) / (v : ℝ)) = ((a : ℝ) / (b : ℝ))
      - ((4 * qq + 3 : ℕ) : ℝ) * (sfrac false Pc PQ / 2) := by
  simpa using sin_reduce_arg_pos_rat a b Pc PQ (4 * qq + 3) u v hlink hv hQ hb
end BSN
end
end CertificatePort149


section CertificatePort150
section
namespace Enclosure
def Complex.IsNear (z : ℂ)
    (reNeg : Bool) (reCn reCd reRn reRd : ℕ)
    (imNeg : Bool) (imCn imCd imRn imRd : ℕ) : Prop :=
  Real.IsNear z.re reNeg reCn reCd reRn reRd ∧
  Real.IsNear z.im imNeg imCn imCd imRn imRd
theorem Complex.IsNear.re_isNear {z : ℂ}
    {reNeg : Bool} {reCn reCd reRn reRd : ℕ} {imNeg : Bool} {imCn imCd imRn imRd : ℕ}
    (h : Complex.IsNear z reNeg reCn reCd reRn reRd imNeg imCn imCd imRn imRd) :
    Real.IsNear z.re reNeg reCn reCd reRn reRd := h.1
theorem Complex.IsNear.im_isNear {z : ℂ}
    {reNeg : Bool} {reCn reCd reRn reRd : ℕ} {imNeg : Bool} {imCn imCd imRn imRd : ℕ}
    (h : Complex.IsNear z reNeg reCn reCd reRn reRd imNeg imCn imCd imRn imRd) :
    Real.IsNear z.im imNeg imCn imCd imRn imRd := h.2
theorem Complex.IsNear.mk {re im : ℝ}
    {reNeg : Bool} {reCn reCd reRn reRd : ℕ} {imNeg : Bool} {imCn imCd imRn imRd : ℕ}
    (hre : Real.IsNear re reNeg reCn reCd reRn reRd)
    (him : Real.IsNear im imNeg imCn imCd imRn imRd) :
    Complex.IsNear ⟨re, im⟩ reNeg reCn reCd reRn reRd imNeg imCn imCd imRn imRd := ⟨hre, him⟩
theorem Complex.IsNear.neg {z : ℂ}
    {reNeg : Bool} {reCn reCd reRn reRd : ℕ} {imNeg : Bool} {imCn imCd imRn imRd : ℕ}
    (h : Complex.IsNear z reNeg reCn reCd reRn reRd imNeg imCn imCd imRn imRd) :
    Complex.IsNear (-z) (!reNeg) reCn reCd reRn reRd (!imNeg) imCn imCd imRn imRd := by
  obtain ⟨hre, him⟩ := h
  refine ⟨?_, ?_⟩
  · rw [Complex.neg_re]; exact hre.neg
  · rw [Complex.neg_im]; exact him.neg
theorem Complex.IsNear.add {z w : ℂ}
    {reN : Bool} {reCn reCd reRn reRd : ℕ} {imN : Bool} {imCn imCd imRn imRd : ℕ}
    (hre : Real.IsNear (z.re + w.re) reN reCn reCd reRn reRd)
    (him : Real.IsNear (z.im + w.im) imN imCn imCd imRn imRd) :
    Complex.IsNear (z + w) reN reCn reCd reRn reRd imN imCn imCd imRn imRd := by
  refine ⟨?_, ?_⟩
  · rw [Complex.add_re]; exact hre
  · rw [Complex.add_im]; exact him
theorem Complex.IsNear.sub {z w : ℂ}
    {reN : Bool} {reCn reCd reRn reRd : ℕ} {imN : Bool} {imCn imCd imRn imRd : ℕ}
    (hre : Real.IsNear (z.re - w.re) reN reCn reCd reRn reRd)
    (him : Real.IsNear (z.im - w.im) imN imCn imCd imRn imRd) :
    Complex.IsNear (z - w) reN reCn reCd reRn reRd imN imCn imCd imRn imRd := by
  refine ⟨?_, ?_⟩
  · rw [Complex.sub_re]; exact hre
  · rw [Complex.sub_im]; exact him
theorem Complex.IsNear.mul {z w : ℂ}
    {reN : Bool} {reCn reCd reRn reRd : ℕ} {imN : Bool} {imCn imCd imRn imRd : ℕ}
    (hre : Real.IsNear (z.re * w.re - z.im * w.im) reN reCn reCd reRn reRd)
    (him : Real.IsNear (z.re * w.im + z.im * w.re) imN imCn imCd imRn imRd) :
    Complex.IsNear (z * w) reN reCn reCd reRn reRd imN imCn imCd imRn imRd := by
  refine ⟨?_, ?_⟩
  · rw [Complex.mul_re]; exact hre
  · rw [Complex.mul_im]; exact him
def numPosC (neg : Bool) (cn : ℕ) : ℕ := @Bool.rec (fun _ => ℕ) cn 0 neg
def numNegC (neg : Bool) (cn : ℕ) : ℕ := @Bool.rec (fun _ => ℕ) 0 cn neg
theorem numPosC_eq (neg : Bool) (cn : ℕ) : numPosC neg cn = numPos neg cn := by
  cases neg <;> rfl
theorem numNegC_eq (neg : Bool) (cn : ℕ) : numNegC neg cn = numNeg neg cn := by
  cases neg <;> rfl
theorem Complex.IsNear.addLitP {z w : ℂ}
    {nxr : Bool} {cnxr cdxr rnxr rdxr : ℕ} {nxi : Bool} {cnxi cdxi rnxi rdxi : ℕ}
    {nyr : Bool} {cnyr cdyr rnyr rdyr : ℕ} {nyi : Bool} {cnyi cdyi rnyi rdyi : ℕ}
    {nRr : Bool} {cnRr cnRr' cdRr' rnRr' rdRr' : ℕ}
    {nRi : Bool} {cnRi cnRi' cdRi' rnRi' rdRi' : ℕ}
    (h1 : Complex.IsNear z nxr cnxr cdxr rnxr rdxr nxi cnxi cdxi rnxi rdxi)
    (h2 : Complex.IsNear w nyr cnyr cdyr rnyr rdyr nyi cnyi cdyi rnyi rdyi)
    (hcdxr : Nat.ble (nat_lit 1) cdxr) (hcdyr : Nat.ble (nat_lit 1) cdyr)
    (hrdxr : Nat.ble (nat_lit 1) rdxr) (hrdyr : Nat.ble (nat_lit 1) rdyr)
    (hnumr : Nat.beq
      (((numPosC nRr cnRr).add ((numNegC nxr cnxr).mul cdyr)).add
        ((numNegC nyr cnyr).mul cdxr))
      (((numNegC nRr cnRr).add ((numPosC nxr cnxr).mul cdyr)).add
        ((numPosC nyr cnyr).mul cdxr)))
    (hcdRr' : Nat.ble (nat_lit 1) cdRr') (hrdRr' : Nat.ble (nat_lit 1) rdRr')
    (hcr : Nat.beq (cnRr.mul cdRr') (cnRr'.mul (cdxr.mul cdyr)))
    (hrr : Nat.ble (((rnxr.mul rdyr).add (rnyr.mul rdxr)).mul rdRr')
      (rnRr'.mul (rdxr.mul rdyr)))
    (hcdxi : Nat.ble (nat_lit 1) cdxi) (hcdyi : Nat.ble (nat_lit 1) cdyi)
    (hrdxi : Nat.ble (nat_lit 1) rdxi) (hrdyi : Nat.ble (nat_lit 1) rdyi)
    (hnumi : Nat.beq
      (((numPosC nRi cnRi).add ((numNegC nxi cnxi).mul cdyi)).add
        ((numNegC nyi cnyi).mul cdxi))
      (((numNegC nRi cnRi).add ((numPosC nxi cnxi).mul cdyi)).add
        ((numPosC nyi cnyi).mul cdxi)))
    (hcdRi' : Nat.ble (nat_lit 1) cdRi') (hrdRi' : Nat.ble (nat_lit 1) rdRi')
    (hci : Nat.beq (cnRi.mul cdRi') (cnRi'.mul (cdxi.mul cdyi)))
    (hri : Nat.ble (((rnxi.mul rdyi).add (rnyi.mul rdxi)).mul rdRi')
      (rnRi'.mul (rdxi.mul rdyi))) :
    Complex.IsNear (z + w) nRr cnRr' cdRr' rnRr' rdRr' nRi cnRi' cdRi' rnRi' rdRi' := by
  simp only [numPosC_eq, numNegC_eq] at hnumr hnumi
  exact Complex.IsNear.add
    (Real.IsNear.addLit h1.1 h2.1 hcdxr hcdyr hrdxr hrdyr hnumr hcdRr' hrdRr' hcr hrr)
    (Real.IsNear.addLit h1.2 h2.2 hcdxi hcdyi hrdxi hrdyi hnumi hcdRi' hrdRi' hci hri)
theorem Complex.IsNear.subLitP {z w : ℂ}
    {nxr : Bool} {cnxr cdxr rnxr rdxr : ℕ} {nxi : Bool} {cnxi cdxi rnxi rdxi : ℕ}
    {nyr : Bool} {cnyr cdyr rnyr rdyr : ℕ} {nyi : Bool} {cnyi cdyi rnyi rdyi : ℕ}
    {nRr : Bool} {cnRr cnRr' cdRr' rnRr' rdRr' : ℕ}
    {nRi : Bool} {cnRi cnRi' cdRi' rnRi' rdRi' : ℕ}
    (h1 : Complex.IsNear z nxr cnxr cdxr rnxr rdxr nxi cnxi cdxi rnxi rdxi)
    (h2 : Complex.IsNear w nyr cnyr cdyr rnyr rdyr nyi cnyi cdyi rnyi rdyi)
    (hcdxr : Nat.ble (nat_lit 1) cdxr) (hcdyr : Nat.ble (nat_lit 1) cdyr)
    (hrdxr : Nat.ble (nat_lit 1) rdxr) (hrdyr : Nat.ble (nat_lit 1) rdyr)
    (hnumr : Nat.beq
      (((numPosC nRr cnRr).add ((numNegC nxr cnxr).mul cdyr)).add
        ((numPosC nyr cnyr).mul cdxr))
      (((numNegC nRr cnRr).add ((numPosC nxr cnxr).mul cdyr)).add
        ((numNegC nyr cnyr).mul cdxr)))
    (hcdRr' : Nat.ble (nat_lit 1) cdRr') (hrdRr' : Nat.ble (nat_lit 1) rdRr')
    (hcr : Nat.beq (cnRr.mul cdRr') (cnRr'.mul (cdxr.mul cdyr)))
    (hrr : Nat.ble (((rnxr.mul rdyr).add (rnyr.mul rdxr)).mul rdRr')
      (rnRr'.mul (rdxr.mul rdyr)))
    (hcdxi : Nat.ble (nat_lit 1) cdxi) (hcdyi : Nat.ble (nat_lit 1) cdyi)
    (hrdxi : Nat.ble (nat_lit 1) rdxi) (hrdyi : Nat.ble (nat_lit 1) rdyi)
    (hnumi : Nat.beq
      (((numPosC nRi cnRi).add ((numNegC nxi cnxi).mul cdyi)).add
        ((numPosC nyi cnyi).mul cdxi))
      (((numNegC nRi cnRi).add ((numPosC nxi cnxi).mul cdyi)).add
        ((numNegC nyi cnyi).mul cdxi)))
    (hcdRi' : Nat.ble (nat_lit 1) cdRi') (hrdRi' : Nat.ble (nat_lit 1) rdRi')
    (hci : Nat.beq (cnRi.mul cdRi') (cnRi'.mul (cdxi.mul cdyi)))
    (hri : Nat.ble (((rnxi.mul rdyi).add (rnyi.mul rdxi)).mul rdRi')
      (rnRi'.mul (rdxi.mul rdyi))) :
    Complex.IsNear (z - w) nRr cnRr' cdRr' rnRr' rdRr' nRi cnRi' cdRi' rnRi' rdRi' := by
  simp only [numPosC_eq, numNegC_eq] at hnumr hnumi
  refine Complex.IsNear.sub
    (Real.IsNear.subLit h1.1 h2.1 hcdxr hcdyr hrdxr hrdyr ?_ hcdRr' hrdRr' hcr hrr)
    (Real.IsNear.subLit h1.2 h2.2 hcdxi hcdyi hrdxi hrdyi ?_ hcdRi' hrdRi' hci hri)
  · cases nyr <;> simpa [numPos, numNeg] using hnumr
  · cases nyi <;> simpa [numPos, numNeg] using hnumi
theorem Complex.IsNear.recentre2 {z : ℂ}
    {rN : Bool} {rCn rCd rRn rRd : ℕ} {iN : Bool} {iCn iCd iRn iRd : ℕ}
    {rCn' rCd' rRn' rRd' iCn' iCd' iRn' iRd' : ℕ}
    (h : Complex.IsNear z rN rCn rCd rRn rRd iN iCn iCd iRn iRd)
    (hrcd : Nat.ble (nat_lit 1) rCd) (hrcd' : Nat.ble (nat_lit 1) rCd') (hrrd : Nat.ble
          (nat_lit 1) rRd)
    (hrrd' : Nat.ble (nat_lit 1) rRd')
    (hrfloor : Nat.ble (rCn'.mul rCd) (rCn.mul rCd'))
    (hrrad : Nat.ble
      (((rRn.mul (rCd.mul rCd')).add (((rCn.mul rCd').sub (rCn'.mul rCd)).mul rRd)).mul rRd')
      (rRn'.mul (rRd.mul (rCd.mul rCd'))))
    (hicd : Nat.ble (nat_lit 1) iCd) (hicd' : Nat.ble (nat_lit 1) iCd') (hird : Nat.ble
          (nat_lit 1) iRd)
    (hird' : Nat.ble (nat_lit 1) iRd')
    (hifloor : Nat.ble (iCn'.mul iCd) (iCn.mul iCd'))
    (hirad : Nat.ble
      (((iRn.mul (iCd.mul iCd')).add (((iCn.mul iCd').sub (iCn'.mul iCd)).mul iRd)).mul iRd')
      (iRn'.mul (iRd.mul (iCd.mul iCd')))) :
    Complex.IsNear z rN rCn' rCd' rRn' rRd' iN iCn' iCd' iRn' iRd' :=
  ⟨h.1.recentre hrcd hrcd' hrrd hrrd' hrfloor hrrad,
   h.2.recentre hicd hicd' hird hird' hifloor hirad⟩
theorem Complex.IsNear.recentreRe {z : ℂ}
    {rN : Bool} {rCn rCd rRn rRd : ℕ} {iN : Bool} {iCn iCd iRn iRd : ℕ}
    {rCn' rCd' rRn' rRd' : ℕ}
    (h : Complex.IsNear z rN rCn rCd rRn rRd iN iCn iCd iRn iRd)
    (hrcd : Nat.ble (nat_lit 1) rCd) (hrcd' : Nat.ble (nat_lit 1) rCd') (hrrd : Nat.ble
          (nat_lit 1) rRd)
    (hrrd' : Nat.ble (nat_lit 1) rRd')
    (hrfloor : Nat.ble (rCn'.mul rCd) (rCn.mul rCd'))
    (hrrad : Nat.ble
      (((rRn.mul (rCd.mul rCd')).add (((rCn.mul rCd').sub (rCn'.mul rCd)).mul rRd)).mul rRd')
      (rRn'.mul (rRd.mul (rCd.mul rCd')))) :
    Complex.IsNear z rN rCn' rCd' rRn' rRd' iN iCn iCd iRn iRd :=
  ⟨h.1.recentre hrcd hrcd' hrrd hrrd' hrfloor hrrad, h.2⟩
theorem Complex.IsNear.recentreIm {z : ℂ}
    {rN : Bool} {rCn rCd rRn rRd : ℕ} {iN : Bool} {iCn iCd iRn iRd : ℕ}
    {iCn' iCd' iRn' iRd' : ℕ}
    (h : Complex.IsNear z rN rCn rCd rRn rRd iN iCn iCd iRn iRd)
    (hicd : Nat.ble (nat_lit 1) iCd) (hicd' : Nat.ble (nat_lit 1) iCd') (hird : Nat.ble
          (nat_lit 1) iRd)
    (hird' : Nat.ble (nat_lit 1) iRd')
    (hifloor : Nat.ble (iCn'.mul iCd) (iCn.mul iCd'))
    (hirad : Nat.ble
      (((iRn.mul (iCd.mul iCd')).add (((iCn.mul iCd').sub (iCn'.mul iCd)).mul iRd)).mul iRd')
      (iRn'.mul (iRd.mul (iCd.mul iCd')))) :
    Complex.IsNear z rN rCn rCd rRn rRd iN iCn' iCd' iRn' iRd' :=
  ⟨h.1, h.2.recentre hicd hicd' hird hird' hifloor hirad⟩
theorem Complex.IsNear.of_parts {z : ℂ}
    {reNeg : Bool} {reCn reCd reRn reRd : ℕ} {imNeg : Bool} {imCn imCd imRn imRd : ℕ}
    (hre : Real.IsNear z.re reNeg reCn reCd reRn reRd)
    (him : Real.IsNear z.im imNeg imCn imCd imRn imRd) :
    Complex.IsNear z reNeg reCn reCd reRn reRd imNeg imCn imCd imRn imRd := ⟨hre, him⟩
theorem Complex.IsNear.of_eq {z w : ℂ}
    {reNeg : Bool} {reCn reCd reRn reRd : ℕ} {imNeg : Bool} {imCn imCd imRn imRd : ℕ}
    (he : z = w) (h : Complex.IsNear w reNeg reCn reCd reRn reRd imNeg imCn imCd imRn imRd) :
    Complex.IsNear z reNeg reCn reCd reRn reRd imNeg imCn imCd imRn imRd := by
  rw [he]; exact h
theorem Complex.inv_re_eq_mul (z : ℂ) : (z⁻¹).re = z.re * (Complex.normSq z)⁻¹ := by
  rw [Complex.inv_re, div_eq_mul_inv]
theorem Complex.inv_im_eq_mul (z : ℂ) : (z⁻¹).im = -z.im * (Complex.normSq z)⁻¹ := by
  rw [Complex.inv_im, div_eq_mul_inv, neg_mul]
theorem Complex.normSq_eq_mul_add_mul (z : ℂ) :
    Complex.normSq z = z.re * z.re + z.im * z.im := Complex.normSq_apply z
theorem Complex.arg_eq_arctan_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    z.arg = Real.arctan (z.im / z.re) := by
  have h1 : -(Real.pi / 2) < z.arg := Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hz)
  have h2 : z.arg < Real.pi / 2 := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  rw [← Complex.tan_arg z, Real.arctan_tan h1 h2]
theorem clog_re_eq (p r q N M : ℕ) (hq : Nat.ble (nat_lit 1) q = true)
    (hN : Nat.beq N ((p.mul p).add (r.mul r)) = true) (hM : Nat.beq M (q.mul q) = true) :
    (Complex.log ⟨sfrac false p q, sfrac false r q⟩).re
      = sfrac false (nat_lit 1) (nat_lit 2) * Real.log (sfrac false N M) := by
  obtain rfl := Nat.eq_of_beq_eq_true hN
  obtain rfl := Nat.eq_of_beq_eq_true hM
  have hqR : (0 : ℝ) < q := pos_real_of_ble hq
  have hq0 : (q : ℝ) ≠ 0 := hqR.ne'
  have hnorm : Complex.normSq ⟨sfrac false p q, sfrac false r q⟩
      = sfrac false ((p.mul p).add (r.mul r)) (q.mul q) := by
    rw [Complex.normSq_mk]
    simp only [sfrac_false_div, Nat.mul_eq, Nat.add_eq]
    push_cast
    field_simp
  rw [Complex.log_re, Complex.norm_def, hnorm, sfrac_false_div, sfrac_false_div,
    Real.log_sqrt (by positivity)]
  push_cast
  ring
theorem clog_im_eq (p r q : ℕ) (hp : Nat.ble (nat_lit 1) p
      = true) (hq : Nat.ble (nat_lit 1) q = true) :
    (Complex.log ⟨sfrac false p q, sfrac false r q⟩).im = Real.arctan ((r : ℝ) / p) := by
  have hpR : (0 : ℝ) < p := pos_real_of_ble hp
  have hqR : (0 : ℝ) < q := pos_real_of_ble hq
  have hproj_re : (⟨sfrac false p q, sfrac false r q⟩ : ℂ).re = sfrac false p q := rfl
  have hproj_im : (⟨sfrac false p q, sfrac false r q⟩ : ℂ).im = sfrac false r q := rfl
  have hre : (0 : ℝ) < (⟨sfrac false p q, sfrac false r q⟩ : ℂ).re := by
    rw [hproj_re, sfrac_false_div]
    exact div_pos hpR hqR
  rw [Complex.log_im, Complex.arg_eq_arctan_of_re_pos hre, hproj_re, hproj_im,
    sfrac_false_div, sfrac_false_div, div_div_div_cancel_right₀ hqR.ne']
end Enclosure
end
end CertificatePort150


section CertificatePort151
section
open MeasureTheory Real Filter Topology
open scoped Nat
private theorem abs_eq_neg_one_pow_mul {m : ℕ} {y : ℝ} (h : 0 ≤ (-1 : ℝ) ^ m * y) :
    |y| = (-1 : ℝ) ^ m * y := by
  rw [← abs_of_nonneg h, abs_mul, abs_neg_one_pow, one_mul]
private theorem hasSum_one_div_nat_pow_bernoulli (m : ℕ) (hm0 : m ≠ 0) :
    HasSum (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ) ^ (2 * m))
      ((-1 : ℝ) ^ (m + 1) * (2 * π) ^ (2 * m) / 2 / (2 * m)! * (bernoulli (2 * m) : ℝ)) := by
  have h2 : (2 : ℝ) ^ (2 * m - 1) * 2 = 2 ^ (2 * m) := by rw [← pow_succ]; congr 1; lia
  rw [show (-1 : ℝ) ^ (m + 1) * (2 * π) ^ (2 * m) / 2 / (2 * m)! * (bernoulli (2 * m) : ℝ)
        = (-1 : ℝ) ^ (m + 1) * 2 ^ (2 * m - 1) * π ^ (2 * m) * (bernoulli (2 * m) : ℝ)
            / (2 * m)! from by rw [mul_pow, ← h2]; ring]
  exact hasSum_zeta_nat hm0
theorem bernoulliFun_sub_self_eq_tsum_cos (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    bernoulliFun (2 * m) (Int.fract x) - (bernoulli (2 * m) : ℝ)
      = (-1 : ℝ) ^ (m + 1) * (2 * ((2 * m)! : ℝ) / (2 * π) ^ (2 * m))
          * ∑' n : ℕ, (cos (2 * π * n * x) - 1) / (n : ℝ) ^ (2 * m) := by
  have hm0 : m ≠ 0 := by lia
  set B : ℝ := bernoulliFun (2 * m) (Int.fract x)
  set b : ℝ := (bernoulli (2 * m) : ℝ)
  set Cval : ℝ := (-1 : ℝ) ^ (m + 1) * (2 * π) ^ (2 * m) / 2 / (2 * m)! with hCval
  have hfracmem : Int.fract x ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  have hcos : ∀ n : ℕ, cos (2 * π * n * Int.fract x) = cos (2 * π * n * x) := by
    intro n
    have heq : (2 : ℝ) * π * n * x
        = 2 * π * n * Int.fract x + ((n : ℤ) * ⌊x⌋ : ℤ) * (2 * π) := by
      have := Int.floor_add_fract x
      push_cast
      linear_combination (-(2 * π * (n : ℝ))) * this
    rw [heq, Real.cos_add_int_mul_two_pi]
  have hsx : HasSum (fun n : ℕ ↦ 1 / (n : ℝ) ^ (2 * m) * cos (2 * π * n * x)) (Cval * B) := by
    have h := hasSum_one_div_nat_pow_mul_cos hm0 hfracmem
    rw [show (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * m))).eval (Int.fract x)
          = B from rfl] at h
    simpa only [hcos] using h
  have hs0 : HasSum (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ) ^ (2 * m)) (Cval * b) :=
    hasSum_one_div_nat_pow_bernoulli m hm0
  have hdiff := hsx.sub hs0
  have key : (∑' n : ℕ, (cos (2 * π * n * x) - 1) / (n : ℝ) ^ (2 * m)) = Cval * B - Cval * b := by
    rw [← hdiff.tsum_eq]; exact tsum_congr fun n ↦ by ring
  rw [key, hCval]
  set a : ℝ := (-1 : ℝ) ^ (m + 1) with ha
  have ha2 : a * a = 1 := by rw [ha, ← pow_add]; exact Even.neg_one_pow ⟨m + 1, by ring⟩
  have hpi : ((2 * π) ^ (2 * m) : ℝ) ≠ 0 := by positivity
  have hfac : ((2 * m)! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hEF : a * (2 * ((2 * m)! : ℝ) / (2 * π) ^ (2 * m))
      * (a * (2 * π) ^ (2 * m) / 2 / (2 * m)!) = 1 := by
    field_simp; linear_combination ha2
  linear_combination (-(B - b)) * hEF
theorem centered_kernel_mul_sign_nonneg (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    0 ≤ (-1 : ℝ) ^ m * (bernoulliFun (2 * m) (Int.fract x) - (bernoulli (2 * m) : ℝ)) := by
  have hA : (0 : ℝ) ≤ 2 * ((2 * m)! : ℝ) / (2 * π) ^ (2 * m) := by positivity
  have hS : (∑' n : ℕ, (cos (2 * π * n * x) - 1) / (n : ℝ) ^ (2 * m)) ≤ 0 :=
    tsum_nonpos fun n ↦
      div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (Real.cos_le_one _)) (by positivity)
  have hs3 : (-1 : ℝ) ^ m * (-1) ^ (m + 1) = -1 := by
    rw [← pow_add]; exact Odd.neg_one_pow ⟨m, by ring⟩
  rw [bernoulliFun_sub_self_eq_tsum_cos m hm x, ← mul_assoc, ← mul_assoc, hs3]
  linarith [mul_nonneg hA (neg_nonneg.mpr hS)]
private theorem integrableOn_Ioi_of_bound_mul_rpow {f : ℝ → ℝ} (hf : Continuous f)
    (hbound : ∀ x, |f x| ≤ 1) {q N : ℝ} (hq : q < -1) (hN : 0 < N) :
    IntegrableOn (fun x ↦ f x * x ^ q) (Set.Ioi N) := by
  refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt hq hN)
    ((hf.continuousOn.mul (fun x hx ↦
      (Real.continuousAt_rpow_const x q
        (Or.inl (hN.trans (Set.mem_Ioi.mp hx)).ne')).continuousWithinAt)).aestronglyMeasurable
      measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : (0 : ℝ) < x := hN.trans (Set.mem_Ioi.mp hx)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hx0.le _) (hbound x)
private theorem integrableOn_Ioi_sin_mul_rpow {ω q N : ℝ} (hq : q < -1) (hN : 0 < N) :
    IntegrableOn (fun x ↦ sin (ω * x) * x ^ q) (Set.Ioi N) :=
  integrableOn_Ioi_of_bound_mul_rpow (Real.continuous_sin.comp (continuous_const.mul continuous_id))
    (fun _ ↦ abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩) hq hN
private theorem integrableOn_Ioi_cos_mul_rpow {ω q N : ℝ} (hq : q < -1) (hN : 0 < N) :
    IntegrableOn (fun x ↦ cos (ω * x) * x ^ q) (Set.Ioi N) :=
  integrableOn_Ioi_of_bound_mul_rpow (Real.continuous_cos.comp (continuous_const.mul continuous_id))
    (fun _ ↦ abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩) hq hN
private theorem integral_Ioi_sin_mul_rpow_nonneg {p : ℝ} (hp : 1 < p) {N k : ℕ}
    (hN : 1 ≤ N) (hk : 1 ≤ k) :
    0 ≤ ∫ x in Set.Ioi (N : ℝ), sin (2 * π * k * x) * x ^ (-p) := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by lia)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by lia : 0 < N)
  set ω : ℝ := 2 * π * (k : ℝ) with hω
  have hω0 : 0 < ω := by rw [hω]; positivity
  set T : ℝ := 1 / (2 * (k : ℝ)) with hT
  have hT0 : 0 < T := by rw [hT]; positivity
  have hωT : ω * T = π := by rw [hω, hT]; field_simp
  set A : ℕ → ℝ := fun j ↦ (N : ℝ) + j * T with hA
  have hAsucc : ∀ j, A (j + 1) = A j + T := fun j ↦ by simp only [hA]; push_cast; ring
  have hApos : ∀ j, 0 < A j := fun j ↦ by simp only [hA]; positivity
  have hAle : ∀ j, A j ≤ A (j + 1) := fun j ↦ by rw [hAsucc]; linarith
  set g : ℝ → ℝ := fun x ↦ sin (ω * x) * x ^ (-p) with hg
  set c : ℕ → ℝ := fun j ↦ ∫ u in (0 : ℝ)..T, sin (ω * u) * (A j + u) ^ (-p) with hc
  have hsincont : Continuous fun x : ℝ ↦ sin (ω * x) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hrpow : ContinuousOn (fun x : ℝ ↦ x ^ (-p)) (Set.Ioi (0 : ℝ)) := fun x hx ↦
    (Real.continuousAt_rpow_const x (-p) (Or.inl (Set.mem_Ioi.mp hx).ne')).continuousWithinAt
  have hgint : ∀ j, IntervalIntegrable g volume (A j) (A (j + 1)) := fun j ↦
    (hsincont.continuousOn.mul (hrpow.mono fun x hx ↦ by
      rw [Set.uIcc_of_le (hAle j)] at hx
      exact lt_of_lt_of_le (hApos j) hx.1)).intervalIntegrable
  have hcint : ∀ j, IntervalIntegrable
      (fun u ↦ sin (ω * u) * (A j + u) ^ (-p)) volume 0 T := fun j ↦ by
    refine (hsincont.continuousOn.mul (ContinuousOn.rpow_const
      (continuous_const.add continuous_id).continuousOn fun u hu ↦ Or.inl ?_)).intervalIntegrable
    rw [Set.uIcc_of_le hT0.le] at hu
    exact (by linarith [hApos j, hu.1] : (0 : ℝ) < A j + u).ne'
  have hsinu : ∀ u ∈ Set.Icc (0 : ℝ) T, 0 ≤ sin (ω * u) := fun u hu ↦
    Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg hω0.le hu.1)
      (by linarith [mul_le_mul_of_nonneg_left hu.2 hω0.le, hωT])
  have hcanti : Antitone c := antitone_nat_of_succ_le fun j ↦ by
    simp only [hc]
    refine intervalIntegral.integral_mono_on hT0.le (hcint (j + 1)) (hcint j) fun u hu ↦ ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos
      (by linarith [hApos j, hu.1]) (by linarith [hAsucc j, hT0]) (by linarith)) (hsinu u hu)
  have hpiece : ∀ j, (∫ x in A j..A (j + 1), g x) = (-1 : ℝ) ^ j * c j := fun j ↦ by
    rw [show (∫ x in A j..A (j + 1), g x) = ∫ u in (0 : ℝ)..T, g (A j + u) from by
      rw [intervalIntegral.integral_comp_add_left g (A j), add_zero, ← hAsucc j]]
    simp only [hc, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ ↦ ?_
    have key : sin (ω * (A j + u)) = (-1 : ℝ) ^ j * sin (ω * u) := by
      rw [show ω * (A j + u) = ω * u + ((j + 2 * k * N : ℕ) : ℝ) * π by
            simp only [hA, hω, hT]; field_simp; push_cast; ring,
        Real.sin_add_nat_mul_pi,
        show ((-1 : ℝ)) ^ (j + 2 * k * N) = (-1 : ℝ) ^ j by
          rw [pow_add, show 2 * k * N = 2 * (k * N) by ring, pow_mul]; norm_num]
    simp only [hg, key]
    ring
  have hA0 : A 0 = (N : ℝ) := by simp [hA]
  have hpartial : ∀ n, ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * c i = ∫ x in (N : ℝ)..A n, g x :=
    fun n ↦ by
      rw [← hA0, ← intervalIntegral.sum_integral_adjacent_intervals
        (f := g) fun k (_ : k < n) ↦ hgint k]
      exact Finset.sum_congr rfl fun i _ ↦ (hpiece i).symm
  have hgintegrable : IntegrableOn g (Set.Ioi (N : ℝ)) := by
    rw [hg]; exact integrableOn_Ioi_sin_mul_rpow (by linarith) hN0
  have hAtop : Tendsto A atTop atTop :=
    (tendsto_atTop_add_const_left atTop (N : ℝ)
      (tendsto_natCast_atTop_atTop.atTop_mul_const hT0)).congr fun _ ↦ rfl
  have htend_sum : Tendsto (fun n ↦ ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * c i) atTop
      (𝓝 (∫ x in Set.Ioi (N : ℝ), g x)) :=
    (intervalIntegral_tendsto_integral_Ioi (N : ℝ) hgintegrable hAtop).congr
      fun n ↦ (hpartial n).symm
  simpa using Antitone.alternating_series_le_tendsto htend_sum hcanti 0
theorem integral_Ioi_cos_mul_rpow_nonneg {a : ℝ} (ha : 1 < a) {N k : ℕ} (hN : 1 ≤ N) :
    0 ≤ ∫ x in Set.Ioi (N : ℝ), cos (2 * π * k * x) * x ^ (-a) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by lia : 0 < N)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine setIntegral_nonneg measurableSet_Ioi fun x hx ↦ ?_
    simpa using Real.rpow_nonneg (hN0.trans hx).le (-a)
  set ω : ℝ := 2 * π * (k : ℝ) with hω
  have hω0 : 0 < ω := by rw [hω]; positivity
  have hJ : 0 ≤ ∫ x in Set.Ioi (N : ℝ), sin (ω * x) * x ^ (-(a + 1)) := by
    rw [hω]; exact integral_Ioi_sin_mul_rpow_nonneg (p := a + 1) (by linarith) hN hk
  have hcoscont : Continuous fun x : ℝ ↦ cos (ω * x) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hcosint : IntegrableOn (fun x ↦ cos (ω * x) * x ^ (-a)) (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_cos_mul_rpow (by linarith) hN0
  have hsinint : IntegrableOn (fun x ↦ sin (ω * x) * x ^ (-(a + 1))) (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_sin_mul_rpow (by linarith) hN0
  have hsinN : sin (ω * N) = 0 := by
    rw [show ω * (N : ℝ) = ((2 * k * N : ℕ) : ℝ) * π by rw [hω]; push_cast; ring]
    exact Real.sin_nat_mul_pi _
  have hrel : ∀ᶠ R in atTop, (∫ x in (N : ℝ)..R, cos (ω * x) * x ^ (-a))
      = R ^ (-a) * sin (ω * R) / ω
        + a / ω * ∫ x in (N : ℝ)..R, sin (ω * x) * x ^ (-(a + 1)) := by
    filter_upwards [eventually_ge_atTop (N : ℝ)] with R hR
    have hne : ∀ x ∈ Set.uIcc (N : ℝ) R, x ≠ 0 := fun x hx ↦ by
      rw [Set.uIcc_of_le hR] at hx; exact (lt_of_lt_of_le hN0 hx.1).ne'
    have hu : ∀ x ∈ Set.uIcc (N : ℝ) R, HasDerivAt (fun x ↦ x ^ (-a)) (-a * x ^ (-(a + 1))) x :=
      fun x hx ↦ by
        have hd := hasDerivAt_rpow_const (x := x) (p := -a) (Or.inl (hne x hx))
        rwa [show -a - 1 = -(a + 1) by ring] at hd
    have hv : ∀ x ∈ Set.uIcc (N : ℝ) R,
        HasDerivAt (fun x ↦ sin (ω * x) / ω) (cos (ω * x)) x := fun x _ ↦ by
      have h2 : HasDerivAt (fun t ↦ sin (ω * t)) (cos (ω * x) * ω) x :=
        (Real.hasDerivAt_sin (ω * x)).comp x (by simpa using (hasDerivAt_id x).const_mul ω)
      have h3 := h2.div_const ω
      rwa [mul_div_assoc, div_self hω0.ne', mul_one] at h3
    have hu'int : IntervalIntegrable (fun x ↦ -a * x ^ (-(a + 1))) volume (N : ℝ) R :=
      (continuousOn_const.mul fun x hx ↦
        (Real.continuousAt_rpow_const x (-(a + 1))
          (Or.inl (hne x hx))).continuousWithinAt).intervalIntegrable
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu'int
      (hcoscont.intervalIntegrable _ _)
    rw [intervalIntegral.integral_congr fun x _ ↦ mul_comm (x ^ (-a)) (cos (ω * x))] at hibp
    rw [hibp, show (∫ x in (N : ℝ)..R, -a * x ^ (-(a + 1)) * (sin (ω * x) / ω))
          = -(a / ω) * ∫ x in (N : ℝ)..R, sin (ω * x) * x ^ (-(a + 1)) by
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_congr fun x _ ↦ by ring, hsinN]
    ring
  have hbdry : Tendsto (fun R : ℝ ↦ R ^ (-a) * sin (ω * R) / ω) atTop (𝓝 0) := by
    have hb0 : Tendsto (fun R : ℝ ↦ R ^ (-a) / ω) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (show (0 : ℝ) < a by linarith)).div_const ω
    refine squeeze_zero_norm' ?_ hb0
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hRa : (0 : ℝ) ≤ R ^ (-a) := Real.rpow_nonneg hR.le _
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hω0, abs_mul, abs_of_nonneg hRa,
      div_le_div_iff_of_pos_right hω0]
    simpa using mul_le_mul_of_nonneg_left
      (abs_le.mpr ⟨Real.neg_one_le_sin (ω * R), Real.sin_le_one (ω * R)⟩) hRa
  have heq := tendsto_nhds_unique
    ((intervalIntegral_tendsto_integral_Ioi (N : ℝ) hcosint tendsto_id).congr' hrel)
    (hbdry.add ((intervalIntegral_tendsto_integral_Ioi (N : ℝ) hsinint
      tendsto_id).const_mul (a / ω)))
  rw [heq, zero_add]
  exact mul_nonneg (div_nonneg (by linarith) hω0.le) hJ
theorem zetaRemainder_eq_integral_bernoulliFun_fract_sub (s : ℂ) (M N : ℕ) (hN : 1 ≤ N)
    (hs : -(2 * M + 1 : ℝ) < s.re) :
    zetaRemainder s M N
      = -((ascPochhammer ℂ (2 * M + 2)).eval s / ((2 * M + 2)! : ℂ))
          * ∫ x in Set.Ioi (N : ℝ),
              ((bernoulliFun (2 * M + 2) (Int.fract x) : ℝ) - (bernoulli (2 * M + 2) : ℝ) : ℂ)
                * (x : ℂ) ^ (-s - ((2 * M + 2 : ℕ) : ℂ)) := by
  rw [zetaRemainder, Complex.eulerMaclaurinRemainderIoi_cpow_eq s (2 * M + 2) N]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set p : ℕ := 2 * M + 2 with hp
  set w : ℂ := -s - (p : ℂ) with hw
  have hwre : w.re < -1 := by
    rw [hw, Complex.sub_re, Complex.neg_re, Complex.natCast_re, hp]; push_cast; linarith
  have hxint : IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ w) (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_cpow_of_lt hwre hN0
  have hBint : IntegrableOn (fun x : ℝ ↦ (bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ w)
      (Set.Ioi (N : ℝ)) := Complex.integrableOn_Ioi_bernoulliFun_fract_mul_cpow p N hN hwre
  have hsubint : IntegrableOn
      (fun x : ℝ ↦ ((bernoulliFun p (Int.fract x) : ℝ) - (bernoulli p : ℝ) : ℂ) * (x : ℂ) ^ w)
      (Set.Ioi (N : ℝ)) :=
    (hBint.sub (hxint.const_mul ((bernoulli p : ℝ) : ℂ))).congr
      (.of_forall fun x ↦ by simp only [Pi.sub_apply]; push_cast; ring)
  have hsplit : (∫ x in Set.Ioi (N : ℝ), (bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ w)
      = (∫ x in Set.Ioi (N : ℝ),
            ((bernoulliFun p (Int.fract x) : ℝ) - (bernoulli p : ℝ) : ℂ) * (x : ℂ) ^ w)
        + ((bernoulli p : ℝ) : ℂ) * ∫ x in Set.Ioi (N : ℝ), (x : ℂ) ^ w := by
    rw [show (∫ x in Set.Ioi (N : ℝ), (bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ w)
          = ∫ x in Set.Ioi (N : ℝ),
              (((bernoulliFun p (Int.fract x) : ℝ) - (bernoulli p : ℝ) : ℂ) * (x : ℂ) ^ w
                + ((bernoulli p : ℝ) : ℂ) * (x : ℂ) ^ w) from
        setIntegral_congr_fun measurableSet_Ioi (fun x _ ↦ by push_cast; ring),
      integral_add hsubint (hxint.const_mul ((bernoulli p : ℝ) : ℂ)), integral_const_mul]
  rw [hsplit, integral_Ioi_cpow_of_lt hwre hN0]
  have hwone : w + 1 = -s - ((2 * M + 1 : ℕ) : ℂ) := by rw [hw, hp]; push_cast; ring
  have hPp : (ascPochhammer ℂ p).eval s
      = (ascPochhammer ℂ (2 * M + 1)).eval s * (s + ((2 * M + 1 : ℕ) : ℂ)) := by
    rw [show p = (2 * M + 1) + 1 from by lia, ascPochhammer_succ_eval]
  have hpne : (p ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos p).ne'
  have hden : -s - ((2 * M + 1 : ℕ) : ℂ) ≠ 0 := fun h ↦ by
    have hre : (-s - ((2 * M + 1 : ℕ) : ℂ)).re = 0 := by rw [h]; simp
    rw [Complex.sub_re, Complex.neg_re, Complex.natCast_re] at hre
    push_cast at hre; linarith
  rw [hwone, hPp]
  push_cast at hden hpne ⊢
  field_simp
  ring
theorem integral_Ioi_abs_bernoulliFun_fract_sub_mul_rpow_le (m : ℕ) (hm : 1 ≤ m) {a : ℝ}
    (ha : 1 < a) {N : ℕ} (hN : 1 ≤ N) :
    ∫ x in Set.Ioi (N : ℝ),
        |bernoulliFun (2 * m) (Int.fract x) - (bernoulli (2 * m) : ℝ)| * x ^ (-a)
      ≤ |(bernoulli (2 * m) : ℝ)| * ∫ x in Set.Ioi (N : ℝ), x ^ (-a) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by lia : 0 < N)
  have hxa_neg : -a < -1 := by linarith
  set b : ℝ := (bernoulli (2 * m) : ℝ)
  set Am : ℝ := 2 * ((2 * m)! : ℝ) / (2 * π) ^ (2 * m) with hAm
  have hAm0 : 0 < Am := by rw [hAm]; positivity
  set W : ℝ := ∫ x in Set.Ioi (N : ℝ), x ^ (-a) with hW
  have hweight_int : IntegrableOn (fun x : ℝ ↦ x ^ (-a)) (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt hxa_neg hN0
  have hcos_int : ∀ k : ℕ,
      IntegrableOn (fun x ↦ cos (2 * π * (k : ℝ) * x) * x ^ (-a)) (Set.Ioi (N : ℝ)) := fun _ ↦
    integrableOn_Ioi_cos_mul_rpow hxa_neg hN0
  set f : ℕ → ℝ → ℝ :=
    fun k x ↦ Am / (k : ℝ) ^ (2 * m) * (1 - cos (2 * π * (k : ℝ) * x)) * x ^ (-a) with hf
  have hf_int : ∀ k, IntegrableOn (f k) (Set.Ioi (N : ℝ)) := fun k ↦
    ((hweight_int.sub (hcos_int k)).const_mul (Am / (k : ℝ) ^ (2 * m))).congr <| by
      filter_upwards with x
      simp only [hf, Pi.sub_apply]; ring
  have hf_nonneg : ∀ k, ∀ x ∈ Set.Ioi (N : ℝ), 0 ≤ f k x := fun k x hx ↦ by
    simp only [hf]
    exact mul_nonneg (mul_nonneg (div_nonneg hAm0.le (by positivity))
        (by linarith [Real.cos_le_one (2 * π * (k : ℝ) * x)]))
      (Real.rpow_nonneg (lt_trans hN0 hx).le _)
  have hbound : ∀ k, (∫ x in Set.Ioi (N : ℝ), f k x) ≤ Am / (k : ℝ) ^ (2 * m) * W := fun k ↦ by
    rw [setIntegral_congr_fun measurableSet_Ioi fun x _ ↦
      show f k x = Am / (k : ℝ) ^ (2 * m) * (x ^ (-a) - cos (2 * π * (k : ℝ) * x) * x ^ (-a))
        by simp only [hf]; ring, integral_const_mul, integral_sub hweight_int (hcos_int k)]
    exact mul_le_mul_of_nonneg_left
      (by linarith [integral_Ioi_cos_mul_rpow_nonneg (a := a) (N := N) (k := k) ha hN])
      (div_nonneg hAm0.le (by positivity))
  have hsummable_bound : Summable (fun k : ℕ ↦ Am / (k : ℝ) ^ (2 * m) * W) :=
    ((((Real.summable_one_div_nat_pow (p := 2 * m)).mpr (by lia)).mul_left Am).congr
      fun k ↦ by ring).mul_right W
  have hsummable_int : Summable (fun k : ℕ ↦ ∫ x in Set.Ioi (N : ℝ), f k x) :=
    Summable.of_nonneg_of_le
      (fun k ↦ setIntegral_nonneg measurableSet_Ioi (hf_nonneg k)) hbound hsummable_bound
  have habs : ∀ x : ℝ, |bernoulliFun (2 * m) (Int.fract x) - b|
      = Am * ∑' k : ℕ, (1 - cos (2 * π * (k : ℝ) * x)) / (k : ℝ) ^ (2 * m) := fun x ↦ by
    rw [abs_eq_neg_one_pow_mul (centered_kernel_mul_sign_nonneg m hm x),
      bernoulliFun_sub_self_eq_tsum_cos m hm x,
      show ∑' k : ℕ, (1 - cos (2 * π * (k : ℝ) * x)) / (k : ℝ) ^ (2 * m)
          = -∑' k : ℕ, (cos (2 * π * (k : ℝ) * x) - 1) / (k : ℝ) ^ (2 * m) from by
        rw [← tsum_neg]; exact tsum_congr fun k ↦ by ring]
    have hsq : (-1 : ℝ) ^ m * (-1) ^ (m + 1) = -1 := by
      rw [← pow_add]; exact Odd.neg_one_pow ⟨m, by ring⟩
    linear_combination
      (Am * ∑' k : ℕ, (cos (2 * π * (k : ℝ) * x) - 1) / (k : ℝ) ^ (2 * m)) * hsq
  calc ∫ x in Set.Ioi (N : ℝ),
        |bernoulliFun (2 * m) (Int.fract x) - b| * x ^ (-a)
      = ∫ x in Set.Ioi (N : ℝ), ∑' k : ℕ, f k x :=
        setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ by
          rw [tsum_congr fun k ↦ show f k x
                = Am * ((1 - cos (2 * π * (k : ℝ) * x)) / (k : ℝ) ^ (2 * m)) * x ^ (-a) by
              simp only [hf]; ring, tsum_mul_right, tsum_mul_left, ← habs x]
    _ = ∑' k : ℕ, ∫ x in Set.Ioi (N : ℝ), f k x :=
        (integral_tsum_of_summable_integral_norm hf_int (hsummable_int.congr fun k ↦
          setIntegral_congr_fun measurableSet_Ioi fun x hx ↦
            (Real.norm_of_nonneg (hf_nonneg k x hx)).symm)).symm
    _ ≤ ∑' k : ℕ, Am / (k : ℝ) ^ (2 * m) * W :=
        hsummable_int.tsum_mono hsummable_bound hbound
    _ = |b| * W := by
        have hAmζ : (∑' k : ℕ, Am / (k : ℝ) ^ (2 * m)) = (-1 : ℝ) ^ (m + 1) * b := by
          have hpi : ((2 * π) ^ (2 * m) : ℝ) ≠ 0 := by positivity
          have hfac : ((2 * m)! : ℝ) ≠ 0 := by positivity
          rw [tsum_congr fun k : ℕ ↦ div_eq_mul_one_div Am ((k : ℝ) ^ (2 * m)), tsum_mul_left,
            (hasSum_one_div_nat_pow_bernoulli m (by lia)).tsum_eq, hAm]
          field_simp
          ring
        have hnn : 0 ≤ (-1 : ℝ) ^ (m + 1) * b :=
          hAmζ ▸ tsum_nonneg fun k ↦ div_nonneg hAm0.le (by positivity)
        rw [tsum_mul_right, hAmζ, ← abs_eq_neg_one_pow_mul hnn]
noncomputable abbrev zetaRemainderBound (s : ℂ) (M N : ℕ) : ℝ :=
  ‖s + ((2 * M + 1 : ℕ) : ℂ)‖ / (s.re + ((2 * M + 1 : ℕ) : ℝ))
    * ‖((bernoulli (2 * M + 2) : ℝ) / ((2 * M + 2)! : ℝ) : ℂ)
        * (ascPochhammer ℂ (2 * M + 1)).eval s
        * (N : ℂ) ^ (-s - ((2 * M + 1 : ℕ) : ℂ))‖
theorem norm_zetaRemainder_le (s : ℂ) (M N : ℕ) (hN : 1 ≤ N) (hs : -(2 * M + 1 : ℝ) < s.re) :
    ‖zetaRemainder s M N‖ ≤ zetaRemainderBound s M N := by
  simp only [zetaRemainderBound]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set a : ℝ := s.re + ((2 * M + 2 : ℕ) : ℝ) with ha_def
  have ha : 1 < a := by rw [ha_def]; push_cast; linarith
  set W : ℝ := ∫ x in Set.Ioi (N : ℝ), x ^ (-a) with hW
  have hwre : (-s - ((2 * M + 2 : ℕ) : ℂ)).re = -a := by
    rw [ha_def]; simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re]; push_cast; ring
  have hre1 : (-s - ((2 * M + 1 : ℕ) : ℂ)).re = -(s.re + ((2 * M + 1 : ℕ) : ℝ)) := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re]; ring
  have hrel : -a + 1 = -(s.re + ((2 * M + 1 : ℕ) : ℝ)) := by rw [ha_def]; push_cast; ring
  have hP : ‖(ascPochhammer ℂ (2 * M + 2)).eval s‖
      = ‖(ascPochhammer ℂ (2 * M + 1)).eval s‖ * ‖s + ((2 * M + 1 : ℕ) : ℂ)‖ := by
    rw [show 2 * M + 2 = (2 * M + 1) + 1 from by lia, ascPochhammer_succ_eval, norm_mul]
  have ht : ‖((bernoulli (2 * M + 2) : ℝ) / ((2 * M + 2)! : ℝ) : ℂ)
        * (ascPochhammer ℂ (2 * M + 1)).eval s * (N : ℂ) ^ (-s - ((2 * M + 1 : ℕ) : ℂ))‖
      = |(bernoulli (2 * M + 2) : ℝ)| / ((2 * M + 2)! : ℝ)
          * ‖(ascPochhammer ℂ (2 * M + 1)).eval s‖
          * (N : ℝ) ^ (-(s.re + ((2 * M + 1 : ℕ) : ℝ))) := by
    rw [norm_mul, norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 * M + 2)! : ℝ)),
      ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hN0, hre1]
  have hWval : W = -(N : ℝ) ^ (-a + 1) / (-a + 1) := by
    rw [hW]; exact integral_Ioi_rpow_of_lt (by linarith : -a < -1) hN0
  have hInorm : ‖∫ x in Set.Ioi (N : ℝ),
        ((bernoulliFun (2 * M + 2) (Int.fract x) : ℝ) - (bernoulli (2 * M + 2) : ℝ) : ℂ)
          * (x : ℂ) ^ (-s - ((2 * M + 2 : ℕ) : ℂ))‖
      ≤ |(bernoulli (2 * M + 2) : ℝ)| * W := by
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [setIntegral_congr_fun measurableSet_Ioi fun x hx ↦
      show ‖((bernoulliFun (2 * M + 2) (Int.fract x) : ℝ) - (bernoulli (2 * M + 2) : ℝ) : ℂ)
            * (x : ℂ) ^ (-s - ((2 * M + 2 : ℕ) : ℂ))‖
          = |bernoulliFun (2 * M + 2) (Int.fract x) - (bernoulli (2 * M + 2) : ℝ)| * x ^ (-a) by
        rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans hN0 hx), hwre]]
    have h3 := integral_Ioi_abs_bernoulliFun_fract_sub_mul_rpow_le (M + 1) (by lia) ha hN
    rwa [show 2 * (M + 1) = 2 * M + 2 from by ring] at h3
  rw [zetaRemainder_eq_integral_bernoulliFun_fract_sub s M N hN hs, norm_mul, norm_neg, norm_div,
    Complex.norm_natCast]
  refine (mul_le_mul_of_nonneg_left hInorm (by positivity)).trans (le_of_eq ?_)
  rw [hP, ht, hWval, hrel]
  have hFacne : ((2 * M + 2)! : ℝ) ≠ 0 := by positivity
  have hDne : s.re + ((2 * M + 1 : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt (by push_cast; linarith : (0 : ℝ) < s.re + ((2 * M + 1 : ℕ) : ℝ))
  field_simp
end
end CertificatePort151


section CertificatePort152
section
open scoped Nat
namespace Enclosure
theorem natCast_cpow_eq (n : ℕ) (hn : 0 < n) (σ t : ℝ) :
    ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)) =
      ⟨Real.exp (σ * Real.log n) * Real.cos (t * Real.log n),
       Real.exp (σ * Real.log n) * Real.sin (t * Real.log n)⟩ := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (by positivity)]
  have hstd : ((Real.log n : ℝ) : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I)
            = ((Real.log n * σ : ℝ) : ℂ) + ((Real.log n * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [Complex.cpow_def_of_ne_zero hn0, hlog, hstd]
  apply Complex.ext
  · rw [Complex.exp_re]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
      add_zero, mul_one]
    congr 1 <;> congr 1 <;> ring
  · rw [Complex.exp_im]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
      add_zero, mul_one]
    congr 1 <;> congr 1 <;> ring
def natAbsSubLe (XP XN Xd YP YN Yd δn δd : ℕ) : Bool :=
  Nat.ble (((XP.mul Yd).add (YN.mul Xd)).mul δd)
      ((δn.mul (Xd.mul Yd)).add (((XN.mul Yd).add (YP.mul Xd)).mul δd)) &&
    Nat.ble (((YP.mul Xd).add (XN.mul Yd)).mul δd)
      ((δn.mul (Xd.mul Yd)).add (((YN.mul Xd).add (XP.mul Yd)).mul δd))
theorem abs_sub_le_of_natAbsSubLe {XP XN Xd YP YN Yd δn δd : ℕ}
    (hXd : 0 < Xd) (hYd : 0 < Yd) (hδd : 0 < δd)
    (h : natAbsSubLe XP XN Xd YP YN Yd δn δd = true) :
    |((XP : ℝ) - XN) / Xd - ((YP : ℝ) - YN) / Yd| ≤ (δn : ℝ) / δd := by
  simp only [natAbsSubLe, Bool.and_eq_true, Nat.ble_eq, Nat.mul_eq, Nat.add_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hX : (0 : ℝ) < Xd := by exact_mod_cast hXd
  have hY : (0 : ℝ) < Yd := by exact_mod_cast hYd
  have hδ : (0 : ℝ) < δd := by exact_mod_cast hδd
  have h1' : ((XP : ℝ) * Yd + YN * Xd) * δd ≤ δn * (Xd * Yd) + (XN * Yd + YP * Xd) * δd := by
    exact_mod_cast h1
  have h2' : ((YP : ℝ) * Xd + XN * Yd) * δd ≤ δn * (Xd * Yd) + (YN * Xd + XP * Yd) * δd := by
    exact_mod_cast h2
  have e : ((XP : ℝ) - XN) / Xd - ((YP : ℝ) - YN) / Yd
      = ((XP : ℝ) * Yd + YN * Xd - (XN * Yd + YP * Xd)) / (Xd * Yd) := by
    field_simp
    ring
  have hXY : (0 : ℝ) < Xd * Yd := mul_pos hX hY
  rw [e, abs_div, abs_of_pos hXY, div_le_div_iff₀ hXY hδ]
  rcases abs_cases ((XP : ℝ) * Yd + YN * Xd - (XN * Yd + YP * Xd)) with ⟨h, _⟩ | ⟨h, _⟩ <;>
    rw [h] <;> nlinarith
end Enclosure
namespace BSN
open Enclosure
open Complex
noncomputable abbrev hardyZErrorBoundStrong (M N : ℕ) (t : ℝ) : ℝ :=
  riemannSiegelThetaStirlingErrorBound M (thetaShift M)
      * ‖zetaApproximant (1 / 2 + Complex.I * t) M N‖
    + zetaRemainderBound (1 / 2 + Complex.I * t) M N
theorem hardyZErrorBoundEM_le_strong (M N : ℕ) (t : ℝ) (hN : Nat.ble 1 N = true) :
    hardyZErrorBoundEM M N t ≤ hardyZErrorBoundStrong M N t := by
  have hN' : 1 ≤ N := Nat.le_of_ble_eq_true hN
  have hs : -(2 * M + 1 : ℝ) < (1 / 2 + Complex.I * (t : ℂ)).re := by
    have hre : (1 / 2 + Complex.I * (t : ℂ)).re = 1 / 2 := by simp
    rw [hre]
    have : (0 : ℝ) ≤ 2 * M + 1 := by positivity
    linarith
  exact add_le_add le_rfl (norm_zetaRemainder_le _ M N hN' hs)
theorem gt_trans_le (x s b : ℝ) (hle : b ≤ s) (h : x > s) : x > b := lt_of_le_of_lt hle h
theorem re_exp_mul (θ : ℝ) (ζ : ℂ) :
    (Complex.exp (Complex.I * (θ : ℂ)) * ζ).re = Real.cos θ * ζ.re - Real.sin θ * ζ.im := by
  rw [mul_comm Complex.I, Complex.exp_mul_I, Complex.mul_re, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im,
    Complex.sin_ofReal_im]
theorem zetaApproximant_eq_folded (s : ℂ) (M N : ℕ) (hN : 0 < N) :
    zetaApproximant s M N
      = (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
        + (N : ℂ) ^ (-s) * ((N : ℂ) / (s - 1) + 1 / 2
            + ∑ k ∈ Finset.Icc 1 M,
                ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
                  * (ascPochhammer ℂ (2 * k - 1)).eval s * ((N : ℂ) ^ (2 * k - 1))⁻¹) := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have h1s : (N : ℂ) ^ (1 - s) = (N : ℂ) * (N : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hN0, Complex.cpow_one]
  have hks : ∀ k : ℕ, (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ))
      = (N : ℂ) ^ (-s) * ((N : ℂ) ^ (2 * k - 1))⁻¹ := fun k => by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hN0]
    congr 1
    rw [Complex.cpow_neg, Complex.cpow_natCast]
  have hsum : (∑ k ∈ Finset.Icc 1 M,
        ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
          * (ascPochhammer ℂ (2 * k - 1)).eval s * (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ)))
      = (N : ℂ) ^ (-s) * ∑ k ∈ Finset.Icc 1 M,
          ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
            * (ascPochhammer ℂ (2 * k - 1)).eval s * ((N : ℂ) ^ (2 * k - 1))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hks k]
    ring
  rw [zetaApproximant, h1s, hsum]
  ring
theorem s_crit_mk (t : ℝ) (tneg : Bool) (tn td : ℕ) (ht : t = sfrac tneg tn td) :
    (1 / 2 + Complex.I * (t : ℂ)) = ⟨sfrac false (nat_lit 1) (nat_lit 2), sfrac tneg tn td⟩ := by
  subst ht
  apply Complex.ext <;>
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, sfrac_false_div]
theorem s_add_nat_mk (t : ℝ) (tneg : Bool) (tn td n : ℕ) (ht : t = sfrac tneg tn td) :
    (1 / 2 + Complex.I * (t : ℂ)) + (n : ℂ)
      = ⟨sfrac false (Nat.add 1 (Nat.mul 2 n)) (nat_lit 2), sfrac tneg tn td⟩ := by
  simp only [Nat.mul_eq, Nat.add_eq]
  subst ht
  apply Complex.ext <;>
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, sfrac_false_div]
  ring
theorem w_shift_mk (t : ℝ) (tneg : Bool) (tn td j : ℕ) (ht : t = sfrac tneg tn td)
    (htd : Nat.ble 1 td = true) :
    1 / 4 + Complex.I * ((t : ℂ) / 2) + (j : ℂ)
      = ⟨sfrac false ((Nat.add 1 (Nat.mul 4 j)).mul td) (Nat.mul 4 td),
         sfrac tneg (Nat.mul 2 tn) (Nat.mul 4 td)⟩ := by
  simp only [Nat.mul_eq, Nat.add_eq]
  subst ht
  have htdR : (0 : ℝ) < td := pos_real_of_ble htd
  apply Complex.ext
  · simp [Complex.add_re, Complex.mul_re, sfrac_false_div]
    field_simp
  · cases tneg <;> simp [Complex.add_im, Complex.mul_im, sfrac] <;> field_simp <;> ring
theorem ascPochhammer_one_eval (s : ℂ) : (ascPochhammer ℂ (nat_lit 1)).eval s = s := by
  rw [ascPochhammer_one, Polynomial.eval_X]
theorem ascPochhammer_succ_eval_c (n b : ℕ) (s : ℂ) (hb : Nat.beq b (n.add 1) = true) :
    (ascPochhammer ℂ b).eval s = (ascPochhammer ℂ n).eval s * (s + n) := by
  obtain rfl := Nat.eq_of_beq_eq_true hb
  exact ascPochhammer_succ_eval n s
theorem complex_zero_mk : (0 : ℂ)
    = ⟨sfrac false (nat_lit 0) (nat_lit 1), sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  apply Complex.ext <;> simp [sfrac]
theorem cpow_neg_s_mk (t : ℝ) (tn td n : ℕ) (ht : t = sfrac false tn td)
    (hn : Nat.ble 1 n = true) :
    (n : ℂ) ^ (-(1 / 2 + Complex.I * (t : ℂ)))
      = ⟨(Real.sqrt (n : ℝ))⁻¹
            * Real.cos (sfrac false tn td * Real.log (sfrac false n (nat_lit 1))),
         (Real.sqrt (n : ℝ))⁻¹
            * -Real.sin (sfrac false tn td * Real.log (sfrac false n (nat_lit 1)))⟩ := by
  have hn' : 0 < n := pos_of_ble hn
  have hnR : (0 : ℝ) < n := pos_real_of_ble hn
  have hexp : -(1 / 2 + Complex.I * (t : ℂ))
      = ((-(1/2) : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hexp, natCast_cpow_eq n hn' (-(1/2)) (-t)]
  have hmag : Real.exp (-(1 / 2 * Real.log n)) = (Real.sqrt (n : ℝ))⁻¹ := by
    have h1 : ((1 : ℝ) / (n : ℝ)) = Real.exp (-Real.log n) := by
      rw [one_div, Real.exp_neg, Real.exp_log hnR]
    have h2 : Real.exp (-(1 / 2 * Real.log n)) = Real.sqrt (1 / (n : ℝ)) := by
      rw [h1, ← Real.exp_half]
      congr 1
      ring
    rw [h2, one_div, Real.sqrt_inv]
  have hlogsfrac : Real.log (sfrac false n (nat_lit 1)) = Real.log n := by
    rw [sfrac_false_div]; simp
  subst ht
  apply Complex.ext <;>
    simp only [hlogsfrac, neg_mul, Real.cos_neg, Real.sin_neg, hmag]
theorem head_sum_base (s : ℂ) :
    (∑ n ∈ Finset.Ico (1 : ℕ) 1, (n : ℂ) ^ (-s))
        = ⟨sfrac false (nat_lit 0) (nat_lit 1), sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  rw [Finset.Ico_self, Finset.sum_empty]
  exact complex_zero_mk
theorem head_sum_succ (s : ℂ) (a b : ℕ) (hb : Nat.beq b (a.add 1) = true)
    (ha : Nat.ble 1 a = true) :
    (∑ n ∈ Finset.Ico 1 b, (n : ℂ) ^ (-s))
      = (∑ n ∈ Finset.Ico 1 a, (n : ℂ) ^ (-s)) + (a : ℂ) ^ (-s) := by
  obtain rfl := Nat.eq_of_beq_eq_true hb
  exact Finset.sum_Ico_succ_top (Nat.le_of_ble_eq_true ha) _
noncomputable def headSumC (s : ℂ) (N : ℕ) : ℂ := ∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s)
theorem head_sum_c_base (s : ℂ) : headSumC s (nat_lit 1)
    = ⟨sfrac false (nat_lit 0) (nat_lit 1), sfrac false (nat_lit 0) (nat_lit 1)⟩ :=
  head_sum_base s
theorem head_sum_c_succ (s : ℂ) (a b : ℕ) (hb : Nat.beq b (a.add 1) = true)
    (ha : Nat.ble 1 a = true) : headSumC s b = headSumC s a + (a : ℂ) ^ (-s) :=
  head_sum_succ s a b hb ha
theorem head_sum_c_two (s : ℂ) :
    headSumC s (nat_lit 2)
      = ⟨sfrac false (nat_lit 1) (nat_lit 1), sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  rw [head_sum_c_succ s (nat_lit 1) (nat_lit 2) (by rfl) (by rfl), head_sum_c_base, Nat.cast_one,
    Complex.one_cpow]
  apply Complex.ext <;> simp [sfrac]
theorem head_sum_c_eq (s : ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s)) = headSumC s N := rfl
theorem bern_sum_base (s : ℂ) (N : ℕ) :
    (∑ k ∈ Finset.Icc (1 : ℕ) (nat_lit 0),
        ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
          * (ascPochhammer ℂ (2 * k - 1)).eval s * ((N : ℂ) ^ (2 * k - 1))⁻¹)
      = ⟨sfrac false (nat_lit 0) (nat_lit 1), sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  have hIcc : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
  rw [hIcc, Finset.sum_empty]
  exact complex_zero_mk
theorem bern_sum_succ (s : ℂ) (N m b e : ℕ) (hb : Nat.beq b (m.add 1) = true)
    (he : Nat.beq (e.add 1) (Nat.mul 2 b) = true) :
    (∑ k ∈ Finset.Icc 1 b,
        ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
          * (ascPochhammer ℂ (2 * k - 1)).eval s * ((N : ℂ) ^ (2 * k - 1))⁻¹)
      = (∑ k ∈ Finset.Icc 1 m,
          ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
            * (ascPochhammer ℂ (2 * k - 1)).eval s * ((N : ℂ) ^ (2 * k - 1))⁻¹)
        + ((bernoulli (2 * b) : ℝ) / ((2 * b)! : ℝ) : ℂ)
            * (ascPochhammer ℂ e).eval s * ((N : ℂ) ^ e)⁻¹ := by
  obtain rfl := Nat.eq_of_beq_eq_true hb
  have he' : e = 2 * (m + 1) - 1 := by
    have h : e + 1 = 2 * (m + 1) := Nat.eq_of_beq_eq_true he
    omega
  subst he'
  exact Finset.sum_Icc_succ_top (by omega) _
theorem half_c_mk : (1 / 2 : ℂ)
    = ⟨sfrac false (nat_lit 1) (nat_lit 2), sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  apply Complex.ext
  · simp [sfrac]
  · simp [sfrac]
theorem N_div_s_sub_one_mk (t : ℝ) (tn td N : ℕ) (ht : t = sfrac false tn td)
    (htn : Nat.ble 1 tn = true) (htd : Nat.ble 1 td = true) :
    (N : ℂ) / ((1 / 2 + Complex.I * (t : ℂ)) - 1)
      = ⟨sfrac true ((Nat.mul 2 N).mul (td.mul td)) ((td.mul td).add (Nat.mul 4 (tn.mul tn))),
         sfrac true ((Nat.mul 4 N).mul (tn.mul td)) ((td.mul td).add (Nat.mul 4 (tn.mul tn)))⟩ := by
  simp only [Nat.mul_eq, Nat.add_eq]
  subst ht
  have h1 : (0 : ℝ) < tn := pos_real_of_ble htn
  have h2 : (0 : ℝ) < td := pos_real_of_ble htd
  have hw : ((1 / 2 + Complex.I * ((sfrac false tn td : ℝ) : ℂ)) - 1)
      = ⟨-(1/2), (tn : ℝ) / td⟩ := by
    apply Complex.ext
    · simp [sfrac_false_div]
      norm_num
    · simp [sfrac_false_div]
  rw [hw]
  have hns : Complex.normSq ⟨-(1/2), (tn : ℝ) / td⟩ = 1/4 + (tn : ℝ)^2 / (td : ℝ)^2 := by
    rw [Complex.normSq_mk]
    ring
  apply Complex.ext
  · rw [Complex.div_re, hns]
    simp [sfrac]
    field_simp
    ring
  · rw [Complex.div_im, hns]
    simp [sfrac]
    field_simp
theorem natCast_pow_inv_mk (N m P : ℕ) (hP : Nat.pow N m = P)
    (_hN : Nat.ble 1 N = true) :
    ((N : ℂ) ^ m)⁻¹ = ⟨sfrac false (nat_lit 1) P, sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  obtain rfl := hP
  simp only [Nat.pow_eq]
  have h : ((N : ℂ) ^ m)⁻¹ = (((N ^ m : ℕ) : ℝ) : ℂ)⁻¹ := by push_cast; ring
  rw [h, ← Complex.ofReal_inv]
  apply Complex.ext
  · rw [Complex.ofReal_re, sfrac_false_div, Nat.cast_one, one_div]
  · rw [Complex.ofReal_im]
    simp [sfrac]
def factNat (n : ℕ) : ℕ := n.rec 1 (fun k acc => Nat.mul (Nat.succ k) acc)
theorem factNat_eq (n : ℕ) : factNat n = Nat.factorial n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have h : factNat (k + 1) = (k + 1) * factNat k := rfl
    rw [h, ih, Nat.factorial_succ]
theorem bern_coeff_mk (k bn bd F : ℕ) (bneg : Bool)
    (hB : (bernoulli (2 * k) : ℝ) = sfrac bneg bn bd)
    (hF : factNat (Nat.mul 2 k) = F) (hbd : Nat.ble 1 bd = true) :
    ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
      = ⟨sfrac bneg bn (bd.mul F), sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  obtain rfl := hF
  simp only [factNat_eq, Nat.mul_eq]
  have hbdR : (0 : ℝ) < bd := pos_real_of_ble hbd
  have hFR : (0 : ℝ) < ((2 * k)! : ℝ) := by exact_mod_cast (2 * k).factorial_pos
  rw [← Complex.ofReal_div]
  apply Complex.ext
  · rw [Complex.ofReal_re, hB]
    simp only [sfrac]
    cases bneg <;> (simp; field_simp)
  · rw [Complex.ofReal_im]
    simp [sfrac]
theorem zetaApproximant_eq_folded' (s : ℂ) (M N : ℕ) (hN : Nat.ble 1 N = true) :
    zetaApproximant s M N
      = (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
        + (N : ℂ) ^ (-s) * ((N : ℂ) / (s - 1) + 1 / 2
            + ∑ k ∈ Finset.Icc 1 M,
                ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
                  * (ascPochhammer ℂ (2 * k - 1)).eval s * ((N : ℂ) ^ (2 * k - 1))⁻¹) :=
  zetaApproximant_eq_folded s M N (pos_of_ble hN)
theorem w_sub_half_zero_mk (t : ℝ) (tneg : Bool) (tn td : ℕ) (ht : t = sfrac tneg tn td)
    (htd : Nat.ble 1 td = true) :
    (1 / 4 + Complex.I * ((t : ℂ) / 2) + ((nat_lit 0 : ℕ) : ℂ)) - 1 / 2
      = ⟨sfrac true td (Nat.mul 4 td), sfrac tneg (Nat.mul 2 tn) (Nat.mul 4 td)⟩ := by
  rw [w_shift_mk t tneg tn td (nat_lit 0) ht htd]
  have htdR : (0 : ℝ) < td := pos_real_of_ble htd
  apply Complex.ext
  · simp only [Nat.mul_eq, mul_zero, Nat.add_eq, add_zero, one_mul, sfrac_false_div, Nat.cast_mul,
      Nat.cast_ofNat, one_div, sub_re, inv_re, re_ofNat, normSq_ofNat, div_self_mul_self',
      sfrac_true_div]
    all_goals (field_simp; try ring)
  · simp
theorem w_sub_half_mk (t : ℝ) (tneg : Bool) (tn td N : ℕ) (ht : t = sfrac tneg tn td)
    (htd : Nat.ble 1 td = true) (hN : Nat.ble 1 N = true) :
    (1 / 4 + Complex.I * ((t : ℂ) / 2) + (N : ℂ)) - 1 / 2
      = ⟨sfrac false (((Nat.mul 4 N).sub 1).mul td) (Nat.mul 4 td),
         sfrac tneg (Nat.mul 2 tn) (Nat.mul 4 td)⟩ := by
  have hN' : 0 < N := pos_of_ble hN
  rw [w_shift_mk t tneg tn td N ht htd]
  simp only [Nat.mul_eq, Nat.add_eq, Nat.sub_eq]
  have htdR : (0 : ℝ) < td := pos_real_of_ble htd
  apply Complex.ext
  · simp only [sfrac_false_div, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, one_div,
      sub_re, inv_re, re_ofNat, normSq_ofNat, div_self_mul_self']
    rw [Nat.cast_sub (by omega : 1 ≤ 4 * N)]
    push_cast
    field_simp
    ring
  · simp
theorem log_two_pi_eq : Real.log (2 * Real.pi)
    = Real.log (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi) := by
  norm_num [sfrac]
theorem t_half_eq (t : ℝ) (tneg : Bool) (tn td : ℕ) (ht : t = sfrac tneg tn td) :
    t / 2 = sfrac tneg tn (2 * td) := by
  subst ht
  cases tneg <;> simp [sfrac] <;> ring
theorem stirling_coeff_mk (k bn bd : ℕ) (bneg : Bool)
    (hB : (bernoulli (2 * k) : ℝ) = sfrac bneg bn bd)
    (hk : Nat.ble 1 k = true) (hbd : Nat.ble 1 bd = true) :
    (bernoulli (2 * k) : ℂ) / (2 * (k : ℂ) * (2 * (k : ℂ) - 1))
      = ⟨sfrac bneg bn (bd.mul ((Nat.mul 2 k).mul ((Nat.mul 2 k).sub 1))),
         sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  simp only [Nat.mul_eq, Nat.sub_eq]
  have hk' : 0 < k := pos_of_ble hk
  have hbdR : (0 : ℝ) < bd := pos_real_of_ble hbd
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast Nat.le_of_ble_eq_true hk
  have hd : (2 * (k : ℂ) * (2 * (k : ℂ) - 1)) = (((2 * k * (2 * k - 1) : ℕ) : ℝ) : ℂ) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * k)]
    ring
  have hn : (bernoulli (2 * k) : ℂ) = ((bernoulli (2 * k) : ℝ) : ℂ) := by
    push_cast
    ring
  have hdR : (0 : ℝ) < ((2 * k * (2 * k - 1) : ℕ) : ℝ) := by
    have h1 : 0 < 2 * k * (2 * k - 1) := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast h1
  rw [hn, hd, ← Complex.ofReal_div]
  apply Complex.ext
  · rw [Complex.ofReal_re, hB]
    simp only [sfrac]
    cases bneg <;> (simp; field_simp)
  · rw [Complex.ofReal_im]
    simp [sfrac]
theorem zpow_one_sub_two_mul (w : ℂ) (k e : ℕ) (hk : Nat.ble 1 k = true)
    (he : Nat.beq (e.add 1) (Nat.mul 2 k) = true) :
    w ^ (1 - 2 * (k : ℤ)) = (w ^ e)⁻¹ := by
  have hk' : 0 < k := pos_of_ble hk
  have he' : e = 2 * k - 1 := by
    have h := Nat.eq_of_beq_eq_true he
    simp only [Nat.add_eq, Nat.mul_eq] at h
    omega
  subst he'
  have h : (1 - 2 * (k : ℤ)) = -(((2 * k - 1 : ℕ) : ℤ)) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * k)]
    ring
  rw [h, zpow_neg, zpow_natCast]
theorem pow_succ_c (w : ℂ) (m b : ℕ) (hb : Nat.beq b (m.add 1) = true) :
    w ^ b = w ^ m * w := by
  obtain rfl := Nat.eq_of_beq_eq_true hb
  exact pow_succ w m
theorem pow_one_c (w : ℂ) : w ^ (nat_lit 1) = w := pow_one w
theorem stirling_sum_base (w : ℂ) :
    (∑ k ∈ Finset.Icc (1 : ℕ) (nat_lit 0),
        (bernoulli (2 * k) : ℂ) / (2 * (k : ℂ) * (2 * (k : ℂ) - 1)) * w ^ (1 - 2 * (k : ℤ)))
      = ⟨sfrac false (nat_lit 0) (nat_lit 1), sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  have hIcc : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
  rw [hIcc, Finset.sum_empty]
  exact complex_zero_mk
theorem stirling_sum_succ (w : ℂ) (m b : ℕ) (hb : Nat.beq b (m.add 1) = true) :
    (∑ k ∈ Finset.Icc (1 : ℕ) b,
        (bernoulli (2 * k) : ℂ) / (2 * (k : ℂ) * (2 * (k : ℂ) - 1)) * w ^ (1 - 2 * (k : ℤ)))
      = (∑ k ∈ Finset.Icc (1 : ℕ) m,
          (bernoulli (2 * k) : ℂ) / (2 * (k : ℂ) * (2 * (k : ℂ) - 1)) * w ^ (1 - 2 * (k : ℤ)))
        + (bernoulli (2 * b) : ℂ) / (2 * (b : ℂ) * (2 * (b : ℂ) - 1)) * w ^ (1 - 2 * (b : ℤ)) := by
  obtain rfl := Nat.eq_of_beq_eq_true hb
  exact Finset.sum_Icc_succ_top (by omega) _
theorem log_sum_base (t : ℝ) :
    (∑ j ∈ Finset.range 0, Complex.log (1 / 4 + Complex.I * ((t : ℂ) / 2) + (j : ℂ)))
      = ⟨sfrac false (nat_lit 0) (nat_lit 1), sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  rw [Finset.range_zero, Finset.sum_empty]
  exact complex_zero_mk
theorem log_sum_succ (t : ℝ) (m b : ℕ) (hb : Nat.beq b (m.add 1) = true) :
    (∑ j ∈ Finset.range b, Complex.log (1 / 4 + Complex.I * ((t : ℂ) / 2) + (j : ℂ)))
      = (∑ j ∈ Finset.range m, Complex.log (1 / 4 + Complex.I * ((t : ℂ) / 2) + (j : ℂ)))
        + Complex.log (1 / 4 + Complex.I * ((t : ℂ) / 2) + (m : ℂ)) := by
  obtain rfl := Nat.eq_of_beq_eq_true hb
  exact Finset.sum_range_succ _ m
noncomputable def logSumC (t : ℝ) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range N, Complex.log (1 / 4 + Complex.I * ((t : ℂ) / 2) + (j : ℂ))
theorem log_sum_c_base (t : ℝ) : logSumC t (nat_lit 0)
    = ⟨sfrac false (nat_lit 0) (nat_lit 1), sfrac false (nat_lit 0) (nat_lit 1)⟩ :=
  log_sum_base t
theorem log_sum_c_succ (t : ℝ) (m b : ℕ) (hb : Nat.beq b (m.add 1) = true) :
    logSumC t b = logSumC t m + Complex.log (1 / 4 + Complex.I * ((t : ℂ) / 2) + (m : ℂ)) :=
  log_sum_succ t m b hb
theorem log_sum_c_eq (t : ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range N, Complex.log (1 / 4 + Complex.I * ((t : ℂ) / 2) + (j : ℂ)))
      = logSumC t N := rfl
theorem logGammaStirling_unfold (M : ℕ) (w : ℂ) :
    Complex.Stirling.logGammaStirling M w
      = (w - 1 / 2) * Complex.log w - w + (1 / 2 : ℂ) * (Real.log (2 * Real.pi) : ℂ)
        + ∑ k ∈ Finset.Icc 1 M,
            (bernoulli (2 * k) : ℂ) / (2 * (k : ℂ) * (2 * (k : ℂ) - 1)) * w ^ (1 - 2 * (k : ℤ)) :=
  rfl
theorem riemannSiegelThetaApproximant_named (M N : ℕ) (t : ℝ) :
    riemannSiegelThetaApproximant M N t
      = ((Complex.Stirling.logGammaStirling M (1 / 4 + Complex.I * (t / 2) + N)
            - ∑ j ∈ Finset.range N, Complex.log (1 / 4 + Complex.I * (t / 2) + j)).im
          - t / 2 * Real.log Real.pi) :=
  rfl
theorem riemannSiegelThetaApproximant_two_zero {t : ℝ} (ht : 0 < t) :
    riemannSiegelThetaApproximant 2 0 t
      = t / 4 * Real.log (1 / 16 + t ^ 2 / 4) - 1 / 4 * (Real.pi / 2 - Real.arctan (1 / (2 * t)))
        - t / 2 - t / 2 * Real.log Real.pi
        - (t / 2) / (12 * (1 / 16 + t ^ 2 / 4))
        + (3 * (1 / 16) * (t / 2) - (t / 2) ^ 3) / (360 * (1 / 16 + t ^ 2 / 4) ^ 3) := by
  set w : ℂ := 1 / 4 + Complex.I * (t / 2) with hw
  have hre : w.re = 1 / 4 := by simp [hw]
  have him : w.im = t / 2 := by simp [hw]
  have hnsq : Complex.normSq w = 1 / 16 + t ^ 2 / 4 := by
    rw [Complex.normSq_apply, hre, him]; ring
  have hnsq_pos : 0 < 1 / 16 + t ^ 2 / 4 := by positivity
  have harg : Complex.arg w = Real.pi / 2 - Real.arctan (1 / (2 * t)) := by
    rw [Complex.arg_eq_arctan (by rw [hre]; norm_num), hre, him]
    have h2t : 0 < 2 * t := by positivity
    rw [show t / 2 / (1 / 4) = 2 * t by ring, one_div, Real.arctan_inv_of_pos h2t]
    ring
  have hlog : Real.log ‖w‖ = 1 / 2 * Real.log (1 / 16 + t ^ 2 / 4) := by
    rw [Complex.norm_def, hnsq, Real.log_sqrt hnsq_pos.le]; ring
  have hw3im : (w ^ 3).im = 3 * (1 / 16) * (t / 2) - (t / 2) ^ 3 := by
    simp only [pow_succ, pow_zero, one_mul, Complex.mul_im, Complex.mul_re, hre, him]; ring
  have hw3nsq : Complex.normSq (w ^ 3) = (1 / 16 + t ^ 2 / 4) ^ 3 := by
    rw [map_pow, hnsq]
  simp only [riemannSiegelThetaApproximant, Nat.cast_zero, add_zero, Finset.range_zero,
    Finset.sum_empty, sub_zero, Complex.Stirling.logGammaStirling_two]
  rw [← hw]
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.inv_im, Complex.log_re,
    Complex.log_im, Complex.sub_re, hre, him, harg, hlog, hw3im, hw3nsq, hnsq,
    Complex.ofReal_im, Complex.ofReal_re]
  norm_num
  field_simp
  ring
theorem riemannSiegelThetaApproximant_two_zero_mk (t : ℝ) (tn td S Q V T4 T2 Rn Rd : ℕ)
    (ht : t = sfrac false tn td) (htn : Nat.ble 1 tn = true) (htd : Nat.ble 1 td = true)
    (hS : Nat.beq S ((td.mul td).add ((Nat.mul 4 tn).mul tn)) = true)
    (hQ : Nat.beq Q ((Nat.mul 16 td).mul td) = true) (hV : Nat.beq V (Nat.mul 2 tn) = true)
    (hT4 : Nat.beq T4 (Nat.mul 4 td) = true) (hT2 : Nat.beq T2 (Nat.mul 2 td) = true)
    (hRn : Nat.beq (Rn.add ((Nat.mul 48 tn).mul (td.pow 5)))
      (((Nat.mul 30 tn).mul td).mul (S.pow 2) |>.add ((Nat.mul 64 (tn.pow 3)).mul (td.pow 3)))
      = true)
    (hRd : Nat.beq Rd (Nat.mul 45 (S.pow 3)) = true) :
    riemannSiegelThetaApproximant 2 0 t
      = sfrac false tn T4 * Real.log (sfrac false S Q)
        - sfrac false 1 4 * (sfrac false 1 2 * Real.pi - Real.arctan ((td : ℝ) / (V : ℝ)))
        - sfrac false tn T2 - sfrac false tn T2 * Real.log Real.pi + sfrac true Rn Rd := by
  simp only [Nat.beq_eq, Nat.mul_eq, Nat.add_eq, Nat.pow_eq] at hS hQ hV hT4 hT2 hRn hRd
  subst hS hQ hV hT4 hT2 hRd ht
  have hn : (0 : ℝ) < tn := pos_real_of_ble htn
  have hd : (0 : ℝ) < td := pos_real_of_ble htd
  have hRn' : (Rn : ℝ) = 30 * tn * td * ((td : ℝ) * td + 4 * tn * tn) ^ 2
      + 64 * (tn : ℝ) ^ 3 * td ^ 3 - 48 * tn * (td : ℝ) ^ 5 := by
    have := congrArg (fun n : ℕ ↦ (n : ℝ)) hRn
    push_cast at this
    linarith
  rw [riemannSiegelThetaApproximant_two_zero (by rw [sfrac_false_div]; positivity)]
  simp only [sfrac, if_false, if_true, one_mul, neg_one_mul, Bool.false_eq_true]
  have hlog : (1 / 16 + ((tn : ℝ) / td) ^ 2 / 4)
      = (((td * td + 4 * tn * tn : ℕ) : ℝ) / ((16 * td * td : ℕ) : ℝ)) := by
    push_cast; field_simp; ring
  have hatan : 1 / (2 * ((tn : ℝ) / td)) = (td : ℝ) / ((2 * tn : ℕ) : ℝ) := by
    push_cast; field_simp
  rw [hlog, hatan, hRn']
  push_cast
  field_simp
  ring
theorem theta_err_eq (M N A B : ℕ)
    (hA : Nat.mul (factNat (Nat.succ (Nat.mul 2 M))) (Nat.pow 4 (Nat.mul 2 M)) = A)
    (hB : Nat.mul (Nat.mul 2 M) (Nat.pow (Nat.succ (Nat.mul 4 N)) (Nat.mul 2 M)) = B)
    (hM : Nat.ble 1 M = true) :
    riemannSiegelThetaStirlingErrorBound M N
      = sfrac false A B * ((2 * Real.pi) ^ (Nat.mul 2 M))⁻¹ := by
  obtain rfl := hA
  obtain rfl := hB
  simp only [factNat_eq, Nat.succ_eq_add_one, Nat.mul_eq, Nat.pow_eq]
  have hM' : 0 < M := pos_of_ble hM
  have hMR : (0 : ℝ) < 2 * M := by
    have : (0 : ℕ) < 2 * M := by omega
    exact_mod_cast this
  have hpi : (0 : ℝ) < (2 * Real.pi) ^ (2 * M) := by positivity
  have h4N : (0 : ℝ) < (4 * (N : ℝ) + 1) ^ (2 * M) := by positivity
  have hz : ((1 / 4 + N : ℝ)) ^ (-(2 * M : ℤ)) = ((1 / 4 + (N : ℝ)) ^ (2 * M))⁻¹ := by
    rw [show (-(2 * M : ℤ)) = -((2 * M : ℕ) : ℤ) from by push_cast; ring, zpow_neg,
      zpow_natCast]
  have hbase : (1 / 4 + (N : ℝ)) = (4 * (N : ℝ) + 1) / 4 := by ring
  rw [riemannSiegelThetaStirlingErrorBound, hz, hbase, div_pow, sfrac_false_div]
  push_cast
  field_simp
theorem theta_err_eq' (t : ℝ) (tn td M N A B : ℕ) (ht : t = sfrac false tn td)
    (hA : Nat.mul (Nat.mul (factNat (Nat.succ (Nat.mul 2 M))) (Nat.pow 2 (Nat.succ (Nat.mul 2 M))))
      (Nat.pow (Nat.mul 16 (Nat.mul td td)) M) = A)
    (hB : Nat.mul (Nat.mul 2 M) (Nat.pow (Nat.add
      (Nat.mul (Nat.mul (Nat.succ (Nat.mul 4 N)) (Nat.succ (Nat.mul 4 N))) (Nat.mul td td))
      (Nat.mul 4 (Nat.mul tn tn))) M) = B)
    (hM : Nat.ble 1 M = true) (htd : Nat.ble 1 td = true) :
    riemannSiegelThetaStirlingErrorBound' M N t
      = sfrac false A B * ((2 * Real.pi) ^ (Nat.mul 2 M))⁻¹ := by
  obtain rfl := hA
  obtain rfl := hB
  subst ht
  simp only [factNat_eq, Nat.succ_eq_add_one, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
  have hd : (0 : ℝ) < td := pos_real_of_ble htd
  have hMR : (0 : ℝ) < 2 * M := by linarith [pos_real_of_ble hM]
  have hz : ((1 / 4 + N : ℝ) ^ 2 + (sfrac false tn td / 2) ^ 2) ^ (-(M : ℤ))
      = ((((4 * N + 1) * (4 * N + 1) * (td * td) + 4 * (tn * tn) : ℝ) / (16 * (td * td)))
            ^ M)⁻¹ := by
    rw [zpow_neg, zpow_natCast, sfrac_false_div]
    congr 2
    field_simp
    ring
  rw [riemannSiegelThetaStirlingErrorBound', hz, div_pow, sfrac_false_div]
  push_cast
  field_simp
theorem norm_eq_sqrt_mul_add (z : ℂ) : ‖z‖ = Real.sqrt (z.re * z.re + z.im * z.im) := by
  rw [Complex.norm_def, Complex.normSq_apply]
theorem two_pi_eq : (2 : ℝ) * Real.pi = sfrac false (nat_lit 2) (nat_lit 1) * Real.pi := by
  norm_num [sfrac]
theorem natCast_mul_pi_eq (n : ℕ) : (n : ℝ) * Real.pi = sfrac false n (nat_lit 1) * Real.pi := by
  norm_num [sfrac]
theorem pow_succ_r (x : ℝ) (m b : ℕ) (hb : Nat.beq b (m.add 1) = true) :
    x ^ b = x ^ m * x := by
  obtain rfl := Nat.eq_of_beq_eq_true hb
  exact pow_succ x m
theorem pow_one_r (x : ℝ) : x ^ (nat_lit 1) = x := pow_one x
theorem zrb_shape_eq (x c t : ℝ) (m : ℕ) :
    x / ((1 / 2 + Complex.I * (t : ℂ)).re + ((m : ℕ) : ℝ)) * c
      = x * sfrac false (nat_lit 2) (Nat.add 1 (Nat.mul 2 m)) * c := by
  simp only [Nat.mul_eq, Nat.add_eq]
  have hre : (1 / 2 + Complex.I * (t : ℂ)).re + ((m : ℕ) : ℝ) = ((1 + 2 * m : ℕ) : ℝ) / 2 := by
    simp
    ring
  rw [hre, sfrac_false_div]
  have h0 : ((1 + 2 * m : ℕ) : ℝ) ≠ 0 := by
    have : (0 : ℕ) < 1 + 2 * m := by omega
    exact_mod_cast Nat.pos_iff_ne_zero.mp this
  field_simp
  ring
theorem cpow_neg_s_sub_mk (t : ℝ) (tn td n m P : ℕ) (ht : t = sfrac false tn td)
    (hn : Nat.ble 1 n = true) (hP : Nat.pow n (Nat.add 1 (Nat.mul 2 m)) = P) :
    (n : ℂ) ^ (-(1 / 2 + Complex.I * (t : ℂ)) - ((m : ℕ) : ℂ))
      = ⟨(Real.sqrt (P : ℝ))⁻¹
            * Real.cos (sfrac false tn td * Real.log (sfrac false n (nat_lit 1))),
         (Real.sqrt (P : ℝ))⁻¹
            * -Real.sin (sfrac false tn td * Real.log (sfrac false n (nat_lit 1)))⟩ := by
  obtain rfl := hP
  simp only [Nat.mul_eq, Nat.add_eq, Nat.pow_eq]
  have hn' : 0 < n := pos_of_ble hn
  have hnR : (0 : ℝ) < n := pos_real_of_ble hn
  have hexp : -(1 / 2 + Complex.I * (t : ℂ)) - ((m : ℕ) : ℂ)
      = ((-(1 / 2) - m : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hexp, natCast_cpow_eq n hn' (-(1 / 2) - m) (-t)]
  have hmag : Real.exp ((-(1 / 2) - m) * Real.log n)
      = (Real.sqrt ((n ^ (1 + 2 * m) : ℕ) : ℝ))⁻¹ := by
    have h1 : (((nat_lit 1 : ℕ) : ℝ) / ((n ^ (1 + 2 * m) : ℕ) : ℝ))
        = Real.exp (-(((1 + 2 * m : ℕ) : ℝ) * Real.log n)) := by
      rw [Nat.cast_one, one_div, Real.exp_neg]
      congr 1
      rw [← Real.log_pow, Real.exp_log (by positivity), Nat.cast_pow]
    have h2 : Real.exp ((-(1 / 2) - m) * Real.log n)
        = Real.sqrt (((nat_lit 1 : ℕ) : ℝ) / ((n ^ (1 + 2 * m) : ℕ) : ℝ)) := by
      rw [h1, ← Real.exp_half]
      congr 1
      push_cast
      ring
    rw [h2, Nat.cast_one, one_div, Real.sqrt_inv]
  have hlogsfrac : Real.log (sfrac false n (nat_lit 1)) = Real.log n := by
    rw [sfrac_false_div]; simp
  subst ht
  apply Complex.ext <;>
    simp only [hlogsfrac, neg_mul, Real.cos_neg, Real.sin_neg, hmag]
theorem main_sum_rs_term_mk (θ t : ℝ) (tn td n : ℕ) (ht : t = sfrac false tn td) :
    Real.cos (θ - t * Real.log n) / Real.sqrt n
      = (Real.sqrt (n : ℝ))⁻¹
          * Real.cos (θ - sfrac false tn td * Real.log (sfrac false n (nat_lit 1))) := by
  have hlogsfrac : Real.log (sfrac false n (nat_lit 1)) = Real.log n := by
    rw [sfrac_false_div]; simp
  subst ht
  rw [hlogsfrac, div_eq_inv_mul]
noncomputable def mainSumRS (θ t : ℝ) (ν : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ν, Real.cos (θ - t * Real.log n) / Real.sqrt n
theorem main_sum_rs_base (θ t : ℝ) :
    mainSumRS θ t (nat_lit 0) = sfrac false (nat_lit 0) (nat_lit 1) := by
  have hIcc : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
  rw [mainSumRS, hIcc, Finset.sum_empty]
  simp [sfrac]
theorem main_sum_rs_succ (θ t : ℝ) (a b : ℕ) (hb : Nat.beq b (a.add 1) = true) :
    mainSumRS θ t b
      = mainSumRS θ t a + Real.cos (θ - t * Real.log b) / Real.sqrt b := by
  obtain rfl := Nat.eq_of_beq_eq_true hb
  exact Finset.sum_Icc_succ_top (Nat.le_add_left 1 a) _
theorem main_sum_rs_one (θ t : ℝ) : mainSumRS θ t (nat_lit 1) = Real.cos θ := by
  rw [main_sum_rs_succ θ t (nat_lit 0) (nat_lit 1) (by rfl), main_sum_rs_base]
  simp [sfrac]
theorem main_sum_of_phase_eq (θ t : ℝ) (ν : ℕ) :
    Zeta.RiemannSiegel.mainSumOfPhase θ t ν = mainSumRS θ t ν + mainSumRS θ t ν :=
  two_mul (mainSumRS θ t ν)
noncomputable def quadSignPos : ℝ := 1
noncomputable def quadSignNeg : ℝ := -1
theorem abs_quadSignPos : |quadSignPos| = 1 := by simp [quadSignPos]
theorem abs_quadSignNeg : |quadSignNeg| = 1 := by simp [quadSignNeg]
theorem sfrac_eq_quadSignPos_mul (n : Bool) (c q : ℕ) :
    sfrac n c q = quadSignPos * sfrac n c q := by
  simp [quadSignPos]
theorem sfrac_not_eq_quadSignNeg_mul (n : Bool) (c q : ℕ) :
    sfrac (!n) c q = quadSignNeg * sfrac n c q := by
  rw [sfrac_not, quadSignNeg, neg_one_mul]
private theorem exists_eq_four_mul_add_of_mod (k j : ℕ) (hk : Nat.beq (k % 4) j = true) :
    ∃ q : ℕ, k = 4 * q + j :=
  ⟨k / 4, by have := Nat.eq_of_beq_eq_true hk; have := Nat.div_add_mod k 4; omega⟩
theorem cos_quad_nat0 (k : ℕ) (hk : Nat.beq (k % 4) 0 = true) (r : ℝ) :
    Real.cos (r + (k : ℝ) * (Real.pi / 2)) = quadSignPos * Real.cos r := by
  obtain ⟨q, rfl⟩ := exists_eq_four_mul_add_of_mod k 0 hk
  rw [quadSignPos, one_mul, ← cos_quad0 r q]; push_cast; ring_nf
theorem cos_quad_nat1 (k : ℕ) (hk : Nat.beq (k % 4) 1 = true) (r : ℝ) :
    Real.cos (r + (k : ℝ) * (Real.pi / 2)) = quadSignNeg * Real.sin r := by
  obtain ⟨q, rfl⟩ := exists_eq_four_mul_add_of_mod k 1 hk
  rw [quadSignNeg, neg_one_mul, ← cos_quad1 r q]; push_cast; ring_nf
theorem cos_quad_nat2 (k : ℕ) (hk : Nat.beq (k % 4) 2 = true) (r : ℝ) :
    Real.cos (r + (k : ℝ) * (Real.pi / 2)) = quadSignNeg * Real.cos r := by
  obtain ⟨q, rfl⟩ := exists_eq_four_mul_add_of_mod k 2 hk
  rw [quadSignNeg, neg_one_mul, ← cos_quad2 r q]; push_cast; ring_nf
theorem cos_quad_nat3 (k : ℕ) (hk : Nat.beq (k % 4) 3 = true) (r : ℝ) :
    Real.cos (r + (k : ℝ) * (Real.pi / 2)) = quadSignPos * Real.sin r := by
  obtain ⟨q, rfl⟩ := exists_eq_four_mul_add_of_mod k 3 hk
  rw [quadSignPos, one_mul, ← cos_quad3 r q]; push_cast; ring_nf
theorem mainSumTerm_bound (θ : ℝ) (g : ℝ → ℝ) (ε : ℝ) (b tn td k B DI M : ℕ)
    (nθ : Bool) (cθ rθ cL rL cA rA : ℕ) (nφ : Bool) (u Pc rπ : ℕ) (nI : Bool) (cI : ℕ) (nC : Bool)
    (hε : |ε| = 1) (hquad : ∀ r : ℝ, Real.cos (r + (k : ℝ) * (Real.pi / 2)) = ε * g r)
    (hsign : sfrac nC cI B = ε * sfrac nI cI B)
    (htd : td ≠ 0) (hB : B ≠ 0) (hM : M ≠ 0) (hDI' : (2 : ℝ) * DI = B)
    (hθ : Real.IsNear θ nθ cθ B rθ B)
    (hL : Real.IsNear (Real.log (sfrac false b (nat_lit 1))) false cL B rL B)
    (hA : Real.IsNear (Real.sqrt (b : ℝ))⁻¹ false cA B rA B)
    (hpi : Real.IsNear Real.pi false Pc M rπ M)
    (hI : Real.IsNear (g ((u : ℝ) / (B : ℝ))) nI cI B 1 DI)
    (hφ : natAbsSubLe (numPosC nθ (td.mul cθ)) ((numNegC nθ (td.mul cθ)).add (tn.mul cL))
      (td.mul B) (numPosC nφ (((Nat.mul 2 M).mul u).add ((k.mul Pc).mul B)))
      (numNegC nφ (((Nat.mul 2 M).mul u).add ((k.mul Pc).mul B))) ((Nat.mul 2 M).mul B)
      (nat_lit 1) B = true) :
    |(Real.sqrt (b : ℝ))⁻¹ * Real.cos (θ - sfrac false tn td * Real.log (sfrac false b 1))
        - sfrac false cA B * sfrac nC cI B|
      ≤ (rA : ℝ) / B + sfrac false cA B
          * (((rθ : ℝ) + 3) / B + sfrac false tn td * ((rL : ℝ) / B) + (k : ℝ) * rπ / (2 * M)) := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast Nat.pos_of_ne_zero hB
  have hMr : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have hφ' := abs_sub_le_of_natAbsSubLe
    (Nat.pos_of_ne_zero (by simp [Nat.mul_eq, htd, hB]))
    (Nat.pos_of_ne_zero (by simp [Nat.mul_eq, hM, hB])) (Nat.pos_of_ne_zero hB) hφ
  simp only [Nat.mul_eq, Nat.add_eq, numPosC_eq, numNegC_eq] at hφ'
  have eφ : ((((numPos nθ (td * cθ) : ℕ) : ℝ)
      - ((numNeg nθ (td * cθ) + tn * cL : ℕ) : ℝ)) / ((td * B : ℕ) : ℝ))
      = sfrac nθ cθ B - sfrac false tn td * sfrac false cL B := by
    rw [sfrac_eq_parts, sfrac_false_div, sfrac_false_div]
    cases nθ <;> simp [numPos, numNeg] <;> field_simp
    all_goals ring
  set σ : ℝ := if nφ then -1 else 1 with hσdef
  set r : ℝ := (u : ℝ) / B
  set Pr : ℝ := sfrac false Pc M
  have eY : (((numPos nφ (2 * M * u + k * Pc * B) : ℕ) : ℝ)
      - ((numNeg nφ (2 * M * u + k * Pc * B) : ℕ) : ℝ)) / ((2 * M * B : ℕ) : ℝ)
      = σ * (r + (k : ℝ) * (Pr / 2)) := by
    rw [← sfrac_eq_parts, sfrac, show Pr = (Pc : ℝ) / M from sfrac_false_div Pc M, hσdef]
    simp only [r]
    push_cast
    field_simp
  rw [eφ, eY] at hφ'
  have hσ : |σ| = 1 := by rw [hσdef]; split <;> simp
  have hpi' : |Pr - Real.pi| ≤ (rπ : ℝ) / M := by
    have := hpi; rw [Real.IsNear, abs_sub_comm] at this; exact this
  set ψ : ℝ := σ * (r + (k : ℝ) * (Real.pi / 2))
  have hψ : |σ * (r + (k : ℝ) * (Pr / 2)) - ψ| ≤ (k : ℝ) * rπ / (2 * M) := by
    have e : σ * (r + (k : ℝ) * (Pr / 2)) - ψ = σ * ((k : ℝ) * ((Pr - Real.pi) / 2)) := by ring
    rw [e, abs_mul, hσ, one_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_div, abs_two]
    calc (k : ℝ) * (|Pr - Real.pi| / 2) ≤ (k : ℝ) * (((rπ : ℝ) / M) / 2) := by gcongr
      _ = (k : ℝ) * rπ / (2 * M) := by field_simp
  have hcosψ : Real.cos ψ = ε * g r := by
    have : Real.cos ψ = Real.cos (r + (k : ℝ) * (Real.pi / 2)) := by
      simp only [ψ, σ]; split
      · rw [neg_one_mul, Real.cos_neg]
      · rw [one_mul]
    rw [this, hquad]
  simp only [Real.IsNear] at hθ hL hA hI
  rw [Nat.cast_one] at hI
  have hT : 0 ≤ sfrac false tn td := by rw [sfrac_false_div]; positivity
  have hAc : 0 ≤ sfrac false cA B := by rw [sfrac_false_div]; positivity
  set L := Real.log (sfrac false b 1)
  set A := (Real.sqrt (b : ℝ))⁻¹
  set T := sfrac false tn td with hTdef
  have hphase : |θ - T * L - ψ|
      ≤ (rθ : ℝ) / B + T * ((rL : ℝ) / B) + 1 / (B : ℝ) + (k : ℝ) * rπ / (2 * M) := by
    have : θ - T * L - ψ = (θ - sfrac nθ cθ B) - T * (L - sfrac false cL B)
        + (sfrac nθ cθ B - T * sfrac false cL B - σ * (r + (k : ℝ) * (Pr / 2)))
        + (σ * (r + (k : ℝ) * (Pr / 2)) - ψ) := by ring
    rw [this]
    calc _ ≤ |θ - sfrac nθ cθ B| + |T * (L - sfrac false cL B)|
          + |sfrac nθ cθ B - T * sfrac false cL B - σ * (r + (k : ℝ) * (Pr / 2))|
          + |σ * (r + (k : ℝ) * (Pr / 2)) - ψ| := by
            refine (abs_add_le _ _).trans ?_
            gcongr
            refine (abs_add_le _ _).trans ?_
            gcongr
            exact abs_sub _ _
      _ ≤ _ := by
            rw [abs_mul, abs_of_nonneg hT]
            gcongr
            simpa using hφ'
  set ρ : ℝ := ((rθ : ℝ) + 3) / B + T * ((rL : ℝ) / B) + (k : ℝ) * rπ / (2 * M)
  have hcos : |Real.cos (θ - T * L) - sfrac nC cI B| ≤ ρ := by
    rw [hsign]
    calc _ ≤ |Real.cos (θ - T * L) - Real.cos ψ| + |Real.cos ψ - ε * sfrac nI cI B| :=
          abs_sub_le _ _ _
      _ ≤ ((rθ : ℝ) / B + T * ((rL : ℝ) / B) + 1 / (B : ℝ) + (k : ℝ) * rπ / (2 * M))
          + 1 / (DI : ℝ) := by
            gcongr
            · exact (Real.abs_cos_sub_cos_le _ _).trans hphase
            · rw [hcosψ, ← mul_sub, abs_mul, hε, one_mul]; exact hI
      _ = ρ := by
            have hDIr : (DI : ℝ) = B / 2 := by linarith
            rw [hDIr]; simp only [ρ]; field_simp; ring
  have hterm : |A * Real.cos (θ - T * L) - sfrac false cA B * sfrac nC cI B|
      ≤ (rA : ℝ) / B + sfrac false cA B * ρ := by
    have : A * Real.cos (θ - T * L) - sfrac false cA B * sfrac nC cI B
        = (A - sfrac false cA B) * Real.cos (θ - T * L)
          + sfrac false cA B * (Real.cos (θ - T * L) - sfrac nC cI B) := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hAc]
    gcongr
    calc |A - sfrac false cA B| * |Real.cos (θ - T * L)| ≤ |A - sfrac false cA B| * 1 := by
          gcongr; exact Real.abs_cos_le_one _
      _ ≤ _ := by rw [mul_one]; exact hA
  exact hterm
theorem mainSumRS_step (θ t : ℝ) (g : ℝ → ℝ) (ε : ℝ) (a b tn td k B DI M : ℕ)
    (nθ : Bool) (cθ rθ cL rL cA rA : ℕ) (nS : Bool) (cS rS : ℕ) (nφ : Bool) (u Pc rπ : ℕ)
    (nI : Bool) (cI : ℕ) (nC nR : Bool) (cR rR : ℕ)
    (hε : |ε| = 1) (hquad : ∀ r : ℝ, Real.cos (r + (k : ℝ) * (Real.pi / 2)) = ε * g r)
    (hsign : sfrac nC cI B = ε * sfrac nI cI B)
    (ht : t = sfrac false tn td) (hb : Nat.beq b (a.add 1) = true)
    (hS : Real.IsNear (mainSumRS θ t a) nS cS B rS B)
    (hθ : Real.IsNear θ nθ cθ B rθ B)
    (hL : Real.IsNear (Real.log (sfrac false b (nat_lit 1))) false cL B rL B)
    (hA : Real.IsNear (Real.sqrt (b : ℝ))⁻¹ false cA B rA B)
    (hpi : Real.IsNear Real.pi false Pc M rπ M)
    (hI : Real.IsNear (g ((u : ℝ) / (B : ℝ))) nI cI B 1 DI)
    (hpos : Nat.ble (nat_lit 1) (((td.mul B).mul M).mul DI) = true)
    (hDI : Nat.beq (Nat.mul 2 DI) B = true)
    (hφ : natAbsSubLe (numPosC nθ (td.mul cθ)) ((numNegC nθ (td.mul cθ)).add (tn.mul cL))
      (td.mul B) (numPosC nφ (((Nat.mul 2 M).mul u).add ((k.mul Pc).mul B)))
      (numNegC nφ (((Nat.mul 2 M).mul u).add ((k.mul Pc).mul B))) ((Nat.mul 2 M).mul B)
      (nat_lit 1) B = true)
    (hR : natAbsSubLe (((numPosC nS cS).mul B).add (cA.mul (numPosC nC cI)))
      (((numNegC nS cS).mul B).add (cA.mul (numNegC nC cI))) (B.mul B)
      (numPosC nR cR) (numNegC nR cR) B (nat_lit 1) B = true)
    (hrad : Nat.ble (((((rS.add rA).add 1).mul B).mul td).mul (Nat.mul 2 M) |>.add
        (cA.mul (((Nat.mul 2 M).mul ((td.mul (rθ.add 3)).add (tn.mul rL))).add
          ((k.mul rπ).mul (td.mul B)))))
      (((rR.mul B).mul td).mul (Nat.mul 2 M)) = true) :
    Real.IsNear (mainSumRS θ t b) nR cR B rR B := by
  rw [main_sum_rs_succ θ t a b hb, main_sum_rs_term_mk θ t tn td b ht]
  simp only [Nat.ble_eq, Nat.mul_eq] at hpos
  have hp : td ≠ 0 ∧ B ≠ 0 ∧ M ≠ 0 ∧ DI ≠ 0 := by
    simpa [Nat.one_le_iff_ne_zero, Nat.mul_ne_zero_iff, and_assoc] using hpos
  obtain ⟨htd, hB, hM, hDI0⟩ := hp
  have hDI' : (2 : ℝ) * DI = B := by
    have := Nat.eq_of_beq_eq_true hDI; simp only [Nat.mul_eq] at this; exact_mod_cast this
  have hBr : (0 : ℝ) < B := by exact_mod_cast Nat.pos_of_ne_zero hB
  have hMr : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have htdr : (0 : ℝ) < td := by exact_mod_cast Nat.pos_of_ne_zero htd
  have hterm := mainSumTerm_bound θ g ε b tn td k B DI M nθ cθ rθ cL rL cA rA nφ u Pc rπ nI cI nC
    hε hquad hsign htd hB hM hDI' hθ hL hA hpi hI hφ
  simp only [Real.IsNear] at hS ⊢
  set T := sfrac false tn td with hTdef
  set L := Real.log (sfrac false b 1)
  set A := (Real.sqrt (b : ℝ))⁻¹
  set ρ : ℝ := ((rθ : ℝ) + 3) / B + T * ((rL : ℝ) / B) + (k : ℝ) * rπ / (2 * M)
  have hR' := abs_sub_le_of_natAbsSubLe
    (Nat.pos_of_ne_zero (by simp [Nat.mul_eq, hB])) (Nat.pos_of_ne_zero hB)
    (Nat.pos_of_ne_zero hB) hR
  simp only [Nat.mul_eq, Nat.add_eq, numPosC_eq, numNegC_eq] at hR'
  have eR' : ((((numPos nS cS * B + cA * numPos nC cI : ℕ) : ℝ)
      - ((numNeg nS cS * B + cA * numNeg nC cI : ℕ) : ℝ)) / ((B * B : ℕ) : ℝ))
      = sfrac nS cS B + sfrac false cA B * sfrac nC cI B := by
    rw [sfrac_eq_parts nS, sfrac_eq_parts nC, sfrac_false_div]
    push_cast
    field_simp
    ring
  rw [eR', ← sfrac_eq_parts] at hR'
  have hsum : |mainSumRS θ t a + A * Real.cos (θ - T * L) - sfrac nR cR B|
      ≤ (rS : ℝ) / B + ((rA : ℝ) / B + sfrac false cA B * ρ) + 1 / B := by
    have : mainSumRS θ t a + A * Real.cos (θ - T * L) - sfrac nR cR B
        = (mainSumRS θ t a - sfrac nS cS B)
          + (A * Real.cos (θ - T * L) - sfrac false cA B * sfrac nC cI B)
          + (sfrac nS cS B + sfrac false cA B * sfrac nC cI B - sfrac nR cR B) := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    gcongr
    · refine (abs_add_le _ _).trans ?_
      gcongr
    · simpa using hR'
  refine hsum.trans ?_
  simp only [Nat.ble_eq, Nat.mul_eq, Nat.add_eq] at hrad
  have hrad' : (((rS + rA + 1) * B * td * (2 * M) + cA * (2 * M * (td * (rθ + 3) + tn * rL)
      + k * rπ * (td * B)) : ℕ) : ℝ) ≤ ((rR * B * td * (2 * M) : ℕ) : ℝ) := by exact_mod_cast hrad
  push_cast at hrad'
  have hden : (0 : ℝ) < (B : ℝ) * B * td * (2 * M) := by positivity
  have key : (rS : ℝ) / B + ((rA : ℝ) / B + sfrac false cA B * ρ) + 1 / B
      = (((rS : ℝ) + rA + 1) * B * td * (2 * M) + cA * (2 * M * (td * ((rθ : ℝ) + 3) + tn * rL)
          + k * rπ * (td * B))) / ((B : ℝ) * B * td * (2 * M)) := by
    simp only [ρ, hTdef, sfrac_false_div]
    field_simp
    ring
  have keyR : (rR : ℝ) / B = (rR : ℝ) * B * td * (2 * M) / ((B : ℝ) * B * td * (2 * M)) := by
    field_simp
  rw [key, keyR]
  exact div_le_div_of_nonneg_right hrad' hden.le
def natFloorLe (XP XN : ℕ) (nR : Bool) (cR B : ℕ) : Bool :=
  Nat.ble (((numPosC nR cR).mul B).add XN) (XP.add ((numNegC nR cR).mul B)) &&
    Nat.ble (XP.add ((numNegC nR cR).mul B)) ((((numPosC nR cR).mul B).add XN).add B)
theorem abs_sub_le_of_natFloorLe {XP XN cR B : ℕ} {nR : Bool} (hB : 0 < B)
    (h : natFloorLe XP XN nR cR B = true) :
    |((XP : ℝ) - XN) / ((B * B : ℕ) : ℝ) - sfrac nR cR B| ≤ 1 / (B : ℝ) := by
  simp only [natFloorLe, Bool.and_eq_true, Nat.ble_eq, Nat.mul_eq, Nat.add_eq, numPosC_eq,
    numNegC_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have h1' : ((numPos nR cR : ℝ) * B + XN) ≤ XP + (numNeg nR cR : ℝ) * B := by exact_mod_cast h1
  have h2' : ((XP : ℝ) + (numNeg nR cR : ℝ) * B) ≤ (numPos nR cR : ℝ) * B + XN + B := by
    exact_mod_cast h2
  rw [sfrac_eq_parts, abs_le]
  push_cast
  constructor
  · rw [show ((XP : ℝ) - XN) / (B * B) - (numPos nR cR - numNeg nR cR) / B
        = (XP - XN - (numPos nR cR - numNeg nR cR) * B) / (B * B) by field_simp]
    have : (0 : ℝ) ≤ (XP - XN - (numPos nR cR - numNeg nR cR) * B) / (B * B) := by
      apply div_nonneg _ (by positivity); linarith
    linarith [show (0 : ℝ) ≤ 1 / B by positivity]
  · rw [show ((XP : ℝ) - XN) / (B * B) - (numPos nR cR - numNeg nR cR) / B
        = (XP - XN - (numPos nR cR - numNeg nR cR) * B) / (B * B) by field_simp,
      div_le_div_iff₀ (by positivity) hBr]
    nlinarith
theorem mainSumRS_step2 (θ t : ℝ) (g₁ g₂ : ℝ → ℝ) (ε₁ ε₂ : ℝ) (a b₁ b₂ tn td k₁ k₂ B DI M : ℕ)
    (nθ : Bool) (cθ rθ cL₁ rL₁ cA₁ rA₁ cL₂ rL₂ cA₂ rA₂ : ℕ) (nS : Bool) (cS rS : ℕ)
    (nφ₁ : Bool) (u₁ : ℕ) (nφ₂ : Bool) (u₂ Pc rπ : ℕ)
    (nI₁ : Bool) (cI₁ : ℕ) (nC₁ nI₂ : Bool) (cI₂ : ℕ) (nC₂ nR : Bool) (cR rR : ℕ)
    (hε₁ : |ε₁| = 1) (hquad₁ : ∀ r : ℝ, Real.cos (r + (k₁ : ℝ) * (Real.pi / 2)) = ε₁ * g₁ r)
    (hsign₁ : sfrac nC₁ cI₁ B = ε₁ * sfrac nI₁ cI₁ B)
    (hε₂ : |ε₂| = 1) (hquad₂ : ∀ r : ℝ, Real.cos (r + (k₂ : ℝ) * (Real.pi / 2)) = ε₂ * g₂ r)
    (hsign₂ : sfrac nC₂ cI₂ B = ε₂ * sfrac nI₂ cI₂ B)
    (ht : t = sfrac false tn td) (hb₁ : Nat.beq b₁ (a.add 1) = true)
    (hb₂ : Nat.beq b₂ (b₁.add 1) = true)
    (hS : Real.IsNear (mainSumRS θ t a) nS cS B rS B)
    (hθ : Real.IsNear θ nθ cθ B rθ B)
    (hL₁ : Real.IsNear (Real.log (sfrac false b₁ (nat_lit 1))) false cL₁ B rL₁ B)
    (hA₁ : Real.IsNear (Real.sqrt (b₁ : ℝ))⁻¹ false cA₁ B rA₁ B)
    (hL₂ : Real.IsNear (Real.log (sfrac false b₂ (nat_lit 1))) false cL₂ B rL₂ B)
    (hA₂ : Real.IsNear (Real.sqrt (b₂ : ℝ))⁻¹ false cA₂ B rA₂ B)
    (hpi : Real.IsNear Real.pi false Pc M rπ M)
    (hI₁ : Real.IsNear (g₁ ((u₁ : ℝ) / (B : ℝ))) nI₁ cI₁ B 1 DI)
    (hI₂ : Real.IsNear (g₂ ((u₂ : ℝ) / (B : ℝ))) nI₂ cI₂ B 1 DI)
    (hpos : Nat.ble (nat_lit 1) (((td.mul B).mul M).mul DI) = true)
    (hDI : Nat.beq (Nat.mul 2 DI) B = true)
    (hφ₁ : natAbsSubLe (numPosC nθ (td.mul cθ)) ((numNegC nθ (td.mul cθ)).add (tn.mul cL₁))
      (td.mul B) (numPosC nφ₁ (((Nat.mul 2 M).mul u₁).add ((k₁.mul Pc).mul B)))
      (numNegC nφ₁ (((Nat.mul 2 M).mul u₁).add ((k₁.mul Pc).mul B))) ((Nat.mul 2 M).mul B)
      (nat_lit 1) B = true)
    (hφ₂ : natAbsSubLe (numPosC nθ (td.mul cθ)) ((numNegC nθ (td.mul cθ)).add (tn.mul cL₂))
      (td.mul B) (numPosC nφ₂ (((Nat.mul 2 M).mul u₂).add ((k₂.mul Pc).mul B)))
      (numNegC nφ₂ (((Nat.mul 2 M).mul u₂).add ((k₂.mul Pc).mul B))) ((Nat.mul 2 M).mul B)
      (nat_lit 1) B = true)
    (hR : natFloorLe ((((numPosC nS cS).mul B).add (cA₁.mul (numPosC nC₁ cI₁))).add
        (cA₂.mul (numPosC nC₂ cI₂)))
      ((((numNegC nS cS).mul B).add (cA₁.mul (numNegC nC₁ cI₁))).add (cA₂.mul (numNegC nC₂ cI₂)))
      nR cR B = true)
    (hrad : Nat.ble (((((((rS.add rA₁).add rA₂).add 1).mul B).mul td).mul (Nat.mul 2 M) |>.add
        (cA₁.mul (((Nat.mul 2 M).mul ((td.mul (rθ.add 3)).add (tn.mul rL₁))).add
          ((k₁.mul rπ).mul (td.mul B))))) |>.add
        (cA₂.mul (((Nat.mul 2 M).mul ((td.mul (rθ.add 3)).add (tn.mul rL₂))).add
          ((k₂.mul rπ).mul (td.mul B)))))
      (((rR.mul B).mul td).mul (Nat.mul 2 M)) = true) :
    Real.IsNear (mainSumRS θ t b₂) nR cR B rR B := by
  rw [main_sum_rs_succ θ t b₁ b₂ hb₂, main_sum_rs_succ θ t a b₁ hb₁,
    main_sum_rs_term_mk θ t tn td b₁ ht, main_sum_rs_term_mk θ t tn td b₂ ht]
  simp only [Nat.ble_eq, Nat.mul_eq] at hpos
  have hp : td ≠ 0 ∧ B ≠ 0 ∧ M ≠ 0 ∧ DI ≠ 0 := by
    simpa [Nat.one_le_iff_ne_zero, Nat.mul_ne_zero_iff, and_assoc] using hpos
  obtain ⟨htd, hB, hM, hDI0⟩ := hp
  have hDI' : (2 : ℝ) * DI = B := by
    have := Nat.eq_of_beq_eq_true hDI; simp only [Nat.mul_eq] at this; exact_mod_cast this
  have hBr : (0 : ℝ) < B := by exact_mod_cast Nat.pos_of_ne_zero hB
  have hMr : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have htdr : (0 : ℝ) < td := by exact_mod_cast Nat.pos_of_ne_zero htd
  have hT₁ := mainSumTerm_bound θ g₁ ε₁ b₁ tn td k₁ B DI M nθ cθ rθ cL₁ rL₁ cA₁ rA₁ nφ₁ u₁ Pc rπ
    nI₁ cI₁ nC₁ hε₁ hquad₁ hsign₁ htd hB hM hDI' hθ hL₁ hA₁ hpi hI₁ hφ₁
  have hT₂ := mainSumTerm_bound θ g₂ ε₂ b₂ tn td k₂ B DI M nθ cθ rθ cL₂ rL₂ cA₂ rA₂ nφ₂ u₂ Pc rπ
    nI₂ cI₂ nC₂ hε₂ hquad₂ hsign₂ htd hB hM hDI' hθ hL₂ hA₂ hpi hI₂ hφ₂
  have hR' := abs_sub_le_of_natFloorLe (Nat.pos_of_ne_zero hB) hR
  simp only [Nat.mul_eq, Nat.add_eq, numPosC_eq, numNegC_eq] at hR'
  have eX : ((((numPos nS cS * B + cA₁ * numPos nC₁ cI₁ + cA₂ * numPos nC₂ cI₂ : ℕ) : ℝ)
      - ((numNeg nS cS * B + cA₁ * numNeg nC₁ cI₁ + cA₂ * numNeg nC₂ cI₂ : ℕ) : ℝ))
      / ((B * B : ℕ) : ℝ))
      = sfrac nS cS B + sfrac false cA₁ B * sfrac nC₁ cI₁ B
        + sfrac false cA₂ B * sfrac nC₂ cI₂ B := by
    rw [sfrac_eq_parts nS, sfrac_eq_parts nC₁, sfrac_eq_parts nC₂, sfrac_false_div,
      sfrac_false_div]
    push_cast
    field_simp
    ring
  rw [eX] at hR'
  simp only [Real.IsNear] at hS ⊢
  set T := sfrac false tn td with hTdef
  set X₁ := (Real.sqrt (b₁ : ℝ))⁻¹ * Real.cos (θ - T * Real.log (sfrac false b₁ 1))
  set X₂ := (Real.sqrt (b₂ : ℝ))⁻¹ * Real.cos (θ - T * Real.log (sfrac false b₂ 1))
  have hsum : |mainSumRS θ t a + X₁ + X₂ - sfrac nR cR B|
      ≤ (rS : ℝ) / B
        + ((rA₁ : ℝ) / B + sfrac false cA₁ B
            * (((rθ : ℝ) + 3) / B + T * ((rL₁ : ℝ) / B) + (k₁ : ℝ) * rπ / (2 * M)))
        + ((rA₂ : ℝ) / B + sfrac false cA₂ B
            * (((rθ : ℝ) + 3) / B + T * ((rL₂ : ℝ) / B) + (k₂ : ℝ) * rπ / (2 * M)))
        + 1 / B := by
    have : mainSumRS θ t a + X₁ + X₂ - sfrac nR cR B
        = (mainSumRS θ t a - sfrac nS cS B)
          + (X₁ - sfrac false cA₁ B * sfrac nC₁ cI₁ B)
          + (X₂ - sfrac false cA₂ B * sfrac nC₂ cI₂ B)
          + (sfrac nS cS B + sfrac false cA₁ B * sfrac nC₁ cI₁ B
              + sfrac false cA₂ B * sfrac nC₂ cI₂ B - sfrac nR cR B) := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    gcongr
    · refine (abs_add_le _ _).trans ?_
      gcongr
      refine (abs_add_le _ _).trans ?_
      gcongr
  refine hsum.trans ?_
  simp only [Nat.ble_eq, Nat.mul_eq, Nat.add_eq] at hrad
  have hrad' : (((rS + rA₁ + rA₂ + 1) * B * td * (2 * M)
      + cA₁ * (2 * M * (td * (rθ + 3) + tn * rL₁) + k₁ * rπ * (td * B))
      + cA₂ * (2 * M * (td * (rθ + 3) + tn * rL₂) + k₂ * rπ * (td * B)) : ℕ) : ℝ)
      ≤ ((rR * B * td * (2 * M) : ℕ) : ℝ) := by exact_mod_cast hrad
  push_cast at hrad'
  have hden : (0 : ℝ) < (B : ℝ) * B * td * (2 * M) := by positivity
  have key : (rS : ℝ) / B
        + ((rA₁ : ℝ) / B + sfrac false cA₁ B
            * (((rθ : ℝ) + 3) / B + T * ((rL₁ : ℝ) / B) + (k₁ : ℝ) * rπ / (2 * M)))
        + ((rA₂ : ℝ) / B + sfrac false cA₂ B
            * (((rθ : ℝ) + 3) / B + T * ((rL₂ : ℝ) / B) + (k₂ : ℝ) * rπ / (2 * M)))
        + 1 / B
      = (((rS : ℝ) + rA₁ + rA₂ + 1) * B * td * (2 * M)
          + cA₁ * (2 * M * (td * ((rθ : ℝ) + 3) + tn * rL₁) + k₁ * rπ * (td * B))
          + cA₂ * (2 * M * (td * ((rθ : ℝ) + 3) + tn * rL₂) + k₂ * rπ * (td * B)))
        / ((B : ℝ) * B * td * (2 * M)) := by
    simp only [hTdef, sfrac_false_div]
    field_simp
    ring
  have keyR : (rR : ℝ) / B = (rR : ℝ) * B * td * (2 * M) / ((B : ℝ) * B * td * (2 * M)) := by
    field_simp
  rw [key, keyR]
  exact div_le_div_of_nonneg_right hrad' hden.le
theorem neg_one_pow_even_mk (n : ℕ) (h : Nat.beq (n % 2) (nat_lit 0) = true) :
    (-1 : ℝ) ^ n = sfrac false (nat_lit 1) (nat_lit 1) := by
  rw [(Nat.even_iff.2 (Nat.eq_of_beq_eq_true h)).neg_one_pow]
  norm_num [sfrac]
theorem neg_one_pow_odd_mk (n : ℕ) (h : Nat.beq (n % 2) (nat_lit 1) = true) :
    (-1 : ℝ) ^ n = sfrac true (nat_lit 1) (nat_lit 1) := by
  rw [(Nat.odd_iff.2 (Nat.eq_of_beq_eq_true h)).neg_one_pow]
  norm_num [sfrac]
theorem t_div_two_pi_mk (t : ℝ) (tn td : ℕ) (ht : t = sfrac false tn td) :
    t / (2 * Real.pi)
      = sfrac false tn td * (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi)⁻¹ := by
  have h2 : sfrac false (nat_lit 2) (nat_lit 1) = (2 : ℝ) := by norm_num [sfrac]
  subst ht
  rw [h2, div_eq_mul_inv]
theorem sfrac_div_two_pi_nonneg (tn td : ℕ) : 0 ≤ sfrac false tn td / (2 * Real.pi) := by
  rw [sfrac_false_div]
  positivity
theorem rpow_neg_quarter_mk (x : ℝ) (hx : 0 ≤ x) :
    x ^ (-(1 / 4) : ℝ) = (Real.sqrt (Real.sqrt x))⁻¹ := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx, Real.rpow_neg hx]
  norm_num
theorem correction_mk (p : ℝ)
    (h : Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p) ≠ 0) :
    Zeta.RiemannSiegel.correction p
      = (Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))⁻¹
        * Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
            * (p * p - p - sfrac false (nat_lit 1) (nat_lit 16))) := by
  have h2 : sfrac false (nat_lit 2) (nat_lit 1) = (2 : ℝ) := by norm_num [sfrac]
  have h16 : sfrac false (nat_lit 1) (nat_lit 16) = (1 / 16 : ℝ) := by norm_num [sfrac]
  rw [h2] at h
  rw [h2, h16, eq_inv_mul_iff_mul_eq₀ h, Zeta.RiemannSiegel.cos_mul_correction p]
  ring_nf
theorem cos_two_pi_p_ne_zero_mk (t : ℝ) (tn td ν : ℕ) (ht : t = sfrac false tn td)
    (htn : Nat.ble 1 tn = true) (htd : Nat.ble 1 td = true)
    (hν : ⌊Real.sqrt (t / (2 * Real.pi))⌋₊ = ν) :
    Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
        * (Real.sqrt (t / (2 * Real.pi)) - sfrac false ν (nat_lit 1))) ≠ 0 := by
  have h2 : sfrac false (nat_lit 2) (nat_lit 1) = (2 : ℝ) := by norm_num [sfrac]
  have hν1 : sfrac false ν (nat_lit 1) = (ν : ℝ) := by norm_num [sfrac]
  have htnR : (0 : ℝ) < tn := pos_real_of_ble htn
  have htdR : (0 : ℝ) < td := pos_real_of_ble htd
  set q : ℚ := (tn : ℚ) / (td : ℚ) with hqdef
  have hq : 0 < q := by
    rw [hqdef]
    exact div_pos (by exact_mod_cast htnR) (by exact_mod_cast htdR)
  have hqt : ((q : ℚ) : ℝ) = t := by
    rw [ht, hqdef, sfrac_false_div]; push_cast; ring
  rw [h2, hν1, ← hν, ← hqt]
  exact Zeta.RiemannSiegel.cos_two_pi_fract_sqrt_ne_zero q hq
theorem thirtyTwoPi_le_dec {t : ℝ} (tn td : ℕ) (ht : t = sfrac false tn td)
    (htd : Nat.ble 1 td = true)
    (h : Nat.ble (Nat.mul 504 td) (Nat.mul 5 tn) = true) : 32 * Real.pi ≤ t := by
  subst ht
  have hd : (0 : ℝ) < td := pos_real_of_ble htd
  have h' : (504 : ℝ) * td ≤ 5 * tn := by
    simp only [Nat.mul_eq] at h; exact_mod_cast Nat.le_of_ble_eq_true h
  have hpi : Real.pi * td ≤ 3.15 * td := mul_le_mul_of_nonneg_right Real.pi_lt_d2.le hd.le
  rw [sfrac_false_div, le_div_iff₀ hd]
  linarith
theorem floor_sqrt_eq_dec {t : ℝ} (tn td ν : ℕ) (ht : t = sfrac false tn td)
    (htd : Nat.ble 1 td = true)
    (hlo : Nat.ble (Nat.mul (Nat.mul 628318530717958647694 (Nat.mul ν ν)) td)
      (Nat.mul 100000000000000000000 tn) = true)
    (hhi : Nat.blt (Nat.mul 100000000000000000000 tn)
      (Nat.mul (Nat.mul 628318530717958647692 (Nat.mul (ν + 1) (ν + 1))) td) = true) :
    ⌊Real.sqrt (t / (2 * Real.pi))⌋₊ = ν := by
  subst ht
  have hd : (0 : ℝ) < td := pos_real_of_ble htd
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hlo' : (628318530717958647694 : ℝ) * (ν * ν) * td ≤ 100000000000000000000 * tn := by
    simp only [Nat.mul_eq] at hlo; exact_mod_cast Nat.le_of_ble_eq_true hlo
  have hhi' : (100000000000000000000 : ℝ) * tn
      < 628318530717958647692 * ((ν + 1) * (ν + 1)) * td := by
    simp only [Nat.mul_eq, Nat.blt_eq] at hhi; exact_mod_cast hhi
  have hsq : (0 : ℝ) ≤ (ν : ℝ) * ν := by positivity
  have hsq' : (0 : ℝ) ≤ ((ν : ℝ) + 1) * ((ν : ℝ) + 1) := by positivity
  have hpiu : (2 * Real.pi) * ((ν : ℝ) * ν) ≤ 6.28318530717958647694 * ((ν : ℝ) * ν) :=
    mul_le_mul_of_nonneg_right (by linarith [Real.pi_lt_d20]) hsq
  have hpil : (6.28318530717958647692 : ℝ) * (((ν : ℝ) + 1) * ((ν : ℝ) + 1))
      ≤ (2 * Real.pi) * (((ν : ℝ) + 1) * ((ν : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_d20]) hsq'
  rw [sfrac_false_div, Nat.floor_eq_iff (Real.sqrt_nonneg _)]
  refine ⟨?_, ?_⟩
  · rw [Real.le_sqrt (Nat.cast_nonneg ν) (by positivity), le_div_iff₀ h2pi, sq]
    rw [le_div_iff₀ hd] at *
    nlinarith [hlo', hpiu, hd]
  · rw [Real.sqrt_lt' (by positivity), div_lt_iff₀ h2pi, div_lt_iff₀ hd, sq]
    nlinarith [hhi', hpil, hd]
theorem sfrac_div_two_pi_pos (tn td : ℕ) (htn : Nat.ble 1 tn = true)
    (htd : Nat.ble 1 td = true) : 0 < sfrac false tn td / (2 * Real.pi) := by
  have h1 : (0 : ℝ) < tn := pos_real_of_ble htn
  have h2 : (0 : ℝ) < td := pos_real_of_ble htd
  rw [sfrac_false_div]
  exact div_pos (div_pos h1 h2) (by positivity)
theorem t_div_two_pi_nonneg (t : ℝ) (tn td : ℕ) (ht : t = sfrac false tn td) :
    0 ≤ t / (2 * Real.pi) := by
  subst ht; exact sfrac_div_two_pi_nonneg tn td
theorem sqrt_sqrt_eq_rpow {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (Real.sqrt x) = x ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  norm_num
theorem rpow_neg_three_quarter_mk (x : ℝ) (hx : 0 < x) :
    x ^ (-(3 / 4) : ℝ)
      = (Real.sqrt (Real.sqrt x) * Real.sqrt (Real.sqrt x) * Real.sqrt (Real.sqrt x))⁻¹ := by
  rw [sqrt_sqrt_eq_rpow hx.le, ← Real.rpow_add hx, ← Real.rpow_add hx, ← Real.rpow_neg hx.le]
  norm_num
theorem rpow_neg_five_quarter_mk (x : ℝ) (hx : 0 < x) :
    x ^ (-(5 / 4) : ℝ) = (Real.sqrt (Real.sqrt x) * x)⁻¹ := by
  rw [sqrt_sqrt_eq_rpow hx.le, ← Real.rpow_add_one hx.ne', ← Real.rpow_neg hx.le]
  norm_num
theorem rpow_neg_fifteen_quarter_mk (x : ℝ) (hx : 0 < x) :
    x ^ (-(15 / 4) : ℝ)
      = (Real.sqrt (Real.sqrt x) * x * (Real.sqrt (Real.sqrt x) * x)
          * (Real.sqrt (Real.sqrt x) * x))⁻¹ := by
  rw [sqrt_sqrt_eq_rpow hx.le, ← Real.rpow_add_one hx.ne', ← Real.rpow_add hx,
    ← Real.rpow_add hx, ← Real.rpow_neg hx.le]
  norm_num
theorem hardyZApproximantRS₀_eq (t : ℝ) (ν : ℕ)
    (hν : ⌊Real.sqrt (t / (2 * Real.pi))⌋₊ = ν) :
    hardyZApproximantRS₀ t
      = Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 t) t ν
        - (-1) ^ ν * (t / (2 * Real.pi)) ^ (-(1 / 4) : ℝ)
            * Zeta.RiemannSiegel.correction
                (Real.sqrt (t / (2 * Real.pi)) - sfrac false ν (nat_lit 1)) := by
  have hs : sfrac false ν (nat_lit 1) = (ν : ℝ) := by norm_num [sfrac]
  rw [hs]
  subst hν
  rfl
theorem hardyZErrorBoundRS₀_mk (t : ℝ) (tn td : ℕ) (ht : t = sfrac false tn td)
    (htn : Nat.ble 1 tn = true) (htd : Nat.ble 1 td = true) :
    hardyZErrorBoundRS₀ t
      = sfrac false (nat_lit 25) (nat_lit 4)
          * (Real.sqrt (Real.sqrt (t / (2 * Real.pi))) * (t / (2 * Real.pi)))⁻¹
        + sfrac false (nat_lit 1) (nat_lit 32)
          * (Real.sqrt (Real.sqrt (t / (2 * Real.pi))) * (t / (2 * Real.pi))
              * (Real.sqrt (Real.sqrt (t / (2 * Real.pi))) * (t / (2 * Real.pi)))
              * (Real.sqrt (Real.sqrt (t / (2 * Real.pi))) * (t / (2 * Real.pi))))⁻¹
        + sfrac false (nat_lit 13) (nat_lit 10)
          * (Real.sqrt (Real.sqrt (t / (2 * Real.pi)))
              * Real.sqrt (Real.sqrt (t / (2 * Real.pi)))
              * Real.sqrt (Real.sqrt (t / (2 * Real.pi))))⁻¹ := by
  subst ht
  have hT : 0 < sfrac false tn td / (2 * Real.pi) := sfrac_div_two_pi_pos tn td htn htd
  have h25 : sfrac false (nat_lit 25) (nat_lit 4) = (25 / 4 : ℝ) := by norm_num [sfrac]
  have h32 : sfrac false (nat_lit 1) (nat_lit 32) = (1 / 32 : ℝ) := by norm_num [sfrac]
  have h13 : sfrac false (nat_lit 13) (nat_lit 10) = (13 / 10 : ℝ) := by norm_num [sfrac]
  rw [h25, h32, h13, ← rpow_neg_five_quarter_mk _ hT, ← rpow_neg_fifteen_quarter_mk _ hT,
    ← rpow_neg_three_quarter_mk _ hT]
theorem hardyZApproximantRS_eq (t : ℝ) (ν : ℕ)
    (hν : ⌊Real.sqrt (t / (2 * Real.pi))⌋₊ = ν) :
    hardyZApproximantRS t
      = Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 t) t ν
        - (-1) ^ ν * (t / (2 * Real.pi)) ^ (-(1 / 4) : ℝ)
            * (Zeta.RiemannSiegel.correction
                  (Real.sqrt (t / (2 * Real.pi)) - sfrac false ν (nat_lit 1))
                + Zeta.RiemannSiegel.correctionLinear
                    (Real.sqrt (t / (2 * Real.pi)) - sfrac false ν (nat_lit 1))
                  * (Real.sqrt (t / (2 * Real.pi)))⁻¹) := by
  have hs : sfrac false ν (nat_lit 1) = (ν : ℝ) := by norm_num [sfrac]
  rw [hs]
  subst hν
  rfl
theorem hardyZErrorBoundRS_mk (t : ℝ) (tn td : ℕ) (ht : t = sfrac false tn td)
    (htn : Nat.ble 1 tn = true) (htd : Nat.ble 1 td = true) :
    hardyZErrorBoundRS t
      = sfrac false (nat_lit 25) (nat_lit 4)
          * (Real.sqrt (Real.sqrt (t / (2 * Real.pi))) * (t / (2 * Real.pi)))⁻¹
        + sfrac false (nat_lit 1) (nat_lit 32)
          * (Real.sqrt (Real.sqrt (t / (2 * Real.pi))) * (t / (2 * Real.pi))
              * (Real.sqrt (Real.sqrt (t / (2 * Real.pi))) * (t / (2 * Real.pi)))
              * (Real.sqrt (Real.sqrt (t / (2 * Real.pi))) * (t / (2 * Real.pi))))⁻¹ := by
  subst ht
  have hT : 0 < sfrac false tn td / (2 * Real.pi) := sfrac_div_two_pi_pos tn td htn htd
  have h25 : sfrac false (nat_lit 25) (nat_lit 4) = (25 / 4 : ℝ) := by norm_num [sfrac]
  have h32 : sfrac false (nat_lit 1) (nat_lit 32) = (1 / 32 : ℝ) := by norm_num [sfrac]
  rw [h25, h32, ← rpow_neg_five_quarter_mk _ hT, ← rpow_neg_fifteen_quarter_mk _ hT]
theorem hardyZErrorBoundRS_anti {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    hardyZErrorBoundRS t ≤ hardyZErrorBoundRS s := by
  have hT : 0 < s / (2 * Real.pi) := div_pos hs (by positivity)
  have hle : s / (2 * Real.pi) ≤ t / (2 * Real.pi) := by gcongr
  have h5 := Real.rpow_le_rpow_of_nonpos hT hle (by norm_num : -(5 / 4 : ℝ) ≤ 0)
  have h15 := Real.rpow_le_rpow_of_nonpos hT hle (by norm_num : -(15 / 4 : ℝ) ≤ 0)
  simp only [hardyZErrorBoundRS]
  linarith
theorem hardyZErrorBoundRS₀_anti {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    hardyZErrorBoundRS₀ t ≤ hardyZErrorBoundRS₀ s := by
  have hT : 0 < s / (2 * Real.pi) := div_pos hs (by positivity)
  have hle : s / (2 * Real.pi) ≤ t / (2 * Real.pi) := by gcongr
  have h3 := Real.rpow_le_rpow_of_nonpos hT hle (by norm_num : -(3 / 4 : ℝ) ≤ 0)
  have h := hardyZErrorBoundRS_anti hs hst
  simp only [hardyZErrorBoundRS₀]
  linarith
theorem norm_gt_hardyZErrorBoundRS_of_le (x s t : ℝ) (sn sd tn td : ℕ)
    (hs : s = sfrac false sn sd) (ht : t = sfrac false tn td) (hsn : Nat.ble 1 sn = true)
    (hsd : Nat.ble 1 sd = true) (htd : Nat.ble 1 td = true)
    (hst : Nat.ble (sn.mul td) (tn.mul sd) = true) (h : ‖x‖ > hardyZErrorBoundRS s) :
    ‖x‖ > hardyZErrorBoundRS t := by
  have hs0 : 0 < s := by
    rw [hs, sfrac_false_div]; exact div_pos (pos_real_of_ble hsn) (pos_real_of_ble hsd)
  exact lt_of_le_of_lt (hardyZErrorBoundRS_anti hs0 (dec_le_dec sn sd tn td hs ht hsd htd hst)) h
theorem norm_gt_hardyZErrorBoundRS₀_of_le (x s t : ℝ) (sn sd tn td : ℕ)
    (hs : s = sfrac false sn sd) (ht : t = sfrac false tn td) (hsn : Nat.ble 1 sn = true)
    (hsd : Nat.ble 1 sd = true) (htd : Nat.ble 1 td = true)
    (hst : Nat.ble (sn.mul td) (tn.mul sd) = true) (h : ‖x‖ > hardyZErrorBoundRS₀ s) :
    ‖x‖ > hardyZErrorBoundRS₀ t := by
  have hs0 : 0 < s := by
    rw [hs, sfrac_false_div]; exact div_pos (pos_real_of_ble hsn) (pos_real_of_ble hsd)
  exact lt_of_le_of_lt (hardyZErrorBoundRS₀_anti hs0 (dec_le_dec sn sd tn td hs ht hsd htd hst)) h
theorem deriv_correction_mk (p : ℝ)
    (h : Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p) ≠ 0) :
    iteratedDeriv 1 Zeta.RiemannSiegel.correction p
      = (Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))⁻¹
        * (-(sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                    * (sfrac false (nat_lit 2) (nat_lit 1) * p
                          - sfrac false (nat_lit 1) (nat_lit 1))
                * Real.sin (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                  * (p * p - p - sfrac false (nat_lit 1) (nat_lit 16))))
            - -(sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                  * Real.sin (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))
                * Zeta.RiemannSiegel.correction p) := by
  have h2 : sfrac false (nat_lit 2) (nat_lit 1) = (2 : ℝ) := by norm_num [sfrac]
  have h16 : sfrac false (nat_lit 1) (nat_lit 16) = (1 / 16 : ℝ) := by norm_num [sfrac]
  have h1 : sfrac false (nat_lit 1) (nat_lit 1) = (1 : ℝ) := by norm_num [sfrac]
  have hsq : p * p = p ^ 2 := by ring
  rw [h2] at h
  rw [h2, h16, h1, hsq, eq_inv_mul_iff_mul_eq₀ h]
  linear_combination Zeta.RiemannSiegel.cos_mul_iteratedDeriv_one p
theorem iteratedDeriv_two_correction_mk (p : ℝ)
    (h : Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p) ≠ 0) :
    iteratedDeriv 2 Zeta.RiemannSiegel.correction p
      = (Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))⁻¹
        * (-((sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                  * (sfrac false (nat_lit 2) (nat_lit 1) * p - sfrac false (nat_lit 1) (nat_lit 1)))
                * (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                  * (sfrac false (nat_lit 2) (nat_lit 1) * p - sfrac false (nat_lit 1) (nat_lit 1)))
                * Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                  * (p * p - p - sfrac false (nat_lit 1) (nat_lit 16))))
            - sfrac false (nat_lit 4) (nat_lit 1) * Real.pi
                * Real.sin (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                  * (p * p - p - sfrac false (nat_lit 1) (nat_lit 16)))
            - sfrac false (nat_lit 2) (nat_lit 1)
                * -(sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                  * Real.sin (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))
                * iteratedDeriv 1 Zeta.RiemannSiegel.correction p
            - -(sfrac false (nat_lit 4) (nat_lit 1) * (Real.pi * Real.pi)
                  * Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))
                * Zeta.RiemannSiegel.correction p) := by
  have h2 : sfrac false (nat_lit 2) (nat_lit 1) = (2 : ℝ) := by norm_num [sfrac]
  have h4 : sfrac false (nat_lit 4) (nat_lit 1) = (4 : ℝ) := by norm_num [sfrac]
  have h16 : sfrac false (nat_lit 1) (nat_lit 16) = (1 / 16 : ℝ) := by norm_num [sfrac]
  have h1 : sfrac false (nat_lit 1) (nat_lit 1) = (1 : ℝ) := by norm_num [sfrac]
  have hsq : p * p = p ^ 2 := by ring
  simp only [h2] at h
  simp only [h2, h4, h16, h1, hsq]
  rw [eq_inv_mul_iff_mul_eq₀ h]
  linear_combination Zeta.RiemannSiegel.cos_mul_iteratedDeriv_two p
theorem iteratedDeriv_three_correction_mk (p : ℝ)
    (h : Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p) ≠ 0) :
    iteratedDeriv 3 Zeta.RiemannSiegel.correction p
      = (Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))⁻¹
        * ((sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                * (sfrac false (nat_lit 2) (nat_lit 1) * p - sfrac false (nat_lit 1) (nat_lit 1)))
              * (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                * (sfrac false (nat_lit 2) (nat_lit 1) * p - sfrac false (nat_lit 1) (nat_lit 1)))
              * (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                * (sfrac false (nat_lit 2) (nat_lit 1) * p - sfrac false (nat_lit 1) (nat_lit 1)))
              * Real.sin (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                * (p * p - p - sfrac false (nat_lit 1) (nat_lit 16)))
            - sfrac false (nat_lit 3) (nat_lit 1)
                * (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                  * (sfrac false (nat_lit 2) (nat_lit 1) * p - sfrac false (nat_lit 1) (nat_lit 1)))
                * (sfrac false (nat_lit 4) (nat_lit 1) * Real.pi)
                    * Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                      * (p * p - p - sfrac false (nat_lit 1) (nat_lit 16)))
            - sfrac false (nat_lit 3) (nat_lit 1)
                * -(sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                  * Real.sin (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))
                * iteratedDeriv 2 Zeta.RiemannSiegel.correction p
            - sfrac false (nat_lit 3) (nat_lit 1)
                * -(sfrac false (nat_lit 4) (nat_lit 1) * (Real.pi * Real.pi)
                  * Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))
                * iteratedDeriv 1 Zeta.RiemannSiegel.correction p
            - sfrac false (nat_lit 8) (nat_lit 1) * (Real.pi * Real.pi * Real.pi)
                * Real.sin (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p)
                * Zeta.RiemannSiegel.correction p) := by
  have h2 : sfrac false (nat_lit 2) (nat_lit 1) = (2 : ℝ) := by norm_num [sfrac]
  have h3 : sfrac false (nat_lit 3) (nat_lit 1) = (3 : ℝ) := by norm_num [sfrac]
  have h4 : sfrac false (nat_lit 4) (nat_lit 1) = (4 : ℝ) := by norm_num [sfrac]
  have h8 : sfrac false (nat_lit 8) (nat_lit 1) = (8 : ℝ) := by norm_num [sfrac]
  have h16 : sfrac false (nat_lit 1) (nat_lit 16) = (1 / 16 : ℝ) := by norm_num [sfrac]
  have h1 : sfrac false (nat_lit 1) (nat_lit 1) = (1 : ℝ) := by norm_num [sfrac]
  have hsq : p * p = p ^ 2 := by ring
  simp only [h2] at h
  simp only [h2, h3, h4, h8, h16, h1, hsq]
  rw [eq_inv_mul_iff_mul_eq₀ h]
  linear_combination Zeta.RiemannSiegel.cos_mul_iteratedDeriv_three p
theorem correctionLinear_mk (p : ℝ) :
    Zeta.RiemannSiegel.correctionLinear p
      = -(iteratedDeriv 3 Zeta.RiemannSiegel.correction p
          * (sfrac false (nat_lit 96) (nat_lit 1) * (Real.pi * Real.pi))⁻¹) := by
  have h96 : sfrac false (nat_lit 96) (nat_lit 1) = (96 : ℝ) := by norm_num [sfrac]
  rw [h96, Zeta.RiemannSiegel.correctionLinear_eq, div_eq_mul_inv]
  ring
theorem inv_eq_neg_inv_neg (x : ℝ) : x⁻¹ = -(-x)⁻¹ := by
  rw [inv_neg, neg_neg]
theorem mul_neg_of_neg_pos_r (x y : ℝ) (hx : x < 0) (hy : 0 < y) : x * y < 0 :=
  mul_neg_of_neg_of_pos hx hy
theorem mul_neg_of_pos_neg_r (x y : ℝ) (hx : 0 < x) (hy : y < 0) : x * y < 0 :=
  mul_neg_of_pos_of_neg hx hy
end BSN
end
end CertificatePort152


section CertificatePort153
section
namespace BSN
open Enclosure
theorem log_nat_of_cert (S Dd n : ℕ) (neg : Bool) (cn cd rn rd : ℕ)
    (hs : Nat.beq S n) (hd : Nat.beq Dd 1)
    (h : Real.IsNear (Real.log ((S : ℝ) / (Dd : ℝ))) neg cn cd rn rd) :
    Real.IsNear (Real.log ((n : ℕ) : ℝ)) neg cn cd rn rd := by
  have hs' : S = n := Nat.eq_of_beq_eq_true hs
  have hd' : Dd = 1 := Nat.eq_of_beq_eq_true hd
  rw [hs', hd'] at h
  rwa [Nat.cast_one, div_one] at h
theorem log_reduce_eq (N M k : ℕ) (hN : 0 < N) (hM : 0 < M) :
    Real.log ((N : ℝ) / M) = Real.log ((N : ℝ) / (M * 2 ^ k)) + (k : ℝ) * Real.log 2 := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have e : (N : ℝ) / (M * 2 ^ k) = ((N : ℝ) / M) / 2 ^ k := by rw [div_div]
  have key : Real.log ((N : ℝ) / (M * 2 ^ k)) = Real.log ((N : ℝ) / M) - (k : ℝ) * Real.log 2 := by
    rw [e, Real.log_div (by positivity) (by positivity), Real.log_pow]
  rw [key]; ring
theorem log_rat_reduce_isNear (a b k S Dd pr Qr p2 Q2 D E : ℕ) (ha : Nat.ble 1 a)
    (hb : Nat.ble 1 b)
    (hS : S.beq (Nat.mul 2 a)) (hDd : Dd.beq (Nat.mul b (Nat.pow 2 (Nat.succ k))))
    (hr : Real.IsNear (Real.log ((S : ℝ) / (Dd : ℝ))) false pr Qr 1 D)
    (h2 : Real.IsNear (Real.log 2) false p2 Q2 1 E)
    (hD : Nat.ble 1 D) (hE : Nat.ble 1 E) (hQr : Nat.ble 1 Qr) (hQ2 : Nat.ble 1 Q2) :
    Real.IsNear (Real.log ((a : ℝ) / b)) false ((pr.mul Q2).add ((k.mul p2).mul Qr)) (Qr.mul Q2)
      (E.add (k.mul D)) (D.mul E) := by
  obtain rfl := Nat.eq_of_beq_eq_true hS
  obtain rfl := Nat.eq_of_beq_eq_true hDd
  simp only [Nat.mul_eq, Nat.add_eq, Nat.pow_eq] at hr ⊢
  rw [Real.IsNear, sfrac_false_div, Nat.cast_one] at hr h2
  have hDR : (0:ℝ) < D := pos_real_of_ble hD
  have hER : (0:ℝ) < E := pos_real_of_ble hE
  have hQrR : (0:ℝ) < Qr := pos_real_of_ble hQr
  have hQ2R : (0:ℝ) < Q2 := pos_real_of_ble hQ2
  have harg : ((↑(2 * a) : ℝ) / ((b * 2 ^ (k + 1) : ℕ) : ℝ)) = (↑a : ℝ) / ((b : ℝ) * 2 ^ k) := by
    push_cast; ring
  rw [harg] at hr
  have hlogn : Real.log ((↑a : ℝ) / b)
      = Real.log ((↑a : ℝ) / ((b : ℝ) * 2 ^ k)) + ↑k * Real.log 2 :=
    log_reduce_eq a b k (pos_of_ble ha) (pos_of_ble hb)
  have hcentre : ((pr * Q2 + k * p2 * Qr : ℕ) : ℝ) / ((Qr * Q2 : ℕ) : ℝ)
              = (pr : ℝ) / Qr + ↑k * ((p2 : ℝ) / Q2) := by
    push_cast; field_simp [hQrR.ne', hQ2R.ne']
  have hrad : ((E + k * D : ℕ) : ℝ) / ((D * E : ℕ) : ℝ) = 1 / ↑D + ↑k * (1 / ↑E) := by
    push_cast; field_simp [hDR.ne', hER.ne']
  rw [Real.IsNear, sfrac_false_div, hlogn, hcentre, hrad]
  calc |Real.log ((↑a : ℝ) / ((b : ℝ) * 2 ^ k)) + ↑k * Real.log 2
          - ((pr : ℝ) / Qr + ↑k * ((p2 : ℝ) / Q2))|
      = |(Real.log ((↑a : ℝ) / ((b : ℝ) * 2 ^ k)) - (pr : ℝ) / Qr)
          + ↑k * (Real.log 2 - (p2 : ℝ) / Q2)| := by ring_nf
    _ ≤ |Real.log ((↑a : ℝ) / ((b : ℝ) * 2 ^ k)) - (pr : ℝ) / Qr|
          + |↑k * (Real.log 2 - (p2 : ℝ) / Q2)| := abs_add_le _ _
    _ = |Real.log ((↑a : ℝ) / ((b : ℝ) * 2 ^ k)) - (pr : ℝ) / Qr|
          + ↑k * |Real.log 2 - (p2 : ℝ) / Q2| := by rw [abs_mul, Nat.abs_cast]
    _ ≤ 1 / ↑D + ↑k * (1 / ↑E) := by gcongr
theorem log_two_eq (p2 Q2 E : ℕ)
    (h : Real.IsNear (Real.log (((4 : ℕ) : ℝ) / ((2 : ℕ) : ℝ))) false p2 Q2 1 E) :
    Real.IsNear (Real.log 2) false p2 Q2 1 E := by
  have e : (((4 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = 2 := by norm_num
  rwa [e] at h
theorem logfrac_isNear (S Dd g a b p Q D : ℕ) (hg : Nat.ble 1 g)
    (hs : Nat.beq (S.mul g) (Nat.mul 2 a))
    (hd : Nat.beq (Dd.mul g) (Nat.mul 2 b))
    (h : Real.IsNear (Real.log ((S : ℝ) / (Dd : ℝ))) false p Q 1 D) :
    Real.IsNear (Real.log ((a : ℝ) / b)) false p Q 1 D := by
  have hs' : S * g = 2 * a := Nat.eq_of_beq_eq_true hs
  have hd' : Dd * g = 2 * b := Nat.eq_of_beq_eq_true hd
  have hgR : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (pos_of_ble hg).ne'
  have h1 : (S : ℝ) * g = 2 * a := by exact_mod_cast hs'
  have h2 : (Dd : ℝ) * g = 2 * b := by exact_mod_cast hd'
  have e : ((S : ℝ) / (Dd : ℝ)) = (a : ℝ) / b := by
    calc (S : ℝ) / (Dd : ℝ)
        = (S : ℝ) * g / ((Dd : ℝ) * g) := (mul_div_mul_right _ _ hgR).symm
      _ = 2 * (a : ℝ) / (2 * (b : ℝ)) := by rw [h1, h2]
      _ = (a : ℝ) / b := mul_div_mul_left _ _ two_ne_zero
  rwa [e] at h
end BSN
end
end CertificatePort153


section CertificatePort156
section
namespace BSN
open Finset in
theorem exp_sub_sum_nonneg (x : ℝ) (N : ℕ) (hx : 0 ≤ x) :
    0 ≤ Real.exp x - ∑ k ∈ range N, x ^ k / k.factorial := by
  have hsum : Summable (fun n => x ^ n / n.factorial) := Real.summable_pow_div_factorial x
  have hexp : Real.exp x = ∑' n, x ^ n / (n.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [hexp, sub_nonneg]
  exact hsum.sum_le_tsum _ (fun i _ => by positivity)
open Finset in
theorem exp_sub_sum_le (x : ℝ) (N : ℕ) (hx : 0 ≤ x) (hxN : x < N + 1) :
    Real.exp x - ∑ k ∈ range N, x ^ k / k.factorial ≤
      x ^ N / N.factorial * ((N + 1) / (N + 1 - x)) := by
  have hsum : Summable (fun n => x ^ n / n.factorial) := Real.summable_pow_div_factorial x
  have hexp : Real.exp x = ∑' n, x ^ n / (n.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hr : (0:ℝ) ≤ x / (N + 1) := by positivity
  have hr1 : x / (N + 1) < 1 := by rw [div_lt_one (by positivity)]; exact hxN
  have htail : Real.exp x - ∑ k ∈ range N, x ^ k / k.factorial
      = ∑' j, x ^ (j + N) / ((j + N).factorial : ℝ) := by
    rw [hexp, ← hsum.sum_add_tsum_nat_add N]; ring
  rw [htail]
  have htsum : Summable (fun j => x ^ (j + N) / ((j + N).factorial : ℝ)) :=
    (summable_nat_add_iff N).2 hsum
  have hgeo : Summable (fun j => x ^ N / N.factorial * (x / (N + 1)) ^ j) :=
    (summable_geometric_of_lt_one hr hr1).mul_left _
  have hterm : ∀ j, x ^ (j + N) / ((j + N).factorial : ℝ)
      ≤ x ^ N / N.factorial * (x / (N + 1)) ^ j := by
    intro j
    have hfac : ((N.factorial : ℝ) * (N + 1) ^ j) ≤ ((j + N).factorial : ℝ) := by
      have := Nat.factorial_mul_pow_le_factorial (m := N) (n := j)
      rw [add_comm j N]
      exact_mod_cast this
    have hnum : (0:ℝ) ≤ x ^ N * x ^ j := by positivity
    calc x ^ (j + N) / ((j + N).factorial : ℝ)
        = (x ^ N * x ^ j) / ((j + N).factorial : ℝ) := by rw [pow_add]; ring_nf
      _ ≤ (x ^ N * x ^ j) / (N.factorial * (N + 1) ^ j) :=
          div_le_div_of_nonneg_left hnum (by positivity) hfac
      _ = x ^ N / N.factorial * (x / (N + 1)) ^ j := by rw [div_pow]; ring
  calc ∑' j, x ^ (j + N) / ((j + N).factorial : ℝ)
      ≤ ∑' j, x ^ N / N.factorial * (x / (N + 1)) ^ j := htsum.tsum_le_tsum hterm hgeo
    _ = x ^ N / N.factorial * ∑' j, (x / (N + 1)) ^ j := tsum_mul_left
    _ = x ^ N / N.factorial * (1 - x / (N + 1))⁻¹ := by rw [tsum_geometric_of_lt_one hr hr1]
    _ = x ^ N / N.factorial * ((N + 1) / (N + 1 - x)) := by
        have h2 : (N:ℝ) + 1 ≠ 0 := by positivity
        rw [show (1:ℝ) - x / (N + 1) = (N + 1 - x) / (N + 1) by field_simp, inv_div]
open Finset in
theorem alt_series_tail_bound (x : ℝ) (E : ℕ) (f : ℕ → ℝ) (N : ℕ) (hx : 0 ≤ x)
    (hsummable : Summable f) (hxE : x < E + 1)
    (hnorm : ∀ j, ‖f (j + N)‖ = x ^ (E + 2 * j) / (E + 2 * j).factorial) :
    |∑' j, f (j + N)| ≤ x ^ E / E.factorial * (1 - (x / (E + 1)) ^ 2)⁻¹ := by
  have hb : x / (E + 1) < 1 := by rw [div_lt_one (by positivity)]; exact hxE
  have hr : (0:ℝ) ≤ (x / (E + 1)) ^ 2 := by positivity
  have hr1 : (x / (E + 1)) ^ 2 < 1 := pow_lt_one₀ (by positivity) hb (by norm_num)
  have htsumnorm : Summable (fun j => ‖f (j + N)‖) :=
    ((summable_nat_add_iff N).2 hsummable).norm
  have hgeo : Summable (fun j => x ^ E / E.factorial * ((x / (E + 1)) ^ 2) ^ j) :=
    (summable_geometric_of_lt_one hr hr1).mul_left _
  have hterm : ∀ j, ‖f (j + N)‖ ≤ x ^ E / E.factorial * ((x / (E + 1)) ^ 2) ^ j := by
    intro j
    rw [hnorm]
    have hfac : (E.factorial : ℝ) * (E + 1) ^ (2 * j) ≤ ((E + 2 * j).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_mul_pow_le_factorial (m := E) (n := 2 * j)
    have hnum : (0:ℝ) ≤ x ^ E * x ^ (2 * j) := by positivity
    calc x ^ (E + 2 * j) / ((E + 2 * j).factorial : ℝ)
        = (x ^ E * x ^ (2 * j)) / ((E + 2 * j).factorial : ℝ) := by rw [pow_add]
      _ ≤ (x ^ E * x ^ (2 * j)) / (E.factorial * (E + 1) ^ (2 * j)) :=
          div_le_div_of_nonneg_left hnum (by positivity) hfac
      _ = x ^ E / E.factorial * ((x / (E + 1)) ^ 2) ^ j := by rw [← pow_mul, div_pow]; ring
  calc |∑' j, f (j + N)|
      = ‖∑' j, f (j + N)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' j, ‖f (j + N)‖ := norm_tsum_le_tsum_norm htsumnorm
    _ ≤ ∑' j, x ^ E / E.factorial * ((x / (E + 1)) ^ 2) ^ j := htsumnorm.tsum_le_tsum hterm hgeo
    _ = x ^ E / E.factorial * ∑' j, ((x / (E + 1)) ^ 2) ^ j := tsum_mul_left
    _ = x ^ E / E.factorial * (1 - (x / (E + 1)) ^ 2)⁻¹ := by rw [tsum_geometric_of_lt_one hr hr1]
open Finset in
theorem sin_sub_sum_le (x : ℝ) (N : ℕ) (hx : 0 ≤ x) (hxN : x < 2 * N + 2) :
    |Real.sin x - ∑ k ∈ range N, (-1) ^ k * x ^ (2 * k + 1) / (2 * k + 1).factorial| ≤
      x ^ (2 * N + 1) / (2 * N + 1).factorial * (1 - (x / (2 * N + 2)) ^ 2)⁻¹ := by
  set f : ℕ → ℝ := fun n => (-1) ^ n * x ^ (2 * n + 1) / (2 * n + 1).factorial with hf
  have hsummable : Summable f := (Real.hasSum_sin x).summable
  have hsin : Real.sin x = ∑' n, f n := Real.sin_eq_tsum x
  have htail : Real.sin x - ∑ k ∈ range N, f k = ∑' j, f (j + N) := by
    rw [hsin, ← hsummable.sum_add_tsum_nat_add N]; ring
  rw [htail]
  have hnorm : ∀ j, ‖f (j + N)‖ = x ^ (2 * N + 1 + 2 * j) / (2 * N + 1 + 2 * j).factorial := by
    intro j
    have he : 2 * (j + N) + 1 = 2 * N + 1 + 2 * j := by ring
    simp only [hf, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Real.norm_eq_abs, abs_of_nonneg hx, Nat.abs_cast, he]
  refine (alt_series_tail_bound x (2 * N + 1) f N hx hsummable (by push_cast; linarith)
    hnorm).trans_eq ?_
  push_cast; ring
open Finset in
theorem cos_sub_sum_le (x : ℝ) (N : ℕ) (hx : 0 ≤ x) (hxN : x < 2 * N + 1) :
    |Real.cos x - ∑ k ∈ range N, (-1) ^ k * x ^ (2 * k) / (2 * k).factorial| ≤
      x ^ (2 * N) / (2 * N).factorial * (1 - (x / (2 * N + 1)) ^ 2)⁻¹ := by
  set f : ℕ → ℝ := fun n => (-1) ^ n * x ^ (2 * n) / (2 * n).factorial with hf
  have hsummable : Summable f := (Real.hasSum_cos x).summable
  have hcos : Real.cos x = ∑' n, f n := Real.cos_eq_tsum x
  have htail : Real.cos x - ∑ k ∈ range N, f k = ∑' j, f (j + N) := by
    rw [hcos, ← hsummable.sum_add_tsum_nat_add N]; ring
  rw [htail]
  have hnorm : ∀ j, ‖f (j + N)‖ = x ^ (2 * N + 2 * j) / (2 * N + 2 * j).factorial := by
    intro j
    have he : 2 * (j + N) = 2 * N + 2 * j := by ring
    simp only [hf, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Real.norm_eq_abs, abs_of_nonneg hx, Nat.abs_cast, he]
  refine (alt_series_tail_bound x (2 * N) f N hx hsummable (by push_cast; linarith)
    hnorm).trans_eq ?_
  push_cast; ring
open Finset in
theorem abs_pow_sub_pow_le {a b M : ℝ} {n : ℕ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haM : a ≤ M) (hbM : b ≤ M) :
    |b ^ n - a ^ n| ≤ n * M ^ (n - 1) * |b - a| := by
  rw [← Commute.geom_sum₂_mul (Commute.all b a) n, abs_mul]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  calc |∑ i ∈ range n, b ^ i * a ^ (n - 1 - i)|
      ≤ ∑ i ∈ range n, |b ^ i * a ^ (n - 1 - i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ range n, b ^ i * a ^ (n - 1 - i) :=
        Finset.sum_congr rfl fun i _ => abs_of_nonneg (by positivity)
    _ ≤ ∑ _i ∈ range n, M ^ (n - 1) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hile : i ≤ n - 1 := by simp only [Finset.mem_range] at hi; omega
        have hM : 0 ≤ M := ha.trans haM
        have hpow : b ^ i * a ^ (n - 1 - i) ≤ M ^ i * M ^ (n - 1 - i) :=
          mul_le_mul (pow_le_pow_left₀ hb hbM i) (pow_le_pow_left₀ ha haM _)
            (by positivity) (by positivity)
        rwa [← pow_add, Nat.add_sub_cancel' hile] at hpow
    _ = n * M ^ (n - 1) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
theorem geo_factor_le (x D : ℝ) (hD : 0 < D) (hx : 2 * x ^ 2 ≤ D ^ 2) :
    (1 - (x / D) ^ 2)⁻¹ ≤ 2 := by
  have h2 : (x / D) ^ 2 ≤ 1 / 2 := by
    rw [div_pow, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  rw [← one_div]
  calc 1 / (1 - (x / D) ^ 2) ≤ 1 / (1 / 2) :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
    _ = 2 := by norm_num
theorem factorial_add_four (m : ℕ) :
    (m + 4).factorial = m.factorial * ((m + 1) * (m + 2) * (m + 3) * (m + 4)) := by
  have e : m + 4 = m + 1 + 1 + 1 + 1 := rfl
  rw [e, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
  ring
open Finset in
theorem sum_range_two_mul {α} [AddCommMonoid α] (f : ℕ → α) (M : ℕ) :
    ∑ i ∈ range (2 * M), f i = ∑ j ∈ range M, (f (2 * j) + f (2 * j + 1)) := by
  induction M with
  | zero => simp
  | succ n ih =>
    have e : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    rw [e, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    abel
theorem sub_grid_round (F Ne De No Do : ℝ) (m : ℤ) (Q D : ℕ)
    (hFV : |F - (Ne / De - No / Do)| ≤ 1 / (2 * D))
    (hr1 : (m : ℝ) * (De * Do) ≤ (Ne * Do - No * De) * Q)
    (hr2 : (Ne * Do - No * De) * Q < ((m : ℝ) + 1) * (De * Do))
    (hDe : 0 < De) (hDo : 0 < Do) (hDr : 0 < (D : ℝ)) (hQr : 0 < (Q : ℝ))
    (hQ : 2 * D ≤ Q) :
    |F - (m : ℝ) / Q| ≤ 1 / D := by
  have hd : (0 : ℝ) < De * Do := mul_pos hDe hDo
  have hV : Ne / De - No / Do = (Ne * Do - No * De) / (De * Do) := by field_simp
  have e1 : (m : ℝ) / Q ≤ (Ne * Do - No * De) / (De * Do) := by
    rw [div_le_div_iff₀ hQr hd]; exact hr1
  have e2 : (Ne * Do - No * De) / (De * Do) < (m : ℝ) / Q + 1 / Q := by
    rw [← add_div, div_lt_div_iff₀ hd hQr]; exact hr2
  have hround' : |(Ne / De - No / Do) - (m : ℝ) / Q| ≤ 1 / (2 * D) := by
    rw [hV, abs_of_nonneg (sub_nonneg.mpr e1)]
    calc (Ne * Do - No * De) / (De * Do) - (m : ℝ) / Q
        ≤ 1 / Q := by linarith [e2]
      _ ≤ 1 / (2 * D) := by
          rw [div_le_div_iff₀ hQr (mul_pos two_pos hDr), one_mul, one_mul]; exact_mod_cast hQ
  calc |F - (m : ℝ) / Q|
      ≤ |F - (Ne / De - No / Do)| + |(Ne / De - No / Do) - (m : ℝ) / Q| := abs_sub_le _ _ _
    _ ≤ 1 / (2 * D) + 1 / (2 * D) := add_le_add hFV hround'
    _ = 1 / D := by rw [← add_div, one_add_one_eq_two, ← div_div, div_self two_ne_zero]
end BSN
end
end CertificatePort156


section CertificatePort157
section
namespace BSN
open Enclosure
open Finset
def expNatP (u : ℕ) : ℕ → ℕ := fun _ => u
def expNatQ (v : ℕ) : ℕ → ℕ := fun j => Nat.mul v (Nat.succ j)
theorem exp_neg_recip_bound (Q D0 Q' D p p' : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (hp : Nat.ble 1 p) (hQ : Nat.ble 1 Q) (hQ' : Nat.ble 1 Q')
    (hD : Nat.ble 1 D) (hD0 : Nat.ble 1 D0) (hQp : Q.ble p)
    (hr1 : (p'.mul p).ble (Q'.mul Q)) (hr2 : (Q'.mul Q).blt ((p'.succ).mul p))
    (hcomb : (D.mul (Q'.add D0)).ble (D0.mul Q'))
    (hpos : Real.IsNear (Real.exp x) false p Q 1 D0) :
    Real.IsNear (Real.exp (-x)) false p' Q' 1 D := by
  rw [Real.IsNear, sfrac_false_div, Nat.cast_one] at hpos ⊢
  simp only [Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq] at hQp hr1 hr2 hcomb
  have hpR : (0 : ℝ) < p := pos_real_of_ble hp
  have hQR : (0 : ℝ) < Q := pos_real_of_ble hQ
  have hQ'R : (0 : ℝ) < Q' := pos_real_of_ble hQ'
  have hDR : (0 : ℝ) < D := pos_real_of_ble hD
  have hD0R : (0 : ℝ) < D0 := pos_real_of_ble hD0
  set a : ℝ := Real.exp x with ha
  have ha1 : 1 ≤ a := by rw [ha]; exact Real.one_le_exp hx
  have ha0 : 0 < a := by linarith
  have hane : a ≠ 0 := ne_of_gt ha0
  set b : ℝ := (p : ℝ) / Q with hbdef
  have hb1 : 1 ≤ b := by rw [hbdef, le_div_iff₀ hQR, one_mul]; exact_mod_cast hQp
  have hb0 : 0 < b := by linarith
  have hbne : b ≠ 0 := ne_of_gt hb0
  have hexpneg : Real.exp (-x) = 1 / a := by rw [Real.exp_neg, one_div, ha]
  rw [hexpneg]
  have hab : |1 / a - 1 / b| ≤ 1 / D0 := by
    have heq : 1 / a - 1 / b = (b - a) / (a * b) := by field_simp
    rw [heq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < a * b),
      div_le_iff₀ (by positivity : (0 : ℝ) < a * b)]
    calc |b - a| = |a - b| := abs_sub_comm b a
      _ ≤ 1 / D0 := hpos
      _ ≤ 1 / D0 * (a * b) := le_mul_of_one_le_right (by positivity) (by nlinarith)
  have hterm2 : |1 / b - (p' : ℝ) / Q'| ≤ 1 / Q' := by
    have h1b : 1 / b = (Q : ℝ) / p := by rw [hbdef, one_div_div]
    rw [h1b]
    have e1 : (p' : ℝ) / Q' ≤ (Q : ℝ) / p := by
      rw [div_le_div_iff₀ hQ'R hpR, mul_comm (Q : ℝ)]; exact_mod_cast hr1
    have e2 : (Q : ℝ) / p < (p' : ℝ) / Q' + 1 / Q' := by
      rw [← add_div, div_lt_div_iff₀ hpR hQ'R, mul_comm (Q : ℝ)]; exact_mod_cast hr2
    rw [abs_of_nonneg (by linarith)]; linarith
  calc |1 / a - (p' : ℝ) / Q'|
      ≤ |1 / a - 1 / b| + |1 / b - (p' : ℝ) / Q'| := abs_sub_le _ _ _
    _ ≤ 1 / D0 + 1 / Q' := add_le_add hab hterm2
    _ ≤ 1 / D := by
        have hc : (D : ℝ) * (Q' + D0) ≤ D0 * Q' := by exact_mod_cast hcomb
        rw [div_add_div _ _ (ne_of_gt hD0R) (ne_of_gt hQ'R), one_mul, mul_one,
          div_le_div_iff₀ (by positivity) hDR, one_mul]
        nlinarith
theorem exp_neg_bound (u v Q D0 Q' D p p' : ℕ)
    (hp : Nat.ble 1 p) (hQ : Nat.ble 1 Q) (hQ' : Nat.ble 1 Q')
    (hD : Nat.ble 1 D) (hD0 : Nat.ble 1 D0) (hQp : Q.ble p)
    (hr1 : (p'.mul p).ble (Q'.mul Q)) (hr2 : (Q'.mul Q).blt ((p'.succ).mul p))
    (hcomb : (D.mul (Q'.add D0)).ble (D0.mul Q'))
    (hpos : Real.IsNear (Real.exp ((u : ℝ) / v)) false p Q 1 D0) :
    Real.IsNear (Real.exp ((-(u : ℝ)) / v)) false p' Q' 1 D := by
  rw [neg_div]
  exact exp_neg_recip_bound Q D0 Q' D p p' ((u : ℝ) / v) (by positivity)
    hp hQ hQ' hD hD0 hQp hr1 hr2 hcomb hpos
theorem exp_fold_term (u v i : ℕ) (hv : v ≠ 0) :
    ∏ j ∈ Finset.Ico 0 (i + 1), ((u : ℚ) / ((v * (j + 1) : ℕ) : ℚ))
      = ((u : ℚ) / v) ^ (i + 1) / ((i + 1).factorial : ℚ) := by
  rw [← Finset.range_eq_Ico]
  push_cast
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_range]
  have hfac : ∏ j ∈ Finset.range (i + 1), ((j : ℚ) + 1) = ((i + 1).factorial : ℚ) := by
    rw [← Finset.prod_range_add_one_eq_factorial (i + 1)]; push_cast; ring
  rw [hfac, div_pow]
  have hvne : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hfne : ((i + 1).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
theorem exp_value (u v N T Q P : ℕ) (hv : v ≠ 0) (hN : 1 ≤ N)
    (h : (T, Q, P) = binarySplit (fun _ => u) (fun j => v * (j + 1)) 0 (N - 1)) :
    (((Q + T : ℕ) : ℚ) / (Q : ℚ))
      = ∑ i ∈ Finset.range N, ((u : ℚ) / v) ^ i / (i.factorial : ℚ) := by
  have hqne : ∀ i, (fun j => v * (j + 1)) i ≠ 0 := by intro i; simp [hv]
  have hQ0 : Q ≠ 0 := by
    have hb := binarySplit_nonzero (p := fun _ => u) (q := fun j => v * (j + 1))
      (m := 0) (n := N - 1) hqne
    rw [← h] at hb
    simpa using hb
  have hspec := (binarySplit_spec (p := fun _ => u) (q := fun j => v * (j + 1))
    (m := 0) (n := N - 1) hqne h).2
  rw [Finset.sum_congr rfl (fun i _ => by simpa using exp_fold_term u v i hv)] at hspec
  rw [← Finset.range_eq_Ico] at hspec
  have hNeq : N = N - 1 + 1 := by omega
  rw [hNeq, Finset.sum_range_succ']
  rw [hspec]
  have hQ0' : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  push_cast
  field_simp
  ring
open Real in
theorem exp_dyadic_bound (u v N Nm Qd D T P Q p : ℕ)
    (hu : u.blt ((N.succ).mul v)) (hQd : Nat.ble 1 Qd) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v)
    (hN : Nat.ble 1 N) (hNm : (Nm.succ).beq N)
    (hsplit : binarySplit (expNatP u) (expNatQ v) 0 Nm = (T, Qd, P))
    (htail : (((u.pow N).mul (N.succ)).mul v).mul (Nat.mul 2 D) |>.ble
      (((v.mul N).mul Qd).mul (((N.succ).mul v).sub u)))
    (hr1 : (p.mul Qd).ble ((Qd.add T).mul Q)) (hr2 : ((Qd.add T).mul Q).blt ((p.succ).mul Qd))
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.exp ((u : ℝ) / v)) false p Q 1 D := by
  have hNm' : Nm = N - 1 := by
    have h : Nm + 1 = N := Nat.eq_of_beq_eq_true hNm
    omega
  subst hNm'
  have hQdeq : Qd = v ^ (N - 1) * (N - 1).factorial := by
    have h := (binarySplit_PQ (p := expNatP u) (q := expNatQ v) (m := 0) (n := N - 1)).2
    rw [hsplit] at h
    have hQdraw : Qd = ∏ j ∈ Finset.Ico 0 (N - 1), expNatQ v j := h
    rw [hQdraw, ← Finset.range_eq_Ico]
    simp only [expNatQ, Nat.mul_eq, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_range]
    rw [Finset.prod_range_add_one_eq_factorial]
  have hbridge : v * N * Qd = v ^ N * N.factorial := by
    rw [hQdeq]
    obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by have := Nat.le_of_ble_eq_true hN; omega⟩
    simp only [Nat.add_sub_cancel]
    rw [pow_succ, Nat.factorial_succ]; ring
  rw [Real.IsNear, sfrac_false_div, Nat.cast_one]
  simp only [Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.pow_eq,
    Nat.sub_eq] at hu htail hr1 hr2 hQ
  rw [hbridge] at htail
  have hDN : 0 < D := pos_of_ble hD
  have hqs' : (0 : ℝ) < Qd := pos_real_of_ble hQd
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  have hvr : (0 : ℝ) < v := pos_real_of_ble hv
  have hvne : v ≠ 0 := (pos_of_ble hv).ne'
  have hvR : (v : ℝ) ≠ 0 := ne_of_gt hvr
  have hQ0 : 0 < Q := by omega
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hx0 : 0 ≤ (u : ℝ) / v := by positivity
  have hxlt : (u : ℝ) / v < (N : ℝ) + 1 := by rw [div_lt_iff₀ hvr]; exact_mod_cast hu
  have hsum : ∑ k ∈ Finset.range N, ((u : ℝ) / v) ^ k / (k.factorial : ℝ)
      = ((Qd + T : ℕ) : ℝ) / (Qd : ℝ) := by
    have hq := exp_value u v N T Qd P hvne (Nat.le_of_ble_eq_true hN) hsplit.symm
    have hr := congrArg (fun r : ℚ => (r : ℝ)) hq
    push_cast at hr ⊢
    rw [← hr]
  have hexp : |Real.exp ((u : ℝ) / v) - ((Qd + T : ℕ) : ℝ) / (Qd : ℝ)|
      ≤ ((u : ℝ) / v) ^ N / N.factorial * (((N : ℝ) + 1) / ((N : ℝ) + 1 - (u : ℝ) / v)) := by
    rw [← hsum, abs_of_nonneg (exp_sub_sum_nonneg _ N hx0)]
    exact exp_sub_sum_le _ N hx0 hxlt
  have htail' : ((u : ℝ) / v) ^ N / N.factorial * (((N : ℝ) + 1) / ((N : ℝ) + 1 - (u : ℝ) / v))
      ≤ 1 / (2 * D) := by
    have hpos : (0 : ℝ) < (N : ℝ) + 1 - (u : ℝ) / v := by linarith
    have hsubpos : 0 < (N + 1) * v - u := by
      have h := hu; simp only [Nat.succ_eq_add_one] at h; omega
    have hfacne : (N.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos N).ne'
    have hvpowne : (v : ℝ) ^ N ≠ 0 := pow_ne_zero N hvR
    have hc1 : ((N : ℝ) + 1 - (u : ℝ) / v) = (((N + 1) * v - u : ℕ) : ℝ) / v := by
      rw [Nat.cast_sub hu.le]; push_cast; field_simp
    have key : ((u : ℝ) / v) ^ N / N.factorial * (((N : ℝ) + 1) / ((N : ℝ) + 1 - (u : ℝ) / v))
        = ((u : ℝ) ^ N * ((N : ℝ) + 1) * v) /
          ((v : ℝ) ^ N * N.factorial * (((N + 1) * v - u : ℕ) : ℝ)) := by
      rw [hc1, div_pow]
      field_simp
    have hden : (0 : ℝ) < (v : ℝ) ^ N * N.factorial * (((N + 1) * v - u : ℕ) : ℝ) :=
      mul_pos (mul_pos (pow_pos hvr N) (by exact_mod_cast Nat.factorial_pos N))
        (by exact_mod_cast hsubpos)
    rw [key, div_le_div_iff₀ hden (mul_pos two_pos hDr), one_mul]
    exact_mod_cast htail
  have e1 : (p : ℝ) / Q ≤ ((Qd + T : ℕ) : ℝ) / (Qd : ℝ) := by
    rw [div_le_div_iff₀ hQr hqs']; exact_mod_cast hr1
  have e2 : ((Qd + T : ℕ) : ℝ) / (Qd : ℝ) < (p : ℝ) / Q + 1 / Q := by
    rw [← add_div, div_lt_div_iff₀ hqs' hQr]; exact_mod_cast hr2
  have hround' : |((Qd + T : ℕ) : ℝ) / (Qd : ℝ) - (p : ℝ) / Q| ≤ 1 / (2 * D) := by
    rw [abs_of_nonneg (sub_nonneg.mpr e1)]
    calc ((Qd + T : ℕ) : ℝ) / (Qd : ℝ) - (p : ℝ) / Q
        ≤ 1 / Q := by linarith [e2]
      _ ≤ 1 / (2 * D) := by
          rw [div_le_div_iff₀ hQr (mul_pos two_pos hDr), one_mul, one_mul]; exact_mod_cast hQ
  calc |Real.exp ((u : ℝ) / v) - (p : ℝ) / Q|
      ≤ |Real.exp ((u : ℝ) / v) - ((Qd + T : ℕ) : ℝ) / (Qd : ℝ)|
          + |((Qd + T : ℕ) : ℝ) / (Qd : ℝ) - (p : ℝ) / Q| := abs_sub_le _ _ _
    _ ≤ 1 / (2 * D) + 1 / (2 * D) := add_le_add (hexp.trans htail') hround'
    _ = 1 / D := by rw [← add_div, one_add_one_eq_two, ← div_div, div_self two_ne_zero]
theorem exp_int_of_rat (u : ℕ) (neg : Bool) (cn cd rn rd : ℕ)
    (h : Real.IsNear (Real.exp ((u : ℝ) / ((1 : ℕ) : ℝ))) neg cn cd rn rd) :
    Real.IsNear (Real.exp ((u : ℕ) : ℝ)) neg cn cd rn rd := by
  rwa [Nat.cast_one, div_one] at h
end BSN
end
end CertificatePort157


section CertificatePort159
section
namespace BSN
open Enclosure
open Finset
theorem prod_even_denom (j : ℕ) :
    ∏ k ∈ range j, ((4 * k + 2) * (4 * k + 3) * (4 * k + 4) * (4 * k + 5))
        = (4 * j + 1).factorial := by
  induction j with
  | zero => simp
  | succ n ih =>
    have e : 4 * (n + 1) + 1 = (4 * n + 1) + 4 := by ring
    rw [prod_range_succ, ih, e, factorial_add_four]
theorem prod_odd_denom (j : ℕ) :
    (∏ k ∈ range j, ((4 * k + 4) * (4 * k + 5) * (4 * k + 6) * (4 * k + 7))) * 6 =
      (4 * j + 3).factorial := by
  induction j with
  | zero => rfl
  | succ n ih =>
    have e : 4 * (n + 1) + 3 = (4 * n + 3) + 4 := by ring
    rw [prod_range_succ, e, factorial_add_four, ← ih]
    ring
theorem sinEven_fold_term (u v i : ℕ) (hv : v ≠ 0) :
    ∏ k ∈ Finset.Ico 0 (i + 1), ((sinEvenP u k : ℚ) / (sinEvenQ v k))
      = (u : ℚ) ^ (4 * (i + 1)) / ((v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 1).factorial) := by
  rw [← Finset.range_eq_Ico]
  simp only [sinEvenP, sinEvenQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  have hden : (∏ k ∈ Finset.range (i + 1),
      ((v ^ 4 * ((4 * k + 2) * (4 * k + 3) * (4 * k + 4) * (4 * k + 5)) : ℕ) : ℚ))
      = (v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 1).factorial := by
    have keyN : ∏ k ∈ Finset.range (i + 1),
        (v ^ 4 * ((4 * k + 2) * (4 * k + 3) * (4 * k + 4) * (4 * k + 5)))
        = v ^ (4 * (i + 1)) * (4 * (i + 1) + 1).factorial := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul, prod_even_denom]
    exact_mod_cast keyN
  rw [hden]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hf : ((4 * (i + 1) + 1).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  push_cast
  rw [← pow_mul]
theorem sinEven_value (u v M T Q P : ℕ) (hv : v ≠ 0) (hM : 1 ≤ M)
    (h : (T, Q, P) = binarySplit (sinEvenP u) (sinEvenQ v) 0 (M - 1)) :
    ((u : ℚ) * (Q + T) / (v * Q))
      = ∑ j ∈ Finset.range M,
          (u : ℚ) ^ (4 * j + 1) / ((v : ℚ) ^ (4 * j + 1) * (4 * j + 1).factorial) := by
  have hqne : ∀ i, sinEvenQ v i ≠ 0 := by
    intro i; simp only [sinEvenQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
    exact Nat.mul_ne_zero (pow_ne_zero 4 hv) (by positivity)
  have hQ0 : Q ≠ 0 := by
    have hb := binarySplit_nonzero (p := sinEvenP u) (q := sinEvenQ v) (m := 0) (n := M - 1) hqne
    rw [← h] at hb
    simpa using hb
  have hspec :=
      (binarySplit_spec (p := sinEvenP u) (q := sinEvenQ v) (m := 0) (n := M - 1) hqne h).2
  rw [Finset.sum_congr rfl (fun i _ => sinEven_fold_term u v i hv)] at hspec
  rw [← Finset.range_eq_Ico] at hspec
  have hNeq : M = M - 1 + 1 := by omega
  rw [hNeq, Finset.sum_range_succ']
  have hterm : ∀ i ∈ Finset.range (M - 1),
      (u : ℚ) ^ (4 * (i + 1) + 1) / ((v : ℚ) ^ (4 * (i + 1) + 1) * (4 * (i + 1) + 1).factorial)
        = (u : ℚ) / v *
          ((u : ℚ) ^ (4 * (i + 1)) / ((v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 1).factorial)) := by
    intro i _
    rw [pow_succ' (u : ℚ), pow_succ' (v : ℚ)]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hspec]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hQ0' : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0
  simp only [Nat.mul_zero, Nat.zero_add, pow_one, Nat.factorial_one, Nat.cast_one, mul_one]
  field_simp
  ring
theorem sinOdd_fold_term (u v i : ℕ) (hv : v ≠ 0) :
    ∏ k ∈ Finset.Ico 0 (i + 1), ((sinOddP u k : ℚ) / (sinOddQ v k))
      = 6 * (u : ℚ) ^ (4 * (i + 1)) / ((v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 3).factorial) := by
  rw [← Finset.range_eq_Ico]
  simp only [sinOddP, sinOddQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  have hden : (∏ k ∈ Finset.range (i + 1),
      ((v ^ 4 * ((4 * k + 4) * (4 * k + 5) * (4 * k + 6) * (4 * k + 7)) : ℕ) : ℚ))
      = (v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 3).factorial / 6 := by
    have keyN : (∏ k ∈ Finset.range (i + 1),
        (v ^ 4 * ((4 * k + 4) * (4 * k + 5) * (4 * k + 6) * (4 * k + 7)))) * 6
        = v ^ (4 * (i + 1)) * (4 * (i + 1) + 3).factorial := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul, mul_assoc,
        prod_odd_denom]
    have keyQ : (∏ k ∈ Finset.range (i + 1),
        ((v ^ 4 * ((4 * k + 4) * (4 * k + 5) * (4 * k + 6) * (4 * k + 7)) : ℕ) : ℚ)) * 6
        = (v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 3).factorial := by exact_mod_cast keyN
    rwa [eq_div_iff (by norm_num : (6 : ℚ) ≠ 0)]
  rw [hden]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hf : ((4 * (i + 1) + 3).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  push_cast
  rw [← pow_mul]
theorem sinOdd_value (u v M T Q P : ℕ) (hv : v ≠ 0) (hM : 1 ≤ M)
    (h : (T, Q, P) = binarySplit (sinOddP u) (sinOddQ v) 0 (M - 1)) :
    ((u : ℚ) ^ 3 * (Q + T) / (6 * v ^ 3 * Q))
      = ∑ j ∈ Finset.range M,
          (u : ℚ) ^ (4 * j + 3) / ((v : ℚ) ^ (4 * j + 3) * (4 * j + 3).factorial) := by
  have hqne : ∀ i, sinOddQ v i ≠ 0 := by
    intro i; simp only [sinOddQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
    exact Nat.mul_ne_zero (pow_ne_zero 4 hv) (by positivity)
  have hQ0 : Q ≠ 0 := by
    have hb := binarySplit_nonzero (p := sinOddP u) (q := sinOddQ v) (m := 0) (n := M - 1) hqne
    rw [← h] at hb
    simpa using hb
  have hspec := (binarySplit_spec (p := sinOddP u) (q := sinOddQ v) (m := 0) (n := M - 1) hqne h).2
  rw [Finset.sum_congr rfl (fun i _ => sinOdd_fold_term u v i hv)] at hspec
  rw [← Finset.range_eq_Ico] at hspec
  have hNeq : M = M - 1 + 1 := by omega
  rw [hNeq, Finset.sum_range_succ']
  have hterm : ∀ i ∈ Finset.range (M - 1),
      (u : ℚ) ^ (4 * (i + 1) + 3) / ((v : ℚ) ^ (4 * (i + 1) + 3) * (4 * (i + 1) + 3).factorial)
        = (u : ℚ) ^ 3 / (6 * v ^ 3) *
          (6 * (u : ℚ) ^ (4 * (i + 1))
                / ((v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 3).factorial)) := by
    intro i _
    rw [pow_add (u : ℚ) (4 * (i + 1)) 3, pow_add (v : ℚ) (4 * (i + 1)) 3]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hspec]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hQ0' : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0
  simp only [Nat.mul_zero, Nat.zero_add, Nat.factorial_succ, Nat.factorial_zero]
  push_cast
  field_simp
  ring
theorem sin_dyadic_bound (u v M Mm Q D Te Qe Pe To Qo Po : ℕ) (neg : Bool) (cn : ℕ)
    (hu : u.blt (((Nat.mul 2 (Nat.mul 2 M)).add 2).mul v))
    (hu2 : (Nat.mul 2 (u.pow 2)).ble ((((Nat.mul 2 (Nat.mul 2 M)).add 2).pow 2).mul (v.pow 2)))
    (hQe : Nat.ble 1 Qe) (hQo : Nat.ble 1 Qo) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v) (hM :
          Nat.ble 1 M)
    (hMm : (Mm.succ).beq M)
    (heven : binarySplit (sinEvenP u) (sinEvenQ v) (nat_lit 0) Mm = (Te, Qe, Pe))
    (hodd : binarySplit (sinOddP u) (sinOddQ v) (nat_lit 0) Mm = (To, Qo, Po))
    (htail : ((Nat.mul 2 (u.pow ((Nat.mul 2 (Nat.mul 2 M)).succ))).mul (Nat.mul 2 D)).ble
      ((v.mul Qe).mul (sinEvenQ v Mm)))
    (hr1 : (((numPos neg cn).mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)).ble
      ((((u.mul (Qe.add Te)).mul ((Nat.mul 6 (v.pow 3)).mul Qo)).mul Q).add
        ((numNeg neg cn).mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo)))) = true)
    (hr2 : ((((u.mul (Qe.add Te)).mul ((Nat.mul 6 (v.pow 3)).mul Qo)).mul Q).add
        ((numNeg neg cn).mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo)))).blt
      ((((numPos neg cn).succ).mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)) = true)
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.sin ((u : ℝ) / v)) neg cn Q 1 D := by
  have hMm' : Mm = M - 1 := by
    have h : Mm + 1 = M := Nat.eq_of_beq_eq_true hMm
    omega
  subst hMm'
  have hMpos0 : 1 ≤ M := Nat.le_of_ble_eq_true hM
  have hbridge : v * (Qe * sinEvenQ v (M - 1))
      = v ^ (2 * (2 * M) + 1) * (2 * (2 * M) + 1).factorial := by
    have hQeprod : Qe = ∏ k ∈ Finset.range (M - 1), sinEvenQ v k := by
      have h := (binarySplit_PQ (p := sinEvenP u) (q := sinEvenQ v) (m := 0) (n := M - 1)).2
      rw [heven, ← Finset.range_eq_Ico] at h; exact h
    rw [hQeprod, ← Finset.prod_range_succ, show M - 1 + 1 = M from by omega]
    simp only [sinEvenQ, Nat.pow_eq, Nat.mul_eq, Nat.add_eq]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul, prod_even_denom,
      show 2 * (2 * M) + 1 = 4 * M + 1 from by ring, pow_succ]
    ring
  set mp := numPos neg cn with hmp_def
  set mn := numNeg neg cn with hmn_def
  have hvN : 0 < v := pos_of_ble hv
  have hQeN : 0 < Qe := pos_of_ble hQe
  have hQoN : 0 < Qo := pos_of_ble hQo
  have hDN : 0 < D := pos_of_ble hD
  have hvne : v ≠ 0 := hvN.ne'
  have hMpos : 1 ≤ M := Nat.le_of_ble_eq_true hM
  have hvalE := sinEven_value u v M Te Qe Pe hvne hMpos heven.symm
  have hvalO := sinOdd_value u v M To Qo Po hvne hMpos hodd.symm
  have hcombine : (u : ℚ) * (Qe + Te) / (v * Qe) - (u : ℚ) ^ 3 * (Qo + To) / (6 * v ^ 3 * Qo)
      = ∑ i ∈ Finset.range (2 * M),
          (-1) ^ i * ((u : ℚ) / v) ^ (2 * i + 1) / (2 * i + 1).factorial := by
    rw [hvalE, hvalO, sum_range_two_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have s1 : ((-1 : ℚ)) ^ (2 * j) = 1 := by rw [pow_mul]; norm_num
    have s2 : ((-1 : ℚ)) ^ (2 * j + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    have e1 : 2 * (2 * j) + 1 = 4 * j + 1 := by ring
    have e2 : 2 * (2 * j + 1) + 1 = 4 * j + 3 := by ring
    rw [e1, e2, s1, s2, div_pow, div_pow]
    ring
  set m : ℤ := (mp : ℤ) - (mn : ℤ) with hm
  rw [Real.IsNear, Nat.cast_one]
  have hvform : sfrac neg cn Q = (m : ℝ) / Q := by
    rw [sfrac_eq_parts neg cn Q, ← hmp_def, ← hmn_def, hm]
    push_cast
    ring
  rw [hvform]
  simp only [Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq,
    Nat.pow_eq] at hu hu2 htail hQ hr1 hr2
  set De := v * Qe with hDe_def
  set Do := 6 * v ^ 3 * Qo with hDo_def
  set Ne := u * (Qe + Te) with hNe_def
  set No := u ^ 3 * (Qo + To) with hNo_def
  have hDeR : (De : ℝ) = (v : ℝ) * Qe := by rw [hDe_def]; push_cast; ring
  have hDoR : (Do : ℝ) = 6 * (v : ℝ) ^ 3 * Qo := by rw [hDo_def]; push_cast; ring
  have hr1z : m * ((De : ℤ) * Do) ≤ ((Ne : ℤ) * Do - (No : ℤ) * De) * Q := by
    have h : (mp : ℤ) * ((De : ℤ) * Do) + (No : ℤ) * De * Q
        ≤ (Ne : ℤ) * Do * Q + (mn : ℤ) * ((De : ℤ) * Do) := by exact_mod_cast hr1
    have e1 : m * ((De : ℤ) * Do) = (mp : ℤ) * ((De : ℤ) * Do) - (mn : ℤ) * ((De : ℤ) * Do) := by
      rw [hm]; ring
    have e2 : ((Ne : ℤ) * Do - (No : ℤ) * De) * Q = (Ne : ℤ) * Do * Q - (No : ℤ) * De * Q := by ring
    rw [e1, e2]; linarith
  have hr2z : ((Ne : ℤ) * Do - (No : ℤ) * De) * Q < (m + 1) * ((De : ℤ) * Do) := by
    have h : (Ne : ℤ) * Do * Q + (mn : ℤ) * ((De : ℤ) * Do)
        < (mp + 1) * ((De : ℤ) * Do) + (No : ℤ) * De * Q := by exact_mod_cast hr2
    have e1 : (m + 1) * ((De : ℤ) * Do)
        = (mp + 1) * ((De : ℤ) * Do) - (mn : ℤ) * ((De : ℤ) * Do) := by rw [hm]; ring
    have e2 : ((Ne : ℤ) * Do - (No : ℤ) * De) * Q = (Ne : ℤ) * Do * Q - (No : ℤ) * De * Q := by ring
    rw [e1, e2]; linarith
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  have hvr : (0 : ℝ) < v := pos_real_of_ble hv
  have hQ0 : 0 < Q := by omega
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hDe0 : (0 : ℝ) < De := by rw [hDeR]; positivity
  have hDo0 : (0 : ℝ) < Do := by rw [hDoR]; positivity
  have hvalR : ((Ne : ℝ) / De - (No : ℝ) / Do)
      = ∑ i ∈ Finset.range (2 * M),
          (-1) ^ i * ((u : ℝ) / v) ^ (2 * i + 1) / (2 * i + 1).factorial := by
    have hcast := congrArg (fun r : ℚ => (r : ℝ)) hcombine
    push_cast at hcast
    rw [hNe_def, hDe_def, hNo_def, hDo_def]
    push_cast
    convert hcast using 2
  have hxnn : (0 : ℝ) ≤ (u : ℝ) / v := by positivity
  have hxlt : (u : ℝ) / v < 2 * ((2 * M : ℕ) : ℝ) + 2 := by
    rw [div_lt_iff₀ hvr]; exact_mod_cast hu
  have hsin := sin_sub_sum_le ((u : ℝ) / v) (2 * M) hxnn hxlt
  rw [← hvalR] at hsin
  have hsin' : |Real.sin ((u : ℝ) / v) - ((Ne : ℝ) / De - (No : ℝ) / Do)| ≤ 1 / (2 * D) := by
    refine hsin.trans ?_
    have hA2 : ((u : ℝ) / v) ^ (2 * (2 * M) + 1) / (2 * (2 * M) + 1).factorial * 2
        ≤ 1 / (2 * D) := by
      rw [div_pow, div_div, div_mul_eq_mul_div,
        div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      have e : (u : ℝ) ^ (2 * (2 * M) + 1) * 2 * (2 * D)
          = 2 * (u : ℝ) ^ (2 * (2 * M) + 1) * (2 * D) := by ring
      rw [e]
      have htR : 2 * (u : ℝ) ^ (2 * (2 * M) + 1) * (2 * D)
          ≤ (v : ℝ) * (Qe : ℝ) * (sinEvenQ v (M - 1) : ℝ) := by exact_mod_cast htail
      have hbR : (v : ℝ) * (Qe : ℝ) * (sinEvenQ v (M - 1) : ℝ)
          = (v : ℝ) ^ (2 * (2 * M) + 1) * ((2 * (2 * M) + 1).factorial : ℝ) := by
        have hb : v * Qe * sinEvenQ v (M - 1)
            = v ^ (2 * (2 * M) + 1) * (2 * (2 * M) + 1).factorial := by
          rw [Nat.mul_assoc]; exact hbridge
        exact_mod_cast hb
      exact le_of_le_of_eq htR hbR
    refine le_trans ?_ hA2
    gcongr
    exact geo_factor_le _ _ (by positivity) (by
      rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
      exact_mod_cast hu2)
  have hr1' : (m : ℝ) * ((De : ℝ) * Do) ≤ ((Ne : ℝ) * Do - No * De) * Q := by exact_mod_cast hr1z
  have hr2' : ((Ne : ℝ) * Do - No * De) * Q < ((m : ℝ) + 1) * ((De : ℝ) * Do) := by
    exact_mod_cast hr2z
  exact sub_grid_round (Real.sin ((u : ℝ) / v)) (Ne : ℝ) (De : ℝ) (No : ℝ) (Do : ℝ) m Q D
    hsin' hr1' hr2' hDe0 hDo0 hDr hQr hQ
theorem sin_dyadic_bound_f (u v M Mm Q D Te Qe Pe To Qo Po cn : ℕ)
    (hu : u.blt (((Nat.mul 2 (Nat.mul 2 M)).add 2).mul v))
    (hu2 : (Nat.mul 2 (u.pow 2)).ble ((((Nat.mul 2 (Nat.mul 2 M)).add 2).pow 2).mul (v.pow 2)))
    (hQe : Nat.ble 1 Qe) (hQo : Nat.ble 1 Qo) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v) (hM :
          Nat.ble 1 M)
    (hMm : (Mm.succ).beq M)
    (heven : binarySplit (sinEvenP u) (sinEvenQ v) (nat_lit 0) Mm = (Te, Qe, Pe))
    (hodd : binarySplit (sinOddP u) (sinOddQ v) (nat_lit 0) Mm = (To, Qo, Po))
    (htail : ((Nat.mul 2 (u.pow ((Nat.mul 2 (Nat.mul 2 M)).succ))).mul (Nat.mul 2 D)).ble
      ((v.mul Qe).mul (sinEvenQ v Mm)))
    (hr1 : ((cn.mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)).ble
      (((u.mul (Qe.add Te)).mul ((Nat.mul 6 (v.pow 3)).mul Qo)).mul Q) = true)
    (hr2 : ((((u.mul (Qe.add Te)).mul ((Nat.mul 6 (v.pow 3)).mul Qo)).mul Q)).blt
      ((((cn.succ)).mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)) = true)
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.sin ((u : ℝ) / v)) false cn Q 1 D := by
  refine sin_dyadic_bound u v M Mm Q D Te Qe Pe To Qo Po false cn hu hu2 hQe hQo hD hv hM hMm
    heven hodd htail ?_ ?_ hQ
  · simp only [numPos, numNeg, if_neg Bool.false_ne_true, Nat.ble_eq, Nat.add_eq,
      Nat.mul_eq, Nat.pow_eq, Nat.zero_mul, Nat.add_zero] at hr1 ⊢
    omega
  · simp only [numPos, numNeg, if_neg Bool.false_ne_true, Nat.blt_eq, Nat.add_eq,
      Nat.mul_eq, Nat.pow_eq, Nat.zero_mul, Nat.add_zero] at hr2 ⊢
    omega
theorem sin_dyadic_bound_t (u v M Mm Q D Te Qe Pe To Qo Po cn : ℕ)
    (hu : u.blt (((Nat.mul 2 (Nat.mul 2 M)).add 2).mul v))
    (hu2 : (Nat.mul 2 (u.pow 2)).ble ((((Nat.mul 2 (Nat.mul 2 M)).add 2).pow 2).mul (v.pow 2)))
    (hQe : Nat.ble 1 Qe) (hQo : Nat.ble 1 Qo) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v) (hM :
          Nat.ble 1 M)
    (hMm : (Mm.succ).beq M)
    (heven : binarySplit (sinEvenP u) (sinEvenQ v) (nat_lit 0) Mm = (Te, Qe, Pe))
    (hodd : binarySplit (sinOddP u) (sinOddQ v) (nat_lit 0) Mm = (To, Qo, Po))
    (htail : ((Nat.mul 2 (u.pow ((Nat.mul 2 (Nat.mul 2 M)).succ))).mul (Nat.mul 2 D)).ble
      ((v.mul Qe).mul (sinEvenQ v Mm)))
    (hr1 : (((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)).ble
      ((((u.mul (Qe.add Te)).mul ((Nat.mul 6 (v.pow 3)).mul Qo)).mul Q).add
        (cn.mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo)))) = true)
    (hr2 : ((((u.mul (Qe.add Te)).mul ((Nat.mul 6 (v.pow 3)).mul Qo)).mul Q).add
        (cn.mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo)))).blt
      ((((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)) = true)
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.sin ((u : ℝ) / v)) true cn Q 1 D := by
  refine sin_dyadic_bound u v M Mm Q D Te Qe Pe To Qo Po true cn hu hu2 hQe hQo hD hv hM hMm
    heven hodd htail ?_ ?_ hQ
  · have hp : numPos true cn = 0 := rfl
    have hn : numNeg true cn = cn := rfl
    simp only [hp, hn, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.pow_eq,
      Nat.zero_mul, Nat.zero_add] at hr1 ⊢
    omega
  · have hp : numPos true cn = 0 := rfl
    have hn : numNeg true cn = cn := rfl
    simp only [hp, hn, Nat.blt_eq, Nat.add_eq, Nat.mul_eq, Nat.pow_eq, Nat.one_mul] at hr2 ⊢
    omega
theorem sin_neg_of_bound (u v : ℕ) (neg : Bool) (cn cd rn rd : ℕ)
    (hpos : Real.IsNear (Real.sin ((u : ℝ) / v)) neg cn cd rn rd) :
    Real.IsNear (Real.sin ((-(u : ℝ)) / v)) (!neg) cn cd rn rd := by
  rw [Real.IsNear, sfrac_not, neg_div, Real.sin_neg]
  have he : -Real.sin ((u : ℝ) / v) - -sfrac neg cn cd
      = -(Real.sin ((u : ℝ) / v) - sfrac neg cn cd) := by ring
  rw [he, abs_neg]
  exact hpos
end BSN
end
end CertificatePort159


section CertificatePort161
section
namespace BSN
open Enclosure
open Finset
theorem prod_cosEven_denom (j : ℕ) :
    ∏ k ∈ range j, ((4 * k + 1) * (4 * k + 2) * (4 * k + 3) * (4 * k + 4)) = (4 * j).factorial := by
  induction j with
  | zero => simp
  | succ n ih =>
    have e : 4 * (n + 1) = (4 * n) + 4 := by ring
    rw [prod_range_succ, ih, e, factorial_add_four]
theorem prod_cosOdd_denom (j : ℕ) :
    (∏ k ∈ range j, ((4 * k + 3) * (4 * k + 4) * (4 * k + 5) * (4 * k + 6))) * 2 =
      (4 * j + 2).factorial := by
  induction j with
  | zero => rfl
  | succ n ih =>
    have e : 4 * (n + 1) + 2 = (4 * n + 2) + 4 := by ring
    rw [prod_range_succ, e, factorial_add_four, ← ih]
    ring
theorem cosEven_fold_term (u v i : ℕ) (hv : v ≠ 0) :
    ∏ k ∈ Finset.Ico 0 (i + 1), ((cosEvenP u k : ℚ) / (cosEvenQ v k))
      = (u : ℚ) ^ (4 * (i + 1)) / ((v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1)).factorial) := by
  rw [← Finset.range_eq_Ico]
  simp only [cosEvenP, cosEvenQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  have hden : (∏ k ∈ Finset.range (i + 1),
      ((v ^ 4 * ((4 * k + 1) * (4 * k + 2) * (4 * k + 3) * (4 * k + 4)) : ℕ) : ℚ))
      = (v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1)).factorial := by
    have keyN : ∏ k ∈ Finset.range (i + 1),
        (v ^ 4 * ((4 * k + 1) * (4 * k + 2) * (4 * k + 3) * (4 * k + 4)))
        = v ^ (4 * (i + 1)) * (4 * (i + 1)).factorial := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul,
        prod_cosEven_denom]
    exact_mod_cast keyN
  rw [hden]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hf : ((4 * (i + 1)).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  push_cast
  rw [← pow_mul]
theorem cosEven_value (u v M T Q P : ℕ) (hv : v ≠ 0) (hM : 1 ≤ M)
    (h : (T, Q, P) = binarySplit (cosEvenP u) (cosEvenQ v) 0 (M - 1)) :
    (((Q + T : ℕ) : ℚ) / Q)
      = ∑ j ∈ Finset.range M, (u : ℚ) ^ (4 * j) / ((v : ℚ) ^ (4 * j) * (4 * j).factorial) := by
  have hqne : ∀ i, cosEvenQ v i ≠ 0 := by
    intro i; simp only [cosEvenQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
    exact Nat.mul_ne_zero (pow_ne_zero 4 hv) (by positivity)
  have hQ0 : Q ≠ 0 := by
    have hb := binarySplit_nonzero (p := cosEvenP u) (q := cosEvenQ v) (m := 0) (n := M - 1) hqne
    rw [← h] at hb
    simpa using hb
  have hspec :=
      (binarySplit_spec (p := cosEvenP u) (q := cosEvenQ v) (m := 0) (n := M - 1) hqne h).2
  rw [Finset.sum_congr rfl (fun i _ => cosEven_fold_term u v i hv)] at hspec
  rw [← Finset.range_eq_Ico] at hspec
  have hNeq : M = M - 1 + 1 := by omega
  rw [hNeq, Finset.sum_range_succ', hspec]
  have hQ0' : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0
  simp only [Nat.mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
  push_cast
  field_simp
  ring
theorem cosOdd_fold_term (u v i : ℕ) (hv : v ≠ 0) :
    ∏ k ∈ Finset.Ico 0 (i + 1), ((cosOddP u k : ℚ) / (cosOddQ v k))
      = 2 * (u : ℚ) ^ (4 * (i + 1)) / ((v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 2).factorial) := by
  rw [← Finset.range_eq_Ico]
  simp only [cosOddP, cosOddQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  have hden : (∏ k ∈ Finset.range (i + 1),
      ((v ^ 4 * ((4 * k + 3) * (4 * k + 4) * (4 * k + 5) * (4 * k + 6)) : ℕ) : ℚ))
      = (v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 2).factorial / 2 := by
    have keyN : (∏ k ∈ Finset.range (i + 1),
        (v ^ 4 * ((4 * k + 3) * (4 * k + 4) * (4 * k + 5) * (4 * k + 6)))) * 2
        = v ^ (4 * (i + 1)) * (4 * (i + 1) + 2).factorial := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul, mul_assoc,
        prod_cosOdd_denom]
    have keyQ : (∏ k ∈ Finset.range (i + 1),
        ((v ^ 4 * ((4 * k + 3) * (4 * k + 4) * (4 * k + 5) * (4 * k + 6)) : ℕ) : ℚ)) * 2
        = (v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 2).factorial := by exact_mod_cast keyN
    rwa [eq_div_iff (by norm_num : (2 : ℚ) ≠ 0)]
  rw [hden]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hf : ((4 * (i + 1) + 2).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  push_cast
  rw [← pow_mul]
theorem cosOdd_value (u v M T Q P : ℕ) (hv : v ≠ 0) (hM : 1 ≤ M)
    (h : (T, Q, P) = binarySplit (cosOddP u) (cosOddQ v) 0 (M - 1)) :
    ((u : ℚ) ^ 2 * (Q + T) / (2 * v ^ 2 * Q))
      = ∑ j ∈ Finset.range M,
          (u : ℚ) ^ (4 * j + 2) / ((v : ℚ) ^ (4 * j + 2) * (4 * j + 2).factorial) := by
  have hqne : ∀ i, cosOddQ v i ≠ 0 := by
    intro i; simp only [cosOddQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
    exact Nat.mul_ne_zero (pow_ne_zero 4 hv) (by positivity)
  have hQ0 : Q ≠ 0 := by
    have hb := binarySplit_nonzero (p := cosOddP u) (q := cosOddQ v) (m := 0) (n := M - 1) hqne
    rw [← h] at hb
    simpa using hb
  have hspec := (binarySplit_spec (p := cosOddP u) (q := cosOddQ v) (m := 0) (n := M - 1) hqne h).2
  rw [Finset.sum_congr rfl (fun i _ => cosOdd_fold_term u v i hv)] at hspec
  rw [← Finset.range_eq_Ico] at hspec
  have hNeq : M = M - 1 + 1 := by omega
  rw [hNeq, Finset.sum_range_succ']
  have hterm : ∀ i ∈ Finset.range (M - 1),
      (u : ℚ) ^ (4 * (i + 1) + 2) / ((v : ℚ) ^ (4 * (i + 1) + 2) * (4 * (i + 1) + 2).factorial)
        = (u : ℚ) ^ 2 / (2 * v ^ 2) *
          (2 * (u : ℚ) ^ (4 * (i + 1))
                / ((v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 2).factorial)) := by
    intro i _
    rw [pow_add (u : ℚ) (4 * (i + 1)) 2, pow_add (v : ℚ) (4 * (i + 1)) 2]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hspec]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hQ0' : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0
  simp only [Nat.mul_zero, Nat.zero_add, Nat.factorial_two]
  push_cast
  field_simp
  ring
theorem cos_dyadic_bound (u v M Mm Q D Te Qe Pe To Qo Po : ℕ) (neg : Bool) (cn : ℕ)
    (hu : u.blt (((Nat.mul 2 (Nat.mul 2 M)).succ).mul v))
    (hu2 : (Nat.mul 2 (u.pow 2)).ble ((((Nat.mul 2 (Nat.mul 2 M)).succ).pow 2).mul (v.pow 2)))
    (hQe : Nat.ble 1 Qe) (hQo : Nat.ble 1 Qo) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v) (hM :
          Nat.ble 1 M)
    (hMm : (Mm.succ).beq M)
    (heven : binarySplit (cosEvenP u) (cosEvenQ v) (nat_lit 0) Mm = (Te, Qe, Pe))
    (hodd : binarySplit (cosOddP u) (cosOddQ v) (nat_lit 0) Mm = (To, Qo, Po))
    (htail : ((Nat.mul 2 (u.pow (Nat.mul 2 (Nat.mul 2 M)))).mul (Nat.mul 2 D)).ble
      (Qe.mul (cosEvenQ v Mm)))
    (hr1 : (((numPos neg cn).mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo))).add
        ((((u.pow 2).mul (Qo.add To)).mul Qe).mul Q)).ble
      ((((Qe.add Te).mul ((Nat.mul 2 (v.pow 2)).mul Qo)).mul Q).add
        ((numNeg neg cn).mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo)))) = true)
    (hr2 : ((((Qe.add Te).mul ((Nat.mul 2 (v.pow 2)).mul Qo)).mul Q).add
        ((numNeg neg cn).mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo)))).blt
      ((((numPos neg cn).succ).mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo))).add
        ((((u.pow 2).mul (Qo.add To)).mul Qe).mul Q)) = true)
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.cos ((u : ℝ) / v)) neg cn Q 1 D := by
  have hMm' : Mm = M - 1 := by
    have h : Mm + 1 = M := Nat.eq_of_beq_eq_true hMm
    omega
  subst hMm'
  have hMpos0 : 1 ≤ M := Nat.le_of_ble_eq_true hM
  have hbridge : Qe * cosEvenQ v (M - 1) = v ^ (2 * (2 * M)) * (2 * (2 * M)).factorial := by
    have hQeprod : Qe = ∏ k ∈ Finset.range (M - 1), cosEvenQ v k := by
      have h := (binarySplit_PQ (p := cosEvenP u) (q := cosEvenQ v) (m := 0) (n := M - 1)).2
      rw [heven, ← Finset.range_eq_Ico] at h; exact h
    rw [hQeprod, ← Finset.prod_range_succ, show M - 1 + 1 = M from by omega]
    simp only [cosEvenQ, Nat.pow_eq, Nat.mul_eq, Nat.add_eq]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul,
      prod_cosEven_denom, show 4 * M = 2 * (2 * M) from by ring]
  set mp := numPos neg cn with hmp_def
  set mn := numNeg neg cn with hmn_def
  have hvN : 0 < v := pos_of_ble hv
  have hQoN : 0 < Qo := pos_of_ble hQo
  have hDN : 0 < D := pos_of_ble hD
  have hvne : v ≠ 0 := hvN.ne'
  have hMpos : 1 ≤ M := Nat.le_of_ble_eq_true hM
  have hvalE := cosEven_value u v M Te Qe Pe hvne hMpos heven.symm
  have hvalO := cosOdd_value u v M To Qo Po hvne hMpos hodd.symm
  have hcombine : ((Qe + Te : ℕ) : ℚ) / Qe - (u : ℚ) ^ 2 * (Qo + To) / (2 * v ^ 2 * Qo)
      = ∑ i ∈ Finset.range (2 * M), (-1) ^ i * ((u : ℚ) / v) ^ (2 * i) / (2 * i).factorial := by
    rw [hvalE, hvalO, sum_range_two_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have s1 : ((-1 : ℚ)) ^ (2 * j) = 1 := by rw [pow_mul]; norm_num
    have s2 : ((-1 : ℚ)) ^ (2 * j + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    have e1 : 2 * (2 * j) = 4 * j := by ring
    have e2 : 2 * (2 * j + 1) = 4 * j + 2 := by ring
    rw [e1, e2, s1, s2, div_pow, div_pow]
    ring
  set m : ℤ := (mp : ℤ) - (mn : ℤ) with hm
  rw [Real.IsNear, Nat.cast_one]
  have hvform : sfrac neg cn Q = (m : ℝ) / Q := by
    rw [sfrac_eq_parts neg cn Q, ← hmp_def, ← hmn_def, hm]
    push_cast
    ring
  rw [hvform]
  simp only [Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq,
    Nat.pow_eq] at hu hu2 htail hQ hr1 hr2
  push_cast at hcombine
  set Do := 2 * v ^ 2 * Qo with hDo_def
  set Ne := Qe + Te with hNe_def
  set No := u ^ 2 * (Qo + To) with hNo_def
  have hDoR : (Do : ℝ) = 2 * (v : ℝ) ^ 2 * Qo := by rw [hDo_def]; push_cast; ring
  have hr1z : m * ((Qe : ℤ) * Do) ≤ ((Ne : ℤ) * Do - (No : ℤ) * Qe) * Q := by
    have h : (mp : ℤ) * ((Qe : ℤ) * Do) + (No : ℤ) * Qe * Q
        ≤ (Ne : ℤ) * Do * Q + (mn : ℤ) * ((Qe : ℤ) * Do) := by exact_mod_cast hr1
    have e1 : m * ((Qe : ℤ) * Do) = (mp : ℤ) * ((Qe : ℤ) * Do) - (mn : ℤ) * ((Qe : ℤ) * Do) := by
      rw [hm]; ring
    have e2 : ((Ne : ℤ) * Do - (No : ℤ) * Qe) * Q = (Ne : ℤ) * Do * Q - (No : ℤ) * Qe * Q := by ring
    rw [e1, e2]; linarith
  have hr2z : ((Ne : ℤ) * Do - (No : ℤ) * Qe) * Q < (m + 1) * ((Qe : ℤ) * Do) := by
    have h : (Ne : ℤ) * Do * Q + (mn : ℤ) * ((Qe : ℤ) * Do)
        < (mp + 1) * ((Qe : ℤ) * Do) + (No : ℤ) * Qe * Q := by exact_mod_cast hr2
    have e1 : (m + 1) * ((Qe : ℤ) * Do)
        = (mp + 1) * ((Qe : ℤ) * Do) - (mn : ℤ) * ((Qe : ℤ) * Do) := by rw [hm]; ring
    have e2 : ((Ne : ℤ) * Do - (No : ℤ) * Qe) * Q = (Ne : ℤ) * Do * Q - (No : ℤ) * Qe * Q := by ring
    rw [e1, e2]; linarith
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  have hvr : (0 : ℝ) < v := pos_real_of_ble hv
  have hQ0 : 0 < Q := by omega
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hQe0 : (0 : ℝ) < Qe := pos_real_of_ble hQe
  have hDo0 : (0 : ℝ) < Do := by rw [hDoR]; positivity
  have hvalR : ((Ne : ℝ) / Qe - (No : ℝ) / Do)
      = ∑ i ∈ Finset.range (2 * M), (-1) ^ i * ((u : ℝ) / v) ^ (2 * i) / (2 * i).factorial := by
    have hcast := congrArg (fun r : ℚ => (r : ℝ)) hcombine
    push_cast at hcast
    rw [hNe_def, hDo_def, hNo_def]
    push_cast
    convert hcast using 2
  have hxnn : (0 : ℝ) ≤ (u : ℝ) / v := by positivity
  have hxlt : (u : ℝ) / v < 2 * ((2 * M : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hvr]; exact_mod_cast hu
  have hcos := cos_sub_sum_le ((u : ℝ) / v) (2 * M) hxnn hxlt
  rw [← hvalR] at hcos
  have hcos' : |Real.cos ((u : ℝ) / v) - ((Ne : ℝ) / Qe - (No : ℝ) / Do)| ≤ 1 / (2 * D) := by
    refine hcos.trans ?_
    have hA2 : ((u : ℝ) / v) ^ (2 * (2 * M)) / (2 * (2 * M)).factorial * 2 ≤ 1 / (2 * D) := by
      rw [div_pow, div_div, div_mul_eq_mul_div,
        div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      have e : (u : ℝ) ^ (2 * (2 * M)) * 2 * (2 * D)
          = 2 * (u : ℝ) ^ (2 * (2 * M)) * (2 * D) := by ring
      rw [e]
      have htR : 2 * (u : ℝ) ^ (2 * (2 * M)) * (2 * D) ≤ (Qe : ℝ) * (cosEvenQ v (M - 1) : ℝ) := by
        exact_mod_cast htail
      have hbR : (Qe : ℝ) * (cosEvenQ v (M - 1) : ℝ)
          = (v : ℝ) ^ (2 * (2 * M)) * ((2 * (2 * M)).factorial : ℝ) := by exact_mod_cast hbridge
      exact le_of_le_of_eq htR hbR
    refine le_trans ?_ hA2
    gcongr
    exact geo_factor_le _ _ (by positivity) (by
      rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
      exact_mod_cast hu2)
  have hr1' : (m : ℝ) * ((Qe : ℝ) * Do) ≤ ((Ne : ℝ) * Do - No * Qe) * Q := by exact_mod_cast hr1z
  have hr2' : ((Ne : ℝ) * Do - No * Qe) * Q < ((m : ℝ) + 1) * ((Qe : ℝ) * Do) := by
    exact_mod_cast hr2z
  exact sub_grid_round (Real.cos ((u : ℝ) / v)) (Ne : ℝ) (Qe : ℝ) (No : ℝ) (Do : ℝ) m Q D
    hcos' hr1' hr2' hQe0 hDo0 hDr hQr hQ
theorem cos_dyadic_bound_f (u v M Mm Q D Te Qe Pe To Qo Po cn : ℕ)
    (hu : u.blt (((Nat.mul 2 (Nat.mul 2 M)).succ).mul v))
    (hu2 : (Nat.mul 2 (u.pow 2)).ble ((((Nat.mul 2 (Nat.mul 2 M)).succ).pow 2).mul (v.pow 2)))
    (hQe : Nat.ble 1 Qe) (hQo : Nat.ble 1 Qo) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v) (hM :
          Nat.ble 1 M)
    (hMm : (Mm.succ).beq M)
    (heven : binarySplit (cosEvenP u) (cosEvenQ v) (nat_lit 0) Mm = (Te, Qe, Pe))
    (hodd : binarySplit (cosOddP u) (cosOddQ v) (nat_lit 0) Mm = (To, Qo, Po))
    (htail : ((Nat.mul 2 (u.pow (Nat.mul 2 (Nat.mul 2 M)))).mul (Nat.mul 2 D)).ble
      (Qe.mul (cosEvenQ v Mm)))
    (hr1 : ((cn.mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo))).add
        ((((u.pow 2).mul (Qo.add To)).mul Qe).mul Q)).ble
      (((Qe.add Te).mul ((Nat.mul 2 (v.pow 2)).mul Qo)).mul Q) = true)
    (hr2 : ((((Qe.add Te).mul ((Nat.mul 2 (v.pow 2)).mul Qo)).mul Q)).blt
      (((cn.succ).mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo))).add
        ((((u.pow 2).mul (Qo.add To)).mul Qe).mul Q)) = true)
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.cos ((u : ℝ) / v)) false cn Q 1 D := by
  refine cos_dyadic_bound u v M Mm Q D Te Qe Pe To Qo Po false cn hu hu2 hQe hQo hD hv hM hMm
    heven hodd htail ?_ ?_ hQ
  · simp only [numPos, numNeg, if_neg Bool.false_ne_true, Nat.ble_eq, Nat.add_eq,
      Nat.mul_eq, Nat.pow_eq, Nat.zero_mul, Nat.add_zero] at hr1 ⊢
    omega
  · simp only [numPos, numNeg, if_neg Bool.false_ne_true, Nat.blt_eq, Nat.add_eq,
      Nat.mul_eq, Nat.pow_eq, Nat.zero_mul, Nat.add_zero] at hr2 ⊢
    omega
theorem cos_dyadic_bound_t (u v M Mm Q D Te Qe Pe To Qo Po cn : ℕ)
    (hu : u.blt (((Nat.mul 2 (Nat.mul 2 M)).succ).mul v))
    (hu2 : (Nat.mul 2 (u.pow 2)).ble ((((Nat.mul 2 (Nat.mul 2 M)).succ).pow 2).mul (v.pow 2)))
    (hQe : Nat.ble 1 Qe) (hQo : Nat.ble 1 Qo) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v) (hM :
          Nat.ble 1 M)
    (hMm : (Mm.succ).beq M)
    (heven : binarySplit (cosEvenP u) (cosEvenQ v) (nat_lit 0) Mm = (Te, Qe, Pe))
    (hodd : binarySplit (cosOddP u) (cosOddQ v) (nat_lit 0) Mm = (To, Qo, Po))
    (htail : ((Nat.mul 2 (u.pow (Nat.mul 2 (Nat.mul 2 M)))).mul (Nat.mul 2 D)).ble
      (Qe.mul (cosEvenQ v Mm)))
    (hr1 : ((((u.pow 2).mul (Qo.add To)).mul Qe).mul Q).ble
      ((((Qe.add Te).mul ((Nat.mul 2 (v.pow 2)).mul Qo)).mul Q).add
        (cn.mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo)))) = true)
    (hr2 : ((((Qe.add Te).mul ((Nat.mul 2 (v.pow 2)).mul Qo)).mul Q).add
        (cn.mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo)))).blt
      ((Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo)).add
        ((((u.pow 2).mul (Qo.add To)).mul Qe).mul Q)) = true)
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.cos ((u : ℝ) / v)) true cn Q 1 D := by
  refine cos_dyadic_bound u v M Mm Q D Te Qe Pe To Qo Po true cn hu hu2 hQe hQo hD hv hM hMm
    heven hodd htail ?_ ?_ hQ
  · have hp : numPos true cn = 0 := rfl
    have hn : numNeg true cn = cn := rfl
    simp only [hp, hn, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.pow_eq,
      Nat.zero_mul, Nat.zero_add] at hr1 ⊢
    omega
  · have hp : numPos true cn = 0 := rfl
    have hn : numNeg true cn = cn := rfl
    simp only [hp, hn, Nat.blt_eq, Nat.add_eq, Nat.mul_eq, Nat.pow_eq, Nat.one_mul] at hr2 ⊢
    omega
theorem cos_neg_of_bound (u v : ℕ) (neg : Bool) (cn cd rn rd : ℕ)
    (h : Real.IsNear (Real.cos ((u : ℝ) / v)) neg cn cd rn rd) :
    Real.IsNear (Real.cos ((-(u : ℝ)) / v)) neg cn cd rn rd := by
  rw [Real.IsNear, neg_div, Real.cos_neg]; exact h
end BSN
end
end CertificatePort161


