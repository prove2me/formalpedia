-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankArgDimLeA15
-- name    : IntMul_Kappa_R8_Data_BitOppbankArgDimLeA15
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T09:42:55.130206+00:00
-- url     : https://prove2.me/theorems/efa0c674-1c36-4af0-9e32-f65f95bc42c9
-- title:
--   argRel dim-inequality certificates on published Pnd, pack A15, nodes 37500–39999
-- statement:
--   # Dimension inequality certificates (published Pnd), pack $A_{15}$
--
--   Range consolidators for $n\in[37500,40000)$:
--   $$\dim F(\mathrm{arg}_0 n)\le \dim F(n)\qquad\text{and}\qquad\dim F(\mathrm{arg}_1 n)\le \dim F(n).$$
--
--   Here $\mathrm{arg}_0 n=\mathrm{argF}(n)\mathbin{\&}65535$ and $\mathrm{arg}_1 n=\mathrm{argF}(n)\gg 16$. Proved on the published (non-Fix) `argF` / `dimF` by Lean `decide` windows of 50 (last window of pack $A_{24}$ is size 28 at offset 62450), then `dim0_range` / `dim1_range`. Used for `argRel_dim_le` on published `argRel`.
--
--   Formalization note. The pack lives in namespace `IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA15` and imports only the published Pnd and SupG data.
-- source:
--   R8 BitOppbank FormalOK published Pnd (non-Fix) ArgDimLeA

-- ArgDimLeA15: dim inequality certificates on published Pnd only, nodes [37500, 40000)
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 1000000
set_option exponentiation.threshold 2000
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG
namespace IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA15
def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16
theorem d0_w0 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 37500)) ≤ dimF (n.val + 37500) := by decide
theorem d1_w0 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 37500)) ≤ dimF (n.val + 37500) := by decide
theorem d0_w1 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 37550)) ≤ dimF (n.val + 37550) := by decide
theorem d1_w1 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 37550)) ≤ dimF (n.val + 37550) := by decide
theorem d0_w2 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 37600)) ≤ dimF (n.val + 37600) := by decide
theorem d1_w2 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 37600)) ≤ dimF (n.val + 37600) := by decide
theorem d0_w3 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 37650)) ≤ dimF (n.val + 37650) := by decide
theorem d1_w3 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 37650)) ≤ dimF (n.val + 37650) := by decide
theorem d0_w4 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 37700)) ≤ dimF (n.val + 37700) := by decide
theorem d1_w4 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 37700)) ≤ dimF (n.val + 37700) := by decide
theorem d0_w5 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 37750)) ≤ dimF (n.val + 37750) := by decide
theorem d1_w5 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 37750)) ≤ dimF (n.val + 37750) := by decide
theorem d0_w6 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 37800)) ≤ dimF (n.val + 37800) := by decide
theorem d1_w6 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 37800)) ≤ dimF (n.val + 37800) := by decide
theorem d0_w7 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 37850)) ≤ dimF (n.val + 37850) := by decide
theorem d1_w7 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 37850)) ≤ dimF (n.val + 37850) := by decide
theorem d0_w8 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 37900)) ≤ dimF (n.val + 37900) := by decide
theorem d1_w8 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 37900)) ≤ dimF (n.val + 37900) := by decide
theorem d0_w9 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 37950)) ≤ dimF (n.val + 37950) := by decide
theorem d1_w9 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 37950)) ≤ dimF (n.val + 37950) := by decide
theorem d0_w10 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 38000)) ≤ dimF (n.val + 38000) := by decide
theorem d1_w10 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 38000)) ≤ dimF (n.val + 38000) := by decide
theorem d0_w11 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 38050)) ≤ dimF (n.val + 38050) := by decide
theorem d1_w11 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 38050)) ≤ dimF (n.val + 38050) := by decide
theorem d0_w12 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 38100)) ≤ dimF (n.val + 38100) := by decide
theorem d1_w12 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 38100)) ≤ dimF (n.val + 38100) := by decide
theorem d0_w13 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 38150)) ≤ dimF (n.val + 38150) := by decide
theorem d1_w13 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 38150)) ≤ dimF (n.val + 38150) := by decide
theorem d0_w14 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 38200)) ≤ dimF (n.val + 38200) := by decide
theorem d1_w14 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 38200)) ≤ dimF (n.val + 38200) := by decide
theorem d0_w15 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 38250)) ≤ dimF (n.val + 38250) := by decide
theorem d1_w15 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 38250)) ≤ dimF (n.val + 38250) := by decide
theorem d0_w16 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 38300)) ≤ dimF (n.val + 38300) := by decide
theorem d1_w16 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 38300)) ≤ dimF (n.val + 38300) := by decide
theorem d0_w17 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 38350)) ≤ dimF (n.val + 38350) := by decide
theorem d1_w17 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 38350)) ≤ dimF (n.val + 38350) := by decide
theorem d0_w18 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 38400)) ≤ dimF (n.val + 38400) := by decide
theorem d1_w18 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 38400)) ≤ dimF (n.val + 38400) := by decide
theorem d0_w19 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 38450)) ≤ dimF (n.val + 38450) := by decide
theorem d1_w19 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 38450)) ≤ dimF (n.val + 38450) := by decide
theorem d0_w20 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 38500)) ≤ dimF (n.val + 38500) := by decide
theorem d1_w20 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 38500)) ≤ dimF (n.val + 38500) := by decide
theorem d0_w21 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 38550)) ≤ dimF (n.val + 38550) := by decide
theorem d1_w21 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 38550)) ≤ dimF (n.val + 38550) := by decide
theorem d0_w22 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 38600)) ≤ dimF (n.val + 38600) := by decide
theorem d1_w22 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 38600)) ≤ dimF (n.val + 38600) := by decide
theorem d0_w23 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 38650)) ≤ dimF (n.val + 38650) := by decide
theorem d1_w23 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 38650)) ≤ dimF (n.val + 38650) := by decide
theorem d0_w24 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 38700)) ≤ dimF (n.val + 38700) := by decide
theorem d1_w24 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 38700)) ≤ dimF (n.val + 38700) := by decide
theorem d0_w25 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 38750)) ≤ dimF (n.val + 38750) := by decide
theorem d1_w25 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 38750)) ≤ dimF (n.val + 38750) := by decide
theorem d0_w26 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 38800)) ≤ dimF (n.val + 38800) := by decide
theorem d1_w26 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 38800)) ≤ dimF (n.val + 38800) := by decide
theorem d0_w27 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 38850)) ≤ dimF (n.val + 38850) := by decide
theorem d1_w27 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 38850)) ≤ dimF (n.val + 38850) := by decide
theorem d0_w28 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 38900)) ≤ dimF (n.val + 38900) := by decide
theorem d1_w28 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 38900)) ≤ dimF (n.val + 38900) := by decide
theorem d0_w29 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 38950)) ≤ dimF (n.val + 38950) := by decide
theorem d1_w29 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 38950)) ≤ dimF (n.val + 38950) := by decide
theorem d0_w30 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 39000)) ≤ dimF (n.val + 39000) := by decide
theorem d1_w30 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 39000)) ≤ dimF (n.val + 39000) := by decide
theorem d0_w31 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 39050)) ≤ dimF (n.val + 39050) := by decide
theorem d1_w31 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 39050)) ≤ dimF (n.val + 39050) := by decide
theorem d0_w32 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 39100)) ≤ dimF (n.val + 39100) := by decide
theorem d1_w32 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 39100)) ≤ dimF (n.val + 39100) := by decide
theorem d0_w33 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 39150)) ≤ dimF (n.val + 39150) := by decide
theorem d1_w33 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 39150)) ≤ dimF (n.val + 39150) := by decide
theorem d0_w34 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 39200)) ≤ dimF (n.val + 39200) := by decide
theorem d1_w34 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 39200)) ≤ dimF (n.val + 39200) := by decide
theorem d0_w35 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 39250)) ≤ dimF (n.val + 39250) := by decide
theorem d1_w35 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 39250)) ≤ dimF (n.val + 39250) := by decide
theorem d0_w36 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 39300)) ≤ dimF (n.val + 39300) := by decide
theorem d1_w36 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 39300)) ≤ dimF (n.val + 39300) := by decide
theorem d0_w37 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 39350)) ≤ dimF (n.val + 39350) := by decide
theorem d1_w37 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 39350)) ≤ dimF (n.val + 39350) := by decide
theorem d0_w38 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 39400)) ≤ dimF (n.val + 39400) := by decide
theorem d1_w38 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 39400)) ≤ dimF (n.val + 39400) := by decide
theorem d0_w39 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 39450)) ≤ dimF (n.val + 39450) := by decide
theorem d1_w39 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 39450)) ≤ dimF (n.val + 39450) := by decide
theorem d0_w40 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 39500)) ≤ dimF (n.val + 39500) := by decide
theorem d1_w40 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 39500)) ≤ dimF (n.val + 39500) := by decide
theorem d0_w41 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 39550)) ≤ dimF (n.val + 39550) := by decide
theorem d1_w41 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 39550)) ≤ dimF (n.val + 39550) := by decide
theorem d0_w42 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 39600)) ≤ dimF (n.val + 39600) := by decide
theorem d1_w42 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 39600)) ≤ dimF (n.val + 39600) := by decide
theorem d0_w43 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 39650)) ≤ dimF (n.val + 39650) := by decide
theorem d1_w43 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 39650)) ≤ dimF (n.val + 39650) := by decide
theorem d0_w44 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 39700)) ≤ dimF (n.val + 39700) := by decide
theorem d1_w44 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 39700)) ≤ dimF (n.val + 39700) := by decide
theorem d0_w45 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 39750)) ≤ dimF (n.val + 39750) := by decide
theorem d1_w45 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 39750)) ≤ dimF (n.val + 39750) := by decide
theorem d0_w46 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 39800)) ≤ dimF (n.val + 39800) := by decide
theorem d1_w46 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 39800)) ≤ dimF (n.val + 39800) := by decide
theorem d0_w47 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 39850)) ≤ dimF (n.val + 39850) := by decide
theorem d1_w47 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 39850)) ≤ dimF (n.val + 39850) := by decide
theorem d0_w48 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 39900)) ≤ dimF (n.val + 39900) := by decide
theorem d1_w48 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 39900)) ≤ dimF (n.val + 39900) := by decide
theorem d0_w49 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 39950)) ≤ dimF (n.val + 39950) := by decide
theorem d1_w49 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 39950)) ≤ dimF (n.val + 39950) := by decide
theorem dim0_range (n : ℕ) (hn0 : 37500 ≤ n) (hn1 : n < 40000) :
    dimF (arg0 n) ≤ dimF n := by
  by_cases h0 : n < 37550
  · have hoff : 37500 ≤ n := by omega
    have hnfin : n - 37500 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using d0_w0 ⟨n - 37500, hnfin⟩
  ·
    by_cases h1 : n < 37600
    · have hoff : 37550 ≤ n := by omega
      have hnfin : n - 37550 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using d0_w1 ⟨n - 37550, hnfin⟩
    ·
      by_cases h2 : n < 37650
      · have hoff : 37600 ≤ n := by omega
        have hnfin : n - 37600 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using d0_w2 ⟨n - 37600, hnfin⟩
      ·
        by_cases h3 : n < 37700
        · have hoff : 37650 ≤ n := by omega
          have hnfin : n - 37650 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using d0_w3 ⟨n - 37650, hnfin⟩
        ·
          by_cases h4 : n < 37750
          · have hoff : 37700 ≤ n := by omega
            have hnfin : n - 37700 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using d0_w4 ⟨n - 37700, hnfin⟩
          ·
            by_cases h5 : n < 37800
            · have hoff : 37750 ≤ n := by omega
              have hnfin : n - 37750 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using d0_w5 ⟨n - 37750, hnfin⟩
            ·
              by_cases h6 : n < 37850
              · have hoff : 37800 ≤ n := by omega
                have hnfin : n - 37800 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using d0_w6 ⟨n - 37800, hnfin⟩
              ·
                by_cases h7 : n < 37900
                · have hoff : 37850 ≤ n := by omega
                  have hnfin : n - 37850 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using d0_w7 ⟨n - 37850, hnfin⟩
                ·
                  by_cases h8 : n < 37950
                  · have hoff : 37900 ≤ n := by omega
                    have hnfin : n - 37900 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using d0_w8 ⟨n - 37900, hnfin⟩
                  ·
                    by_cases h9 : n < 38000
                    · have hoff : 37950 ≤ n := by omega
                      have hnfin : n - 37950 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using d0_w9 ⟨n - 37950, hnfin⟩
                    ·
                      by_cases h10 : n < 38050
                      · have hoff : 38000 ≤ n := by omega
                        have hnfin : n - 38000 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using d0_w10 ⟨n - 38000, hnfin⟩
                      ·
                        by_cases h11 : n < 38100
                        · have hoff : 38050 ≤ n := by omega
                          have hnfin : n - 38050 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using d0_w11 ⟨n - 38050, hnfin⟩
                        ·
                          by_cases h12 : n < 38150
                          · have hoff : 38100 ≤ n := by omega
                            have hnfin : n - 38100 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using d0_w12 ⟨n - 38100, hnfin⟩
                          ·
                            by_cases h13 : n < 38200
                            · have hoff : 38150 ≤ n := by omega
                              have hnfin : n - 38150 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using d0_w13 ⟨n - 38150, hnfin⟩
                            ·
                              by_cases h14 : n < 38250
                              · have hoff : 38200 ≤ n := by omega
                                have hnfin : n - 38200 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using d0_w14 ⟨n - 38200, hnfin⟩
                              ·
                                by_cases h15 : n < 38300
                                · have hoff : 38250 ≤ n := by omega
                                  have hnfin : n - 38250 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using d0_w15 ⟨n - 38250, hnfin⟩
                                ·
                                  by_cases h16 : n < 38350
                                  · have hoff : 38300 ≤ n := by omega
                                    have hnfin : n - 38300 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using d0_w16 ⟨n - 38300, hnfin⟩
                                  ·
                                    by_cases h17 : n < 38400
                                    · have hoff : 38350 ≤ n := by omega
                                      have hnfin : n - 38350 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using d0_w17 ⟨n - 38350, hnfin⟩
                                    ·
                                      by_cases h18 : n < 38450
                                      · have hoff : 38400 ≤ n := by omega
                                        have hnfin : n - 38400 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using d0_w18 ⟨n - 38400, hnfin⟩
                                      ·
                                        by_cases h19 : n < 38500
                                        · have hoff : 38450 ≤ n := by omega
                                          have hnfin : n - 38450 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using d0_w19 ⟨n - 38450, hnfin⟩
                                        ·
                                          by_cases h20 : n < 38550
                                          · have hoff : 38500 ≤ n := by omega
                                            have hnfin : n - 38500 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using d0_w20 ⟨n - 38500, hnfin⟩
                                          ·
                                            by_cases h21 : n < 38600
                                            · have hoff : 38550 ≤ n := by omega
                                              have hnfin : n - 38550 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using d0_w21 ⟨n - 38550, hnfin⟩
                                            ·
                                              by_cases h22 : n < 38650
                                              · have hoff : 38600 ≤ n := by omega
                                                have hnfin : n - 38600 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using d0_w22 ⟨n - 38600, hnfin⟩
                                              ·
                                                by_cases h23 : n < 38700
                                                · have hoff : 38650 ≤ n := by omega
                                                  have hnfin : n - 38650 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using d0_w23 ⟨n - 38650, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 38750
                                                  · have hoff : 38700 ≤ n := by omega
                                                    have hnfin : n - 38700 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using d0_w24 ⟨n - 38700, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 38800
                                                    · have hoff : 38750 ≤ n := by omega
                                                      have hnfin : n - 38750 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using d0_w25 ⟨n - 38750, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 38850
                                                      · have hoff : 38800 ≤ n := by omega
                                                        have hnfin : n - 38800 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using d0_w26 ⟨n - 38800, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 38900
                                                        · have hoff : 38850 ≤ n := by omega
                                                          have hnfin : n - 38850 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using d0_w27 ⟨n - 38850, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 38950
                                                          · have hoff : 38900 ≤ n := by omega
                                                            have hnfin : n - 38900 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using d0_w28 ⟨n - 38900, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 39000
                                                            · have hoff : 38950 ≤ n := by omega
                                                              have hnfin : n - 38950 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using d0_w29 ⟨n - 38950, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 39050
                                                              · have hoff : 39000 ≤ n := by omega
                                                                have hnfin : n - 39000 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using d0_w30 ⟨n - 39000, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 39100
                                                                · have hoff : 39050 ≤ n := by omega
                                                                  have hnfin : n - 39050 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using d0_w31 ⟨n - 39050, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 39150
                                                                  · have hoff : 39100 ≤ n := by omega
                                                                    have hnfin : n - 39100 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w32 ⟨n - 39100, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 39200
                                                                    · have hoff : 39150 ≤ n := by omega
                                                                      have hnfin : n - 39150 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using d0_w33 ⟨n - 39150, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 39250
                                                                      · have hoff : 39200 ≤ n := by omega
                                                                        have hnfin : n - 39200 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using d0_w34 ⟨n - 39200, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 39300
                                                                        · have hoff : 39250 ≤ n := by omega
                                                                          have hnfin : n - 39250 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using d0_w35 ⟨n - 39250, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 39350
                                                                          · have hoff : 39300 ≤ n := by omega
                                                                            have hnfin : n - 39300 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using d0_w36 ⟨n - 39300, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 39400
                                                                            · have hoff : 39350 ≤ n := by omega
                                                                              have hnfin : n - 39350 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using d0_w37 ⟨n - 39350, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 39450
                                                                              · have hoff : 39400 ≤ n := by omega
                                                                                have hnfin : n - 39400 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using d0_w38 ⟨n - 39400, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 39500
                                                                                · have hoff : 39450 ≤ n := by omega
                                                                                  have hnfin : n - 39450 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using d0_w39 ⟨n - 39450, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 39550
                                                                                  · have hoff : 39500 ≤ n := by omega
                                                                                    have hnfin : n - 39500 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w40 ⟨n - 39500, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 39600
                                                                                    · have hoff : 39550 ≤ n := by omega
                                                                                      have hnfin : n - 39550 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using d0_w41 ⟨n - 39550, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 39650
                                                                                      · have hoff : 39600 ≤ n := by omega
                                                                                        have hnfin : n - 39600 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using d0_w42 ⟨n - 39600, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 39700
                                                                                        · have hoff : 39650 ≤ n := by omega
                                                                                          have hnfin : n - 39650 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using d0_w43 ⟨n - 39650, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 39750
                                                                                          · have hoff : 39700 ≤ n := by omega
                                                                                            have hnfin : n - 39700 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using d0_w44 ⟨n - 39700, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 39800
                                                                                            · have hoff : 39750 ≤ n := by omega
                                                                                              have hnfin : n - 39750 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using d0_w45 ⟨n - 39750, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 39850
                                                                                              · have hoff : 39800 ≤ n := by omega
                                                                                                have hnfin : n - 39800 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using d0_w46 ⟨n - 39800, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 39900
                                                                                                · have hoff : 39850 ≤ n := by omega
                                                                                                  have hnfin : n - 39850 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using d0_w47 ⟨n - 39850, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 39950
                                                                                                  · have hoff : 39900 ≤ n := by omega
                                                                                                    have hnfin : n - 39900 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w48 ⟨n - 39900, hnfin⟩
                                                                                                  · have hoff : 39950 ≤ n := by omega
                                                                                                    have hnfin : n - 39950 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w49 ⟨n - 39950, hnfin⟩
theorem dim1_range (n : ℕ) (hn0 : 37500 ≤ n) (hn1 : n < 40000) :
    dimF (arg1 n) ≤ dimF n := by
  by_cases h0 : n < 37550
  · have hoff : 37500 ≤ n := by omega
    have hnfin : n - 37500 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using d1_w0 ⟨n - 37500, hnfin⟩
  ·
    by_cases h1 : n < 37600
    · have hoff : 37550 ≤ n := by omega
      have hnfin : n - 37550 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using d1_w1 ⟨n - 37550, hnfin⟩
    ·
      by_cases h2 : n < 37650
      · have hoff : 37600 ≤ n := by omega
        have hnfin : n - 37600 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using d1_w2 ⟨n - 37600, hnfin⟩
      ·
        by_cases h3 : n < 37700
        · have hoff : 37650 ≤ n := by omega
          have hnfin : n - 37650 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using d1_w3 ⟨n - 37650, hnfin⟩
        ·
          by_cases h4 : n < 37750
          · have hoff : 37700 ≤ n := by omega
            have hnfin : n - 37700 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using d1_w4 ⟨n - 37700, hnfin⟩
          ·
            by_cases h5 : n < 37800
            · have hoff : 37750 ≤ n := by omega
              have hnfin : n - 37750 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using d1_w5 ⟨n - 37750, hnfin⟩
            ·
              by_cases h6 : n < 37850
              · have hoff : 37800 ≤ n := by omega
                have hnfin : n - 37800 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using d1_w6 ⟨n - 37800, hnfin⟩
              ·
                by_cases h7 : n < 37900
                · have hoff : 37850 ≤ n := by omega
                  have hnfin : n - 37850 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using d1_w7 ⟨n - 37850, hnfin⟩
                ·
                  by_cases h8 : n < 37950
                  · have hoff : 37900 ≤ n := by omega
                    have hnfin : n - 37900 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using d1_w8 ⟨n - 37900, hnfin⟩
                  ·
                    by_cases h9 : n < 38000
                    · have hoff : 37950 ≤ n := by omega
                      have hnfin : n - 37950 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using d1_w9 ⟨n - 37950, hnfin⟩
                    ·
                      by_cases h10 : n < 38050
                      · have hoff : 38000 ≤ n := by omega
                        have hnfin : n - 38000 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using d1_w10 ⟨n - 38000, hnfin⟩
                      ·
                        by_cases h11 : n < 38100
                        · have hoff : 38050 ≤ n := by omega
                          have hnfin : n - 38050 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using d1_w11 ⟨n - 38050, hnfin⟩
                        ·
                          by_cases h12 : n < 38150
                          · have hoff : 38100 ≤ n := by omega
                            have hnfin : n - 38100 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using d1_w12 ⟨n - 38100, hnfin⟩
                          ·
                            by_cases h13 : n < 38200
                            · have hoff : 38150 ≤ n := by omega
                              have hnfin : n - 38150 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using d1_w13 ⟨n - 38150, hnfin⟩
                            ·
                              by_cases h14 : n < 38250
                              · have hoff : 38200 ≤ n := by omega
                                have hnfin : n - 38200 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using d1_w14 ⟨n - 38200, hnfin⟩
                              ·
                                by_cases h15 : n < 38300
                                · have hoff : 38250 ≤ n := by omega
                                  have hnfin : n - 38250 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using d1_w15 ⟨n - 38250, hnfin⟩
                                ·
                                  by_cases h16 : n < 38350
                                  · have hoff : 38300 ≤ n := by omega
                                    have hnfin : n - 38300 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using d1_w16 ⟨n - 38300, hnfin⟩
                                  ·
                                    by_cases h17 : n < 38400
                                    · have hoff : 38350 ≤ n := by omega
                                      have hnfin : n - 38350 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using d1_w17 ⟨n - 38350, hnfin⟩
                                    ·
                                      by_cases h18 : n < 38450
                                      · have hoff : 38400 ≤ n := by omega
                                        have hnfin : n - 38400 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using d1_w18 ⟨n - 38400, hnfin⟩
                                      ·
                                        by_cases h19 : n < 38500
                                        · have hoff : 38450 ≤ n := by omega
                                          have hnfin : n - 38450 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using d1_w19 ⟨n - 38450, hnfin⟩
                                        ·
                                          by_cases h20 : n < 38550
                                          · have hoff : 38500 ≤ n := by omega
                                            have hnfin : n - 38500 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using d1_w20 ⟨n - 38500, hnfin⟩
                                          ·
                                            by_cases h21 : n < 38600
                                            · have hoff : 38550 ≤ n := by omega
                                              have hnfin : n - 38550 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using d1_w21 ⟨n - 38550, hnfin⟩
                                            ·
                                              by_cases h22 : n < 38650
                                              · have hoff : 38600 ≤ n := by omega
                                                have hnfin : n - 38600 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using d1_w22 ⟨n - 38600, hnfin⟩
                                              ·
                                                by_cases h23 : n < 38700
                                                · have hoff : 38650 ≤ n := by omega
                                                  have hnfin : n - 38650 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using d1_w23 ⟨n - 38650, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 38750
                                                  · have hoff : 38700 ≤ n := by omega
                                                    have hnfin : n - 38700 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using d1_w24 ⟨n - 38700, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 38800
                                                    · have hoff : 38750 ≤ n := by omega
                                                      have hnfin : n - 38750 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using d1_w25 ⟨n - 38750, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 38850
                                                      · have hoff : 38800 ≤ n := by omega
                                                        have hnfin : n - 38800 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using d1_w26 ⟨n - 38800, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 38900
                                                        · have hoff : 38850 ≤ n := by omega
                                                          have hnfin : n - 38850 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using d1_w27 ⟨n - 38850, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 38950
                                                          · have hoff : 38900 ≤ n := by omega
                                                            have hnfin : n - 38900 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using d1_w28 ⟨n - 38900, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 39000
                                                            · have hoff : 38950 ≤ n := by omega
                                                              have hnfin : n - 38950 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using d1_w29 ⟨n - 38950, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 39050
                                                              · have hoff : 39000 ≤ n := by omega
                                                                have hnfin : n - 39000 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using d1_w30 ⟨n - 39000, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 39100
                                                                · have hoff : 39050 ≤ n := by omega
                                                                  have hnfin : n - 39050 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using d1_w31 ⟨n - 39050, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 39150
                                                                  · have hoff : 39100 ≤ n := by omega
                                                                    have hnfin : n - 39100 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w32 ⟨n - 39100, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 39200
                                                                    · have hoff : 39150 ≤ n := by omega
                                                                      have hnfin : n - 39150 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using d1_w33 ⟨n - 39150, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 39250
                                                                      · have hoff : 39200 ≤ n := by omega
                                                                        have hnfin : n - 39200 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using d1_w34 ⟨n - 39200, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 39300
                                                                        · have hoff : 39250 ≤ n := by omega
                                                                          have hnfin : n - 39250 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using d1_w35 ⟨n - 39250, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 39350
                                                                          · have hoff : 39300 ≤ n := by omega
                                                                            have hnfin : n - 39300 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using d1_w36 ⟨n - 39300, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 39400
                                                                            · have hoff : 39350 ≤ n := by omega
                                                                              have hnfin : n - 39350 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using d1_w37 ⟨n - 39350, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 39450
                                                                              · have hoff : 39400 ≤ n := by omega
                                                                                have hnfin : n - 39400 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using d1_w38 ⟨n - 39400, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 39500
                                                                                · have hoff : 39450 ≤ n := by omega
                                                                                  have hnfin : n - 39450 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using d1_w39 ⟨n - 39450, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 39550
                                                                                  · have hoff : 39500 ≤ n := by omega
                                                                                    have hnfin : n - 39500 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w40 ⟨n - 39500, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 39600
                                                                                    · have hoff : 39550 ≤ n := by omega
                                                                                      have hnfin : n - 39550 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using d1_w41 ⟨n - 39550, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 39650
                                                                                      · have hoff : 39600 ≤ n := by omega
                                                                                        have hnfin : n - 39600 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using d1_w42 ⟨n - 39600, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 39700
                                                                                        · have hoff : 39650 ≤ n := by omega
                                                                                          have hnfin : n - 39650 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using d1_w43 ⟨n - 39650, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 39750
                                                                                          · have hoff : 39700 ≤ n := by omega
                                                                                            have hnfin : n - 39700 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using d1_w44 ⟨n - 39700, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 39800
                                                                                            · have hoff : 39750 ≤ n := by omega
                                                                                              have hnfin : n - 39750 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using d1_w45 ⟨n - 39750, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 39850
                                                                                              · have hoff : 39800 ≤ n := by omega
                                                                                                have hnfin : n - 39800 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using d1_w46 ⟨n - 39800, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 39900
                                                                                                · have hoff : 39850 ≤ n := by omega
                                                                                                  have hnfin : n - 39850 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using d1_w47 ⟨n - 39850, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 39950
                                                                                                  · have hoff : 39900 ≤ n := by omega
                                                                                                    have hnfin : n - 39900 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w48 ⟨n - 39900, hnfin⟩
                                                                                                  · have hoff : 39950 ≤ n := by omega
                                                                                                    have hnfin : n - 39950 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w49 ⟨n - 39950, hnfin⟩
end IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA15


