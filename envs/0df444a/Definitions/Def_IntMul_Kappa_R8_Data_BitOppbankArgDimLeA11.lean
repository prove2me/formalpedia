-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankArgDimLeA11
-- name    : IntMul_Kappa_R8_Data_BitOppbankArgDimLeA11
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T09:43:41.162191+00:00
-- url     : https://prove2.me/theorems/1d5abe99-bd28-44b4-a42c-9fade09ea0f6
-- title:
--   argRel dim-inequality certificates on published Pnd, pack A11, nodes 27500–29999
-- statement:
--   # Dimension inequality certificates (published Pnd), pack $A_{11}$
--
--   Range consolidators for $n\in[27500,30000)$:
--   $$\dim F(\mathrm{arg}_0 n)\le \dim F(n)\qquad\text{and}\qquad\dim F(\mathrm{arg}_1 n)\le \dim F(n).$$
--
--   Here $\mathrm{arg}_0 n=\mathrm{argF}(n)\mathbin{\&}65535$ and $\mathrm{arg}_1 n=\mathrm{argF}(n)\gg 16$. Proved on the published (non-Fix) `argF` / `dimF` by Lean `decide` windows of 50 (last window of pack $A_{24}$ is size 28 at offset 62450), then `dim0_range` / `dim1_range`. Used for `argRel_dim_le` on published `argRel`.
--
--   Formalization note. The pack lives in namespace `IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA11` and imports only the published Pnd and SupG data.
-- source:
--   R8 BitOppbank FormalOK published Pnd (non-Fix) ArgDimLeA

-- ArgDimLeA11: dim inequality certificates on published Pnd only, nodes [27500, 30000)
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
namespace IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA11
def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16
theorem d0_w0 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 27500)) ≤ dimF (n.val + 27500) := by decide
theorem d1_w0 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 27500)) ≤ dimF (n.val + 27500) := by decide
theorem d0_w1 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 27550)) ≤ dimF (n.val + 27550) := by decide
theorem d1_w1 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 27550)) ≤ dimF (n.val + 27550) := by decide
theorem d0_w2 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 27600)) ≤ dimF (n.val + 27600) := by decide
theorem d1_w2 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 27600)) ≤ dimF (n.val + 27600) := by decide
theorem d0_w3 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 27650)) ≤ dimF (n.val + 27650) := by decide
theorem d1_w3 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 27650)) ≤ dimF (n.val + 27650) := by decide
theorem d0_w4 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 27700)) ≤ dimF (n.val + 27700) := by decide
theorem d1_w4 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 27700)) ≤ dimF (n.val + 27700) := by decide
theorem d0_w5 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 27750)) ≤ dimF (n.val + 27750) := by decide
theorem d1_w5 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 27750)) ≤ dimF (n.val + 27750) := by decide
theorem d0_w6 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 27800)) ≤ dimF (n.val + 27800) := by decide
theorem d1_w6 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 27800)) ≤ dimF (n.val + 27800) := by decide
theorem d0_w7 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 27850)) ≤ dimF (n.val + 27850) := by decide
theorem d1_w7 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 27850)) ≤ dimF (n.val + 27850) := by decide
theorem d0_w8 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 27900)) ≤ dimF (n.val + 27900) := by decide
theorem d1_w8 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 27900)) ≤ dimF (n.val + 27900) := by decide
theorem d0_w9 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 27950)) ≤ dimF (n.val + 27950) := by decide
theorem d1_w9 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 27950)) ≤ dimF (n.val + 27950) := by decide
theorem d0_w10 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 28000)) ≤ dimF (n.val + 28000) := by decide
theorem d1_w10 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 28000)) ≤ dimF (n.val + 28000) := by decide
theorem d0_w11 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 28050)) ≤ dimF (n.val + 28050) := by decide
theorem d1_w11 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 28050)) ≤ dimF (n.val + 28050) := by decide
theorem d0_w12 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 28100)) ≤ dimF (n.val + 28100) := by decide
theorem d1_w12 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 28100)) ≤ dimF (n.val + 28100) := by decide
theorem d0_w13 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 28150)) ≤ dimF (n.val + 28150) := by decide
theorem d1_w13 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 28150)) ≤ dimF (n.val + 28150) := by decide
theorem d0_w14 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 28200)) ≤ dimF (n.val + 28200) := by decide
theorem d1_w14 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 28200)) ≤ dimF (n.val + 28200) := by decide
theorem d0_w15 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 28250)) ≤ dimF (n.val + 28250) := by decide
theorem d1_w15 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 28250)) ≤ dimF (n.val + 28250) := by decide
theorem d0_w16 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 28300)) ≤ dimF (n.val + 28300) := by decide
theorem d1_w16 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 28300)) ≤ dimF (n.val + 28300) := by decide
theorem d0_w17 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 28350)) ≤ dimF (n.val + 28350) := by decide
theorem d1_w17 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 28350)) ≤ dimF (n.val + 28350) := by decide
theorem d0_w18 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 28400)) ≤ dimF (n.val + 28400) := by decide
theorem d1_w18 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 28400)) ≤ dimF (n.val + 28400) := by decide
theorem d0_w19 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 28450)) ≤ dimF (n.val + 28450) := by decide
theorem d1_w19 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 28450)) ≤ dimF (n.val + 28450) := by decide
theorem d0_w20 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 28500)) ≤ dimF (n.val + 28500) := by decide
theorem d1_w20 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 28500)) ≤ dimF (n.val + 28500) := by decide
theorem d0_w21 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 28550)) ≤ dimF (n.val + 28550) := by decide
theorem d1_w21 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 28550)) ≤ dimF (n.val + 28550) := by decide
theorem d0_w22 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 28600)) ≤ dimF (n.val + 28600) := by decide
theorem d1_w22 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 28600)) ≤ dimF (n.val + 28600) := by decide
theorem d0_w23 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 28650)) ≤ dimF (n.val + 28650) := by decide
theorem d1_w23 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 28650)) ≤ dimF (n.val + 28650) := by decide
theorem d0_w24 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 28700)) ≤ dimF (n.val + 28700) := by decide
theorem d1_w24 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 28700)) ≤ dimF (n.val + 28700) := by decide
theorem d0_w25 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 28750)) ≤ dimF (n.val + 28750) := by decide
theorem d1_w25 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 28750)) ≤ dimF (n.val + 28750) := by decide
theorem d0_w26 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 28800)) ≤ dimF (n.val + 28800) := by decide
theorem d1_w26 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 28800)) ≤ dimF (n.val + 28800) := by decide
theorem d0_w27 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 28850)) ≤ dimF (n.val + 28850) := by decide
theorem d1_w27 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 28850)) ≤ dimF (n.val + 28850) := by decide
theorem d0_w28 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 28900)) ≤ dimF (n.val + 28900) := by decide
theorem d1_w28 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 28900)) ≤ dimF (n.val + 28900) := by decide
theorem d0_w29 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 28950)) ≤ dimF (n.val + 28950) := by decide
theorem d1_w29 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 28950)) ≤ dimF (n.val + 28950) := by decide
theorem d0_w30 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 29000)) ≤ dimF (n.val + 29000) := by decide
theorem d1_w30 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 29000)) ≤ dimF (n.val + 29000) := by decide
theorem d0_w31 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 29050)) ≤ dimF (n.val + 29050) := by decide
theorem d1_w31 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 29050)) ≤ dimF (n.val + 29050) := by decide
theorem d0_w32 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 29100)) ≤ dimF (n.val + 29100) := by decide
theorem d1_w32 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 29100)) ≤ dimF (n.val + 29100) := by decide
theorem d0_w33 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 29150)) ≤ dimF (n.val + 29150) := by decide
theorem d1_w33 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 29150)) ≤ dimF (n.val + 29150) := by decide
theorem d0_w34 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 29200)) ≤ dimF (n.val + 29200) := by decide
theorem d1_w34 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 29200)) ≤ dimF (n.val + 29200) := by decide
theorem d0_w35 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 29250)) ≤ dimF (n.val + 29250) := by decide
theorem d1_w35 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 29250)) ≤ dimF (n.val + 29250) := by decide
theorem d0_w36 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 29300)) ≤ dimF (n.val + 29300) := by decide
theorem d1_w36 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 29300)) ≤ dimF (n.val + 29300) := by decide
theorem d0_w37 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 29350)) ≤ dimF (n.val + 29350) := by decide
theorem d1_w37 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 29350)) ≤ dimF (n.val + 29350) := by decide
theorem d0_w38 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 29400)) ≤ dimF (n.val + 29400) := by decide
theorem d1_w38 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 29400)) ≤ dimF (n.val + 29400) := by decide
theorem d0_w39 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 29450)) ≤ dimF (n.val + 29450) := by decide
theorem d1_w39 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 29450)) ≤ dimF (n.val + 29450) := by decide
theorem d0_w40 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 29500)) ≤ dimF (n.val + 29500) := by decide
theorem d1_w40 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 29500)) ≤ dimF (n.val + 29500) := by decide
theorem d0_w41 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 29550)) ≤ dimF (n.val + 29550) := by decide
theorem d1_w41 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 29550)) ≤ dimF (n.val + 29550) := by decide
theorem d0_w42 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 29600)) ≤ dimF (n.val + 29600) := by decide
theorem d1_w42 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 29600)) ≤ dimF (n.val + 29600) := by decide
theorem d0_w43 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 29650)) ≤ dimF (n.val + 29650) := by decide
theorem d1_w43 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 29650)) ≤ dimF (n.val + 29650) := by decide
theorem d0_w44 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 29700)) ≤ dimF (n.val + 29700) := by decide
theorem d1_w44 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 29700)) ≤ dimF (n.val + 29700) := by decide
theorem d0_w45 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 29750)) ≤ dimF (n.val + 29750) := by decide
theorem d1_w45 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 29750)) ≤ dimF (n.val + 29750) := by decide
theorem d0_w46 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 29800)) ≤ dimF (n.val + 29800) := by decide
theorem d1_w46 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 29800)) ≤ dimF (n.val + 29800) := by decide
theorem d0_w47 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 29850)) ≤ dimF (n.val + 29850) := by decide
theorem d1_w47 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 29850)) ≤ dimF (n.val + 29850) := by decide
theorem d0_w48 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 29900)) ≤ dimF (n.val + 29900) := by decide
theorem d1_w48 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 29900)) ≤ dimF (n.val + 29900) := by decide
theorem d0_w49 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 29950)) ≤ dimF (n.val + 29950) := by decide
theorem d1_w49 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 29950)) ≤ dimF (n.val + 29950) := by decide
theorem dim0_range (n : ℕ) (hn0 : 27500 ≤ n) (hn1 : n < 30000) :
    dimF (arg0 n) ≤ dimF n := by
  by_cases h0 : n < 27550
  · have hoff : 27500 ≤ n := by omega
    have hnfin : n - 27500 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using d0_w0 ⟨n - 27500, hnfin⟩
  ·
    by_cases h1 : n < 27600
    · have hoff : 27550 ≤ n := by omega
      have hnfin : n - 27550 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using d0_w1 ⟨n - 27550, hnfin⟩
    ·
      by_cases h2 : n < 27650
      · have hoff : 27600 ≤ n := by omega
        have hnfin : n - 27600 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using d0_w2 ⟨n - 27600, hnfin⟩
      ·
        by_cases h3 : n < 27700
        · have hoff : 27650 ≤ n := by omega
          have hnfin : n - 27650 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using d0_w3 ⟨n - 27650, hnfin⟩
        ·
          by_cases h4 : n < 27750
          · have hoff : 27700 ≤ n := by omega
            have hnfin : n - 27700 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using d0_w4 ⟨n - 27700, hnfin⟩
          ·
            by_cases h5 : n < 27800
            · have hoff : 27750 ≤ n := by omega
              have hnfin : n - 27750 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using d0_w5 ⟨n - 27750, hnfin⟩
            ·
              by_cases h6 : n < 27850
              · have hoff : 27800 ≤ n := by omega
                have hnfin : n - 27800 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using d0_w6 ⟨n - 27800, hnfin⟩
              ·
                by_cases h7 : n < 27900
                · have hoff : 27850 ≤ n := by omega
                  have hnfin : n - 27850 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using d0_w7 ⟨n - 27850, hnfin⟩
                ·
                  by_cases h8 : n < 27950
                  · have hoff : 27900 ≤ n := by omega
                    have hnfin : n - 27900 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using d0_w8 ⟨n - 27900, hnfin⟩
                  ·
                    by_cases h9 : n < 28000
                    · have hoff : 27950 ≤ n := by omega
                      have hnfin : n - 27950 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using d0_w9 ⟨n - 27950, hnfin⟩
                    ·
                      by_cases h10 : n < 28050
                      · have hoff : 28000 ≤ n := by omega
                        have hnfin : n - 28000 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using d0_w10 ⟨n - 28000, hnfin⟩
                      ·
                        by_cases h11 : n < 28100
                        · have hoff : 28050 ≤ n := by omega
                          have hnfin : n - 28050 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using d0_w11 ⟨n - 28050, hnfin⟩
                        ·
                          by_cases h12 : n < 28150
                          · have hoff : 28100 ≤ n := by omega
                            have hnfin : n - 28100 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using d0_w12 ⟨n - 28100, hnfin⟩
                          ·
                            by_cases h13 : n < 28200
                            · have hoff : 28150 ≤ n := by omega
                              have hnfin : n - 28150 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using d0_w13 ⟨n - 28150, hnfin⟩
                            ·
                              by_cases h14 : n < 28250
                              · have hoff : 28200 ≤ n := by omega
                                have hnfin : n - 28200 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using d0_w14 ⟨n - 28200, hnfin⟩
                              ·
                                by_cases h15 : n < 28300
                                · have hoff : 28250 ≤ n := by omega
                                  have hnfin : n - 28250 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using d0_w15 ⟨n - 28250, hnfin⟩
                                ·
                                  by_cases h16 : n < 28350
                                  · have hoff : 28300 ≤ n := by omega
                                    have hnfin : n - 28300 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using d0_w16 ⟨n - 28300, hnfin⟩
                                  ·
                                    by_cases h17 : n < 28400
                                    · have hoff : 28350 ≤ n := by omega
                                      have hnfin : n - 28350 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using d0_w17 ⟨n - 28350, hnfin⟩
                                    ·
                                      by_cases h18 : n < 28450
                                      · have hoff : 28400 ≤ n := by omega
                                        have hnfin : n - 28400 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using d0_w18 ⟨n - 28400, hnfin⟩
                                      ·
                                        by_cases h19 : n < 28500
                                        · have hoff : 28450 ≤ n := by omega
                                          have hnfin : n - 28450 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using d0_w19 ⟨n - 28450, hnfin⟩
                                        ·
                                          by_cases h20 : n < 28550
                                          · have hoff : 28500 ≤ n := by omega
                                            have hnfin : n - 28500 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using d0_w20 ⟨n - 28500, hnfin⟩
                                          ·
                                            by_cases h21 : n < 28600
                                            · have hoff : 28550 ≤ n := by omega
                                              have hnfin : n - 28550 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using d0_w21 ⟨n - 28550, hnfin⟩
                                            ·
                                              by_cases h22 : n < 28650
                                              · have hoff : 28600 ≤ n := by omega
                                                have hnfin : n - 28600 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using d0_w22 ⟨n - 28600, hnfin⟩
                                              ·
                                                by_cases h23 : n < 28700
                                                · have hoff : 28650 ≤ n := by omega
                                                  have hnfin : n - 28650 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using d0_w23 ⟨n - 28650, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 28750
                                                  · have hoff : 28700 ≤ n := by omega
                                                    have hnfin : n - 28700 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using d0_w24 ⟨n - 28700, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 28800
                                                    · have hoff : 28750 ≤ n := by omega
                                                      have hnfin : n - 28750 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using d0_w25 ⟨n - 28750, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 28850
                                                      · have hoff : 28800 ≤ n := by omega
                                                        have hnfin : n - 28800 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using d0_w26 ⟨n - 28800, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 28900
                                                        · have hoff : 28850 ≤ n := by omega
                                                          have hnfin : n - 28850 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using d0_w27 ⟨n - 28850, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 28950
                                                          · have hoff : 28900 ≤ n := by omega
                                                            have hnfin : n - 28900 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using d0_w28 ⟨n - 28900, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 29000
                                                            · have hoff : 28950 ≤ n := by omega
                                                              have hnfin : n - 28950 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using d0_w29 ⟨n - 28950, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 29050
                                                              · have hoff : 29000 ≤ n := by omega
                                                                have hnfin : n - 29000 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using d0_w30 ⟨n - 29000, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 29100
                                                                · have hoff : 29050 ≤ n := by omega
                                                                  have hnfin : n - 29050 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using d0_w31 ⟨n - 29050, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 29150
                                                                  · have hoff : 29100 ≤ n := by omega
                                                                    have hnfin : n - 29100 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w32 ⟨n - 29100, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 29200
                                                                    · have hoff : 29150 ≤ n := by omega
                                                                      have hnfin : n - 29150 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using d0_w33 ⟨n - 29150, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 29250
                                                                      · have hoff : 29200 ≤ n := by omega
                                                                        have hnfin : n - 29200 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using d0_w34 ⟨n - 29200, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 29300
                                                                        · have hoff : 29250 ≤ n := by omega
                                                                          have hnfin : n - 29250 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using d0_w35 ⟨n - 29250, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 29350
                                                                          · have hoff : 29300 ≤ n := by omega
                                                                            have hnfin : n - 29300 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using d0_w36 ⟨n - 29300, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 29400
                                                                            · have hoff : 29350 ≤ n := by omega
                                                                              have hnfin : n - 29350 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using d0_w37 ⟨n - 29350, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 29450
                                                                              · have hoff : 29400 ≤ n := by omega
                                                                                have hnfin : n - 29400 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using d0_w38 ⟨n - 29400, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 29500
                                                                                · have hoff : 29450 ≤ n := by omega
                                                                                  have hnfin : n - 29450 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using d0_w39 ⟨n - 29450, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 29550
                                                                                  · have hoff : 29500 ≤ n := by omega
                                                                                    have hnfin : n - 29500 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w40 ⟨n - 29500, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 29600
                                                                                    · have hoff : 29550 ≤ n := by omega
                                                                                      have hnfin : n - 29550 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using d0_w41 ⟨n - 29550, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 29650
                                                                                      · have hoff : 29600 ≤ n := by omega
                                                                                        have hnfin : n - 29600 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using d0_w42 ⟨n - 29600, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 29700
                                                                                        · have hoff : 29650 ≤ n := by omega
                                                                                          have hnfin : n - 29650 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using d0_w43 ⟨n - 29650, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 29750
                                                                                          · have hoff : 29700 ≤ n := by omega
                                                                                            have hnfin : n - 29700 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using d0_w44 ⟨n - 29700, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 29800
                                                                                            · have hoff : 29750 ≤ n := by omega
                                                                                              have hnfin : n - 29750 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using d0_w45 ⟨n - 29750, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 29850
                                                                                              · have hoff : 29800 ≤ n := by omega
                                                                                                have hnfin : n - 29800 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using d0_w46 ⟨n - 29800, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 29900
                                                                                                · have hoff : 29850 ≤ n := by omega
                                                                                                  have hnfin : n - 29850 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using d0_w47 ⟨n - 29850, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 29950
                                                                                                  · have hoff : 29900 ≤ n := by omega
                                                                                                    have hnfin : n - 29900 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w48 ⟨n - 29900, hnfin⟩
                                                                                                  · have hoff : 29950 ≤ n := by omega
                                                                                                    have hnfin : n - 29950 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w49 ⟨n - 29950, hnfin⟩
theorem dim1_range (n : ℕ) (hn0 : 27500 ≤ n) (hn1 : n < 30000) :
    dimF (arg1 n) ≤ dimF n := by
  by_cases h0 : n < 27550
  · have hoff : 27500 ≤ n := by omega
    have hnfin : n - 27500 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using d1_w0 ⟨n - 27500, hnfin⟩
  ·
    by_cases h1 : n < 27600
    · have hoff : 27550 ≤ n := by omega
      have hnfin : n - 27550 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using d1_w1 ⟨n - 27550, hnfin⟩
    ·
      by_cases h2 : n < 27650
      · have hoff : 27600 ≤ n := by omega
        have hnfin : n - 27600 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using d1_w2 ⟨n - 27600, hnfin⟩
      ·
        by_cases h3 : n < 27700
        · have hoff : 27650 ≤ n := by omega
          have hnfin : n - 27650 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using d1_w3 ⟨n - 27650, hnfin⟩
        ·
          by_cases h4 : n < 27750
          · have hoff : 27700 ≤ n := by omega
            have hnfin : n - 27700 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using d1_w4 ⟨n - 27700, hnfin⟩
          ·
            by_cases h5 : n < 27800
            · have hoff : 27750 ≤ n := by omega
              have hnfin : n - 27750 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using d1_w5 ⟨n - 27750, hnfin⟩
            ·
              by_cases h6 : n < 27850
              · have hoff : 27800 ≤ n := by omega
                have hnfin : n - 27800 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using d1_w6 ⟨n - 27800, hnfin⟩
              ·
                by_cases h7 : n < 27900
                · have hoff : 27850 ≤ n := by omega
                  have hnfin : n - 27850 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using d1_w7 ⟨n - 27850, hnfin⟩
                ·
                  by_cases h8 : n < 27950
                  · have hoff : 27900 ≤ n := by omega
                    have hnfin : n - 27900 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using d1_w8 ⟨n - 27900, hnfin⟩
                  ·
                    by_cases h9 : n < 28000
                    · have hoff : 27950 ≤ n := by omega
                      have hnfin : n - 27950 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using d1_w9 ⟨n - 27950, hnfin⟩
                    ·
                      by_cases h10 : n < 28050
                      · have hoff : 28000 ≤ n := by omega
                        have hnfin : n - 28000 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using d1_w10 ⟨n - 28000, hnfin⟩
                      ·
                        by_cases h11 : n < 28100
                        · have hoff : 28050 ≤ n := by omega
                          have hnfin : n - 28050 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using d1_w11 ⟨n - 28050, hnfin⟩
                        ·
                          by_cases h12 : n < 28150
                          · have hoff : 28100 ≤ n := by omega
                            have hnfin : n - 28100 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using d1_w12 ⟨n - 28100, hnfin⟩
                          ·
                            by_cases h13 : n < 28200
                            · have hoff : 28150 ≤ n := by omega
                              have hnfin : n - 28150 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using d1_w13 ⟨n - 28150, hnfin⟩
                            ·
                              by_cases h14 : n < 28250
                              · have hoff : 28200 ≤ n := by omega
                                have hnfin : n - 28200 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using d1_w14 ⟨n - 28200, hnfin⟩
                              ·
                                by_cases h15 : n < 28300
                                · have hoff : 28250 ≤ n := by omega
                                  have hnfin : n - 28250 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using d1_w15 ⟨n - 28250, hnfin⟩
                                ·
                                  by_cases h16 : n < 28350
                                  · have hoff : 28300 ≤ n := by omega
                                    have hnfin : n - 28300 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using d1_w16 ⟨n - 28300, hnfin⟩
                                  ·
                                    by_cases h17 : n < 28400
                                    · have hoff : 28350 ≤ n := by omega
                                      have hnfin : n - 28350 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using d1_w17 ⟨n - 28350, hnfin⟩
                                    ·
                                      by_cases h18 : n < 28450
                                      · have hoff : 28400 ≤ n := by omega
                                        have hnfin : n - 28400 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using d1_w18 ⟨n - 28400, hnfin⟩
                                      ·
                                        by_cases h19 : n < 28500
                                        · have hoff : 28450 ≤ n := by omega
                                          have hnfin : n - 28450 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using d1_w19 ⟨n - 28450, hnfin⟩
                                        ·
                                          by_cases h20 : n < 28550
                                          · have hoff : 28500 ≤ n := by omega
                                            have hnfin : n - 28500 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using d1_w20 ⟨n - 28500, hnfin⟩
                                          ·
                                            by_cases h21 : n < 28600
                                            · have hoff : 28550 ≤ n := by omega
                                              have hnfin : n - 28550 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using d1_w21 ⟨n - 28550, hnfin⟩
                                            ·
                                              by_cases h22 : n < 28650
                                              · have hoff : 28600 ≤ n := by omega
                                                have hnfin : n - 28600 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using d1_w22 ⟨n - 28600, hnfin⟩
                                              ·
                                                by_cases h23 : n < 28700
                                                · have hoff : 28650 ≤ n := by omega
                                                  have hnfin : n - 28650 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using d1_w23 ⟨n - 28650, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 28750
                                                  · have hoff : 28700 ≤ n := by omega
                                                    have hnfin : n - 28700 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using d1_w24 ⟨n - 28700, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 28800
                                                    · have hoff : 28750 ≤ n := by omega
                                                      have hnfin : n - 28750 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using d1_w25 ⟨n - 28750, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 28850
                                                      · have hoff : 28800 ≤ n := by omega
                                                        have hnfin : n - 28800 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using d1_w26 ⟨n - 28800, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 28900
                                                        · have hoff : 28850 ≤ n := by omega
                                                          have hnfin : n - 28850 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using d1_w27 ⟨n - 28850, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 28950
                                                          · have hoff : 28900 ≤ n := by omega
                                                            have hnfin : n - 28900 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using d1_w28 ⟨n - 28900, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 29000
                                                            · have hoff : 28950 ≤ n := by omega
                                                              have hnfin : n - 28950 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using d1_w29 ⟨n - 28950, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 29050
                                                              · have hoff : 29000 ≤ n := by omega
                                                                have hnfin : n - 29000 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using d1_w30 ⟨n - 29000, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 29100
                                                                · have hoff : 29050 ≤ n := by omega
                                                                  have hnfin : n - 29050 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using d1_w31 ⟨n - 29050, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 29150
                                                                  · have hoff : 29100 ≤ n := by omega
                                                                    have hnfin : n - 29100 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w32 ⟨n - 29100, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 29200
                                                                    · have hoff : 29150 ≤ n := by omega
                                                                      have hnfin : n - 29150 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using d1_w33 ⟨n - 29150, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 29250
                                                                      · have hoff : 29200 ≤ n := by omega
                                                                        have hnfin : n - 29200 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using d1_w34 ⟨n - 29200, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 29300
                                                                        · have hoff : 29250 ≤ n := by omega
                                                                          have hnfin : n - 29250 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using d1_w35 ⟨n - 29250, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 29350
                                                                          · have hoff : 29300 ≤ n := by omega
                                                                            have hnfin : n - 29300 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using d1_w36 ⟨n - 29300, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 29400
                                                                            · have hoff : 29350 ≤ n := by omega
                                                                              have hnfin : n - 29350 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using d1_w37 ⟨n - 29350, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 29450
                                                                              · have hoff : 29400 ≤ n := by omega
                                                                                have hnfin : n - 29400 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using d1_w38 ⟨n - 29400, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 29500
                                                                                · have hoff : 29450 ≤ n := by omega
                                                                                  have hnfin : n - 29450 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using d1_w39 ⟨n - 29450, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 29550
                                                                                  · have hoff : 29500 ≤ n := by omega
                                                                                    have hnfin : n - 29500 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w40 ⟨n - 29500, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 29600
                                                                                    · have hoff : 29550 ≤ n := by omega
                                                                                      have hnfin : n - 29550 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using d1_w41 ⟨n - 29550, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 29650
                                                                                      · have hoff : 29600 ≤ n := by omega
                                                                                        have hnfin : n - 29600 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using d1_w42 ⟨n - 29600, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 29700
                                                                                        · have hoff : 29650 ≤ n := by omega
                                                                                          have hnfin : n - 29650 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using d1_w43 ⟨n - 29650, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 29750
                                                                                          · have hoff : 29700 ≤ n := by omega
                                                                                            have hnfin : n - 29700 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using d1_w44 ⟨n - 29700, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 29800
                                                                                            · have hoff : 29750 ≤ n := by omega
                                                                                              have hnfin : n - 29750 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using d1_w45 ⟨n - 29750, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 29850
                                                                                              · have hoff : 29800 ≤ n := by omega
                                                                                                have hnfin : n - 29800 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using d1_w46 ⟨n - 29800, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 29900
                                                                                                · have hoff : 29850 ≤ n := by omega
                                                                                                  have hnfin : n - 29850 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using d1_w47 ⟨n - 29850, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 29950
                                                                                                  · have hoff : 29900 ≤ n := by omega
                                                                                                    have hnfin : n - 29900 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w48 ⟨n - 29900, hnfin⟩
                                                                                                  · have hoff : 29950 ≤ n := by omega
                                                                                                    have hnfin : n - 29950 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w49 ⟨n - 29950, hnfin⟩
end IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA11


