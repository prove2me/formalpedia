-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankArgDimLeA5
-- name    : IntMul_Kappa_R8_Data_BitOppbankArgDimLeA5
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T09:42:51.540722+00:00
-- url     : https://prove2.me/theorems/bc8cca68-e644-48f1-9736-8437364c3bbf
-- title:
--   argRel dim-inequality certificates on published Pnd, pack A5, nodes 12500–14999
-- statement:
--   # Dimension inequality certificates (published Pnd), pack $A_{5}$
--
--   Range consolidators for $n\in[12500,15000)$:
--   $$\dim F(\mathrm{arg}_0 n)\le \dim F(n)\qquad\text{and}\qquad\dim F(\mathrm{arg}_1 n)\le \dim F(n).$$
--
--   Here $\mathrm{arg}_0 n=\mathrm{argF}(n)\mathbin{\&}65535$ and $\mathrm{arg}_1 n=\mathrm{argF}(n)\gg 16$. Proved on the published (non-Fix) `argF` / `dimF` by Lean `decide` windows of 50 (last window of pack $A_{24}$ is size 28 at offset 62450), then `dim0_range` / `dim1_range`. Used for `argRel_dim_le` on published `argRel`.
--
--   Formalization note. The pack lives in namespace `IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA5` and imports only the published Pnd and SupG data.
-- source:
--   R8 BitOppbank FormalOK published Pnd (non-Fix) ArgDimLeA

-- ArgDimLeA5: dim inequality certificates on published Pnd only, nodes [12500, 15000)
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
namespace IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA5
def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16
theorem d0_w0 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 12500)) ≤ dimF (n.val + 12500) := by decide
theorem d1_w0 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 12500)) ≤ dimF (n.val + 12500) := by decide
theorem d0_w1 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 12550)) ≤ dimF (n.val + 12550) := by decide
theorem d1_w1 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 12550)) ≤ dimF (n.val + 12550) := by decide
theorem d0_w2 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 12600)) ≤ dimF (n.val + 12600) := by decide
theorem d1_w2 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 12600)) ≤ dimF (n.val + 12600) := by decide
theorem d0_w3 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 12650)) ≤ dimF (n.val + 12650) := by decide
theorem d1_w3 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 12650)) ≤ dimF (n.val + 12650) := by decide
theorem d0_w4 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 12700)) ≤ dimF (n.val + 12700) := by decide
theorem d1_w4 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 12700)) ≤ dimF (n.val + 12700) := by decide
theorem d0_w5 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 12750)) ≤ dimF (n.val + 12750) := by decide
theorem d1_w5 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 12750)) ≤ dimF (n.val + 12750) := by decide
theorem d0_w6 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 12800)) ≤ dimF (n.val + 12800) := by decide
theorem d1_w6 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 12800)) ≤ dimF (n.val + 12800) := by decide
theorem d0_w7 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 12850)) ≤ dimF (n.val + 12850) := by decide
theorem d1_w7 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 12850)) ≤ dimF (n.val + 12850) := by decide
theorem d0_w8 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 12900)) ≤ dimF (n.val + 12900) := by decide
theorem d1_w8 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 12900)) ≤ dimF (n.val + 12900) := by decide
theorem d0_w9 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 12950)) ≤ dimF (n.val + 12950) := by decide
theorem d1_w9 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 12950)) ≤ dimF (n.val + 12950) := by decide
theorem d0_w10 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 13000)) ≤ dimF (n.val + 13000) := by decide
theorem d1_w10 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 13000)) ≤ dimF (n.val + 13000) := by decide
theorem d0_w11 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 13050)) ≤ dimF (n.val + 13050) := by decide
theorem d1_w11 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 13050)) ≤ dimF (n.val + 13050) := by decide
theorem d0_w12 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 13100)) ≤ dimF (n.val + 13100) := by decide
theorem d1_w12 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 13100)) ≤ dimF (n.val + 13100) := by decide
theorem d0_w13 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 13150)) ≤ dimF (n.val + 13150) := by decide
theorem d1_w13 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 13150)) ≤ dimF (n.val + 13150) := by decide
theorem d0_w14 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 13200)) ≤ dimF (n.val + 13200) := by decide
theorem d1_w14 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 13200)) ≤ dimF (n.val + 13200) := by decide
theorem d0_w15 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 13250)) ≤ dimF (n.val + 13250) := by decide
theorem d1_w15 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 13250)) ≤ dimF (n.val + 13250) := by decide
theorem d0_w16 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 13300)) ≤ dimF (n.val + 13300) := by decide
theorem d1_w16 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 13300)) ≤ dimF (n.val + 13300) := by decide
theorem d0_w17 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 13350)) ≤ dimF (n.val + 13350) := by decide
theorem d1_w17 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 13350)) ≤ dimF (n.val + 13350) := by decide
theorem d0_w18 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 13400)) ≤ dimF (n.val + 13400) := by decide
theorem d1_w18 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 13400)) ≤ dimF (n.val + 13400) := by decide
theorem d0_w19 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 13450)) ≤ dimF (n.val + 13450) := by decide
theorem d1_w19 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 13450)) ≤ dimF (n.val + 13450) := by decide
theorem d0_w20 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 13500)) ≤ dimF (n.val + 13500) := by decide
theorem d1_w20 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 13500)) ≤ dimF (n.val + 13500) := by decide
theorem d0_w21 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 13550)) ≤ dimF (n.val + 13550) := by decide
theorem d1_w21 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 13550)) ≤ dimF (n.val + 13550) := by decide
theorem d0_w22 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 13600)) ≤ dimF (n.val + 13600) := by decide
theorem d1_w22 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 13600)) ≤ dimF (n.val + 13600) := by decide
theorem d0_w23 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 13650)) ≤ dimF (n.val + 13650) := by decide
theorem d1_w23 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 13650)) ≤ dimF (n.val + 13650) := by decide
theorem d0_w24 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 13700)) ≤ dimF (n.val + 13700) := by decide
theorem d1_w24 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 13700)) ≤ dimF (n.val + 13700) := by decide
theorem d0_w25 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 13750)) ≤ dimF (n.val + 13750) := by decide
theorem d1_w25 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 13750)) ≤ dimF (n.val + 13750) := by decide
theorem d0_w26 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 13800)) ≤ dimF (n.val + 13800) := by decide
theorem d1_w26 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 13800)) ≤ dimF (n.val + 13800) := by decide
theorem d0_w27 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 13850)) ≤ dimF (n.val + 13850) := by decide
theorem d1_w27 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 13850)) ≤ dimF (n.val + 13850) := by decide
theorem d0_w28 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 13900)) ≤ dimF (n.val + 13900) := by decide
theorem d1_w28 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 13900)) ≤ dimF (n.val + 13900) := by decide
theorem d0_w29 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 13950)) ≤ dimF (n.val + 13950) := by decide
theorem d1_w29 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 13950)) ≤ dimF (n.val + 13950) := by decide
theorem d0_w30 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 14000)) ≤ dimF (n.val + 14000) := by decide
theorem d1_w30 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 14000)) ≤ dimF (n.val + 14000) := by decide
theorem d0_w31 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 14050)) ≤ dimF (n.val + 14050) := by decide
theorem d1_w31 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 14050)) ≤ dimF (n.val + 14050) := by decide
theorem d0_w32 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 14100)) ≤ dimF (n.val + 14100) := by decide
theorem d1_w32 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 14100)) ≤ dimF (n.val + 14100) := by decide
theorem d0_w33 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 14150)) ≤ dimF (n.val + 14150) := by decide
theorem d1_w33 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 14150)) ≤ dimF (n.val + 14150) := by decide
theorem d0_w34 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 14200)) ≤ dimF (n.val + 14200) := by decide
theorem d1_w34 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 14200)) ≤ dimF (n.val + 14200) := by decide
theorem d0_w35 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 14250)) ≤ dimF (n.val + 14250) := by decide
theorem d1_w35 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 14250)) ≤ dimF (n.val + 14250) := by decide
theorem d0_w36 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 14300)) ≤ dimF (n.val + 14300) := by decide
theorem d1_w36 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 14300)) ≤ dimF (n.val + 14300) := by decide
theorem d0_w37 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 14350)) ≤ dimF (n.val + 14350) := by decide
theorem d1_w37 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 14350)) ≤ dimF (n.val + 14350) := by decide
theorem d0_w38 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 14400)) ≤ dimF (n.val + 14400) := by decide
theorem d1_w38 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 14400)) ≤ dimF (n.val + 14400) := by decide
theorem d0_w39 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 14450)) ≤ dimF (n.val + 14450) := by decide
theorem d1_w39 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 14450)) ≤ dimF (n.val + 14450) := by decide
theorem d0_w40 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 14500)) ≤ dimF (n.val + 14500) := by decide
theorem d1_w40 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 14500)) ≤ dimF (n.val + 14500) := by decide
theorem d0_w41 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 14550)) ≤ dimF (n.val + 14550) := by decide
theorem d1_w41 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 14550)) ≤ dimF (n.val + 14550) := by decide
theorem d0_w42 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 14600)) ≤ dimF (n.val + 14600) := by decide
theorem d1_w42 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 14600)) ≤ dimF (n.val + 14600) := by decide
theorem d0_w43 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 14650)) ≤ dimF (n.val + 14650) := by decide
theorem d1_w43 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 14650)) ≤ dimF (n.val + 14650) := by decide
theorem d0_w44 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 14700)) ≤ dimF (n.val + 14700) := by decide
theorem d1_w44 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 14700)) ≤ dimF (n.val + 14700) := by decide
theorem d0_w45 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 14750)) ≤ dimF (n.val + 14750) := by decide
theorem d1_w45 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 14750)) ≤ dimF (n.val + 14750) := by decide
theorem d0_w46 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 14800)) ≤ dimF (n.val + 14800) := by decide
theorem d1_w46 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 14800)) ≤ dimF (n.val + 14800) := by decide
theorem d0_w47 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 14850)) ≤ dimF (n.val + 14850) := by decide
theorem d1_w47 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 14850)) ≤ dimF (n.val + 14850) := by decide
theorem d0_w48 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 14900)) ≤ dimF (n.val + 14900) := by decide
theorem d1_w48 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 14900)) ≤ dimF (n.val + 14900) := by decide
theorem d0_w49 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 14950)) ≤ dimF (n.val + 14950) := by decide
theorem d1_w49 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 14950)) ≤ dimF (n.val + 14950) := by decide
theorem dim0_range (n : ℕ) (hn0 : 12500 ≤ n) (hn1 : n < 15000) :
    dimF (arg0 n) ≤ dimF n := by
  by_cases h0 : n < 12550
  · have hoff : 12500 ≤ n := by omega
    have hnfin : n - 12500 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using d0_w0 ⟨n - 12500, hnfin⟩
  ·
    by_cases h1 : n < 12600
    · have hoff : 12550 ≤ n := by omega
      have hnfin : n - 12550 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using d0_w1 ⟨n - 12550, hnfin⟩
    ·
      by_cases h2 : n < 12650
      · have hoff : 12600 ≤ n := by omega
        have hnfin : n - 12600 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using d0_w2 ⟨n - 12600, hnfin⟩
      ·
        by_cases h3 : n < 12700
        · have hoff : 12650 ≤ n := by omega
          have hnfin : n - 12650 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using d0_w3 ⟨n - 12650, hnfin⟩
        ·
          by_cases h4 : n < 12750
          · have hoff : 12700 ≤ n := by omega
            have hnfin : n - 12700 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using d0_w4 ⟨n - 12700, hnfin⟩
          ·
            by_cases h5 : n < 12800
            · have hoff : 12750 ≤ n := by omega
              have hnfin : n - 12750 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using d0_w5 ⟨n - 12750, hnfin⟩
            ·
              by_cases h6 : n < 12850
              · have hoff : 12800 ≤ n := by omega
                have hnfin : n - 12800 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using d0_w6 ⟨n - 12800, hnfin⟩
              ·
                by_cases h7 : n < 12900
                · have hoff : 12850 ≤ n := by omega
                  have hnfin : n - 12850 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using d0_w7 ⟨n - 12850, hnfin⟩
                ·
                  by_cases h8 : n < 12950
                  · have hoff : 12900 ≤ n := by omega
                    have hnfin : n - 12900 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using d0_w8 ⟨n - 12900, hnfin⟩
                  ·
                    by_cases h9 : n < 13000
                    · have hoff : 12950 ≤ n := by omega
                      have hnfin : n - 12950 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using d0_w9 ⟨n - 12950, hnfin⟩
                    ·
                      by_cases h10 : n < 13050
                      · have hoff : 13000 ≤ n := by omega
                        have hnfin : n - 13000 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using d0_w10 ⟨n - 13000, hnfin⟩
                      ·
                        by_cases h11 : n < 13100
                        · have hoff : 13050 ≤ n := by omega
                          have hnfin : n - 13050 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using d0_w11 ⟨n - 13050, hnfin⟩
                        ·
                          by_cases h12 : n < 13150
                          · have hoff : 13100 ≤ n := by omega
                            have hnfin : n - 13100 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using d0_w12 ⟨n - 13100, hnfin⟩
                          ·
                            by_cases h13 : n < 13200
                            · have hoff : 13150 ≤ n := by omega
                              have hnfin : n - 13150 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using d0_w13 ⟨n - 13150, hnfin⟩
                            ·
                              by_cases h14 : n < 13250
                              · have hoff : 13200 ≤ n := by omega
                                have hnfin : n - 13200 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using d0_w14 ⟨n - 13200, hnfin⟩
                              ·
                                by_cases h15 : n < 13300
                                · have hoff : 13250 ≤ n := by omega
                                  have hnfin : n - 13250 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using d0_w15 ⟨n - 13250, hnfin⟩
                                ·
                                  by_cases h16 : n < 13350
                                  · have hoff : 13300 ≤ n := by omega
                                    have hnfin : n - 13300 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using d0_w16 ⟨n - 13300, hnfin⟩
                                  ·
                                    by_cases h17 : n < 13400
                                    · have hoff : 13350 ≤ n := by omega
                                      have hnfin : n - 13350 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using d0_w17 ⟨n - 13350, hnfin⟩
                                    ·
                                      by_cases h18 : n < 13450
                                      · have hoff : 13400 ≤ n := by omega
                                        have hnfin : n - 13400 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using d0_w18 ⟨n - 13400, hnfin⟩
                                      ·
                                        by_cases h19 : n < 13500
                                        · have hoff : 13450 ≤ n := by omega
                                          have hnfin : n - 13450 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using d0_w19 ⟨n - 13450, hnfin⟩
                                        ·
                                          by_cases h20 : n < 13550
                                          · have hoff : 13500 ≤ n := by omega
                                            have hnfin : n - 13500 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using d0_w20 ⟨n - 13500, hnfin⟩
                                          ·
                                            by_cases h21 : n < 13600
                                            · have hoff : 13550 ≤ n := by omega
                                              have hnfin : n - 13550 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using d0_w21 ⟨n - 13550, hnfin⟩
                                            ·
                                              by_cases h22 : n < 13650
                                              · have hoff : 13600 ≤ n := by omega
                                                have hnfin : n - 13600 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using d0_w22 ⟨n - 13600, hnfin⟩
                                              ·
                                                by_cases h23 : n < 13700
                                                · have hoff : 13650 ≤ n := by omega
                                                  have hnfin : n - 13650 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using d0_w23 ⟨n - 13650, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 13750
                                                  · have hoff : 13700 ≤ n := by omega
                                                    have hnfin : n - 13700 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using d0_w24 ⟨n - 13700, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 13800
                                                    · have hoff : 13750 ≤ n := by omega
                                                      have hnfin : n - 13750 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using d0_w25 ⟨n - 13750, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 13850
                                                      · have hoff : 13800 ≤ n := by omega
                                                        have hnfin : n - 13800 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using d0_w26 ⟨n - 13800, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 13900
                                                        · have hoff : 13850 ≤ n := by omega
                                                          have hnfin : n - 13850 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using d0_w27 ⟨n - 13850, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 13950
                                                          · have hoff : 13900 ≤ n := by omega
                                                            have hnfin : n - 13900 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using d0_w28 ⟨n - 13900, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 14000
                                                            · have hoff : 13950 ≤ n := by omega
                                                              have hnfin : n - 13950 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using d0_w29 ⟨n - 13950, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 14050
                                                              · have hoff : 14000 ≤ n := by omega
                                                                have hnfin : n - 14000 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using d0_w30 ⟨n - 14000, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 14100
                                                                · have hoff : 14050 ≤ n := by omega
                                                                  have hnfin : n - 14050 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using d0_w31 ⟨n - 14050, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 14150
                                                                  · have hoff : 14100 ≤ n := by omega
                                                                    have hnfin : n - 14100 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w32 ⟨n - 14100, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 14200
                                                                    · have hoff : 14150 ≤ n := by omega
                                                                      have hnfin : n - 14150 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using d0_w33 ⟨n - 14150, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 14250
                                                                      · have hoff : 14200 ≤ n := by omega
                                                                        have hnfin : n - 14200 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using d0_w34 ⟨n - 14200, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 14300
                                                                        · have hoff : 14250 ≤ n := by omega
                                                                          have hnfin : n - 14250 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using d0_w35 ⟨n - 14250, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 14350
                                                                          · have hoff : 14300 ≤ n := by omega
                                                                            have hnfin : n - 14300 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using d0_w36 ⟨n - 14300, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 14400
                                                                            · have hoff : 14350 ≤ n := by omega
                                                                              have hnfin : n - 14350 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using d0_w37 ⟨n - 14350, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 14450
                                                                              · have hoff : 14400 ≤ n := by omega
                                                                                have hnfin : n - 14400 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using d0_w38 ⟨n - 14400, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 14500
                                                                                · have hoff : 14450 ≤ n := by omega
                                                                                  have hnfin : n - 14450 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using d0_w39 ⟨n - 14450, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 14550
                                                                                  · have hoff : 14500 ≤ n := by omega
                                                                                    have hnfin : n - 14500 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w40 ⟨n - 14500, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 14600
                                                                                    · have hoff : 14550 ≤ n := by omega
                                                                                      have hnfin : n - 14550 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using d0_w41 ⟨n - 14550, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 14650
                                                                                      · have hoff : 14600 ≤ n := by omega
                                                                                        have hnfin : n - 14600 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using d0_w42 ⟨n - 14600, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 14700
                                                                                        · have hoff : 14650 ≤ n := by omega
                                                                                          have hnfin : n - 14650 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using d0_w43 ⟨n - 14650, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 14750
                                                                                          · have hoff : 14700 ≤ n := by omega
                                                                                            have hnfin : n - 14700 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using d0_w44 ⟨n - 14700, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 14800
                                                                                            · have hoff : 14750 ≤ n := by omega
                                                                                              have hnfin : n - 14750 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using d0_w45 ⟨n - 14750, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 14850
                                                                                              · have hoff : 14800 ≤ n := by omega
                                                                                                have hnfin : n - 14800 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using d0_w46 ⟨n - 14800, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 14900
                                                                                                · have hoff : 14850 ≤ n := by omega
                                                                                                  have hnfin : n - 14850 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using d0_w47 ⟨n - 14850, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 14950
                                                                                                  · have hoff : 14900 ≤ n := by omega
                                                                                                    have hnfin : n - 14900 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w48 ⟨n - 14900, hnfin⟩
                                                                                                  · have hoff : 14950 ≤ n := by omega
                                                                                                    have hnfin : n - 14950 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w49 ⟨n - 14950, hnfin⟩
theorem dim1_range (n : ℕ) (hn0 : 12500 ≤ n) (hn1 : n < 15000) :
    dimF (arg1 n) ≤ dimF n := by
  by_cases h0 : n < 12550
  · have hoff : 12500 ≤ n := by omega
    have hnfin : n - 12500 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using d1_w0 ⟨n - 12500, hnfin⟩
  ·
    by_cases h1 : n < 12600
    · have hoff : 12550 ≤ n := by omega
      have hnfin : n - 12550 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using d1_w1 ⟨n - 12550, hnfin⟩
    ·
      by_cases h2 : n < 12650
      · have hoff : 12600 ≤ n := by omega
        have hnfin : n - 12600 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using d1_w2 ⟨n - 12600, hnfin⟩
      ·
        by_cases h3 : n < 12700
        · have hoff : 12650 ≤ n := by omega
          have hnfin : n - 12650 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using d1_w3 ⟨n - 12650, hnfin⟩
        ·
          by_cases h4 : n < 12750
          · have hoff : 12700 ≤ n := by omega
            have hnfin : n - 12700 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using d1_w4 ⟨n - 12700, hnfin⟩
          ·
            by_cases h5 : n < 12800
            · have hoff : 12750 ≤ n := by omega
              have hnfin : n - 12750 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using d1_w5 ⟨n - 12750, hnfin⟩
            ·
              by_cases h6 : n < 12850
              · have hoff : 12800 ≤ n := by omega
                have hnfin : n - 12800 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using d1_w6 ⟨n - 12800, hnfin⟩
              ·
                by_cases h7 : n < 12900
                · have hoff : 12850 ≤ n := by omega
                  have hnfin : n - 12850 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using d1_w7 ⟨n - 12850, hnfin⟩
                ·
                  by_cases h8 : n < 12950
                  · have hoff : 12900 ≤ n := by omega
                    have hnfin : n - 12900 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using d1_w8 ⟨n - 12900, hnfin⟩
                  ·
                    by_cases h9 : n < 13000
                    · have hoff : 12950 ≤ n := by omega
                      have hnfin : n - 12950 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using d1_w9 ⟨n - 12950, hnfin⟩
                    ·
                      by_cases h10 : n < 13050
                      · have hoff : 13000 ≤ n := by omega
                        have hnfin : n - 13000 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using d1_w10 ⟨n - 13000, hnfin⟩
                      ·
                        by_cases h11 : n < 13100
                        · have hoff : 13050 ≤ n := by omega
                          have hnfin : n - 13050 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using d1_w11 ⟨n - 13050, hnfin⟩
                        ·
                          by_cases h12 : n < 13150
                          · have hoff : 13100 ≤ n := by omega
                            have hnfin : n - 13100 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using d1_w12 ⟨n - 13100, hnfin⟩
                          ·
                            by_cases h13 : n < 13200
                            · have hoff : 13150 ≤ n := by omega
                              have hnfin : n - 13150 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using d1_w13 ⟨n - 13150, hnfin⟩
                            ·
                              by_cases h14 : n < 13250
                              · have hoff : 13200 ≤ n := by omega
                                have hnfin : n - 13200 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using d1_w14 ⟨n - 13200, hnfin⟩
                              ·
                                by_cases h15 : n < 13300
                                · have hoff : 13250 ≤ n := by omega
                                  have hnfin : n - 13250 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using d1_w15 ⟨n - 13250, hnfin⟩
                                ·
                                  by_cases h16 : n < 13350
                                  · have hoff : 13300 ≤ n := by omega
                                    have hnfin : n - 13300 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using d1_w16 ⟨n - 13300, hnfin⟩
                                  ·
                                    by_cases h17 : n < 13400
                                    · have hoff : 13350 ≤ n := by omega
                                      have hnfin : n - 13350 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using d1_w17 ⟨n - 13350, hnfin⟩
                                    ·
                                      by_cases h18 : n < 13450
                                      · have hoff : 13400 ≤ n := by omega
                                        have hnfin : n - 13400 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using d1_w18 ⟨n - 13400, hnfin⟩
                                      ·
                                        by_cases h19 : n < 13500
                                        · have hoff : 13450 ≤ n := by omega
                                          have hnfin : n - 13450 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using d1_w19 ⟨n - 13450, hnfin⟩
                                        ·
                                          by_cases h20 : n < 13550
                                          · have hoff : 13500 ≤ n := by omega
                                            have hnfin : n - 13500 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using d1_w20 ⟨n - 13500, hnfin⟩
                                          ·
                                            by_cases h21 : n < 13600
                                            · have hoff : 13550 ≤ n := by omega
                                              have hnfin : n - 13550 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using d1_w21 ⟨n - 13550, hnfin⟩
                                            ·
                                              by_cases h22 : n < 13650
                                              · have hoff : 13600 ≤ n := by omega
                                                have hnfin : n - 13600 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using d1_w22 ⟨n - 13600, hnfin⟩
                                              ·
                                                by_cases h23 : n < 13700
                                                · have hoff : 13650 ≤ n := by omega
                                                  have hnfin : n - 13650 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using d1_w23 ⟨n - 13650, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 13750
                                                  · have hoff : 13700 ≤ n := by omega
                                                    have hnfin : n - 13700 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using d1_w24 ⟨n - 13700, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 13800
                                                    · have hoff : 13750 ≤ n := by omega
                                                      have hnfin : n - 13750 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using d1_w25 ⟨n - 13750, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 13850
                                                      · have hoff : 13800 ≤ n := by omega
                                                        have hnfin : n - 13800 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using d1_w26 ⟨n - 13800, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 13900
                                                        · have hoff : 13850 ≤ n := by omega
                                                          have hnfin : n - 13850 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using d1_w27 ⟨n - 13850, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 13950
                                                          · have hoff : 13900 ≤ n := by omega
                                                            have hnfin : n - 13900 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using d1_w28 ⟨n - 13900, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 14000
                                                            · have hoff : 13950 ≤ n := by omega
                                                              have hnfin : n - 13950 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using d1_w29 ⟨n - 13950, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 14050
                                                              · have hoff : 14000 ≤ n := by omega
                                                                have hnfin : n - 14000 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using d1_w30 ⟨n - 14000, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 14100
                                                                · have hoff : 14050 ≤ n := by omega
                                                                  have hnfin : n - 14050 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using d1_w31 ⟨n - 14050, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 14150
                                                                  · have hoff : 14100 ≤ n := by omega
                                                                    have hnfin : n - 14100 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w32 ⟨n - 14100, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 14200
                                                                    · have hoff : 14150 ≤ n := by omega
                                                                      have hnfin : n - 14150 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using d1_w33 ⟨n - 14150, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 14250
                                                                      · have hoff : 14200 ≤ n := by omega
                                                                        have hnfin : n - 14200 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using d1_w34 ⟨n - 14200, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 14300
                                                                        · have hoff : 14250 ≤ n := by omega
                                                                          have hnfin : n - 14250 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using d1_w35 ⟨n - 14250, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 14350
                                                                          · have hoff : 14300 ≤ n := by omega
                                                                            have hnfin : n - 14300 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using d1_w36 ⟨n - 14300, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 14400
                                                                            · have hoff : 14350 ≤ n := by omega
                                                                              have hnfin : n - 14350 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using d1_w37 ⟨n - 14350, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 14450
                                                                              · have hoff : 14400 ≤ n := by omega
                                                                                have hnfin : n - 14400 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using d1_w38 ⟨n - 14400, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 14500
                                                                                · have hoff : 14450 ≤ n := by omega
                                                                                  have hnfin : n - 14450 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using d1_w39 ⟨n - 14450, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 14550
                                                                                  · have hoff : 14500 ≤ n := by omega
                                                                                    have hnfin : n - 14500 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w40 ⟨n - 14500, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 14600
                                                                                    · have hoff : 14550 ≤ n := by omega
                                                                                      have hnfin : n - 14550 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using d1_w41 ⟨n - 14550, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 14650
                                                                                      · have hoff : 14600 ≤ n := by omega
                                                                                        have hnfin : n - 14600 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using d1_w42 ⟨n - 14600, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 14700
                                                                                        · have hoff : 14650 ≤ n := by omega
                                                                                          have hnfin : n - 14650 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using d1_w43 ⟨n - 14650, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 14750
                                                                                          · have hoff : 14700 ≤ n := by omega
                                                                                            have hnfin : n - 14700 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using d1_w44 ⟨n - 14700, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 14800
                                                                                            · have hoff : 14750 ≤ n := by omega
                                                                                              have hnfin : n - 14750 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using d1_w45 ⟨n - 14750, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 14850
                                                                                              · have hoff : 14800 ≤ n := by omega
                                                                                                have hnfin : n - 14800 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using d1_w46 ⟨n - 14800, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 14900
                                                                                                · have hoff : 14850 ≤ n := by omega
                                                                                                  have hnfin : n - 14850 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using d1_w47 ⟨n - 14850, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 14950
                                                                                                  · have hoff : 14900 ≤ n := by omega
                                                                                                    have hnfin : n - 14900 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w48 ⟨n - 14900, hnfin⟩
                                                                                                  · have hoff : 14950 ≤ n := by omega
                                                                                                    have hnfin : n - 14950 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w49 ⟨n - 14950, hnfin⟩
end IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA5


