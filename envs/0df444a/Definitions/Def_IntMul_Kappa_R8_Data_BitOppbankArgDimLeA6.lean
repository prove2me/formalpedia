-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankArgDimLeA6
-- name    : IntMul_Kappa_R8_Data_BitOppbankArgDimLeA6
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T09:43:05.82895+00:00
-- url     : https://prove2.me/theorems/7990b1f9-a01a-4d68-9c33-275f2bb61c82
-- title:
--   argRel dim-inequality certificates on published Pnd, pack A6, nodes 15000–17499
-- statement:
--   # Dimension inequality certificates (published Pnd), pack $A_{6}$
--
--   Range consolidators for $n\in[15000,17500)$:
--   $$\dim F(\mathrm{arg}_0 n)\le \dim F(n)\qquad\text{and}\qquad\dim F(\mathrm{arg}_1 n)\le \dim F(n).$$
--
--   Here $\mathrm{arg}_0 n=\mathrm{argF}(n)\mathbin{\&}65535$ and $\mathrm{arg}_1 n=\mathrm{argF}(n)\gg 16$. Proved on the published (non-Fix) `argF` / `dimF` by Lean `decide` windows of 50 (last window of pack $A_{24}$ is size 28 at offset 62450), then `dim0_range` / `dim1_range`. Used for `argRel_dim_le` on published `argRel`.
--
--   Formalization note. The pack lives in namespace `IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA6` and imports only the published Pnd and SupG data.
-- source:
--   R8 BitOppbank FormalOK published Pnd (non-Fix) ArgDimLeA

-- ArgDimLeA6: dim inequality certificates on published Pnd only, nodes [15000, 17500)
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
namespace IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA6
def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16
theorem d0_w0 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 15000)) ≤ dimF (n.val + 15000) := by decide
theorem d1_w0 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 15000)) ≤ dimF (n.val + 15000) := by decide
theorem d0_w1 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 15050)) ≤ dimF (n.val + 15050) := by decide
theorem d1_w1 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 15050)) ≤ dimF (n.val + 15050) := by decide
theorem d0_w2 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 15100)) ≤ dimF (n.val + 15100) := by decide
theorem d1_w2 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 15100)) ≤ dimF (n.val + 15100) := by decide
theorem d0_w3 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 15150)) ≤ dimF (n.val + 15150) := by decide
theorem d1_w3 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 15150)) ≤ dimF (n.val + 15150) := by decide
theorem d0_w4 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 15200)) ≤ dimF (n.val + 15200) := by decide
theorem d1_w4 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 15200)) ≤ dimF (n.val + 15200) := by decide
theorem d0_w5 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 15250)) ≤ dimF (n.val + 15250) := by decide
theorem d1_w5 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 15250)) ≤ dimF (n.val + 15250) := by decide
theorem d0_w6 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 15300)) ≤ dimF (n.val + 15300) := by decide
theorem d1_w6 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 15300)) ≤ dimF (n.val + 15300) := by decide
theorem d0_w7 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 15350)) ≤ dimF (n.val + 15350) := by decide
theorem d1_w7 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 15350)) ≤ dimF (n.val + 15350) := by decide
theorem d0_w8 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 15400)) ≤ dimF (n.val + 15400) := by decide
theorem d1_w8 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 15400)) ≤ dimF (n.val + 15400) := by decide
theorem d0_w9 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 15450)) ≤ dimF (n.val + 15450) := by decide
theorem d1_w9 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 15450)) ≤ dimF (n.val + 15450) := by decide
theorem d0_w10 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 15500)) ≤ dimF (n.val + 15500) := by decide
theorem d1_w10 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 15500)) ≤ dimF (n.val + 15500) := by decide
theorem d0_w11 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 15550)) ≤ dimF (n.val + 15550) := by decide
theorem d1_w11 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 15550)) ≤ dimF (n.val + 15550) := by decide
theorem d0_w12 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 15600)) ≤ dimF (n.val + 15600) := by decide
theorem d1_w12 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 15600)) ≤ dimF (n.val + 15600) := by decide
theorem d0_w13 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 15650)) ≤ dimF (n.val + 15650) := by decide
theorem d1_w13 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 15650)) ≤ dimF (n.val + 15650) := by decide
theorem d0_w14 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 15700)) ≤ dimF (n.val + 15700) := by decide
theorem d1_w14 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 15700)) ≤ dimF (n.val + 15700) := by decide
theorem d0_w15 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 15750)) ≤ dimF (n.val + 15750) := by decide
theorem d1_w15 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 15750)) ≤ dimF (n.val + 15750) := by decide
theorem d0_w16 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 15800)) ≤ dimF (n.val + 15800) := by decide
theorem d1_w16 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 15800)) ≤ dimF (n.val + 15800) := by decide
theorem d0_w17 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 15850)) ≤ dimF (n.val + 15850) := by decide
theorem d1_w17 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 15850)) ≤ dimF (n.val + 15850) := by decide
theorem d0_w18 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 15900)) ≤ dimF (n.val + 15900) := by decide
theorem d1_w18 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 15900)) ≤ dimF (n.val + 15900) := by decide
theorem d0_w19 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 15950)) ≤ dimF (n.val + 15950) := by decide
theorem d1_w19 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 15950)) ≤ dimF (n.val + 15950) := by decide
theorem d0_w20 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 16000)) ≤ dimF (n.val + 16000) := by decide
theorem d1_w20 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 16000)) ≤ dimF (n.val + 16000) := by decide
theorem d0_w21 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 16050)) ≤ dimF (n.val + 16050) := by decide
theorem d1_w21 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 16050)) ≤ dimF (n.val + 16050) := by decide
theorem d0_w22 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 16100)) ≤ dimF (n.val + 16100) := by decide
theorem d1_w22 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 16100)) ≤ dimF (n.val + 16100) := by decide
theorem d0_w23 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 16150)) ≤ dimF (n.val + 16150) := by decide
theorem d1_w23 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 16150)) ≤ dimF (n.val + 16150) := by decide
theorem d0_w24 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 16200)) ≤ dimF (n.val + 16200) := by decide
theorem d1_w24 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 16200)) ≤ dimF (n.val + 16200) := by decide
theorem d0_w25 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 16250)) ≤ dimF (n.val + 16250) := by decide
theorem d1_w25 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 16250)) ≤ dimF (n.val + 16250) := by decide
theorem d0_w26 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 16300)) ≤ dimF (n.val + 16300) := by decide
theorem d1_w26 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 16300)) ≤ dimF (n.val + 16300) := by decide
theorem d0_w27 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 16350)) ≤ dimF (n.val + 16350) := by decide
theorem d1_w27 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 16350)) ≤ dimF (n.val + 16350) := by decide
theorem d0_w28 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 16400)) ≤ dimF (n.val + 16400) := by decide
theorem d1_w28 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 16400)) ≤ dimF (n.val + 16400) := by decide
theorem d0_w29 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 16450)) ≤ dimF (n.val + 16450) := by decide
theorem d1_w29 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 16450)) ≤ dimF (n.val + 16450) := by decide
theorem d0_w30 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 16500)) ≤ dimF (n.val + 16500) := by decide
theorem d1_w30 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 16500)) ≤ dimF (n.val + 16500) := by decide
theorem d0_w31 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 16550)) ≤ dimF (n.val + 16550) := by decide
theorem d1_w31 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 16550)) ≤ dimF (n.val + 16550) := by decide
theorem d0_w32 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 16600)) ≤ dimF (n.val + 16600) := by decide
theorem d1_w32 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 16600)) ≤ dimF (n.val + 16600) := by decide
theorem d0_w33 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 16650)) ≤ dimF (n.val + 16650) := by decide
theorem d1_w33 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 16650)) ≤ dimF (n.val + 16650) := by decide
theorem d0_w34 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 16700)) ≤ dimF (n.val + 16700) := by decide
theorem d1_w34 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 16700)) ≤ dimF (n.val + 16700) := by decide
theorem d0_w35 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 16750)) ≤ dimF (n.val + 16750) := by decide
theorem d1_w35 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 16750)) ≤ dimF (n.val + 16750) := by decide
theorem d0_w36 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 16800)) ≤ dimF (n.val + 16800) := by decide
theorem d1_w36 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 16800)) ≤ dimF (n.val + 16800) := by decide
theorem d0_w37 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 16850)) ≤ dimF (n.val + 16850) := by decide
theorem d1_w37 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 16850)) ≤ dimF (n.val + 16850) := by decide
theorem d0_w38 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 16900)) ≤ dimF (n.val + 16900) := by decide
theorem d1_w38 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 16900)) ≤ dimF (n.val + 16900) := by decide
theorem d0_w39 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 16950)) ≤ dimF (n.val + 16950) := by decide
theorem d1_w39 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 16950)) ≤ dimF (n.val + 16950) := by decide
theorem d0_w40 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 17000)) ≤ dimF (n.val + 17000) := by decide
theorem d1_w40 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 17000)) ≤ dimF (n.val + 17000) := by decide
theorem d0_w41 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 17050)) ≤ dimF (n.val + 17050) := by decide
theorem d1_w41 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 17050)) ≤ dimF (n.val + 17050) := by decide
theorem d0_w42 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 17100)) ≤ dimF (n.val + 17100) := by decide
theorem d1_w42 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 17100)) ≤ dimF (n.val + 17100) := by decide
theorem d0_w43 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 17150)) ≤ dimF (n.val + 17150) := by decide
theorem d1_w43 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 17150)) ≤ dimF (n.val + 17150) := by decide
theorem d0_w44 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 17200)) ≤ dimF (n.val + 17200) := by decide
theorem d1_w44 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 17200)) ≤ dimF (n.val + 17200) := by decide
theorem d0_w45 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 17250)) ≤ dimF (n.val + 17250) := by decide
theorem d1_w45 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 17250)) ≤ dimF (n.val + 17250) := by decide
theorem d0_w46 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 17300)) ≤ dimF (n.val + 17300) := by decide
theorem d1_w46 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 17300)) ≤ dimF (n.val + 17300) := by decide
theorem d0_w47 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 17350)) ≤ dimF (n.val + 17350) := by decide
theorem d1_w47 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 17350)) ≤ dimF (n.val + 17350) := by decide
theorem d0_w48 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 17400)) ≤ dimF (n.val + 17400) := by decide
theorem d1_w48 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 17400)) ≤ dimF (n.val + 17400) := by decide
theorem d0_w49 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 17450)) ≤ dimF (n.val + 17450) := by decide
theorem d1_w49 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 17450)) ≤ dimF (n.val + 17450) := by decide
theorem dim0_range (n : ℕ) (hn0 : 15000 ≤ n) (hn1 : n < 17500) :
    dimF (arg0 n) ≤ dimF n := by
  by_cases h0 : n < 15050
  · have hoff : 15000 ≤ n := by omega
    have hnfin : n - 15000 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using d0_w0 ⟨n - 15000, hnfin⟩
  ·
    by_cases h1 : n < 15100
    · have hoff : 15050 ≤ n := by omega
      have hnfin : n - 15050 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using d0_w1 ⟨n - 15050, hnfin⟩
    ·
      by_cases h2 : n < 15150
      · have hoff : 15100 ≤ n := by omega
        have hnfin : n - 15100 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using d0_w2 ⟨n - 15100, hnfin⟩
      ·
        by_cases h3 : n < 15200
        · have hoff : 15150 ≤ n := by omega
          have hnfin : n - 15150 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using d0_w3 ⟨n - 15150, hnfin⟩
        ·
          by_cases h4 : n < 15250
          · have hoff : 15200 ≤ n := by omega
            have hnfin : n - 15200 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using d0_w4 ⟨n - 15200, hnfin⟩
          ·
            by_cases h5 : n < 15300
            · have hoff : 15250 ≤ n := by omega
              have hnfin : n - 15250 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using d0_w5 ⟨n - 15250, hnfin⟩
            ·
              by_cases h6 : n < 15350
              · have hoff : 15300 ≤ n := by omega
                have hnfin : n - 15300 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using d0_w6 ⟨n - 15300, hnfin⟩
              ·
                by_cases h7 : n < 15400
                · have hoff : 15350 ≤ n := by omega
                  have hnfin : n - 15350 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using d0_w7 ⟨n - 15350, hnfin⟩
                ·
                  by_cases h8 : n < 15450
                  · have hoff : 15400 ≤ n := by omega
                    have hnfin : n - 15400 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using d0_w8 ⟨n - 15400, hnfin⟩
                  ·
                    by_cases h9 : n < 15500
                    · have hoff : 15450 ≤ n := by omega
                      have hnfin : n - 15450 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using d0_w9 ⟨n - 15450, hnfin⟩
                    ·
                      by_cases h10 : n < 15550
                      · have hoff : 15500 ≤ n := by omega
                        have hnfin : n - 15500 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using d0_w10 ⟨n - 15500, hnfin⟩
                      ·
                        by_cases h11 : n < 15600
                        · have hoff : 15550 ≤ n := by omega
                          have hnfin : n - 15550 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using d0_w11 ⟨n - 15550, hnfin⟩
                        ·
                          by_cases h12 : n < 15650
                          · have hoff : 15600 ≤ n := by omega
                            have hnfin : n - 15600 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using d0_w12 ⟨n - 15600, hnfin⟩
                          ·
                            by_cases h13 : n < 15700
                            · have hoff : 15650 ≤ n := by omega
                              have hnfin : n - 15650 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using d0_w13 ⟨n - 15650, hnfin⟩
                            ·
                              by_cases h14 : n < 15750
                              · have hoff : 15700 ≤ n := by omega
                                have hnfin : n - 15700 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using d0_w14 ⟨n - 15700, hnfin⟩
                              ·
                                by_cases h15 : n < 15800
                                · have hoff : 15750 ≤ n := by omega
                                  have hnfin : n - 15750 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using d0_w15 ⟨n - 15750, hnfin⟩
                                ·
                                  by_cases h16 : n < 15850
                                  · have hoff : 15800 ≤ n := by omega
                                    have hnfin : n - 15800 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using d0_w16 ⟨n - 15800, hnfin⟩
                                  ·
                                    by_cases h17 : n < 15900
                                    · have hoff : 15850 ≤ n := by omega
                                      have hnfin : n - 15850 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using d0_w17 ⟨n - 15850, hnfin⟩
                                    ·
                                      by_cases h18 : n < 15950
                                      · have hoff : 15900 ≤ n := by omega
                                        have hnfin : n - 15900 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using d0_w18 ⟨n - 15900, hnfin⟩
                                      ·
                                        by_cases h19 : n < 16000
                                        · have hoff : 15950 ≤ n := by omega
                                          have hnfin : n - 15950 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using d0_w19 ⟨n - 15950, hnfin⟩
                                        ·
                                          by_cases h20 : n < 16050
                                          · have hoff : 16000 ≤ n := by omega
                                            have hnfin : n - 16000 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using d0_w20 ⟨n - 16000, hnfin⟩
                                          ·
                                            by_cases h21 : n < 16100
                                            · have hoff : 16050 ≤ n := by omega
                                              have hnfin : n - 16050 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using d0_w21 ⟨n - 16050, hnfin⟩
                                            ·
                                              by_cases h22 : n < 16150
                                              · have hoff : 16100 ≤ n := by omega
                                                have hnfin : n - 16100 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using d0_w22 ⟨n - 16100, hnfin⟩
                                              ·
                                                by_cases h23 : n < 16200
                                                · have hoff : 16150 ≤ n := by omega
                                                  have hnfin : n - 16150 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using d0_w23 ⟨n - 16150, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 16250
                                                  · have hoff : 16200 ≤ n := by omega
                                                    have hnfin : n - 16200 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using d0_w24 ⟨n - 16200, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 16300
                                                    · have hoff : 16250 ≤ n := by omega
                                                      have hnfin : n - 16250 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using d0_w25 ⟨n - 16250, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 16350
                                                      · have hoff : 16300 ≤ n := by omega
                                                        have hnfin : n - 16300 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using d0_w26 ⟨n - 16300, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 16400
                                                        · have hoff : 16350 ≤ n := by omega
                                                          have hnfin : n - 16350 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using d0_w27 ⟨n - 16350, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 16450
                                                          · have hoff : 16400 ≤ n := by omega
                                                            have hnfin : n - 16400 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using d0_w28 ⟨n - 16400, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 16500
                                                            · have hoff : 16450 ≤ n := by omega
                                                              have hnfin : n - 16450 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using d0_w29 ⟨n - 16450, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 16550
                                                              · have hoff : 16500 ≤ n := by omega
                                                                have hnfin : n - 16500 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using d0_w30 ⟨n - 16500, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 16600
                                                                · have hoff : 16550 ≤ n := by omega
                                                                  have hnfin : n - 16550 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using d0_w31 ⟨n - 16550, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 16650
                                                                  · have hoff : 16600 ≤ n := by omega
                                                                    have hnfin : n - 16600 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w32 ⟨n - 16600, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 16700
                                                                    · have hoff : 16650 ≤ n := by omega
                                                                      have hnfin : n - 16650 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using d0_w33 ⟨n - 16650, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 16750
                                                                      · have hoff : 16700 ≤ n := by omega
                                                                        have hnfin : n - 16700 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using d0_w34 ⟨n - 16700, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 16800
                                                                        · have hoff : 16750 ≤ n := by omega
                                                                          have hnfin : n - 16750 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using d0_w35 ⟨n - 16750, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 16850
                                                                          · have hoff : 16800 ≤ n := by omega
                                                                            have hnfin : n - 16800 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using d0_w36 ⟨n - 16800, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 16900
                                                                            · have hoff : 16850 ≤ n := by omega
                                                                              have hnfin : n - 16850 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using d0_w37 ⟨n - 16850, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 16950
                                                                              · have hoff : 16900 ≤ n := by omega
                                                                                have hnfin : n - 16900 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using d0_w38 ⟨n - 16900, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 17000
                                                                                · have hoff : 16950 ≤ n := by omega
                                                                                  have hnfin : n - 16950 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using d0_w39 ⟨n - 16950, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 17050
                                                                                  · have hoff : 17000 ≤ n := by omega
                                                                                    have hnfin : n - 17000 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w40 ⟨n - 17000, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 17100
                                                                                    · have hoff : 17050 ≤ n := by omega
                                                                                      have hnfin : n - 17050 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using d0_w41 ⟨n - 17050, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 17150
                                                                                      · have hoff : 17100 ≤ n := by omega
                                                                                        have hnfin : n - 17100 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using d0_w42 ⟨n - 17100, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 17200
                                                                                        · have hoff : 17150 ≤ n := by omega
                                                                                          have hnfin : n - 17150 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using d0_w43 ⟨n - 17150, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 17250
                                                                                          · have hoff : 17200 ≤ n := by omega
                                                                                            have hnfin : n - 17200 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using d0_w44 ⟨n - 17200, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 17300
                                                                                            · have hoff : 17250 ≤ n := by omega
                                                                                              have hnfin : n - 17250 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using d0_w45 ⟨n - 17250, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 17350
                                                                                              · have hoff : 17300 ≤ n := by omega
                                                                                                have hnfin : n - 17300 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using d0_w46 ⟨n - 17300, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 17400
                                                                                                · have hoff : 17350 ≤ n := by omega
                                                                                                  have hnfin : n - 17350 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using d0_w47 ⟨n - 17350, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 17450
                                                                                                  · have hoff : 17400 ≤ n := by omega
                                                                                                    have hnfin : n - 17400 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w48 ⟨n - 17400, hnfin⟩
                                                                                                  · have hoff : 17450 ≤ n := by omega
                                                                                                    have hnfin : n - 17450 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w49 ⟨n - 17450, hnfin⟩
theorem dim1_range (n : ℕ) (hn0 : 15000 ≤ n) (hn1 : n < 17500) :
    dimF (arg1 n) ≤ dimF n := by
  by_cases h0 : n < 15050
  · have hoff : 15000 ≤ n := by omega
    have hnfin : n - 15000 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using d1_w0 ⟨n - 15000, hnfin⟩
  ·
    by_cases h1 : n < 15100
    · have hoff : 15050 ≤ n := by omega
      have hnfin : n - 15050 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using d1_w1 ⟨n - 15050, hnfin⟩
    ·
      by_cases h2 : n < 15150
      · have hoff : 15100 ≤ n := by omega
        have hnfin : n - 15100 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using d1_w2 ⟨n - 15100, hnfin⟩
      ·
        by_cases h3 : n < 15200
        · have hoff : 15150 ≤ n := by omega
          have hnfin : n - 15150 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using d1_w3 ⟨n - 15150, hnfin⟩
        ·
          by_cases h4 : n < 15250
          · have hoff : 15200 ≤ n := by omega
            have hnfin : n - 15200 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using d1_w4 ⟨n - 15200, hnfin⟩
          ·
            by_cases h5 : n < 15300
            · have hoff : 15250 ≤ n := by omega
              have hnfin : n - 15250 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using d1_w5 ⟨n - 15250, hnfin⟩
            ·
              by_cases h6 : n < 15350
              · have hoff : 15300 ≤ n := by omega
                have hnfin : n - 15300 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using d1_w6 ⟨n - 15300, hnfin⟩
              ·
                by_cases h7 : n < 15400
                · have hoff : 15350 ≤ n := by omega
                  have hnfin : n - 15350 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using d1_w7 ⟨n - 15350, hnfin⟩
                ·
                  by_cases h8 : n < 15450
                  · have hoff : 15400 ≤ n := by omega
                    have hnfin : n - 15400 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using d1_w8 ⟨n - 15400, hnfin⟩
                  ·
                    by_cases h9 : n < 15500
                    · have hoff : 15450 ≤ n := by omega
                      have hnfin : n - 15450 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using d1_w9 ⟨n - 15450, hnfin⟩
                    ·
                      by_cases h10 : n < 15550
                      · have hoff : 15500 ≤ n := by omega
                        have hnfin : n - 15500 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using d1_w10 ⟨n - 15500, hnfin⟩
                      ·
                        by_cases h11 : n < 15600
                        · have hoff : 15550 ≤ n := by omega
                          have hnfin : n - 15550 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using d1_w11 ⟨n - 15550, hnfin⟩
                        ·
                          by_cases h12 : n < 15650
                          · have hoff : 15600 ≤ n := by omega
                            have hnfin : n - 15600 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using d1_w12 ⟨n - 15600, hnfin⟩
                          ·
                            by_cases h13 : n < 15700
                            · have hoff : 15650 ≤ n := by omega
                              have hnfin : n - 15650 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using d1_w13 ⟨n - 15650, hnfin⟩
                            ·
                              by_cases h14 : n < 15750
                              · have hoff : 15700 ≤ n := by omega
                                have hnfin : n - 15700 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using d1_w14 ⟨n - 15700, hnfin⟩
                              ·
                                by_cases h15 : n < 15800
                                · have hoff : 15750 ≤ n := by omega
                                  have hnfin : n - 15750 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using d1_w15 ⟨n - 15750, hnfin⟩
                                ·
                                  by_cases h16 : n < 15850
                                  · have hoff : 15800 ≤ n := by omega
                                    have hnfin : n - 15800 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using d1_w16 ⟨n - 15800, hnfin⟩
                                  ·
                                    by_cases h17 : n < 15900
                                    · have hoff : 15850 ≤ n := by omega
                                      have hnfin : n - 15850 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using d1_w17 ⟨n - 15850, hnfin⟩
                                    ·
                                      by_cases h18 : n < 15950
                                      · have hoff : 15900 ≤ n := by omega
                                        have hnfin : n - 15900 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using d1_w18 ⟨n - 15900, hnfin⟩
                                      ·
                                        by_cases h19 : n < 16000
                                        · have hoff : 15950 ≤ n := by omega
                                          have hnfin : n - 15950 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using d1_w19 ⟨n - 15950, hnfin⟩
                                        ·
                                          by_cases h20 : n < 16050
                                          · have hoff : 16000 ≤ n := by omega
                                            have hnfin : n - 16000 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using d1_w20 ⟨n - 16000, hnfin⟩
                                          ·
                                            by_cases h21 : n < 16100
                                            · have hoff : 16050 ≤ n := by omega
                                              have hnfin : n - 16050 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using d1_w21 ⟨n - 16050, hnfin⟩
                                            ·
                                              by_cases h22 : n < 16150
                                              · have hoff : 16100 ≤ n := by omega
                                                have hnfin : n - 16100 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using d1_w22 ⟨n - 16100, hnfin⟩
                                              ·
                                                by_cases h23 : n < 16200
                                                · have hoff : 16150 ≤ n := by omega
                                                  have hnfin : n - 16150 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using d1_w23 ⟨n - 16150, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 16250
                                                  · have hoff : 16200 ≤ n := by omega
                                                    have hnfin : n - 16200 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using d1_w24 ⟨n - 16200, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 16300
                                                    · have hoff : 16250 ≤ n := by omega
                                                      have hnfin : n - 16250 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using d1_w25 ⟨n - 16250, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 16350
                                                      · have hoff : 16300 ≤ n := by omega
                                                        have hnfin : n - 16300 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using d1_w26 ⟨n - 16300, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 16400
                                                        · have hoff : 16350 ≤ n := by omega
                                                          have hnfin : n - 16350 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using d1_w27 ⟨n - 16350, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 16450
                                                          · have hoff : 16400 ≤ n := by omega
                                                            have hnfin : n - 16400 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using d1_w28 ⟨n - 16400, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 16500
                                                            · have hoff : 16450 ≤ n := by omega
                                                              have hnfin : n - 16450 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using d1_w29 ⟨n - 16450, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 16550
                                                              · have hoff : 16500 ≤ n := by omega
                                                                have hnfin : n - 16500 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using d1_w30 ⟨n - 16500, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 16600
                                                                · have hoff : 16550 ≤ n := by omega
                                                                  have hnfin : n - 16550 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using d1_w31 ⟨n - 16550, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 16650
                                                                  · have hoff : 16600 ≤ n := by omega
                                                                    have hnfin : n - 16600 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w32 ⟨n - 16600, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 16700
                                                                    · have hoff : 16650 ≤ n := by omega
                                                                      have hnfin : n - 16650 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using d1_w33 ⟨n - 16650, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 16750
                                                                      · have hoff : 16700 ≤ n := by omega
                                                                        have hnfin : n - 16700 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using d1_w34 ⟨n - 16700, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 16800
                                                                        · have hoff : 16750 ≤ n := by omega
                                                                          have hnfin : n - 16750 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using d1_w35 ⟨n - 16750, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 16850
                                                                          · have hoff : 16800 ≤ n := by omega
                                                                            have hnfin : n - 16800 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using d1_w36 ⟨n - 16800, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 16900
                                                                            · have hoff : 16850 ≤ n := by omega
                                                                              have hnfin : n - 16850 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using d1_w37 ⟨n - 16850, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 16950
                                                                              · have hoff : 16900 ≤ n := by omega
                                                                                have hnfin : n - 16900 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using d1_w38 ⟨n - 16900, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 17000
                                                                                · have hoff : 16950 ≤ n := by omega
                                                                                  have hnfin : n - 16950 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using d1_w39 ⟨n - 16950, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 17050
                                                                                  · have hoff : 17000 ≤ n := by omega
                                                                                    have hnfin : n - 17000 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w40 ⟨n - 17000, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 17100
                                                                                    · have hoff : 17050 ≤ n := by omega
                                                                                      have hnfin : n - 17050 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using d1_w41 ⟨n - 17050, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 17150
                                                                                      · have hoff : 17100 ≤ n := by omega
                                                                                        have hnfin : n - 17100 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using d1_w42 ⟨n - 17100, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 17200
                                                                                        · have hoff : 17150 ≤ n := by omega
                                                                                          have hnfin : n - 17150 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using d1_w43 ⟨n - 17150, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 17250
                                                                                          · have hoff : 17200 ≤ n := by omega
                                                                                            have hnfin : n - 17200 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using d1_w44 ⟨n - 17200, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 17300
                                                                                            · have hoff : 17250 ≤ n := by omega
                                                                                              have hnfin : n - 17250 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using d1_w45 ⟨n - 17250, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 17350
                                                                                              · have hoff : 17300 ≤ n := by omega
                                                                                                have hnfin : n - 17300 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using d1_w46 ⟨n - 17300, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 17400
                                                                                                · have hoff : 17350 ≤ n := by omega
                                                                                                  have hnfin : n - 17350 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using d1_w47 ⟨n - 17350, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 17450
                                                                                                  · have hoff : 17400 ≤ n := by omega
                                                                                                    have hnfin : n - 17400 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w48 ⟨n - 17400, hnfin⟩
                                                                                                  · have hoff : 17450 ≤ n := by omega
                                                                                                    have hnfin : n - 17450 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w49 ⟨n - 17450, hnfin⟩
end IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA6


