-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankArgDimLeA8
-- name    : IntMul_Kappa_R8_Data_BitOppbankArgDimLeA8
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T09:43:18.510264+00:00
-- url     : https://prove2.me/theorems/95a88c4d-73d0-43fe-9dce-110e45a50cca
-- title:
--   argRel dim-inequality certificates on published Pnd, pack A8, nodes 20000–22499
-- statement:
--   # Dimension inequality certificates (published Pnd), pack $A_{8}$
--
--   Range consolidators for $n\in[20000,22500)$:
--   $$\dim F(\mathrm{arg}_0 n)\le \dim F(n)\qquad\text{and}\qquad\dim F(\mathrm{arg}_1 n)\le \dim F(n).$$
--
--   Here $\mathrm{arg}_0 n=\mathrm{argF}(n)\mathbin{\&}65535$ and $\mathrm{arg}_1 n=\mathrm{argF}(n)\gg 16$. Proved on the published (non-Fix) `argF` / `dimF` by Lean `decide` windows of 50 (last window of pack $A_{24}$ is size 28 at offset 62450), then `dim0_range` / `dim1_range`. Used for `argRel_dim_le` on published `argRel`.
--
--   Formalization note. The pack lives in namespace `IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA8` and imports only the published Pnd and SupG data.
-- source:
--   R8 BitOppbank FormalOK published Pnd (non-Fix) ArgDimLeA

-- ArgDimLeA8: dim inequality certificates on published Pnd only, nodes [20000, 22500)
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
namespace IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA8
def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16
theorem d0_w0 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 20000)) ≤ dimF (n.val + 20000) := by decide
theorem d1_w0 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 20000)) ≤ dimF (n.val + 20000) := by decide
theorem d0_w1 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 20050)) ≤ dimF (n.val + 20050) := by decide
theorem d1_w1 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 20050)) ≤ dimF (n.val + 20050) := by decide
theorem d0_w2 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 20100)) ≤ dimF (n.val + 20100) := by decide
theorem d1_w2 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 20100)) ≤ dimF (n.val + 20100) := by decide
theorem d0_w3 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 20150)) ≤ dimF (n.val + 20150) := by decide
theorem d1_w3 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 20150)) ≤ dimF (n.val + 20150) := by decide
theorem d0_w4 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 20200)) ≤ dimF (n.val + 20200) := by decide
theorem d1_w4 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 20200)) ≤ dimF (n.val + 20200) := by decide
theorem d0_w5 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 20250)) ≤ dimF (n.val + 20250) := by decide
theorem d1_w5 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 20250)) ≤ dimF (n.val + 20250) := by decide
theorem d0_w6 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 20300)) ≤ dimF (n.val + 20300) := by decide
theorem d1_w6 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 20300)) ≤ dimF (n.val + 20300) := by decide
theorem d0_w7 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 20350)) ≤ dimF (n.val + 20350) := by decide
theorem d1_w7 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 20350)) ≤ dimF (n.val + 20350) := by decide
theorem d0_w8 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 20400)) ≤ dimF (n.val + 20400) := by decide
theorem d1_w8 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 20400)) ≤ dimF (n.val + 20400) := by decide
theorem d0_w9 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 20450)) ≤ dimF (n.val + 20450) := by decide
theorem d1_w9 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 20450)) ≤ dimF (n.val + 20450) := by decide
theorem d0_w10 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 20500)) ≤ dimF (n.val + 20500) := by decide
theorem d1_w10 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 20500)) ≤ dimF (n.val + 20500) := by decide
theorem d0_w11 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 20550)) ≤ dimF (n.val + 20550) := by decide
theorem d1_w11 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 20550)) ≤ dimF (n.val + 20550) := by decide
theorem d0_w12 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 20600)) ≤ dimF (n.val + 20600) := by decide
theorem d1_w12 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 20600)) ≤ dimF (n.val + 20600) := by decide
theorem d0_w13 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 20650)) ≤ dimF (n.val + 20650) := by decide
theorem d1_w13 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 20650)) ≤ dimF (n.val + 20650) := by decide
theorem d0_w14 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 20700)) ≤ dimF (n.val + 20700) := by decide
theorem d1_w14 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 20700)) ≤ dimF (n.val + 20700) := by decide
theorem d0_w15 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 20750)) ≤ dimF (n.val + 20750) := by decide
theorem d1_w15 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 20750)) ≤ dimF (n.val + 20750) := by decide
theorem d0_w16 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 20800)) ≤ dimF (n.val + 20800) := by decide
theorem d1_w16 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 20800)) ≤ dimF (n.val + 20800) := by decide
theorem d0_w17 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 20850)) ≤ dimF (n.val + 20850) := by decide
theorem d1_w17 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 20850)) ≤ dimF (n.val + 20850) := by decide
theorem d0_w18 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 20900)) ≤ dimF (n.val + 20900) := by decide
theorem d1_w18 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 20900)) ≤ dimF (n.val + 20900) := by decide
theorem d0_w19 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 20950)) ≤ dimF (n.val + 20950) := by decide
theorem d1_w19 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 20950)) ≤ dimF (n.val + 20950) := by decide
theorem d0_w20 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 21000)) ≤ dimF (n.val + 21000) := by decide
theorem d1_w20 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 21000)) ≤ dimF (n.val + 21000) := by decide
theorem d0_w21 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 21050)) ≤ dimF (n.val + 21050) := by decide
theorem d1_w21 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 21050)) ≤ dimF (n.val + 21050) := by decide
theorem d0_w22 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 21100)) ≤ dimF (n.val + 21100) := by decide
theorem d1_w22 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 21100)) ≤ dimF (n.val + 21100) := by decide
theorem d0_w23 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 21150)) ≤ dimF (n.val + 21150) := by decide
theorem d1_w23 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 21150)) ≤ dimF (n.val + 21150) := by decide
theorem d0_w24 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 21200)) ≤ dimF (n.val + 21200) := by decide
theorem d1_w24 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 21200)) ≤ dimF (n.val + 21200) := by decide
theorem d0_w25 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 21250)) ≤ dimF (n.val + 21250) := by decide
theorem d1_w25 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 21250)) ≤ dimF (n.val + 21250) := by decide
theorem d0_w26 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 21300)) ≤ dimF (n.val + 21300) := by decide
theorem d1_w26 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 21300)) ≤ dimF (n.val + 21300) := by decide
theorem d0_w27 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 21350)) ≤ dimF (n.val + 21350) := by decide
theorem d1_w27 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 21350)) ≤ dimF (n.val + 21350) := by decide
theorem d0_w28 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 21400)) ≤ dimF (n.val + 21400) := by decide
theorem d1_w28 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 21400)) ≤ dimF (n.val + 21400) := by decide
theorem d0_w29 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 21450)) ≤ dimF (n.val + 21450) := by decide
theorem d1_w29 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 21450)) ≤ dimF (n.val + 21450) := by decide
theorem d0_w30 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 21500)) ≤ dimF (n.val + 21500) := by decide
theorem d1_w30 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 21500)) ≤ dimF (n.val + 21500) := by decide
theorem d0_w31 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 21550)) ≤ dimF (n.val + 21550) := by decide
theorem d1_w31 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 21550)) ≤ dimF (n.val + 21550) := by decide
theorem d0_w32 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 21600)) ≤ dimF (n.val + 21600) := by decide
theorem d1_w32 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 21600)) ≤ dimF (n.val + 21600) := by decide
theorem d0_w33 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 21650)) ≤ dimF (n.val + 21650) := by decide
theorem d1_w33 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 21650)) ≤ dimF (n.val + 21650) := by decide
theorem d0_w34 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 21700)) ≤ dimF (n.val + 21700) := by decide
theorem d1_w34 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 21700)) ≤ dimF (n.val + 21700) := by decide
theorem d0_w35 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 21750)) ≤ dimF (n.val + 21750) := by decide
theorem d1_w35 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 21750)) ≤ dimF (n.val + 21750) := by decide
theorem d0_w36 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 21800)) ≤ dimF (n.val + 21800) := by decide
theorem d1_w36 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 21800)) ≤ dimF (n.val + 21800) := by decide
theorem d0_w37 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 21850)) ≤ dimF (n.val + 21850) := by decide
theorem d1_w37 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 21850)) ≤ dimF (n.val + 21850) := by decide
theorem d0_w38 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 21900)) ≤ dimF (n.val + 21900) := by decide
theorem d1_w38 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 21900)) ≤ dimF (n.val + 21900) := by decide
theorem d0_w39 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 21950)) ≤ dimF (n.val + 21950) := by decide
theorem d1_w39 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 21950)) ≤ dimF (n.val + 21950) := by decide
theorem d0_w40 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 22000)) ≤ dimF (n.val + 22000) := by decide
theorem d1_w40 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 22000)) ≤ dimF (n.val + 22000) := by decide
theorem d0_w41 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 22050)) ≤ dimF (n.val + 22050) := by decide
theorem d1_w41 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 22050)) ≤ dimF (n.val + 22050) := by decide
theorem d0_w42 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 22100)) ≤ dimF (n.val + 22100) := by decide
theorem d1_w42 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 22100)) ≤ dimF (n.val + 22100) := by decide
theorem d0_w43 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 22150)) ≤ dimF (n.val + 22150) := by decide
theorem d1_w43 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 22150)) ≤ dimF (n.val + 22150) := by decide
theorem d0_w44 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 22200)) ≤ dimF (n.val + 22200) := by decide
theorem d1_w44 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 22200)) ≤ dimF (n.val + 22200) := by decide
theorem d0_w45 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 22250)) ≤ dimF (n.val + 22250) := by decide
theorem d1_w45 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 22250)) ≤ dimF (n.val + 22250) := by decide
theorem d0_w46 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 22300)) ≤ dimF (n.val + 22300) := by decide
theorem d1_w46 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 22300)) ≤ dimF (n.val + 22300) := by decide
theorem d0_w47 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 22350)) ≤ dimF (n.val + 22350) := by decide
theorem d1_w47 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 22350)) ≤ dimF (n.val + 22350) := by decide
theorem d0_w48 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 22400)) ≤ dimF (n.val + 22400) := by decide
theorem d1_w48 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 22400)) ≤ dimF (n.val + 22400) := by decide
theorem d0_w49 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 22450)) ≤ dimF (n.val + 22450) := by decide
theorem d1_w49 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 22450)) ≤ dimF (n.val + 22450) := by decide
theorem dim0_range (n : ℕ) (hn0 : 20000 ≤ n) (hn1 : n < 22500) :
    dimF (arg0 n) ≤ dimF n := by
  by_cases h0 : n < 20050
  · have hoff : 20000 ≤ n := by omega
    have hnfin : n - 20000 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using d0_w0 ⟨n - 20000, hnfin⟩
  ·
    by_cases h1 : n < 20100
    · have hoff : 20050 ≤ n := by omega
      have hnfin : n - 20050 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using d0_w1 ⟨n - 20050, hnfin⟩
    ·
      by_cases h2 : n < 20150
      · have hoff : 20100 ≤ n := by omega
        have hnfin : n - 20100 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using d0_w2 ⟨n - 20100, hnfin⟩
      ·
        by_cases h3 : n < 20200
        · have hoff : 20150 ≤ n := by omega
          have hnfin : n - 20150 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using d0_w3 ⟨n - 20150, hnfin⟩
        ·
          by_cases h4 : n < 20250
          · have hoff : 20200 ≤ n := by omega
            have hnfin : n - 20200 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using d0_w4 ⟨n - 20200, hnfin⟩
          ·
            by_cases h5 : n < 20300
            · have hoff : 20250 ≤ n := by omega
              have hnfin : n - 20250 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using d0_w5 ⟨n - 20250, hnfin⟩
            ·
              by_cases h6 : n < 20350
              · have hoff : 20300 ≤ n := by omega
                have hnfin : n - 20300 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using d0_w6 ⟨n - 20300, hnfin⟩
              ·
                by_cases h7 : n < 20400
                · have hoff : 20350 ≤ n := by omega
                  have hnfin : n - 20350 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using d0_w7 ⟨n - 20350, hnfin⟩
                ·
                  by_cases h8 : n < 20450
                  · have hoff : 20400 ≤ n := by omega
                    have hnfin : n - 20400 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using d0_w8 ⟨n - 20400, hnfin⟩
                  ·
                    by_cases h9 : n < 20500
                    · have hoff : 20450 ≤ n := by omega
                      have hnfin : n - 20450 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using d0_w9 ⟨n - 20450, hnfin⟩
                    ·
                      by_cases h10 : n < 20550
                      · have hoff : 20500 ≤ n := by omega
                        have hnfin : n - 20500 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using d0_w10 ⟨n - 20500, hnfin⟩
                      ·
                        by_cases h11 : n < 20600
                        · have hoff : 20550 ≤ n := by omega
                          have hnfin : n - 20550 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using d0_w11 ⟨n - 20550, hnfin⟩
                        ·
                          by_cases h12 : n < 20650
                          · have hoff : 20600 ≤ n := by omega
                            have hnfin : n - 20600 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using d0_w12 ⟨n - 20600, hnfin⟩
                          ·
                            by_cases h13 : n < 20700
                            · have hoff : 20650 ≤ n := by omega
                              have hnfin : n - 20650 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using d0_w13 ⟨n - 20650, hnfin⟩
                            ·
                              by_cases h14 : n < 20750
                              · have hoff : 20700 ≤ n := by omega
                                have hnfin : n - 20700 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using d0_w14 ⟨n - 20700, hnfin⟩
                              ·
                                by_cases h15 : n < 20800
                                · have hoff : 20750 ≤ n := by omega
                                  have hnfin : n - 20750 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using d0_w15 ⟨n - 20750, hnfin⟩
                                ·
                                  by_cases h16 : n < 20850
                                  · have hoff : 20800 ≤ n := by omega
                                    have hnfin : n - 20800 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using d0_w16 ⟨n - 20800, hnfin⟩
                                  ·
                                    by_cases h17 : n < 20900
                                    · have hoff : 20850 ≤ n := by omega
                                      have hnfin : n - 20850 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using d0_w17 ⟨n - 20850, hnfin⟩
                                    ·
                                      by_cases h18 : n < 20950
                                      · have hoff : 20900 ≤ n := by omega
                                        have hnfin : n - 20900 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using d0_w18 ⟨n - 20900, hnfin⟩
                                      ·
                                        by_cases h19 : n < 21000
                                        · have hoff : 20950 ≤ n := by omega
                                          have hnfin : n - 20950 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using d0_w19 ⟨n - 20950, hnfin⟩
                                        ·
                                          by_cases h20 : n < 21050
                                          · have hoff : 21000 ≤ n := by omega
                                            have hnfin : n - 21000 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using d0_w20 ⟨n - 21000, hnfin⟩
                                          ·
                                            by_cases h21 : n < 21100
                                            · have hoff : 21050 ≤ n := by omega
                                              have hnfin : n - 21050 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using d0_w21 ⟨n - 21050, hnfin⟩
                                            ·
                                              by_cases h22 : n < 21150
                                              · have hoff : 21100 ≤ n := by omega
                                                have hnfin : n - 21100 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using d0_w22 ⟨n - 21100, hnfin⟩
                                              ·
                                                by_cases h23 : n < 21200
                                                · have hoff : 21150 ≤ n := by omega
                                                  have hnfin : n - 21150 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using d0_w23 ⟨n - 21150, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 21250
                                                  · have hoff : 21200 ≤ n := by omega
                                                    have hnfin : n - 21200 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using d0_w24 ⟨n - 21200, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 21300
                                                    · have hoff : 21250 ≤ n := by omega
                                                      have hnfin : n - 21250 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using d0_w25 ⟨n - 21250, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 21350
                                                      · have hoff : 21300 ≤ n := by omega
                                                        have hnfin : n - 21300 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using d0_w26 ⟨n - 21300, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 21400
                                                        · have hoff : 21350 ≤ n := by omega
                                                          have hnfin : n - 21350 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using d0_w27 ⟨n - 21350, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 21450
                                                          · have hoff : 21400 ≤ n := by omega
                                                            have hnfin : n - 21400 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using d0_w28 ⟨n - 21400, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 21500
                                                            · have hoff : 21450 ≤ n := by omega
                                                              have hnfin : n - 21450 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using d0_w29 ⟨n - 21450, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 21550
                                                              · have hoff : 21500 ≤ n := by omega
                                                                have hnfin : n - 21500 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using d0_w30 ⟨n - 21500, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 21600
                                                                · have hoff : 21550 ≤ n := by omega
                                                                  have hnfin : n - 21550 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using d0_w31 ⟨n - 21550, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 21650
                                                                  · have hoff : 21600 ≤ n := by omega
                                                                    have hnfin : n - 21600 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w32 ⟨n - 21600, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 21700
                                                                    · have hoff : 21650 ≤ n := by omega
                                                                      have hnfin : n - 21650 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using d0_w33 ⟨n - 21650, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 21750
                                                                      · have hoff : 21700 ≤ n := by omega
                                                                        have hnfin : n - 21700 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using d0_w34 ⟨n - 21700, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 21800
                                                                        · have hoff : 21750 ≤ n := by omega
                                                                          have hnfin : n - 21750 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using d0_w35 ⟨n - 21750, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 21850
                                                                          · have hoff : 21800 ≤ n := by omega
                                                                            have hnfin : n - 21800 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using d0_w36 ⟨n - 21800, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 21900
                                                                            · have hoff : 21850 ≤ n := by omega
                                                                              have hnfin : n - 21850 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using d0_w37 ⟨n - 21850, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 21950
                                                                              · have hoff : 21900 ≤ n := by omega
                                                                                have hnfin : n - 21900 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using d0_w38 ⟨n - 21900, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 22000
                                                                                · have hoff : 21950 ≤ n := by omega
                                                                                  have hnfin : n - 21950 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using d0_w39 ⟨n - 21950, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 22050
                                                                                  · have hoff : 22000 ≤ n := by omega
                                                                                    have hnfin : n - 22000 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w40 ⟨n - 22000, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 22100
                                                                                    · have hoff : 22050 ≤ n := by omega
                                                                                      have hnfin : n - 22050 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using d0_w41 ⟨n - 22050, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 22150
                                                                                      · have hoff : 22100 ≤ n := by omega
                                                                                        have hnfin : n - 22100 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using d0_w42 ⟨n - 22100, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 22200
                                                                                        · have hoff : 22150 ≤ n := by omega
                                                                                          have hnfin : n - 22150 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using d0_w43 ⟨n - 22150, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 22250
                                                                                          · have hoff : 22200 ≤ n := by omega
                                                                                            have hnfin : n - 22200 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using d0_w44 ⟨n - 22200, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 22300
                                                                                            · have hoff : 22250 ≤ n := by omega
                                                                                              have hnfin : n - 22250 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using d0_w45 ⟨n - 22250, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 22350
                                                                                              · have hoff : 22300 ≤ n := by omega
                                                                                                have hnfin : n - 22300 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using d0_w46 ⟨n - 22300, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 22400
                                                                                                · have hoff : 22350 ≤ n := by omega
                                                                                                  have hnfin : n - 22350 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using d0_w47 ⟨n - 22350, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 22450
                                                                                                  · have hoff : 22400 ≤ n := by omega
                                                                                                    have hnfin : n - 22400 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w48 ⟨n - 22400, hnfin⟩
                                                                                                  · have hoff : 22450 ≤ n := by omega
                                                                                                    have hnfin : n - 22450 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w49 ⟨n - 22450, hnfin⟩
theorem dim1_range (n : ℕ) (hn0 : 20000 ≤ n) (hn1 : n < 22500) :
    dimF (arg1 n) ≤ dimF n := by
  by_cases h0 : n < 20050
  · have hoff : 20000 ≤ n := by omega
    have hnfin : n - 20000 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using d1_w0 ⟨n - 20000, hnfin⟩
  ·
    by_cases h1 : n < 20100
    · have hoff : 20050 ≤ n := by omega
      have hnfin : n - 20050 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using d1_w1 ⟨n - 20050, hnfin⟩
    ·
      by_cases h2 : n < 20150
      · have hoff : 20100 ≤ n := by omega
        have hnfin : n - 20100 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using d1_w2 ⟨n - 20100, hnfin⟩
      ·
        by_cases h3 : n < 20200
        · have hoff : 20150 ≤ n := by omega
          have hnfin : n - 20150 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using d1_w3 ⟨n - 20150, hnfin⟩
        ·
          by_cases h4 : n < 20250
          · have hoff : 20200 ≤ n := by omega
            have hnfin : n - 20200 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using d1_w4 ⟨n - 20200, hnfin⟩
          ·
            by_cases h5 : n < 20300
            · have hoff : 20250 ≤ n := by omega
              have hnfin : n - 20250 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using d1_w5 ⟨n - 20250, hnfin⟩
            ·
              by_cases h6 : n < 20350
              · have hoff : 20300 ≤ n := by omega
                have hnfin : n - 20300 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using d1_w6 ⟨n - 20300, hnfin⟩
              ·
                by_cases h7 : n < 20400
                · have hoff : 20350 ≤ n := by omega
                  have hnfin : n - 20350 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using d1_w7 ⟨n - 20350, hnfin⟩
                ·
                  by_cases h8 : n < 20450
                  · have hoff : 20400 ≤ n := by omega
                    have hnfin : n - 20400 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using d1_w8 ⟨n - 20400, hnfin⟩
                  ·
                    by_cases h9 : n < 20500
                    · have hoff : 20450 ≤ n := by omega
                      have hnfin : n - 20450 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using d1_w9 ⟨n - 20450, hnfin⟩
                    ·
                      by_cases h10 : n < 20550
                      · have hoff : 20500 ≤ n := by omega
                        have hnfin : n - 20500 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using d1_w10 ⟨n - 20500, hnfin⟩
                      ·
                        by_cases h11 : n < 20600
                        · have hoff : 20550 ≤ n := by omega
                          have hnfin : n - 20550 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using d1_w11 ⟨n - 20550, hnfin⟩
                        ·
                          by_cases h12 : n < 20650
                          · have hoff : 20600 ≤ n := by omega
                            have hnfin : n - 20600 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using d1_w12 ⟨n - 20600, hnfin⟩
                          ·
                            by_cases h13 : n < 20700
                            · have hoff : 20650 ≤ n := by omega
                              have hnfin : n - 20650 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using d1_w13 ⟨n - 20650, hnfin⟩
                            ·
                              by_cases h14 : n < 20750
                              · have hoff : 20700 ≤ n := by omega
                                have hnfin : n - 20700 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using d1_w14 ⟨n - 20700, hnfin⟩
                              ·
                                by_cases h15 : n < 20800
                                · have hoff : 20750 ≤ n := by omega
                                  have hnfin : n - 20750 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using d1_w15 ⟨n - 20750, hnfin⟩
                                ·
                                  by_cases h16 : n < 20850
                                  · have hoff : 20800 ≤ n := by omega
                                    have hnfin : n - 20800 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using d1_w16 ⟨n - 20800, hnfin⟩
                                  ·
                                    by_cases h17 : n < 20900
                                    · have hoff : 20850 ≤ n := by omega
                                      have hnfin : n - 20850 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using d1_w17 ⟨n - 20850, hnfin⟩
                                    ·
                                      by_cases h18 : n < 20950
                                      · have hoff : 20900 ≤ n := by omega
                                        have hnfin : n - 20900 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using d1_w18 ⟨n - 20900, hnfin⟩
                                      ·
                                        by_cases h19 : n < 21000
                                        · have hoff : 20950 ≤ n := by omega
                                          have hnfin : n - 20950 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using d1_w19 ⟨n - 20950, hnfin⟩
                                        ·
                                          by_cases h20 : n < 21050
                                          · have hoff : 21000 ≤ n := by omega
                                            have hnfin : n - 21000 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using d1_w20 ⟨n - 21000, hnfin⟩
                                          ·
                                            by_cases h21 : n < 21100
                                            · have hoff : 21050 ≤ n := by omega
                                              have hnfin : n - 21050 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using d1_w21 ⟨n - 21050, hnfin⟩
                                            ·
                                              by_cases h22 : n < 21150
                                              · have hoff : 21100 ≤ n := by omega
                                                have hnfin : n - 21100 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using d1_w22 ⟨n - 21100, hnfin⟩
                                              ·
                                                by_cases h23 : n < 21200
                                                · have hoff : 21150 ≤ n := by omega
                                                  have hnfin : n - 21150 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using d1_w23 ⟨n - 21150, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 21250
                                                  · have hoff : 21200 ≤ n := by omega
                                                    have hnfin : n - 21200 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using d1_w24 ⟨n - 21200, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 21300
                                                    · have hoff : 21250 ≤ n := by omega
                                                      have hnfin : n - 21250 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using d1_w25 ⟨n - 21250, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 21350
                                                      · have hoff : 21300 ≤ n := by omega
                                                        have hnfin : n - 21300 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using d1_w26 ⟨n - 21300, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 21400
                                                        · have hoff : 21350 ≤ n := by omega
                                                          have hnfin : n - 21350 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using d1_w27 ⟨n - 21350, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 21450
                                                          · have hoff : 21400 ≤ n := by omega
                                                            have hnfin : n - 21400 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using d1_w28 ⟨n - 21400, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 21500
                                                            · have hoff : 21450 ≤ n := by omega
                                                              have hnfin : n - 21450 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using d1_w29 ⟨n - 21450, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 21550
                                                              · have hoff : 21500 ≤ n := by omega
                                                                have hnfin : n - 21500 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using d1_w30 ⟨n - 21500, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 21600
                                                                · have hoff : 21550 ≤ n := by omega
                                                                  have hnfin : n - 21550 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using d1_w31 ⟨n - 21550, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 21650
                                                                  · have hoff : 21600 ≤ n := by omega
                                                                    have hnfin : n - 21600 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w32 ⟨n - 21600, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 21700
                                                                    · have hoff : 21650 ≤ n := by omega
                                                                      have hnfin : n - 21650 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using d1_w33 ⟨n - 21650, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 21750
                                                                      · have hoff : 21700 ≤ n := by omega
                                                                        have hnfin : n - 21700 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using d1_w34 ⟨n - 21700, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 21800
                                                                        · have hoff : 21750 ≤ n := by omega
                                                                          have hnfin : n - 21750 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using d1_w35 ⟨n - 21750, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 21850
                                                                          · have hoff : 21800 ≤ n := by omega
                                                                            have hnfin : n - 21800 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using d1_w36 ⟨n - 21800, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 21900
                                                                            · have hoff : 21850 ≤ n := by omega
                                                                              have hnfin : n - 21850 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using d1_w37 ⟨n - 21850, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 21950
                                                                              · have hoff : 21900 ≤ n := by omega
                                                                                have hnfin : n - 21900 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using d1_w38 ⟨n - 21900, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 22000
                                                                                · have hoff : 21950 ≤ n := by omega
                                                                                  have hnfin : n - 21950 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using d1_w39 ⟨n - 21950, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 22050
                                                                                  · have hoff : 22000 ≤ n := by omega
                                                                                    have hnfin : n - 22000 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w40 ⟨n - 22000, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 22100
                                                                                    · have hoff : 22050 ≤ n := by omega
                                                                                      have hnfin : n - 22050 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using d1_w41 ⟨n - 22050, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 22150
                                                                                      · have hoff : 22100 ≤ n := by omega
                                                                                        have hnfin : n - 22100 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using d1_w42 ⟨n - 22100, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 22200
                                                                                        · have hoff : 22150 ≤ n := by omega
                                                                                          have hnfin : n - 22150 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using d1_w43 ⟨n - 22150, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 22250
                                                                                          · have hoff : 22200 ≤ n := by omega
                                                                                            have hnfin : n - 22200 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using d1_w44 ⟨n - 22200, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 22300
                                                                                            · have hoff : 22250 ≤ n := by omega
                                                                                              have hnfin : n - 22250 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using d1_w45 ⟨n - 22250, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 22350
                                                                                              · have hoff : 22300 ≤ n := by omega
                                                                                                have hnfin : n - 22300 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using d1_w46 ⟨n - 22300, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 22400
                                                                                                · have hoff : 22350 ≤ n := by omega
                                                                                                  have hnfin : n - 22350 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using d1_w47 ⟨n - 22350, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 22450
                                                                                                  · have hoff : 22400 ≤ n := by omega
                                                                                                    have hnfin : n - 22400 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w48 ⟨n - 22400, hnfin⟩
                                                                                                  · have hoff : 22450 ≤ n := by omega
                                                                                                    have hnfin : n - 22450 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w49 ⟨n - 22450, hnfin⟩
end IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA8


