-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankArgDimLeA23
-- name    : IntMul_Kappa_R8_Data_BitOppbankArgDimLeA23
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T09:43:04.408209+00:00
-- url     : https://prove2.me/theorems/c67c2d9b-a2bd-43a8-8b19-e0af0c0bf53e
-- title:
--   argRel dim-inequality certificates on published Pnd, pack A23, nodes 57500–59999
-- statement:
--   # Dimension inequality certificates (published Pnd), pack $A_{23}$
--
--   Range consolidators for $n\in[57500,60000)$:
--   $$\dim F(\mathrm{arg}_0 n)\le \dim F(n)\qquad\text{and}\qquad\dim F(\mathrm{arg}_1 n)\le \dim F(n).$$
--
--   Here $\mathrm{arg}_0 n=\mathrm{argF}(n)\mathbin{\&}65535$ and $\mathrm{arg}_1 n=\mathrm{argF}(n)\gg 16$. Proved on the published (non-Fix) `argF` / `dimF` by Lean `decide` windows of 50 (last window of pack $A_{24}$ is size 28 at offset 62450), then `dim0_range` / `dim1_range`. Used for `argRel_dim_le` on published `argRel`.
--
--   Formalization note. The pack lives in namespace `IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA23` and imports only the published Pnd and SupG data.
-- source:
--   R8 BitOppbank FormalOK published Pnd (non-Fix) ArgDimLeA

-- ArgDimLeA23: dim inequality certificates on published Pnd only, nodes [57500, 60000)
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
namespace IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA23
def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16
theorem d0_w0 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 57500)) ≤ dimF (n.val + 57500) := by decide
theorem d1_w0 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 57500)) ≤ dimF (n.val + 57500) := by decide
theorem d0_w1 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 57550)) ≤ dimF (n.val + 57550) := by decide
theorem d1_w1 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 57550)) ≤ dimF (n.val + 57550) := by decide
theorem d0_w2 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 57600)) ≤ dimF (n.val + 57600) := by decide
theorem d1_w2 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 57600)) ≤ dimF (n.val + 57600) := by decide
theorem d0_w3 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 57650)) ≤ dimF (n.val + 57650) := by decide
theorem d1_w3 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 57650)) ≤ dimF (n.val + 57650) := by decide
theorem d0_w4 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 57700)) ≤ dimF (n.val + 57700) := by decide
theorem d1_w4 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 57700)) ≤ dimF (n.val + 57700) := by decide
theorem d0_w5 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 57750)) ≤ dimF (n.val + 57750) := by decide
theorem d1_w5 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 57750)) ≤ dimF (n.val + 57750) := by decide
theorem d0_w6 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 57800)) ≤ dimF (n.val + 57800) := by decide
theorem d1_w6 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 57800)) ≤ dimF (n.val + 57800) := by decide
theorem d0_w7 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 57850)) ≤ dimF (n.val + 57850) := by decide
theorem d1_w7 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 57850)) ≤ dimF (n.val + 57850) := by decide
theorem d0_w8 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 57900)) ≤ dimF (n.val + 57900) := by decide
theorem d1_w8 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 57900)) ≤ dimF (n.val + 57900) := by decide
theorem d0_w9 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 57950)) ≤ dimF (n.val + 57950) := by decide
theorem d1_w9 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 57950)) ≤ dimF (n.val + 57950) := by decide
theorem d0_w10 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 58000)) ≤ dimF (n.val + 58000) := by decide
theorem d1_w10 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 58000)) ≤ dimF (n.val + 58000) := by decide
theorem d0_w11 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 58050)) ≤ dimF (n.val + 58050) := by decide
theorem d1_w11 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 58050)) ≤ dimF (n.val + 58050) := by decide
theorem d0_w12 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 58100)) ≤ dimF (n.val + 58100) := by decide
theorem d1_w12 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 58100)) ≤ dimF (n.val + 58100) := by decide
theorem d0_w13 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 58150)) ≤ dimF (n.val + 58150) := by decide
theorem d1_w13 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 58150)) ≤ dimF (n.val + 58150) := by decide
theorem d0_w14 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 58200)) ≤ dimF (n.val + 58200) := by decide
theorem d1_w14 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 58200)) ≤ dimF (n.val + 58200) := by decide
theorem d0_w15 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 58250)) ≤ dimF (n.val + 58250) := by decide
theorem d1_w15 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 58250)) ≤ dimF (n.val + 58250) := by decide
theorem d0_w16 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 58300)) ≤ dimF (n.val + 58300) := by decide
theorem d1_w16 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 58300)) ≤ dimF (n.val + 58300) := by decide
theorem d0_w17 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 58350)) ≤ dimF (n.val + 58350) := by decide
theorem d1_w17 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 58350)) ≤ dimF (n.val + 58350) := by decide
theorem d0_w18 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 58400)) ≤ dimF (n.val + 58400) := by decide
theorem d1_w18 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 58400)) ≤ dimF (n.val + 58400) := by decide
theorem d0_w19 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 58450)) ≤ dimF (n.val + 58450) := by decide
theorem d1_w19 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 58450)) ≤ dimF (n.val + 58450) := by decide
theorem d0_w20 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 58500)) ≤ dimF (n.val + 58500) := by decide
theorem d1_w20 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 58500)) ≤ dimF (n.val + 58500) := by decide
theorem d0_w21 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 58550)) ≤ dimF (n.val + 58550) := by decide
theorem d1_w21 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 58550)) ≤ dimF (n.val + 58550) := by decide
theorem d0_w22 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 58600)) ≤ dimF (n.val + 58600) := by decide
theorem d1_w22 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 58600)) ≤ dimF (n.val + 58600) := by decide
theorem d0_w23 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 58650)) ≤ dimF (n.val + 58650) := by decide
theorem d1_w23 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 58650)) ≤ dimF (n.val + 58650) := by decide
theorem d0_w24 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 58700)) ≤ dimF (n.val + 58700) := by decide
theorem d1_w24 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 58700)) ≤ dimF (n.val + 58700) := by decide
theorem d0_w25 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 58750)) ≤ dimF (n.val + 58750) := by decide
theorem d1_w25 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 58750)) ≤ dimF (n.val + 58750) := by decide
theorem d0_w26 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 58800)) ≤ dimF (n.val + 58800) := by decide
theorem d1_w26 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 58800)) ≤ dimF (n.val + 58800) := by decide
theorem d0_w27 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 58850)) ≤ dimF (n.val + 58850) := by decide
theorem d1_w27 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 58850)) ≤ dimF (n.val + 58850) := by decide
theorem d0_w28 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 58900)) ≤ dimF (n.val + 58900) := by decide
theorem d1_w28 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 58900)) ≤ dimF (n.val + 58900) := by decide
theorem d0_w29 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 58950)) ≤ dimF (n.val + 58950) := by decide
theorem d1_w29 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 58950)) ≤ dimF (n.val + 58950) := by decide
theorem d0_w30 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 59000)) ≤ dimF (n.val + 59000) := by decide
theorem d1_w30 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 59000)) ≤ dimF (n.val + 59000) := by decide
theorem d0_w31 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 59050)) ≤ dimF (n.val + 59050) := by decide
theorem d1_w31 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 59050)) ≤ dimF (n.val + 59050) := by decide
theorem d0_w32 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 59100)) ≤ dimF (n.val + 59100) := by decide
theorem d1_w32 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 59100)) ≤ dimF (n.val + 59100) := by decide
theorem d0_w33 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 59150)) ≤ dimF (n.val + 59150) := by decide
theorem d1_w33 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 59150)) ≤ dimF (n.val + 59150) := by decide
theorem d0_w34 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 59200)) ≤ dimF (n.val + 59200) := by decide
theorem d1_w34 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 59200)) ≤ dimF (n.val + 59200) := by decide
theorem d0_w35 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 59250)) ≤ dimF (n.val + 59250) := by decide
theorem d1_w35 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 59250)) ≤ dimF (n.val + 59250) := by decide
theorem d0_w36 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 59300)) ≤ dimF (n.val + 59300) := by decide
theorem d1_w36 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 59300)) ≤ dimF (n.val + 59300) := by decide
theorem d0_w37 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 59350)) ≤ dimF (n.val + 59350) := by decide
theorem d1_w37 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 59350)) ≤ dimF (n.val + 59350) := by decide
theorem d0_w38 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 59400)) ≤ dimF (n.val + 59400) := by decide
theorem d1_w38 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 59400)) ≤ dimF (n.val + 59400) := by decide
theorem d0_w39 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 59450)) ≤ dimF (n.val + 59450) := by decide
theorem d1_w39 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 59450)) ≤ dimF (n.val + 59450) := by decide
theorem d0_w40 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 59500)) ≤ dimF (n.val + 59500) := by decide
theorem d1_w40 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 59500)) ≤ dimF (n.val + 59500) := by decide
theorem d0_w41 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 59550)) ≤ dimF (n.val + 59550) := by decide
theorem d1_w41 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 59550)) ≤ dimF (n.val + 59550) := by decide
theorem d0_w42 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 59600)) ≤ dimF (n.val + 59600) := by decide
theorem d1_w42 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 59600)) ≤ dimF (n.val + 59600) := by decide
theorem d0_w43 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 59650)) ≤ dimF (n.val + 59650) := by decide
theorem d1_w43 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 59650)) ≤ dimF (n.val + 59650) := by decide
theorem d0_w44 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 59700)) ≤ dimF (n.val + 59700) := by decide
theorem d1_w44 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 59700)) ≤ dimF (n.val + 59700) := by decide
theorem d0_w45 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 59750)) ≤ dimF (n.val + 59750) := by decide
theorem d1_w45 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 59750)) ≤ dimF (n.val + 59750) := by decide
theorem d0_w46 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 59800)) ≤ dimF (n.val + 59800) := by decide
theorem d1_w46 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 59800)) ≤ dimF (n.val + 59800) := by decide
theorem d0_w47 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 59850)) ≤ dimF (n.val + 59850) := by decide
theorem d1_w47 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 59850)) ≤ dimF (n.val + 59850) := by decide
theorem d0_w48 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 59900)) ≤ dimF (n.val + 59900) := by decide
theorem d1_w48 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 59900)) ≤ dimF (n.val + 59900) := by decide
theorem d0_w49 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 59950)) ≤ dimF (n.val + 59950) := by decide
theorem d1_w49 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 59950)) ≤ dimF (n.val + 59950) := by decide
theorem dim0_range (n : ℕ) (hn0 : 57500 ≤ n) (hn1 : n < 60000) :
    dimF (arg0 n) ≤ dimF n := by
  by_cases h0 : n < 57550
  · have hoff : 57500 ≤ n := by omega
    have hnfin : n - 57500 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using d0_w0 ⟨n - 57500, hnfin⟩
  ·
    by_cases h1 : n < 57600
    · have hoff : 57550 ≤ n := by omega
      have hnfin : n - 57550 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using d0_w1 ⟨n - 57550, hnfin⟩
    ·
      by_cases h2 : n < 57650
      · have hoff : 57600 ≤ n := by omega
        have hnfin : n - 57600 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using d0_w2 ⟨n - 57600, hnfin⟩
      ·
        by_cases h3 : n < 57700
        · have hoff : 57650 ≤ n := by omega
          have hnfin : n - 57650 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using d0_w3 ⟨n - 57650, hnfin⟩
        ·
          by_cases h4 : n < 57750
          · have hoff : 57700 ≤ n := by omega
            have hnfin : n - 57700 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using d0_w4 ⟨n - 57700, hnfin⟩
          ·
            by_cases h5 : n < 57800
            · have hoff : 57750 ≤ n := by omega
              have hnfin : n - 57750 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using d0_w5 ⟨n - 57750, hnfin⟩
            ·
              by_cases h6 : n < 57850
              · have hoff : 57800 ≤ n := by omega
                have hnfin : n - 57800 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using d0_w6 ⟨n - 57800, hnfin⟩
              ·
                by_cases h7 : n < 57900
                · have hoff : 57850 ≤ n := by omega
                  have hnfin : n - 57850 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using d0_w7 ⟨n - 57850, hnfin⟩
                ·
                  by_cases h8 : n < 57950
                  · have hoff : 57900 ≤ n := by omega
                    have hnfin : n - 57900 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using d0_w8 ⟨n - 57900, hnfin⟩
                  ·
                    by_cases h9 : n < 58000
                    · have hoff : 57950 ≤ n := by omega
                      have hnfin : n - 57950 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using d0_w9 ⟨n - 57950, hnfin⟩
                    ·
                      by_cases h10 : n < 58050
                      · have hoff : 58000 ≤ n := by omega
                        have hnfin : n - 58000 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using d0_w10 ⟨n - 58000, hnfin⟩
                      ·
                        by_cases h11 : n < 58100
                        · have hoff : 58050 ≤ n := by omega
                          have hnfin : n - 58050 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using d0_w11 ⟨n - 58050, hnfin⟩
                        ·
                          by_cases h12 : n < 58150
                          · have hoff : 58100 ≤ n := by omega
                            have hnfin : n - 58100 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using d0_w12 ⟨n - 58100, hnfin⟩
                          ·
                            by_cases h13 : n < 58200
                            · have hoff : 58150 ≤ n := by omega
                              have hnfin : n - 58150 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using d0_w13 ⟨n - 58150, hnfin⟩
                            ·
                              by_cases h14 : n < 58250
                              · have hoff : 58200 ≤ n := by omega
                                have hnfin : n - 58200 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using d0_w14 ⟨n - 58200, hnfin⟩
                              ·
                                by_cases h15 : n < 58300
                                · have hoff : 58250 ≤ n := by omega
                                  have hnfin : n - 58250 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using d0_w15 ⟨n - 58250, hnfin⟩
                                ·
                                  by_cases h16 : n < 58350
                                  · have hoff : 58300 ≤ n := by omega
                                    have hnfin : n - 58300 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using d0_w16 ⟨n - 58300, hnfin⟩
                                  ·
                                    by_cases h17 : n < 58400
                                    · have hoff : 58350 ≤ n := by omega
                                      have hnfin : n - 58350 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using d0_w17 ⟨n - 58350, hnfin⟩
                                    ·
                                      by_cases h18 : n < 58450
                                      · have hoff : 58400 ≤ n := by omega
                                        have hnfin : n - 58400 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using d0_w18 ⟨n - 58400, hnfin⟩
                                      ·
                                        by_cases h19 : n < 58500
                                        · have hoff : 58450 ≤ n := by omega
                                          have hnfin : n - 58450 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using d0_w19 ⟨n - 58450, hnfin⟩
                                        ·
                                          by_cases h20 : n < 58550
                                          · have hoff : 58500 ≤ n := by omega
                                            have hnfin : n - 58500 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using d0_w20 ⟨n - 58500, hnfin⟩
                                          ·
                                            by_cases h21 : n < 58600
                                            · have hoff : 58550 ≤ n := by omega
                                              have hnfin : n - 58550 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using d0_w21 ⟨n - 58550, hnfin⟩
                                            ·
                                              by_cases h22 : n < 58650
                                              · have hoff : 58600 ≤ n := by omega
                                                have hnfin : n - 58600 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using d0_w22 ⟨n - 58600, hnfin⟩
                                              ·
                                                by_cases h23 : n < 58700
                                                · have hoff : 58650 ≤ n := by omega
                                                  have hnfin : n - 58650 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using d0_w23 ⟨n - 58650, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 58750
                                                  · have hoff : 58700 ≤ n := by omega
                                                    have hnfin : n - 58700 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using d0_w24 ⟨n - 58700, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 58800
                                                    · have hoff : 58750 ≤ n := by omega
                                                      have hnfin : n - 58750 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using d0_w25 ⟨n - 58750, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 58850
                                                      · have hoff : 58800 ≤ n := by omega
                                                        have hnfin : n - 58800 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using d0_w26 ⟨n - 58800, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 58900
                                                        · have hoff : 58850 ≤ n := by omega
                                                          have hnfin : n - 58850 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using d0_w27 ⟨n - 58850, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 58950
                                                          · have hoff : 58900 ≤ n := by omega
                                                            have hnfin : n - 58900 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using d0_w28 ⟨n - 58900, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 59000
                                                            · have hoff : 58950 ≤ n := by omega
                                                              have hnfin : n - 58950 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using d0_w29 ⟨n - 58950, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 59050
                                                              · have hoff : 59000 ≤ n := by omega
                                                                have hnfin : n - 59000 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using d0_w30 ⟨n - 59000, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 59100
                                                                · have hoff : 59050 ≤ n := by omega
                                                                  have hnfin : n - 59050 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using d0_w31 ⟨n - 59050, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 59150
                                                                  · have hoff : 59100 ≤ n := by omega
                                                                    have hnfin : n - 59100 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w32 ⟨n - 59100, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 59200
                                                                    · have hoff : 59150 ≤ n := by omega
                                                                      have hnfin : n - 59150 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using d0_w33 ⟨n - 59150, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 59250
                                                                      · have hoff : 59200 ≤ n := by omega
                                                                        have hnfin : n - 59200 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using d0_w34 ⟨n - 59200, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 59300
                                                                        · have hoff : 59250 ≤ n := by omega
                                                                          have hnfin : n - 59250 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using d0_w35 ⟨n - 59250, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 59350
                                                                          · have hoff : 59300 ≤ n := by omega
                                                                            have hnfin : n - 59300 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using d0_w36 ⟨n - 59300, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 59400
                                                                            · have hoff : 59350 ≤ n := by omega
                                                                              have hnfin : n - 59350 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using d0_w37 ⟨n - 59350, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 59450
                                                                              · have hoff : 59400 ≤ n := by omega
                                                                                have hnfin : n - 59400 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using d0_w38 ⟨n - 59400, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 59500
                                                                                · have hoff : 59450 ≤ n := by omega
                                                                                  have hnfin : n - 59450 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using d0_w39 ⟨n - 59450, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 59550
                                                                                  · have hoff : 59500 ≤ n := by omega
                                                                                    have hnfin : n - 59500 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w40 ⟨n - 59500, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 59600
                                                                                    · have hoff : 59550 ≤ n := by omega
                                                                                      have hnfin : n - 59550 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using d0_w41 ⟨n - 59550, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 59650
                                                                                      · have hoff : 59600 ≤ n := by omega
                                                                                        have hnfin : n - 59600 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using d0_w42 ⟨n - 59600, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 59700
                                                                                        · have hoff : 59650 ≤ n := by omega
                                                                                          have hnfin : n - 59650 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using d0_w43 ⟨n - 59650, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 59750
                                                                                          · have hoff : 59700 ≤ n := by omega
                                                                                            have hnfin : n - 59700 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using d0_w44 ⟨n - 59700, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 59800
                                                                                            · have hoff : 59750 ≤ n := by omega
                                                                                              have hnfin : n - 59750 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using d0_w45 ⟨n - 59750, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 59850
                                                                                              · have hoff : 59800 ≤ n := by omega
                                                                                                have hnfin : n - 59800 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using d0_w46 ⟨n - 59800, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 59900
                                                                                                · have hoff : 59850 ≤ n := by omega
                                                                                                  have hnfin : n - 59850 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using d0_w47 ⟨n - 59850, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 59950
                                                                                                  · have hoff : 59900 ≤ n := by omega
                                                                                                    have hnfin : n - 59900 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w48 ⟨n - 59900, hnfin⟩
                                                                                                  · have hoff : 59950 ≤ n := by omega
                                                                                                    have hnfin : n - 59950 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w49 ⟨n - 59950, hnfin⟩
theorem dim1_range (n : ℕ) (hn0 : 57500 ≤ n) (hn1 : n < 60000) :
    dimF (arg1 n) ≤ dimF n := by
  by_cases h0 : n < 57550
  · have hoff : 57500 ≤ n := by omega
    have hnfin : n - 57500 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using d1_w0 ⟨n - 57500, hnfin⟩
  ·
    by_cases h1 : n < 57600
    · have hoff : 57550 ≤ n := by omega
      have hnfin : n - 57550 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using d1_w1 ⟨n - 57550, hnfin⟩
    ·
      by_cases h2 : n < 57650
      · have hoff : 57600 ≤ n := by omega
        have hnfin : n - 57600 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using d1_w2 ⟨n - 57600, hnfin⟩
      ·
        by_cases h3 : n < 57700
        · have hoff : 57650 ≤ n := by omega
          have hnfin : n - 57650 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using d1_w3 ⟨n - 57650, hnfin⟩
        ·
          by_cases h4 : n < 57750
          · have hoff : 57700 ≤ n := by omega
            have hnfin : n - 57700 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using d1_w4 ⟨n - 57700, hnfin⟩
          ·
            by_cases h5 : n < 57800
            · have hoff : 57750 ≤ n := by omega
              have hnfin : n - 57750 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using d1_w5 ⟨n - 57750, hnfin⟩
            ·
              by_cases h6 : n < 57850
              · have hoff : 57800 ≤ n := by omega
                have hnfin : n - 57800 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using d1_w6 ⟨n - 57800, hnfin⟩
              ·
                by_cases h7 : n < 57900
                · have hoff : 57850 ≤ n := by omega
                  have hnfin : n - 57850 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using d1_w7 ⟨n - 57850, hnfin⟩
                ·
                  by_cases h8 : n < 57950
                  · have hoff : 57900 ≤ n := by omega
                    have hnfin : n - 57900 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using d1_w8 ⟨n - 57900, hnfin⟩
                  ·
                    by_cases h9 : n < 58000
                    · have hoff : 57950 ≤ n := by omega
                      have hnfin : n - 57950 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using d1_w9 ⟨n - 57950, hnfin⟩
                    ·
                      by_cases h10 : n < 58050
                      · have hoff : 58000 ≤ n := by omega
                        have hnfin : n - 58000 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using d1_w10 ⟨n - 58000, hnfin⟩
                      ·
                        by_cases h11 : n < 58100
                        · have hoff : 58050 ≤ n := by omega
                          have hnfin : n - 58050 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using d1_w11 ⟨n - 58050, hnfin⟩
                        ·
                          by_cases h12 : n < 58150
                          · have hoff : 58100 ≤ n := by omega
                            have hnfin : n - 58100 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using d1_w12 ⟨n - 58100, hnfin⟩
                          ·
                            by_cases h13 : n < 58200
                            · have hoff : 58150 ≤ n := by omega
                              have hnfin : n - 58150 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using d1_w13 ⟨n - 58150, hnfin⟩
                            ·
                              by_cases h14 : n < 58250
                              · have hoff : 58200 ≤ n := by omega
                                have hnfin : n - 58200 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using d1_w14 ⟨n - 58200, hnfin⟩
                              ·
                                by_cases h15 : n < 58300
                                · have hoff : 58250 ≤ n := by omega
                                  have hnfin : n - 58250 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using d1_w15 ⟨n - 58250, hnfin⟩
                                ·
                                  by_cases h16 : n < 58350
                                  · have hoff : 58300 ≤ n := by omega
                                    have hnfin : n - 58300 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using d1_w16 ⟨n - 58300, hnfin⟩
                                  ·
                                    by_cases h17 : n < 58400
                                    · have hoff : 58350 ≤ n := by omega
                                      have hnfin : n - 58350 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using d1_w17 ⟨n - 58350, hnfin⟩
                                    ·
                                      by_cases h18 : n < 58450
                                      · have hoff : 58400 ≤ n := by omega
                                        have hnfin : n - 58400 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using d1_w18 ⟨n - 58400, hnfin⟩
                                      ·
                                        by_cases h19 : n < 58500
                                        · have hoff : 58450 ≤ n := by omega
                                          have hnfin : n - 58450 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using d1_w19 ⟨n - 58450, hnfin⟩
                                        ·
                                          by_cases h20 : n < 58550
                                          · have hoff : 58500 ≤ n := by omega
                                            have hnfin : n - 58500 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using d1_w20 ⟨n - 58500, hnfin⟩
                                          ·
                                            by_cases h21 : n < 58600
                                            · have hoff : 58550 ≤ n := by omega
                                              have hnfin : n - 58550 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using d1_w21 ⟨n - 58550, hnfin⟩
                                            ·
                                              by_cases h22 : n < 58650
                                              · have hoff : 58600 ≤ n := by omega
                                                have hnfin : n - 58600 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using d1_w22 ⟨n - 58600, hnfin⟩
                                              ·
                                                by_cases h23 : n < 58700
                                                · have hoff : 58650 ≤ n := by omega
                                                  have hnfin : n - 58650 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using d1_w23 ⟨n - 58650, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 58750
                                                  · have hoff : 58700 ≤ n := by omega
                                                    have hnfin : n - 58700 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using d1_w24 ⟨n - 58700, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 58800
                                                    · have hoff : 58750 ≤ n := by omega
                                                      have hnfin : n - 58750 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using d1_w25 ⟨n - 58750, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 58850
                                                      · have hoff : 58800 ≤ n := by omega
                                                        have hnfin : n - 58800 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using d1_w26 ⟨n - 58800, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 58900
                                                        · have hoff : 58850 ≤ n := by omega
                                                          have hnfin : n - 58850 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using d1_w27 ⟨n - 58850, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 58950
                                                          · have hoff : 58900 ≤ n := by omega
                                                            have hnfin : n - 58900 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using d1_w28 ⟨n - 58900, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 59000
                                                            · have hoff : 58950 ≤ n := by omega
                                                              have hnfin : n - 58950 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using d1_w29 ⟨n - 58950, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 59050
                                                              · have hoff : 59000 ≤ n := by omega
                                                                have hnfin : n - 59000 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using d1_w30 ⟨n - 59000, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 59100
                                                                · have hoff : 59050 ≤ n := by omega
                                                                  have hnfin : n - 59050 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using d1_w31 ⟨n - 59050, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 59150
                                                                  · have hoff : 59100 ≤ n := by omega
                                                                    have hnfin : n - 59100 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w32 ⟨n - 59100, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 59200
                                                                    · have hoff : 59150 ≤ n := by omega
                                                                      have hnfin : n - 59150 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using d1_w33 ⟨n - 59150, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 59250
                                                                      · have hoff : 59200 ≤ n := by omega
                                                                        have hnfin : n - 59200 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using d1_w34 ⟨n - 59200, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 59300
                                                                        · have hoff : 59250 ≤ n := by omega
                                                                          have hnfin : n - 59250 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using d1_w35 ⟨n - 59250, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 59350
                                                                          · have hoff : 59300 ≤ n := by omega
                                                                            have hnfin : n - 59300 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using d1_w36 ⟨n - 59300, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 59400
                                                                            · have hoff : 59350 ≤ n := by omega
                                                                              have hnfin : n - 59350 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using d1_w37 ⟨n - 59350, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 59450
                                                                              · have hoff : 59400 ≤ n := by omega
                                                                                have hnfin : n - 59400 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using d1_w38 ⟨n - 59400, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 59500
                                                                                · have hoff : 59450 ≤ n := by omega
                                                                                  have hnfin : n - 59450 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using d1_w39 ⟨n - 59450, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 59550
                                                                                  · have hoff : 59500 ≤ n := by omega
                                                                                    have hnfin : n - 59500 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w40 ⟨n - 59500, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 59600
                                                                                    · have hoff : 59550 ≤ n := by omega
                                                                                      have hnfin : n - 59550 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using d1_w41 ⟨n - 59550, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 59650
                                                                                      · have hoff : 59600 ≤ n := by omega
                                                                                        have hnfin : n - 59600 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using d1_w42 ⟨n - 59600, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 59700
                                                                                        · have hoff : 59650 ≤ n := by omega
                                                                                          have hnfin : n - 59650 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using d1_w43 ⟨n - 59650, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 59750
                                                                                          · have hoff : 59700 ≤ n := by omega
                                                                                            have hnfin : n - 59700 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using d1_w44 ⟨n - 59700, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 59800
                                                                                            · have hoff : 59750 ≤ n := by omega
                                                                                              have hnfin : n - 59750 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using d1_w45 ⟨n - 59750, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 59850
                                                                                              · have hoff : 59800 ≤ n := by omega
                                                                                                have hnfin : n - 59800 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using d1_w46 ⟨n - 59800, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 59900
                                                                                                · have hoff : 59850 ≤ n := by omega
                                                                                                  have hnfin : n - 59850 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using d1_w47 ⟨n - 59850, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 59950
                                                                                                  · have hoff : 59900 ≤ n := by omega
                                                                                                    have hnfin : n - 59900 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w48 ⟨n - 59900, hnfin⟩
                                                                                                  · have hoff : 59950 ≤ n := by omega
                                                                                                    have hnfin : n - 59950 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w49 ⟨n - 59950, hnfin⟩
end IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA23


