-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankArgDimLeA21
-- name    : IntMul_Kappa_R8_Data_BitOppbankArgDimLeA21
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T09:43:08.247202+00:00
-- url     : https://prove2.me/theorems/ba85307c-8c2b-423f-ab4b-821592310e60
-- title:
--   argRel dim-inequality certificates on published Pnd, pack A21, nodes 52500–54999
-- statement:
--   # Dimension inequality certificates (published Pnd), pack $A_{21}$
--
--   Range consolidators for $n\in[52500,55000)$:
--   $$\dim F(\mathrm{arg}_0 n)\le \dim F(n)\qquad\text{and}\qquad\dim F(\mathrm{arg}_1 n)\le \dim F(n).$$
--
--   Here $\mathrm{arg}_0 n=\mathrm{argF}(n)\mathbin{\&}65535$ and $\mathrm{arg}_1 n=\mathrm{argF}(n)\gg 16$. Proved on the published (non-Fix) `argF` / `dimF` by Lean `decide` windows of 50 (last window of pack $A_{24}$ is size 28 at offset 62450), then `dim0_range` / `dim1_range`. Used for `argRel_dim_le` on published `argRel`.
--
--   Formalization note. The pack lives in namespace `IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA21` and imports only the published Pnd and SupG data.
-- source:
--   R8 BitOppbank FormalOK published Pnd (non-Fix) ArgDimLeA

-- ArgDimLeA21: dim inequality certificates on published Pnd only, nodes [52500, 55000)
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
namespace IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA21
def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16
theorem d0_w0 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 52500)) ≤ dimF (n.val + 52500) := by decide
theorem d1_w0 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 52500)) ≤ dimF (n.val + 52500) := by decide
theorem d0_w1 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 52550)) ≤ dimF (n.val + 52550) := by decide
theorem d1_w1 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 52550)) ≤ dimF (n.val + 52550) := by decide
theorem d0_w2 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 52600)) ≤ dimF (n.val + 52600) := by decide
theorem d1_w2 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 52600)) ≤ dimF (n.val + 52600) := by decide
theorem d0_w3 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 52650)) ≤ dimF (n.val + 52650) := by decide
theorem d1_w3 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 52650)) ≤ dimF (n.val + 52650) := by decide
theorem d0_w4 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 52700)) ≤ dimF (n.val + 52700) := by decide
theorem d1_w4 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 52700)) ≤ dimF (n.val + 52700) := by decide
theorem d0_w5 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 52750)) ≤ dimF (n.val + 52750) := by decide
theorem d1_w5 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 52750)) ≤ dimF (n.val + 52750) := by decide
theorem d0_w6 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 52800)) ≤ dimF (n.val + 52800) := by decide
theorem d1_w6 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 52800)) ≤ dimF (n.val + 52800) := by decide
theorem d0_w7 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 52850)) ≤ dimF (n.val + 52850) := by decide
theorem d1_w7 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 52850)) ≤ dimF (n.val + 52850) := by decide
theorem d0_w8 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 52900)) ≤ dimF (n.val + 52900) := by decide
theorem d1_w8 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 52900)) ≤ dimF (n.val + 52900) := by decide
theorem d0_w9 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 52950)) ≤ dimF (n.val + 52950) := by decide
theorem d1_w9 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 52950)) ≤ dimF (n.val + 52950) := by decide
theorem d0_w10 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 53000)) ≤ dimF (n.val + 53000) := by decide
theorem d1_w10 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 53000)) ≤ dimF (n.val + 53000) := by decide
theorem d0_w11 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 53050)) ≤ dimF (n.val + 53050) := by decide
theorem d1_w11 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 53050)) ≤ dimF (n.val + 53050) := by decide
theorem d0_w12 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 53100)) ≤ dimF (n.val + 53100) := by decide
theorem d1_w12 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 53100)) ≤ dimF (n.val + 53100) := by decide
theorem d0_w13 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 53150)) ≤ dimF (n.val + 53150) := by decide
theorem d1_w13 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 53150)) ≤ dimF (n.val + 53150) := by decide
theorem d0_w14 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 53200)) ≤ dimF (n.val + 53200) := by decide
theorem d1_w14 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 53200)) ≤ dimF (n.val + 53200) := by decide
theorem d0_w15 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 53250)) ≤ dimF (n.val + 53250) := by decide
theorem d1_w15 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 53250)) ≤ dimF (n.val + 53250) := by decide
theorem d0_w16 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 53300)) ≤ dimF (n.val + 53300) := by decide
theorem d1_w16 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 53300)) ≤ dimF (n.val + 53300) := by decide
theorem d0_w17 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 53350)) ≤ dimF (n.val + 53350) := by decide
theorem d1_w17 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 53350)) ≤ dimF (n.val + 53350) := by decide
theorem d0_w18 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 53400)) ≤ dimF (n.val + 53400) := by decide
theorem d1_w18 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 53400)) ≤ dimF (n.val + 53400) := by decide
theorem d0_w19 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 53450)) ≤ dimF (n.val + 53450) := by decide
theorem d1_w19 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 53450)) ≤ dimF (n.val + 53450) := by decide
theorem d0_w20 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 53500)) ≤ dimF (n.val + 53500) := by decide
theorem d1_w20 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 53500)) ≤ dimF (n.val + 53500) := by decide
theorem d0_w21 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 53550)) ≤ dimF (n.val + 53550) := by decide
theorem d1_w21 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 53550)) ≤ dimF (n.val + 53550) := by decide
theorem d0_w22 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 53600)) ≤ dimF (n.val + 53600) := by decide
theorem d1_w22 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 53600)) ≤ dimF (n.val + 53600) := by decide
theorem d0_w23 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 53650)) ≤ dimF (n.val + 53650) := by decide
theorem d1_w23 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 53650)) ≤ dimF (n.val + 53650) := by decide
theorem d0_w24 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 53700)) ≤ dimF (n.val + 53700) := by decide
theorem d1_w24 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 53700)) ≤ dimF (n.val + 53700) := by decide
theorem d0_w25 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 53750)) ≤ dimF (n.val + 53750) := by decide
theorem d1_w25 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 53750)) ≤ dimF (n.val + 53750) := by decide
theorem d0_w26 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 53800)) ≤ dimF (n.val + 53800) := by decide
theorem d1_w26 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 53800)) ≤ dimF (n.val + 53800) := by decide
theorem d0_w27 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 53850)) ≤ dimF (n.val + 53850) := by decide
theorem d1_w27 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 53850)) ≤ dimF (n.val + 53850) := by decide
theorem d0_w28 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 53900)) ≤ dimF (n.val + 53900) := by decide
theorem d1_w28 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 53900)) ≤ dimF (n.val + 53900) := by decide
theorem d0_w29 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 53950)) ≤ dimF (n.val + 53950) := by decide
theorem d1_w29 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 53950)) ≤ dimF (n.val + 53950) := by decide
theorem d0_w30 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 54000)) ≤ dimF (n.val + 54000) := by decide
theorem d1_w30 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 54000)) ≤ dimF (n.val + 54000) := by decide
theorem d0_w31 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 54050)) ≤ dimF (n.val + 54050) := by decide
theorem d1_w31 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 54050)) ≤ dimF (n.val + 54050) := by decide
theorem d0_w32 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 54100)) ≤ dimF (n.val + 54100) := by decide
theorem d1_w32 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 54100)) ≤ dimF (n.val + 54100) := by decide
theorem d0_w33 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 54150)) ≤ dimF (n.val + 54150) := by decide
theorem d1_w33 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 54150)) ≤ dimF (n.val + 54150) := by decide
theorem d0_w34 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 54200)) ≤ dimF (n.val + 54200) := by decide
theorem d1_w34 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 54200)) ≤ dimF (n.val + 54200) := by decide
theorem d0_w35 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 54250)) ≤ dimF (n.val + 54250) := by decide
theorem d1_w35 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 54250)) ≤ dimF (n.val + 54250) := by decide
theorem d0_w36 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 54300)) ≤ dimF (n.val + 54300) := by decide
theorem d1_w36 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 54300)) ≤ dimF (n.val + 54300) := by decide
theorem d0_w37 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 54350)) ≤ dimF (n.val + 54350) := by decide
theorem d1_w37 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 54350)) ≤ dimF (n.val + 54350) := by decide
theorem d0_w38 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 54400)) ≤ dimF (n.val + 54400) := by decide
theorem d1_w38 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 54400)) ≤ dimF (n.val + 54400) := by decide
theorem d0_w39 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 54450)) ≤ dimF (n.val + 54450) := by decide
theorem d1_w39 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 54450)) ≤ dimF (n.val + 54450) := by decide
theorem d0_w40 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 54500)) ≤ dimF (n.val + 54500) := by decide
theorem d1_w40 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 54500)) ≤ dimF (n.val + 54500) := by decide
theorem d0_w41 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 54550)) ≤ dimF (n.val + 54550) := by decide
theorem d1_w41 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 54550)) ≤ dimF (n.val + 54550) := by decide
theorem d0_w42 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 54600)) ≤ dimF (n.val + 54600) := by decide
theorem d1_w42 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 54600)) ≤ dimF (n.val + 54600) := by decide
theorem d0_w43 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 54650)) ≤ dimF (n.val + 54650) := by decide
theorem d1_w43 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 54650)) ≤ dimF (n.val + 54650) := by decide
theorem d0_w44 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 54700)) ≤ dimF (n.val + 54700) := by decide
theorem d1_w44 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 54700)) ≤ dimF (n.val + 54700) := by decide
theorem d0_w45 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 54750)) ≤ dimF (n.val + 54750) := by decide
theorem d1_w45 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 54750)) ≤ dimF (n.val + 54750) := by decide
theorem d0_w46 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 54800)) ≤ dimF (n.val + 54800) := by decide
theorem d1_w46 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 54800)) ≤ dimF (n.val + 54800) := by decide
theorem d0_w47 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 54850)) ≤ dimF (n.val + 54850) := by decide
theorem d1_w47 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 54850)) ≤ dimF (n.val + 54850) := by decide
theorem d0_w48 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 54900)) ≤ dimF (n.val + 54900) := by decide
theorem d1_w48 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 54900)) ≤ dimF (n.val + 54900) := by decide
theorem d0_w49 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 54950)) ≤ dimF (n.val + 54950) := by decide
theorem d1_w49 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 54950)) ≤ dimF (n.val + 54950) := by decide
theorem dim0_range (n : ℕ) (hn0 : 52500 ≤ n) (hn1 : n < 55000) :
    dimF (arg0 n) ≤ dimF n := by
  by_cases h0 : n < 52550
  · have hoff : 52500 ≤ n := by omega
    have hnfin : n - 52500 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using d0_w0 ⟨n - 52500, hnfin⟩
  ·
    by_cases h1 : n < 52600
    · have hoff : 52550 ≤ n := by omega
      have hnfin : n - 52550 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using d0_w1 ⟨n - 52550, hnfin⟩
    ·
      by_cases h2 : n < 52650
      · have hoff : 52600 ≤ n := by omega
        have hnfin : n - 52600 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using d0_w2 ⟨n - 52600, hnfin⟩
      ·
        by_cases h3 : n < 52700
        · have hoff : 52650 ≤ n := by omega
          have hnfin : n - 52650 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using d0_w3 ⟨n - 52650, hnfin⟩
        ·
          by_cases h4 : n < 52750
          · have hoff : 52700 ≤ n := by omega
            have hnfin : n - 52700 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using d0_w4 ⟨n - 52700, hnfin⟩
          ·
            by_cases h5 : n < 52800
            · have hoff : 52750 ≤ n := by omega
              have hnfin : n - 52750 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using d0_w5 ⟨n - 52750, hnfin⟩
            ·
              by_cases h6 : n < 52850
              · have hoff : 52800 ≤ n := by omega
                have hnfin : n - 52800 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using d0_w6 ⟨n - 52800, hnfin⟩
              ·
                by_cases h7 : n < 52900
                · have hoff : 52850 ≤ n := by omega
                  have hnfin : n - 52850 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using d0_w7 ⟨n - 52850, hnfin⟩
                ·
                  by_cases h8 : n < 52950
                  · have hoff : 52900 ≤ n := by omega
                    have hnfin : n - 52900 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using d0_w8 ⟨n - 52900, hnfin⟩
                  ·
                    by_cases h9 : n < 53000
                    · have hoff : 52950 ≤ n := by omega
                      have hnfin : n - 52950 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using d0_w9 ⟨n - 52950, hnfin⟩
                    ·
                      by_cases h10 : n < 53050
                      · have hoff : 53000 ≤ n := by omega
                        have hnfin : n - 53000 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using d0_w10 ⟨n - 53000, hnfin⟩
                      ·
                        by_cases h11 : n < 53100
                        · have hoff : 53050 ≤ n := by omega
                          have hnfin : n - 53050 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using d0_w11 ⟨n - 53050, hnfin⟩
                        ·
                          by_cases h12 : n < 53150
                          · have hoff : 53100 ≤ n := by omega
                            have hnfin : n - 53100 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using d0_w12 ⟨n - 53100, hnfin⟩
                          ·
                            by_cases h13 : n < 53200
                            · have hoff : 53150 ≤ n := by omega
                              have hnfin : n - 53150 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using d0_w13 ⟨n - 53150, hnfin⟩
                            ·
                              by_cases h14 : n < 53250
                              · have hoff : 53200 ≤ n := by omega
                                have hnfin : n - 53200 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using d0_w14 ⟨n - 53200, hnfin⟩
                              ·
                                by_cases h15 : n < 53300
                                · have hoff : 53250 ≤ n := by omega
                                  have hnfin : n - 53250 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using d0_w15 ⟨n - 53250, hnfin⟩
                                ·
                                  by_cases h16 : n < 53350
                                  · have hoff : 53300 ≤ n := by omega
                                    have hnfin : n - 53300 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using d0_w16 ⟨n - 53300, hnfin⟩
                                  ·
                                    by_cases h17 : n < 53400
                                    · have hoff : 53350 ≤ n := by omega
                                      have hnfin : n - 53350 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using d0_w17 ⟨n - 53350, hnfin⟩
                                    ·
                                      by_cases h18 : n < 53450
                                      · have hoff : 53400 ≤ n := by omega
                                        have hnfin : n - 53400 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using d0_w18 ⟨n - 53400, hnfin⟩
                                      ·
                                        by_cases h19 : n < 53500
                                        · have hoff : 53450 ≤ n := by omega
                                          have hnfin : n - 53450 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using d0_w19 ⟨n - 53450, hnfin⟩
                                        ·
                                          by_cases h20 : n < 53550
                                          · have hoff : 53500 ≤ n := by omega
                                            have hnfin : n - 53500 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using d0_w20 ⟨n - 53500, hnfin⟩
                                          ·
                                            by_cases h21 : n < 53600
                                            · have hoff : 53550 ≤ n := by omega
                                              have hnfin : n - 53550 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using d0_w21 ⟨n - 53550, hnfin⟩
                                            ·
                                              by_cases h22 : n < 53650
                                              · have hoff : 53600 ≤ n := by omega
                                                have hnfin : n - 53600 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using d0_w22 ⟨n - 53600, hnfin⟩
                                              ·
                                                by_cases h23 : n < 53700
                                                · have hoff : 53650 ≤ n := by omega
                                                  have hnfin : n - 53650 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using d0_w23 ⟨n - 53650, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 53750
                                                  · have hoff : 53700 ≤ n := by omega
                                                    have hnfin : n - 53700 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using d0_w24 ⟨n - 53700, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 53800
                                                    · have hoff : 53750 ≤ n := by omega
                                                      have hnfin : n - 53750 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using d0_w25 ⟨n - 53750, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 53850
                                                      · have hoff : 53800 ≤ n := by omega
                                                        have hnfin : n - 53800 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using d0_w26 ⟨n - 53800, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 53900
                                                        · have hoff : 53850 ≤ n := by omega
                                                          have hnfin : n - 53850 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using d0_w27 ⟨n - 53850, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 53950
                                                          · have hoff : 53900 ≤ n := by omega
                                                            have hnfin : n - 53900 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using d0_w28 ⟨n - 53900, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 54000
                                                            · have hoff : 53950 ≤ n := by omega
                                                              have hnfin : n - 53950 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using d0_w29 ⟨n - 53950, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 54050
                                                              · have hoff : 54000 ≤ n := by omega
                                                                have hnfin : n - 54000 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using d0_w30 ⟨n - 54000, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 54100
                                                                · have hoff : 54050 ≤ n := by omega
                                                                  have hnfin : n - 54050 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using d0_w31 ⟨n - 54050, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 54150
                                                                  · have hoff : 54100 ≤ n := by omega
                                                                    have hnfin : n - 54100 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w32 ⟨n - 54100, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 54200
                                                                    · have hoff : 54150 ≤ n := by omega
                                                                      have hnfin : n - 54150 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using d0_w33 ⟨n - 54150, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 54250
                                                                      · have hoff : 54200 ≤ n := by omega
                                                                        have hnfin : n - 54200 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using d0_w34 ⟨n - 54200, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 54300
                                                                        · have hoff : 54250 ≤ n := by omega
                                                                          have hnfin : n - 54250 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using d0_w35 ⟨n - 54250, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 54350
                                                                          · have hoff : 54300 ≤ n := by omega
                                                                            have hnfin : n - 54300 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using d0_w36 ⟨n - 54300, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 54400
                                                                            · have hoff : 54350 ≤ n := by omega
                                                                              have hnfin : n - 54350 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using d0_w37 ⟨n - 54350, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 54450
                                                                              · have hoff : 54400 ≤ n := by omega
                                                                                have hnfin : n - 54400 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using d0_w38 ⟨n - 54400, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 54500
                                                                                · have hoff : 54450 ≤ n := by omega
                                                                                  have hnfin : n - 54450 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using d0_w39 ⟨n - 54450, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 54550
                                                                                  · have hoff : 54500 ≤ n := by omega
                                                                                    have hnfin : n - 54500 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w40 ⟨n - 54500, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 54600
                                                                                    · have hoff : 54550 ≤ n := by omega
                                                                                      have hnfin : n - 54550 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using d0_w41 ⟨n - 54550, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 54650
                                                                                      · have hoff : 54600 ≤ n := by omega
                                                                                        have hnfin : n - 54600 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using d0_w42 ⟨n - 54600, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 54700
                                                                                        · have hoff : 54650 ≤ n := by omega
                                                                                          have hnfin : n - 54650 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using d0_w43 ⟨n - 54650, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 54750
                                                                                          · have hoff : 54700 ≤ n := by omega
                                                                                            have hnfin : n - 54700 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using d0_w44 ⟨n - 54700, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 54800
                                                                                            · have hoff : 54750 ≤ n := by omega
                                                                                              have hnfin : n - 54750 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using d0_w45 ⟨n - 54750, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 54850
                                                                                              · have hoff : 54800 ≤ n := by omega
                                                                                                have hnfin : n - 54800 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using d0_w46 ⟨n - 54800, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 54900
                                                                                                · have hoff : 54850 ≤ n := by omega
                                                                                                  have hnfin : n - 54850 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using d0_w47 ⟨n - 54850, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 54950
                                                                                                  · have hoff : 54900 ≤ n := by omega
                                                                                                    have hnfin : n - 54900 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w48 ⟨n - 54900, hnfin⟩
                                                                                                  · have hoff : 54950 ≤ n := by omega
                                                                                                    have hnfin : n - 54950 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w49 ⟨n - 54950, hnfin⟩
theorem dim1_range (n : ℕ) (hn0 : 52500 ≤ n) (hn1 : n < 55000) :
    dimF (arg1 n) ≤ dimF n := by
  by_cases h0 : n < 52550
  · have hoff : 52500 ≤ n := by omega
    have hnfin : n - 52500 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using d1_w0 ⟨n - 52500, hnfin⟩
  ·
    by_cases h1 : n < 52600
    · have hoff : 52550 ≤ n := by omega
      have hnfin : n - 52550 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using d1_w1 ⟨n - 52550, hnfin⟩
    ·
      by_cases h2 : n < 52650
      · have hoff : 52600 ≤ n := by omega
        have hnfin : n - 52600 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using d1_w2 ⟨n - 52600, hnfin⟩
      ·
        by_cases h3 : n < 52700
        · have hoff : 52650 ≤ n := by omega
          have hnfin : n - 52650 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using d1_w3 ⟨n - 52650, hnfin⟩
        ·
          by_cases h4 : n < 52750
          · have hoff : 52700 ≤ n := by omega
            have hnfin : n - 52700 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using d1_w4 ⟨n - 52700, hnfin⟩
          ·
            by_cases h5 : n < 52800
            · have hoff : 52750 ≤ n := by omega
              have hnfin : n - 52750 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using d1_w5 ⟨n - 52750, hnfin⟩
            ·
              by_cases h6 : n < 52850
              · have hoff : 52800 ≤ n := by omega
                have hnfin : n - 52800 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using d1_w6 ⟨n - 52800, hnfin⟩
              ·
                by_cases h7 : n < 52900
                · have hoff : 52850 ≤ n := by omega
                  have hnfin : n - 52850 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using d1_w7 ⟨n - 52850, hnfin⟩
                ·
                  by_cases h8 : n < 52950
                  · have hoff : 52900 ≤ n := by omega
                    have hnfin : n - 52900 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using d1_w8 ⟨n - 52900, hnfin⟩
                  ·
                    by_cases h9 : n < 53000
                    · have hoff : 52950 ≤ n := by omega
                      have hnfin : n - 52950 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using d1_w9 ⟨n - 52950, hnfin⟩
                    ·
                      by_cases h10 : n < 53050
                      · have hoff : 53000 ≤ n := by omega
                        have hnfin : n - 53000 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using d1_w10 ⟨n - 53000, hnfin⟩
                      ·
                        by_cases h11 : n < 53100
                        · have hoff : 53050 ≤ n := by omega
                          have hnfin : n - 53050 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using d1_w11 ⟨n - 53050, hnfin⟩
                        ·
                          by_cases h12 : n < 53150
                          · have hoff : 53100 ≤ n := by omega
                            have hnfin : n - 53100 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using d1_w12 ⟨n - 53100, hnfin⟩
                          ·
                            by_cases h13 : n < 53200
                            · have hoff : 53150 ≤ n := by omega
                              have hnfin : n - 53150 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using d1_w13 ⟨n - 53150, hnfin⟩
                            ·
                              by_cases h14 : n < 53250
                              · have hoff : 53200 ≤ n := by omega
                                have hnfin : n - 53200 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using d1_w14 ⟨n - 53200, hnfin⟩
                              ·
                                by_cases h15 : n < 53300
                                · have hoff : 53250 ≤ n := by omega
                                  have hnfin : n - 53250 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using d1_w15 ⟨n - 53250, hnfin⟩
                                ·
                                  by_cases h16 : n < 53350
                                  · have hoff : 53300 ≤ n := by omega
                                    have hnfin : n - 53300 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using d1_w16 ⟨n - 53300, hnfin⟩
                                  ·
                                    by_cases h17 : n < 53400
                                    · have hoff : 53350 ≤ n := by omega
                                      have hnfin : n - 53350 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using d1_w17 ⟨n - 53350, hnfin⟩
                                    ·
                                      by_cases h18 : n < 53450
                                      · have hoff : 53400 ≤ n := by omega
                                        have hnfin : n - 53400 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using d1_w18 ⟨n - 53400, hnfin⟩
                                      ·
                                        by_cases h19 : n < 53500
                                        · have hoff : 53450 ≤ n := by omega
                                          have hnfin : n - 53450 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using d1_w19 ⟨n - 53450, hnfin⟩
                                        ·
                                          by_cases h20 : n < 53550
                                          · have hoff : 53500 ≤ n := by omega
                                            have hnfin : n - 53500 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using d1_w20 ⟨n - 53500, hnfin⟩
                                          ·
                                            by_cases h21 : n < 53600
                                            · have hoff : 53550 ≤ n := by omega
                                              have hnfin : n - 53550 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using d1_w21 ⟨n - 53550, hnfin⟩
                                            ·
                                              by_cases h22 : n < 53650
                                              · have hoff : 53600 ≤ n := by omega
                                                have hnfin : n - 53600 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using d1_w22 ⟨n - 53600, hnfin⟩
                                              ·
                                                by_cases h23 : n < 53700
                                                · have hoff : 53650 ≤ n := by omega
                                                  have hnfin : n - 53650 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using d1_w23 ⟨n - 53650, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 53750
                                                  · have hoff : 53700 ≤ n := by omega
                                                    have hnfin : n - 53700 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using d1_w24 ⟨n - 53700, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 53800
                                                    · have hoff : 53750 ≤ n := by omega
                                                      have hnfin : n - 53750 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using d1_w25 ⟨n - 53750, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 53850
                                                      · have hoff : 53800 ≤ n := by omega
                                                        have hnfin : n - 53800 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using d1_w26 ⟨n - 53800, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 53900
                                                        · have hoff : 53850 ≤ n := by omega
                                                          have hnfin : n - 53850 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using d1_w27 ⟨n - 53850, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 53950
                                                          · have hoff : 53900 ≤ n := by omega
                                                            have hnfin : n - 53900 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using d1_w28 ⟨n - 53900, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 54000
                                                            · have hoff : 53950 ≤ n := by omega
                                                              have hnfin : n - 53950 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using d1_w29 ⟨n - 53950, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 54050
                                                              · have hoff : 54000 ≤ n := by omega
                                                                have hnfin : n - 54000 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using d1_w30 ⟨n - 54000, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 54100
                                                                · have hoff : 54050 ≤ n := by omega
                                                                  have hnfin : n - 54050 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using d1_w31 ⟨n - 54050, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 54150
                                                                  · have hoff : 54100 ≤ n := by omega
                                                                    have hnfin : n - 54100 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w32 ⟨n - 54100, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 54200
                                                                    · have hoff : 54150 ≤ n := by omega
                                                                      have hnfin : n - 54150 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using d1_w33 ⟨n - 54150, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 54250
                                                                      · have hoff : 54200 ≤ n := by omega
                                                                        have hnfin : n - 54200 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using d1_w34 ⟨n - 54200, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 54300
                                                                        · have hoff : 54250 ≤ n := by omega
                                                                          have hnfin : n - 54250 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using d1_w35 ⟨n - 54250, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 54350
                                                                          · have hoff : 54300 ≤ n := by omega
                                                                            have hnfin : n - 54300 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using d1_w36 ⟨n - 54300, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 54400
                                                                            · have hoff : 54350 ≤ n := by omega
                                                                              have hnfin : n - 54350 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using d1_w37 ⟨n - 54350, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 54450
                                                                              · have hoff : 54400 ≤ n := by omega
                                                                                have hnfin : n - 54400 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using d1_w38 ⟨n - 54400, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 54500
                                                                                · have hoff : 54450 ≤ n := by omega
                                                                                  have hnfin : n - 54450 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using d1_w39 ⟨n - 54450, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 54550
                                                                                  · have hoff : 54500 ≤ n := by omega
                                                                                    have hnfin : n - 54500 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w40 ⟨n - 54500, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 54600
                                                                                    · have hoff : 54550 ≤ n := by omega
                                                                                      have hnfin : n - 54550 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using d1_w41 ⟨n - 54550, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 54650
                                                                                      · have hoff : 54600 ≤ n := by omega
                                                                                        have hnfin : n - 54600 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using d1_w42 ⟨n - 54600, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 54700
                                                                                        · have hoff : 54650 ≤ n := by omega
                                                                                          have hnfin : n - 54650 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using d1_w43 ⟨n - 54650, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 54750
                                                                                          · have hoff : 54700 ≤ n := by omega
                                                                                            have hnfin : n - 54700 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using d1_w44 ⟨n - 54700, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 54800
                                                                                            · have hoff : 54750 ≤ n := by omega
                                                                                              have hnfin : n - 54750 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using d1_w45 ⟨n - 54750, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 54850
                                                                                              · have hoff : 54800 ≤ n := by omega
                                                                                                have hnfin : n - 54800 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using d1_w46 ⟨n - 54800, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 54900
                                                                                                · have hoff : 54850 ≤ n := by omega
                                                                                                  have hnfin : n - 54850 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using d1_w47 ⟨n - 54850, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 54950
                                                                                                  · have hoff : 54900 ≤ n := by omega
                                                                                                    have hnfin : n - 54900 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w48 ⟨n - 54900, hnfin⟩
                                                                                                  · have hoff : 54950 ≤ n := by omega
                                                                                                    have hnfin : n - 54950 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w49 ⟨n - 54950, hnfin⟩
end IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA21


