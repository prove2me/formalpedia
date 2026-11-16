-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankArgDimLeA10
-- name    : IntMul_Kappa_R8_Data_BitOppbankArgDimLeA10
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T09:43:00.660042+00:00
-- url     : https://prove2.me/theorems/109bf10d-96f5-4b81-be24-8de5d0b70393
-- title:
--   argRel dim-inequality certificates on published Pnd, pack A10, nodes 25000–27499
-- statement:
--   # Dimension inequality certificates (published Pnd), pack $A_{10}$
--
--   Range consolidators for $n\in[25000,27500)$:
--   $$\dim F(\mathrm{arg}_0 n)\le \dim F(n)\qquad\text{and}\qquad\dim F(\mathrm{arg}_1 n)\le \dim F(n).$$
--
--   Here $\mathrm{arg}_0 n=\mathrm{argF}(n)\mathbin{\&}65535$ and $\mathrm{arg}_1 n=\mathrm{argF}(n)\gg 16$. Proved on the published (non-Fix) `argF` / `dimF` by Lean `decide` windows of 50 (last window of pack $A_{24}$ is size 28 at offset 62450), then `dim0_range` / `dim1_range`. Used for `argRel_dim_le` on published `argRel`.
--
--   Formalization note. The pack lives in namespace `IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA10` and imports only the published Pnd and SupG data.
-- source:
--   R8 BitOppbank FormalOK published Pnd (non-Fix) ArgDimLeA

-- ArgDimLeA10: dim inequality certificates on published Pnd only, nodes [25000, 27500)
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
namespace IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA10
def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16
theorem d0_w0 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 25000)) ≤ dimF (n.val + 25000) := by decide
theorem d1_w0 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 25000)) ≤ dimF (n.val + 25000) := by decide
theorem d0_w1 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 25050)) ≤ dimF (n.val + 25050) := by decide
theorem d1_w1 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 25050)) ≤ dimF (n.val + 25050) := by decide
theorem d0_w2 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 25100)) ≤ dimF (n.val + 25100) := by decide
theorem d1_w2 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 25100)) ≤ dimF (n.val + 25100) := by decide
theorem d0_w3 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 25150)) ≤ dimF (n.val + 25150) := by decide
theorem d1_w3 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 25150)) ≤ dimF (n.val + 25150) := by decide
theorem d0_w4 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 25200)) ≤ dimF (n.val + 25200) := by decide
theorem d1_w4 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 25200)) ≤ dimF (n.val + 25200) := by decide
theorem d0_w5 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 25250)) ≤ dimF (n.val + 25250) := by decide
theorem d1_w5 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 25250)) ≤ dimF (n.val + 25250) := by decide
theorem d0_w6 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 25300)) ≤ dimF (n.val + 25300) := by decide
theorem d1_w6 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 25300)) ≤ dimF (n.val + 25300) := by decide
theorem d0_w7 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 25350)) ≤ dimF (n.val + 25350) := by decide
theorem d1_w7 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 25350)) ≤ dimF (n.val + 25350) := by decide
theorem d0_w8 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 25400)) ≤ dimF (n.val + 25400) := by decide
theorem d1_w8 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 25400)) ≤ dimF (n.val + 25400) := by decide
theorem d0_w9 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 25450)) ≤ dimF (n.val + 25450) := by decide
theorem d1_w9 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 25450)) ≤ dimF (n.val + 25450) := by decide
theorem d0_w10 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 25500)) ≤ dimF (n.val + 25500) := by decide
theorem d1_w10 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 25500)) ≤ dimF (n.val + 25500) := by decide
theorem d0_w11 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 25550)) ≤ dimF (n.val + 25550) := by decide
theorem d1_w11 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 25550)) ≤ dimF (n.val + 25550) := by decide
theorem d0_w12 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 25600)) ≤ dimF (n.val + 25600) := by decide
theorem d1_w12 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 25600)) ≤ dimF (n.val + 25600) := by decide
theorem d0_w13 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 25650)) ≤ dimF (n.val + 25650) := by decide
theorem d1_w13 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 25650)) ≤ dimF (n.val + 25650) := by decide
theorem d0_w14 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 25700)) ≤ dimF (n.val + 25700) := by decide
theorem d1_w14 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 25700)) ≤ dimF (n.val + 25700) := by decide
theorem d0_w15 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 25750)) ≤ dimF (n.val + 25750) := by decide
theorem d1_w15 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 25750)) ≤ dimF (n.val + 25750) := by decide
theorem d0_w16 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 25800)) ≤ dimF (n.val + 25800) := by decide
theorem d1_w16 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 25800)) ≤ dimF (n.val + 25800) := by decide
theorem d0_w17 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 25850)) ≤ dimF (n.val + 25850) := by decide
theorem d1_w17 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 25850)) ≤ dimF (n.val + 25850) := by decide
theorem d0_w18 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 25900)) ≤ dimF (n.val + 25900) := by decide
theorem d1_w18 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 25900)) ≤ dimF (n.val + 25900) := by decide
theorem d0_w19 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 25950)) ≤ dimF (n.val + 25950) := by decide
theorem d1_w19 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 25950)) ≤ dimF (n.val + 25950) := by decide
theorem d0_w20 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 26000)) ≤ dimF (n.val + 26000) := by decide
theorem d1_w20 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 26000)) ≤ dimF (n.val + 26000) := by decide
theorem d0_w21 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 26050)) ≤ dimF (n.val + 26050) := by decide
theorem d1_w21 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 26050)) ≤ dimF (n.val + 26050) := by decide
theorem d0_w22 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 26100)) ≤ dimF (n.val + 26100) := by decide
theorem d1_w22 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 26100)) ≤ dimF (n.val + 26100) := by decide
theorem d0_w23 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 26150)) ≤ dimF (n.val + 26150) := by decide
theorem d1_w23 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 26150)) ≤ dimF (n.val + 26150) := by decide
theorem d0_w24 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 26200)) ≤ dimF (n.val + 26200) := by decide
theorem d1_w24 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 26200)) ≤ dimF (n.val + 26200) := by decide
theorem d0_w25 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 26250)) ≤ dimF (n.val + 26250) := by decide
theorem d1_w25 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 26250)) ≤ dimF (n.val + 26250) := by decide
theorem d0_w26 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 26300)) ≤ dimF (n.val + 26300) := by decide
theorem d1_w26 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 26300)) ≤ dimF (n.val + 26300) := by decide
theorem d0_w27 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 26350)) ≤ dimF (n.val + 26350) := by decide
theorem d1_w27 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 26350)) ≤ dimF (n.val + 26350) := by decide
theorem d0_w28 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 26400)) ≤ dimF (n.val + 26400) := by decide
theorem d1_w28 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 26400)) ≤ dimF (n.val + 26400) := by decide
theorem d0_w29 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 26450)) ≤ dimF (n.val + 26450) := by decide
theorem d1_w29 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 26450)) ≤ dimF (n.val + 26450) := by decide
theorem d0_w30 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 26500)) ≤ dimF (n.val + 26500) := by decide
theorem d1_w30 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 26500)) ≤ dimF (n.val + 26500) := by decide
theorem d0_w31 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 26550)) ≤ dimF (n.val + 26550) := by decide
theorem d1_w31 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 26550)) ≤ dimF (n.val + 26550) := by decide
theorem d0_w32 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 26600)) ≤ dimF (n.val + 26600) := by decide
theorem d1_w32 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 26600)) ≤ dimF (n.val + 26600) := by decide
theorem d0_w33 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 26650)) ≤ dimF (n.val + 26650) := by decide
theorem d1_w33 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 26650)) ≤ dimF (n.val + 26650) := by decide
theorem d0_w34 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 26700)) ≤ dimF (n.val + 26700) := by decide
theorem d1_w34 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 26700)) ≤ dimF (n.val + 26700) := by decide
theorem d0_w35 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 26750)) ≤ dimF (n.val + 26750) := by decide
theorem d1_w35 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 26750)) ≤ dimF (n.val + 26750) := by decide
theorem d0_w36 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 26800)) ≤ dimF (n.val + 26800) := by decide
theorem d1_w36 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 26800)) ≤ dimF (n.val + 26800) := by decide
theorem d0_w37 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 26850)) ≤ dimF (n.val + 26850) := by decide
theorem d1_w37 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 26850)) ≤ dimF (n.val + 26850) := by decide
theorem d0_w38 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 26900)) ≤ dimF (n.val + 26900) := by decide
theorem d1_w38 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 26900)) ≤ dimF (n.val + 26900) := by decide
theorem d0_w39 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 26950)) ≤ dimF (n.val + 26950) := by decide
theorem d1_w39 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 26950)) ≤ dimF (n.val + 26950) := by decide
theorem d0_w40 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 27000)) ≤ dimF (n.val + 27000) := by decide
theorem d1_w40 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 27000)) ≤ dimF (n.val + 27000) := by decide
theorem d0_w41 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 27050)) ≤ dimF (n.val + 27050) := by decide
theorem d1_w41 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 27050)) ≤ dimF (n.val + 27050) := by decide
theorem d0_w42 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 27100)) ≤ dimF (n.val + 27100) := by decide
theorem d1_w42 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 27100)) ≤ dimF (n.val + 27100) := by decide
theorem d0_w43 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 27150)) ≤ dimF (n.val + 27150) := by decide
theorem d1_w43 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 27150)) ≤ dimF (n.val + 27150) := by decide
theorem d0_w44 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 27200)) ≤ dimF (n.val + 27200) := by decide
theorem d1_w44 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 27200)) ≤ dimF (n.val + 27200) := by decide
theorem d0_w45 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 27250)) ≤ dimF (n.val + 27250) := by decide
theorem d1_w45 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 27250)) ≤ dimF (n.val + 27250) := by decide
theorem d0_w46 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 27300)) ≤ dimF (n.val + 27300) := by decide
theorem d1_w46 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 27300)) ≤ dimF (n.val + 27300) := by decide
theorem d0_w47 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 27350)) ≤ dimF (n.val + 27350) := by decide
theorem d1_w47 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 27350)) ≤ dimF (n.val + 27350) := by decide
theorem d0_w48 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 27400)) ≤ dimF (n.val + 27400) := by decide
theorem d1_w48 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 27400)) ≤ dimF (n.val + 27400) := by decide
theorem d0_w49 : ∀ n : Fin 50,
  dimF (arg0 (n.val + 27450)) ≤ dimF (n.val + 27450) := by decide
theorem d1_w49 : ∀ n : Fin 50,
  dimF (arg1 (n.val + 27450)) ≤ dimF (n.val + 27450) := by decide
theorem dim0_range (n : ℕ) (hn0 : 25000 ≤ n) (hn1 : n < 27500) :
    dimF (arg0 n) ≤ dimF n := by
  by_cases h0 : n < 25050
  · have hoff : 25000 ≤ n := by omega
    have hnfin : n - 25000 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using d0_w0 ⟨n - 25000, hnfin⟩
  ·
    by_cases h1 : n < 25100
    · have hoff : 25050 ≤ n := by omega
      have hnfin : n - 25050 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using d0_w1 ⟨n - 25050, hnfin⟩
    ·
      by_cases h2 : n < 25150
      · have hoff : 25100 ≤ n := by omega
        have hnfin : n - 25100 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using d0_w2 ⟨n - 25100, hnfin⟩
      ·
        by_cases h3 : n < 25200
        · have hoff : 25150 ≤ n := by omega
          have hnfin : n - 25150 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using d0_w3 ⟨n - 25150, hnfin⟩
        ·
          by_cases h4 : n < 25250
          · have hoff : 25200 ≤ n := by omega
            have hnfin : n - 25200 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using d0_w4 ⟨n - 25200, hnfin⟩
          ·
            by_cases h5 : n < 25300
            · have hoff : 25250 ≤ n := by omega
              have hnfin : n - 25250 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using d0_w5 ⟨n - 25250, hnfin⟩
            ·
              by_cases h6 : n < 25350
              · have hoff : 25300 ≤ n := by omega
                have hnfin : n - 25300 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using d0_w6 ⟨n - 25300, hnfin⟩
              ·
                by_cases h7 : n < 25400
                · have hoff : 25350 ≤ n := by omega
                  have hnfin : n - 25350 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using d0_w7 ⟨n - 25350, hnfin⟩
                ·
                  by_cases h8 : n < 25450
                  · have hoff : 25400 ≤ n := by omega
                    have hnfin : n - 25400 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using d0_w8 ⟨n - 25400, hnfin⟩
                  ·
                    by_cases h9 : n < 25500
                    · have hoff : 25450 ≤ n := by omega
                      have hnfin : n - 25450 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using d0_w9 ⟨n - 25450, hnfin⟩
                    ·
                      by_cases h10 : n < 25550
                      · have hoff : 25500 ≤ n := by omega
                        have hnfin : n - 25500 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using d0_w10 ⟨n - 25500, hnfin⟩
                      ·
                        by_cases h11 : n < 25600
                        · have hoff : 25550 ≤ n := by omega
                          have hnfin : n - 25550 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using d0_w11 ⟨n - 25550, hnfin⟩
                        ·
                          by_cases h12 : n < 25650
                          · have hoff : 25600 ≤ n := by omega
                            have hnfin : n - 25600 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using d0_w12 ⟨n - 25600, hnfin⟩
                          ·
                            by_cases h13 : n < 25700
                            · have hoff : 25650 ≤ n := by omega
                              have hnfin : n - 25650 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using d0_w13 ⟨n - 25650, hnfin⟩
                            ·
                              by_cases h14 : n < 25750
                              · have hoff : 25700 ≤ n := by omega
                                have hnfin : n - 25700 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using d0_w14 ⟨n - 25700, hnfin⟩
                              ·
                                by_cases h15 : n < 25800
                                · have hoff : 25750 ≤ n := by omega
                                  have hnfin : n - 25750 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using d0_w15 ⟨n - 25750, hnfin⟩
                                ·
                                  by_cases h16 : n < 25850
                                  · have hoff : 25800 ≤ n := by omega
                                    have hnfin : n - 25800 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using d0_w16 ⟨n - 25800, hnfin⟩
                                  ·
                                    by_cases h17 : n < 25900
                                    · have hoff : 25850 ≤ n := by omega
                                      have hnfin : n - 25850 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using d0_w17 ⟨n - 25850, hnfin⟩
                                    ·
                                      by_cases h18 : n < 25950
                                      · have hoff : 25900 ≤ n := by omega
                                        have hnfin : n - 25900 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using d0_w18 ⟨n - 25900, hnfin⟩
                                      ·
                                        by_cases h19 : n < 26000
                                        · have hoff : 25950 ≤ n := by omega
                                          have hnfin : n - 25950 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using d0_w19 ⟨n - 25950, hnfin⟩
                                        ·
                                          by_cases h20 : n < 26050
                                          · have hoff : 26000 ≤ n := by omega
                                            have hnfin : n - 26000 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using d0_w20 ⟨n - 26000, hnfin⟩
                                          ·
                                            by_cases h21 : n < 26100
                                            · have hoff : 26050 ≤ n := by omega
                                              have hnfin : n - 26050 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using d0_w21 ⟨n - 26050, hnfin⟩
                                            ·
                                              by_cases h22 : n < 26150
                                              · have hoff : 26100 ≤ n := by omega
                                                have hnfin : n - 26100 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using d0_w22 ⟨n - 26100, hnfin⟩
                                              ·
                                                by_cases h23 : n < 26200
                                                · have hoff : 26150 ≤ n := by omega
                                                  have hnfin : n - 26150 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using d0_w23 ⟨n - 26150, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 26250
                                                  · have hoff : 26200 ≤ n := by omega
                                                    have hnfin : n - 26200 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using d0_w24 ⟨n - 26200, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 26300
                                                    · have hoff : 26250 ≤ n := by omega
                                                      have hnfin : n - 26250 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using d0_w25 ⟨n - 26250, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 26350
                                                      · have hoff : 26300 ≤ n := by omega
                                                        have hnfin : n - 26300 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using d0_w26 ⟨n - 26300, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 26400
                                                        · have hoff : 26350 ≤ n := by omega
                                                          have hnfin : n - 26350 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using d0_w27 ⟨n - 26350, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 26450
                                                          · have hoff : 26400 ≤ n := by omega
                                                            have hnfin : n - 26400 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using d0_w28 ⟨n - 26400, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 26500
                                                            · have hoff : 26450 ≤ n := by omega
                                                              have hnfin : n - 26450 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using d0_w29 ⟨n - 26450, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 26550
                                                              · have hoff : 26500 ≤ n := by omega
                                                                have hnfin : n - 26500 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using d0_w30 ⟨n - 26500, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 26600
                                                                · have hoff : 26550 ≤ n := by omega
                                                                  have hnfin : n - 26550 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using d0_w31 ⟨n - 26550, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 26650
                                                                  · have hoff : 26600 ≤ n := by omega
                                                                    have hnfin : n - 26600 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w32 ⟨n - 26600, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 26700
                                                                    · have hoff : 26650 ≤ n := by omega
                                                                      have hnfin : n - 26650 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using d0_w33 ⟨n - 26650, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 26750
                                                                      · have hoff : 26700 ≤ n := by omega
                                                                        have hnfin : n - 26700 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using d0_w34 ⟨n - 26700, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 26800
                                                                        · have hoff : 26750 ≤ n := by omega
                                                                          have hnfin : n - 26750 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using d0_w35 ⟨n - 26750, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 26850
                                                                          · have hoff : 26800 ≤ n := by omega
                                                                            have hnfin : n - 26800 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using d0_w36 ⟨n - 26800, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 26900
                                                                            · have hoff : 26850 ≤ n := by omega
                                                                              have hnfin : n - 26850 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using d0_w37 ⟨n - 26850, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 26950
                                                                              · have hoff : 26900 ≤ n := by omega
                                                                                have hnfin : n - 26900 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using d0_w38 ⟨n - 26900, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 27000
                                                                                · have hoff : 26950 ≤ n := by omega
                                                                                  have hnfin : n - 26950 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using d0_w39 ⟨n - 26950, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 27050
                                                                                  · have hoff : 27000 ≤ n := by omega
                                                                                    have hnfin : n - 27000 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w40 ⟨n - 27000, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 27100
                                                                                    · have hoff : 27050 ≤ n := by omega
                                                                                      have hnfin : n - 27050 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using d0_w41 ⟨n - 27050, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 27150
                                                                                      · have hoff : 27100 ≤ n := by omega
                                                                                        have hnfin : n - 27100 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using d0_w42 ⟨n - 27100, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 27200
                                                                                        · have hoff : 27150 ≤ n := by omega
                                                                                          have hnfin : n - 27150 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using d0_w43 ⟨n - 27150, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 27250
                                                                                          · have hoff : 27200 ≤ n := by omega
                                                                                            have hnfin : n - 27200 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using d0_w44 ⟨n - 27200, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 27300
                                                                                            · have hoff : 27250 ≤ n := by omega
                                                                                              have hnfin : n - 27250 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using d0_w45 ⟨n - 27250, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 27350
                                                                                              · have hoff : 27300 ≤ n := by omega
                                                                                                have hnfin : n - 27300 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using d0_w46 ⟨n - 27300, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 27400
                                                                                                · have hoff : 27350 ≤ n := by omega
                                                                                                  have hnfin : n - 27350 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using d0_w47 ⟨n - 27350, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 27450
                                                                                                  · have hoff : 27400 ≤ n := by omega
                                                                                                    have hnfin : n - 27400 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w48 ⟨n - 27400, hnfin⟩
                                                                                                  · have hoff : 27450 ≤ n := by omega
                                                                                                    have hnfin : n - 27450 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d0_w49 ⟨n - 27450, hnfin⟩
theorem dim1_range (n : ℕ) (hn0 : 25000 ≤ n) (hn1 : n < 27500) :
    dimF (arg1 n) ≤ dimF n := by
  by_cases h0 : n < 25050
  · have hoff : 25000 ≤ n := by omega
    have hnfin : n - 25000 < 50 := by omega
    simpa [Nat.sub_add_cancel hoff] using d1_w0 ⟨n - 25000, hnfin⟩
  ·
    by_cases h1 : n < 25100
    · have hoff : 25050 ≤ n := by omega
      have hnfin : n - 25050 < 50 := by omega
      simpa [Nat.sub_add_cancel hoff] using d1_w1 ⟨n - 25050, hnfin⟩
    ·
      by_cases h2 : n < 25150
      · have hoff : 25100 ≤ n := by omega
        have hnfin : n - 25100 < 50 := by omega
        simpa [Nat.sub_add_cancel hoff] using d1_w2 ⟨n - 25100, hnfin⟩
      ·
        by_cases h3 : n < 25200
        · have hoff : 25150 ≤ n := by omega
          have hnfin : n - 25150 < 50 := by omega
          simpa [Nat.sub_add_cancel hoff] using d1_w3 ⟨n - 25150, hnfin⟩
        ·
          by_cases h4 : n < 25250
          · have hoff : 25200 ≤ n := by omega
            have hnfin : n - 25200 < 50 := by omega
            simpa [Nat.sub_add_cancel hoff] using d1_w4 ⟨n - 25200, hnfin⟩
          ·
            by_cases h5 : n < 25300
            · have hoff : 25250 ≤ n := by omega
              have hnfin : n - 25250 < 50 := by omega
              simpa [Nat.sub_add_cancel hoff] using d1_w5 ⟨n - 25250, hnfin⟩
            ·
              by_cases h6 : n < 25350
              · have hoff : 25300 ≤ n := by omega
                have hnfin : n - 25300 < 50 := by omega
                simpa [Nat.sub_add_cancel hoff] using d1_w6 ⟨n - 25300, hnfin⟩
              ·
                by_cases h7 : n < 25400
                · have hoff : 25350 ≤ n := by omega
                  have hnfin : n - 25350 < 50 := by omega
                  simpa [Nat.sub_add_cancel hoff] using d1_w7 ⟨n - 25350, hnfin⟩
                ·
                  by_cases h8 : n < 25450
                  · have hoff : 25400 ≤ n := by omega
                    have hnfin : n - 25400 < 50 := by omega
                    simpa [Nat.sub_add_cancel hoff] using d1_w8 ⟨n - 25400, hnfin⟩
                  ·
                    by_cases h9 : n < 25500
                    · have hoff : 25450 ≤ n := by omega
                      have hnfin : n - 25450 < 50 := by omega
                      simpa [Nat.sub_add_cancel hoff] using d1_w9 ⟨n - 25450, hnfin⟩
                    ·
                      by_cases h10 : n < 25550
                      · have hoff : 25500 ≤ n := by omega
                        have hnfin : n - 25500 < 50 := by omega
                        simpa [Nat.sub_add_cancel hoff] using d1_w10 ⟨n - 25500, hnfin⟩
                      ·
                        by_cases h11 : n < 25600
                        · have hoff : 25550 ≤ n := by omega
                          have hnfin : n - 25550 < 50 := by omega
                          simpa [Nat.sub_add_cancel hoff] using d1_w11 ⟨n - 25550, hnfin⟩
                        ·
                          by_cases h12 : n < 25650
                          · have hoff : 25600 ≤ n := by omega
                            have hnfin : n - 25600 < 50 := by omega
                            simpa [Nat.sub_add_cancel hoff] using d1_w12 ⟨n - 25600, hnfin⟩
                          ·
                            by_cases h13 : n < 25700
                            · have hoff : 25650 ≤ n := by omega
                              have hnfin : n - 25650 < 50 := by omega
                              simpa [Nat.sub_add_cancel hoff] using d1_w13 ⟨n - 25650, hnfin⟩
                            ·
                              by_cases h14 : n < 25750
                              · have hoff : 25700 ≤ n := by omega
                                have hnfin : n - 25700 < 50 := by omega
                                simpa [Nat.sub_add_cancel hoff] using d1_w14 ⟨n - 25700, hnfin⟩
                              ·
                                by_cases h15 : n < 25800
                                · have hoff : 25750 ≤ n := by omega
                                  have hnfin : n - 25750 < 50 := by omega
                                  simpa [Nat.sub_add_cancel hoff] using d1_w15 ⟨n - 25750, hnfin⟩
                                ·
                                  by_cases h16 : n < 25850
                                  · have hoff : 25800 ≤ n := by omega
                                    have hnfin : n - 25800 < 50 := by omega
                                    simpa [Nat.sub_add_cancel hoff] using d1_w16 ⟨n - 25800, hnfin⟩
                                  ·
                                    by_cases h17 : n < 25900
                                    · have hoff : 25850 ≤ n := by omega
                                      have hnfin : n - 25850 < 50 := by omega
                                      simpa [Nat.sub_add_cancel hoff] using d1_w17 ⟨n - 25850, hnfin⟩
                                    ·
                                      by_cases h18 : n < 25950
                                      · have hoff : 25900 ≤ n := by omega
                                        have hnfin : n - 25900 < 50 := by omega
                                        simpa [Nat.sub_add_cancel hoff] using d1_w18 ⟨n - 25900, hnfin⟩
                                      ·
                                        by_cases h19 : n < 26000
                                        · have hoff : 25950 ≤ n := by omega
                                          have hnfin : n - 25950 < 50 := by omega
                                          simpa [Nat.sub_add_cancel hoff] using d1_w19 ⟨n - 25950, hnfin⟩
                                        ·
                                          by_cases h20 : n < 26050
                                          · have hoff : 26000 ≤ n := by omega
                                            have hnfin : n - 26000 < 50 := by omega
                                            simpa [Nat.sub_add_cancel hoff] using d1_w20 ⟨n - 26000, hnfin⟩
                                          ·
                                            by_cases h21 : n < 26100
                                            · have hoff : 26050 ≤ n := by omega
                                              have hnfin : n - 26050 < 50 := by omega
                                              simpa [Nat.sub_add_cancel hoff] using d1_w21 ⟨n - 26050, hnfin⟩
                                            ·
                                              by_cases h22 : n < 26150
                                              · have hoff : 26100 ≤ n := by omega
                                                have hnfin : n - 26100 < 50 := by omega
                                                simpa [Nat.sub_add_cancel hoff] using d1_w22 ⟨n - 26100, hnfin⟩
                                              ·
                                                by_cases h23 : n < 26200
                                                · have hoff : 26150 ≤ n := by omega
                                                  have hnfin : n - 26150 < 50 := by omega
                                                  simpa [Nat.sub_add_cancel hoff] using d1_w23 ⟨n - 26150, hnfin⟩
                                                ·
                                                  by_cases h24 : n < 26250
                                                  · have hoff : 26200 ≤ n := by omega
                                                    have hnfin : n - 26200 < 50 := by omega
                                                    simpa [Nat.sub_add_cancel hoff] using d1_w24 ⟨n - 26200, hnfin⟩
                                                  ·
                                                    by_cases h25 : n < 26300
                                                    · have hoff : 26250 ≤ n := by omega
                                                      have hnfin : n - 26250 < 50 := by omega
                                                      simpa [Nat.sub_add_cancel hoff] using d1_w25 ⟨n - 26250, hnfin⟩
                                                    ·
                                                      by_cases h26 : n < 26350
                                                      · have hoff : 26300 ≤ n := by omega
                                                        have hnfin : n - 26300 < 50 := by omega
                                                        simpa [Nat.sub_add_cancel hoff] using d1_w26 ⟨n - 26300, hnfin⟩
                                                      ·
                                                        by_cases h27 : n < 26400
                                                        · have hoff : 26350 ≤ n := by omega
                                                          have hnfin : n - 26350 < 50 := by omega
                                                          simpa [Nat.sub_add_cancel hoff] using d1_w27 ⟨n - 26350, hnfin⟩
                                                        ·
                                                          by_cases h28 : n < 26450
                                                          · have hoff : 26400 ≤ n := by omega
                                                            have hnfin : n - 26400 < 50 := by omega
                                                            simpa [Nat.sub_add_cancel hoff] using d1_w28 ⟨n - 26400, hnfin⟩
                                                          ·
                                                            by_cases h29 : n < 26500
                                                            · have hoff : 26450 ≤ n := by omega
                                                              have hnfin : n - 26450 < 50 := by omega
                                                              simpa [Nat.sub_add_cancel hoff] using d1_w29 ⟨n - 26450, hnfin⟩
                                                            ·
                                                              by_cases h30 : n < 26550
                                                              · have hoff : 26500 ≤ n := by omega
                                                                have hnfin : n - 26500 < 50 := by omega
                                                                simpa [Nat.sub_add_cancel hoff] using d1_w30 ⟨n - 26500, hnfin⟩
                                                              ·
                                                                by_cases h31 : n < 26600
                                                                · have hoff : 26550 ≤ n := by omega
                                                                  have hnfin : n - 26550 < 50 := by omega
                                                                  simpa [Nat.sub_add_cancel hoff] using d1_w31 ⟨n - 26550, hnfin⟩
                                                                ·
                                                                  by_cases h32 : n < 26650
                                                                  · have hoff : 26600 ≤ n := by omega
                                                                    have hnfin : n - 26600 < 50 := by omega
                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w32 ⟨n - 26600, hnfin⟩
                                                                  ·
                                                                    by_cases h33 : n < 26700
                                                                    · have hoff : 26650 ≤ n := by omega
                                                                      have hnfin : n - 26650 < 50 := by omega
                                                                      simpa [Nat.sub_add_cancel hoff] using d1_w33 ⟨n - 26650, hnfin⟩
                                                                    ·
                                                                      by_cases h34 : n < 26750
                                                                      · have hoff : 26700 ≤ n := by omega
                                                                        have hnfin : n - 26700 < 50 := by omega
                                                                        simpa [Nat.sub_add_cancel hoff] using d1_w34 ⟨n - 26700, hnfin⟩
                                                                      ·
                                                                        by_cases h35 : n < 26800
                                                                        · have hoff : 26750 ≤ n := by omega
                                                                          have hnfin : n - 26750 < 50 := by omega
                                                                          simpa [Nat.sub_add_cancel hoff] using d1_w35 ⟨n - 26750, hnfin⟩
                                                                        ·
                                                                          by_cases h36 : n < 26850
                                                                          · have hoff : 26800 ≤ n := by omega
                                                                            have hnfin : n - 26800 < 50 := by omega
                                                                            simpa [Nat.sub_add_cancel hoff] using d1_w36 ⟨n - 26800, hnfin⟩
                                                                          ·
                                                                            by_cases h37 : n < 26900
                                                                            · have hoff : 26850 ≤ n := by omega
                                                                              have hnfin : n - 26850 < 50 := by omega
                                                                              simpa [Nat.sub_add_cancel hoff] using d1_w37 ⟨n - 26850, hnfin⟩
                                                                            ·
                                                                              by_cases h38 : n < 26950
                                                                              · have hoff : 26900 ≤ n := by omega
                                                                                have hnfin : n - 26900 < 50 := by omega
                                                                                simpa [Nat.sub_add_cancel hoff] using d1_w38 ⟨n - 26900, hnfin⟩
                                                                              ·
                                                                                by_cases h39 : n < 27000
                                                                                · have hoff : 26950 ≤ n := by omega
                                                                                  have hnfin : n - 26950 < 50 := by omega
                                                                                  simpa [Nat.sub_add_cancel hoff] using d1_w39 ⟨n - 26950, hnfin⟩
                                                                                ·
                                                                                  by_cases h40 : n < 27050
                                                                                  · have hoff : 27000 ≤ n := by omega
                                                                                    have hnfin : n - 27000 < 50 := by omega
                                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w40 ⟨n - 27000, hnfin⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 27100
                                                                                    · have hoff : 27050 ≤ n := by omega
                                                                                      have hnfin : n - 27050 < 50 := by omega
                                                                                      simpa [Nat.sub_add_cancel hoff] using d1_w41 ⟨n - 27050, hnfin⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 27150
                                                                                      · have hoff : 27100 ≤ n := by omega
                                                                                        have hnfin : n - 27100 < 50 := by omega
                                                                                        simpa [Nat.sub_add_cancel hoff] using d1_w42 ⟨n - 27100, hnfin⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 27200
                                                                                        · have hoff : 27150 ≤ n := by omega
                                                                                          have hnfin : n - 27150 < 50 := by omega
                                                                                          simpa [Nat.sub_add_cancel hoff] using d1_w43 ⟨n - 27150, hnfin⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 27250
                                                                                          · have hoff : 27200 ≤ n := by omega
                                                                                            have hnfin : n - 27200 < 50 := by omega
                                                                                            simpa [Nat.sub_add_cancel hoff] using d1_w44 ⟨n - 27200, hnfin⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 27300
                                                                                            · have hoff : 27250 ≤ n := by omega
                                                                                              have hnfin : n - 27250 < 50 := by omega
                                                                                              simpa [Nat.sub_add_cancel hoff] using d1_w45 ⟨n - 27250, hnfin⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 27350
                                                                                              · have hoff : 27300 ≤ n := by omega
                                                                                                have hnfin : n - 27300 < 50 := by omega
                                                                                                simpa [Nat.sub_add_cancel hoff] using d1_w46 ⟨n - 27300, hnfin⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 27400
                                                                                                · have hoff : 27350 ≤ n := by omega
                                                                                                  have hnfin : n - 27350 < 50 := by omega
                                                                                                  simpa [Nat.sub_add_cancel hoff] using d1_w47 ⟨n - 27350, hnfin⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 27450
                                                                                                  · have hoff : 27400 ≤ n := by omega
                                                                                                    have hnfin : n - 27400 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w48 ⟨n - 27400, hnfin⟩
                                                                                                  · have hoff : 27450 ≤ n := by omega
                                                                                                    have hnfin : n - 27450 < 50 := by omega
                                                                                                    simpa [Nat.sub_add_cancel hoff] using d1_w49 ⟨n - 27450, hnfin⟩
end IntMul.Kappa.R8.Bit.Oppbank.ArgDimLeA10


