-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound10b
-- name    : IntMul_Kappa_R8_Data_BitOppbankCentBound10b
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:12:25.107875+00:00
-- url     : https://prove2.me/theorems/50b13ff5-3f76-4b70-a8e5-6e3ed0395ebe
-- title:
--   HasCentre certificates dens nodes [52500,55000)
-- statement:
--   # CentBound10b
--
--   centredStar/centF/densSupG for $52500\le n<55000$ via Fin50 decide (no native_decide).
-- source:
--   R8 BitOppbank AllDensCentred

-- CentBound pack 10b: densified HasCentre certificates on n ∈ [52500, 55000)
-- Half-pack for server 300s compile budget.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCent
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
set_option exponentiation.threshold 2000

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open IntMul.Kappa.R8.Bit.Oppbank.Cent

namespace IntMul.Kappa.R8.Bit.Oppbank.CentBound10b


private theorem cs_w0 : ∀ n : Fin 50, centredStar (densSupG (n.val + 52500)) (centF (n.val + 52500)) = true := by decide
private theorem cl_w0 : ∀ n : Fin 50, centF (n.val + 52500) < 23 := by decide
private theorem bd_w0 : ∀ n : Fin 50, densSupG (n.val + 52500) < 2 ^ 1771 := by decide
private theorem cs_w1 : ∀ n : Fin 50, centredStar (densSupG (n.val + 52550)) (centF (n.val + 52550)) = true := by decide
private theorem cl_w1 : ∀ n : Fin 50, centF (n.val + 52550) < 23 := by decide
private theorem bd_w1 : ∀ n : Fin 50, densSupG (n.val + 52550) < 2 ^ 1771 := by decide
private theorem cs_w2 : ∀ n : Fin 50, centredStar (densSupG (n.val + 52600)) (centF (n.val + 52600)) = true := by decide
private theorem cl_w2 : ∀ n : Fin 50, centF (n.val + 52600) < 23 := by decide
private theorem bd_w2 : ∀ n : Fin 50, densSupG (n.val + 52600) < 2 ^ 1771 := by decide
private theorem cs_w3 : ∀ n : Fin 50, centredStar (densSupG (n.val + 52650)) (centF (n.val + 52650)) = true := by decide
private theorem cl_w3 : ∀ n : Fin 50, centF (n.val + 52650) < 23 := by decide
private theorem bd_w3 : ∀ n : Fin 50, densSupG (n.val + 52650) < 2 ^ 1771 := by decide
private theorem cs_w4 : ∀ n : Fin 50, centredStar (densSupG (n.val + 52700)) (centF (n.val + 52700)) = true := by decide
private theorem cl_w4 : ∀ n : Fin 50, centF (n.val + 52700) < 23 := by decide
private theorem bd_w4 : ∀ n : Fin 50, densSupG (n.val + 52700) < 2 ^ 1771 := by decide
private theorem cs_w5 : ∀ n : Fin 50, centredStar (densSupG (n.val + 52750)) (centF (n.val + 52750)) = true := by decide
private theorem cl_w5 : ∀ n : Fin 50, centF (n.val + 52750) < 23 := by decide
private theorem bd_w5 : ∀ n : Fin 50, densSupG (n.val + 52750) < 2 ^ 1771 := by decide
private theorem cs_w6 : ∀ n : Fin 50, centredStar (densSupG (n.val + 52800)) (centF (n.val + 52800)) = true := by decide
private theorem cl_w6 : ∀ n : Fin 50, centF (n.val + 52800) < 23 := by decide
private theorem bd_w6 : ∀ n : Fin 50, densSupG (n.val + 52800) < 2 ^ 1771 := by decide
private theorem cs_w7 : ∀ n : Fin 50, centredStar (densSupG (n.val + 52850)) (centF (n.val + 52850)) = true := by decide
private theorem cl_w7 : ∀ n : Fin 50, centF (n.val + 52850) < 23 := by decide
private theorem bd_w7 : ∀ n : Fin 50, densSupG (n.val + 52850) < 2 ^ 1771 := by decide
private theorem cs_w8 : ∀ n : Fin 50, centredStar (densSupG (n.val + 52900)) (centF (n.val + 52900)) = true := by decide
private theorem cl_w8 : ∀ n : Fin 50, centF (n.val + 52900) < 23 := by decide
private theorem bd_w8 : ∀ n : Fin 50, densSupG (n.val + 52900) < 2 ^ 1771 := by decide
private theorem cs_w9 : ∀ n : Fin 50, centredStar (densSupG (n.val + 52950)) (centF (n.val + 52950)) = true := by decide
private theorem cl_w9 : ∀ n : Fin 50, centF (n.val + 52950) < 23 := by decide
private theorem bd_w9 : ∀ n : Fin 50, densSupG (n.val + 52950) < 2 ^ 1771 := by decide
private theorem cs_w10 : ∀ n : Fin 50, centredStar (densSupG (n.val + 53000)) (centF (n.val + 53000)) = true := by decide
private theorem cl_w10 : ∀ n : Fin 50, centF (n.val + 53000) < 23 := by decide
private theorem bd_w10 : ∀ n : Fin 50, densSupG (n.val + 53000) < 2 ^ 1771 := by decide
private theorem cs_w11 : ∀ n : Fin 50, centredStar (densSupG (n.val + 53050)) (centF (n.val + 53050)) = true := by decide
private theorem cl_w11 : ∀ n : Fin 50, centF (n.val + 53050) < 23 := by decide
private theorem bd_w11 : ∀ n : Fin 50, densSupG (n.val + 53050) < 2 ^ 1771 := by decide
private theorem cs_w12 : ∀ n : Fin 50, centredStar (densSupG (n.val + 53100)) (centF (n.val + 53100)) = true := by decide
private theorem cl_w12 : ∀ n : Fin 50, centF (n.val + 53100) < 23 := by decide
private theorem bd_w12 : ∀ n : Fin 50, densSupG (n.val + 53100) < 2 ^ 1771 := by decide
private theorem cs_w13 : ∀ n : Fin 50, centredStar (densSupG (n.val + 53150)) (centF (n.val + 53150)) = true := by decide
private theorem cl_w13 : ∀ n : Fin 50, centF (n.val + 53150) < 23 := by decide
private theorem bd_w13 : ∀ n : Fin 50, densSupG (n.val + 53150) < 2 ^ 1771 := by decide
private theorem cs_w14 : ∀ n : Fin 50, centredStar (densSupG (n.val + 53200)) (centF (n.val + 53200)) = true := by decide
private theorem cl_w14 : ∀ n : Fin 50, centF (n.val + 53200) < 23 := by decide
private theorem bd_w14 : ∀ n : Fin 50, densSupG (n.val + 53200) < 2 ^ 1771 := by decide
private theorem cs_w15 : ∀ n : Fin 50, centredStar (densSupG (n.val + 53250)) (centF (n.val + 53250)) = true := by decide
private theorem cl_w15 : ∀ n : Fin 50, centF (n.val + 53250) < 23 := by decide
private theorem bd_w15 : ∀ n : Fin 50, densSupG (n.val + 53250) < 2 ^ 1771 := by decide
private theorem cs_w16 : ∀ n : Fin 50, centredStar (densSupG (n.val + 53300)) (centF (n.val + 53300)) = true := by decide
private theorem cl_w16 : ∀ n : Fin 50, centF (n.val + 53300) < 23 := by decide
private theorem bd_w16 : ∀ n : Fin 50, densSupG (n.val + 53300) < 2 ^ 1771 := by decide
private theorem cs_w17 : ∀ n : Fin 50, centredStar (densSupG (n.val + 53350)) (centF (n.val + 53350)) = true := by decide
private theorem cl_w17 : ∀ n : Fin 50, centF (n.val + 53350) < 23 := by decide
private theorem bd_w17 : ∀ n : Fin 50, densSupG (n.val + 53350) < 2 ^ 1771 := by decide
private theorem cs_w18 : ∀ n : Fin 50, centredStar (densSupG (n.val + 53400)) (centF (n.val + 53400)) = true := by decide
private theorem cl_w18 : ∀ n : Fin 50, centF (n.val + 53400) < 23 := by decide
private theorem bd_w18 : ∀ n : Fin 50, densSupG (n.val + 53400) < 2 ^ 1771 := by decide
private theorem cs_w19 : ∀ n : Fin 50, centredStar (densSupG (n.val + 53450)) (centF (n.val + 53450)) = true := by decide
private theorem cl_w19 : ∀ n : Fin 50, centF (n.val + 53450) < 23 := by decide
private theorem bd_w19 : ∀ n : Fin 50, densSupG (n.val + 53450) < 2 ^ 1771 := by decide
private theorem cs_w20 : ∀ n : Fin 50, centredStar (densSupG (n.val + 53500)) (centF (n.val + 53500)) = true := by decide
private theorem cl_w20 : ∀ n : Fin 50, centF (n.val + 53500) < 23 := by decide
private theorem bd_w20 : ∀ n : Fin 50, densSupG (n.val + 53500) < 2 ^ 1771 := by decide
private theorem cs_w21 : ∀ n : Fin 50, centredStar (densSupG (n.val + 53550)) (centF (n.val + 53550)) = true := by decide
private theorem cl_w21 : ∀ n : Fin 50, centF (n.val + 53550) < 23 := by decide
private theorem bd_w21 : ∀ n : Fin 50, densSupG (n.val + 53550) < 2 ^ 1771 := by decide
private theorem cs_w22 : ∀ n : Fin 50, centredStar (densSupG (n.val + 53600)) (centF (n.val + 53600)) = true := by decide
private theorem cl_w22 : ∀ n : Fin 50, centF (n.val + 53600) < 23 := by decide
private theorem bd_w22 : ∀ n : Fin 50, densSupG (n.val + 53600) < 2 ^ 1771 := by decide
private theorem cs_w23 : ∀ n : Fin 50, centredStar (densSupG (n.val + 53650)) (centF (n.val + 53650)) = true := by decide
private theorem cl_w23 : ∀ n : Fin 50, centF (n.val + 53650) < 23 := by decide
private theorem bd_w23 : ∀ n : Fin 50, densSupG (n.val + 53650) < 2 ^ 1771 := by decide
private theorem cs_w24 : ∀ n : Fin 50, centredStar (densSupG (n.val + 53700)) (centF (n.val + 53700)) = true := by decide
private theorem cl_w24 : ∀ n : Fin 50, centF (n.val + 53700) < 23 := by decide
private theorem bd_w24 : ∀ n : Fin 50, densSupG (n.val + 53700) < 2 ^ 1771 := by decide
private theorem cs_w25 : ∀ n : Fin 50, centredStar (densSupG (n.val + 53750)) (centF (n.val + 53750)) = true := by decide
private theorem cl_w25 : ∀ n : Fin 50, centF (n.val + 53750) < 23 := by decide
private theorem bd_w25 : ∀ n : Fin 50, densSupG (n.val + 53750) < 2 ^ 1771 := by decide
private theorem cs_w26 : ∀ n : Fin 50, centredStar (densSupG (n.val + 53800)) (centF (n.val + 53800)) = true := by decide
private theorem cl_w26 : ∀ n : Fin 50, centF (n.val + 53800) < 23 := by decide
private theorem bd_w26 : ∀ n : Fin 50, densSupG (n.val + 53800) < 2 ^ 1771 := by decide
private theorem cs_w27 : ∀ n : Fin 50, centredStar (densSupG (n.val + 53850)) (centF (n.val + 53850)) = true := by decide
private theorem cl_w27 : ∀ n : Fin 50, centF (n.val + 53850) < 23 := by decide
private theorem bd_w27 : ∀ n : Fin 50, densSupG (n.val + 53850) < 2 ^ 1771 := by decide
private theorem cs_w28 : ∀ n : Fin 50, centredStar (densSupG (n.val + 53900)) (centF (n.val + 53900)) = true := by decide
private theorem cl_w28 : ∀ n : Fin 50, centF (n.val + 53900) < 23 := by decide
private theorem bd_w28 : ∀ n : Fin 50, densSupG (n.val + 53900) < 2 ^ 1771 := by decide
private theorem cs_w29 : ∀ n : Fin 50, centredStar (densSupG (n.val + 53950)) (centF (n.val + 53950)) = true := by decide
private theorem cl_w29 : ∀ n : Fin 50, centF (n.val + 53950) < 23 := by decide
private theorem bd_w29 : ∀ n : Fin 50, densSupG (n.val + 53950) < 2 ^ 1771 := by decide
private theorem cs_w30 : ∀ n : Fin 50, centredStar (densSupG (n.val + 54000)) (centF (n.val + 54000)) = true := by decide
private theorem cl_w30 : ∀ n : Fin 50, centF (n.val + 54000) < 23 := by decide
private theorem bd_w30 : ∀ n : Fin 50, densSupG (n.val + 54000) < 2 ^ 1771 := by decide
private theorem cs_w31 : ∀ n : Fin 50, centredStar (densSupG (n.val + 54050)) (centF (n.val + 54050)) = true := by decide
private theorem cl_w31 : ∀ n : Fin 50, centF (n.val + 54050) < 23 := by decide
private theorem bd_w31 : ∀ n : Fin 50, densSupG (n.val + 54050) < 2 ^ 1771 := by decide
private theorem cs_w32 : ∀ n : Fin 50, centredStar (densSupG (n.val + 54100)) (centF (n.val + 54100)) = true := by decide
private theorem cl_w32 : ∀ n : Fin 50, centF (n.val + 54100) < 23 := by decide
private theorem bd_w32 : ∀ n : Fin 50, densSupG (n.val + 54100) < 2 ^ 1771 := by decide
private theorem cs_w33 : ∀ n : Fin 50, centredStar (densSupG (n.val + 54150)) (centF (n.val + 54150)) = true := by decide
private theorem cl_w33 : ∀ n : Fin 50, centF (n.val + 54150) < 23 := by decide
private theorem bd_w33 : ∀ n : Fin 50, densSupG (n.val + 54150) < 2 ^ 1771 := by decide
private theorem cs_w34 : ∀ n : Fin 50, centredStar (densSupG (n.val + 54200)) (centF (n.val + 54200)) = true := by decide
private theorem cl_w34 : ∀ n : Fin 50, centF (n.val + 54200) < 23 := by decide
private theorem bd_w34 : ∀ n : Fin 50, densSupG (n.val + 54200) < 2 ^ 1771 := by decide
private theorem cs_w35 : ∀ n : Fin 50, centredStar (densSupG (n.val + 54250)) (centF (n.val + 54250)) = true := by decide
private theorem cl_w35 : ∀ n : Fin 50, centF (n.val + 54250) < 23 := by decide
private theorem bd_w35 : ∀ n : Fin 50, densSupG (n.val + 54250) < 2 ^ 1771 := by decide
private theorem cs_w36 : ∀ n : Fin 50, centredStar (densSupG (n.val + 54300)) (centF (n.val + 54300)) = true := by decide
private theorem cl_w36 : ∀ n : Fin 50, centF (n.val + 54300) < 23 := by decide
private theorem bd_w36 : ∀ n : Fin 50, densSupG (n.val + 54300) < 2 ^ 1771 := by decide
private theorem cs_w37 : ∀ n : Fin 50, centredStar (densSupG (n.val + 54350)) (centF (n.val + 54350)) = true := by decide
private theorem cl_w37 : ∀ n : Fin 50, centF (n.val + 54350) < 23 := by decide
private theorem bd_w37 : ∀ n : Fin 50, densSupG (n.val + 54350) < 2 ^ 1771 := by decide
private theorem cs_w38 : ∀ n : Fin 50, centredStar (densSupG (n.val + 54400)) (centF (n.val + 54400)) = true := by decide
private theorem cl_w38 : ∀ n : Fin 50, centF (n.val + 54400) < 23 := by decide
private theorem bd_w38 : ∀ n : Fin 50, densSupG (n.val + 54400) < 2 ^ 1771 := by decide
private theorem cs_w39 : ∀ n : Fin 50, centredStar (densSupG (n.val + 54450)) (centF (n.val + 54450)) = true := by decide
private theorem cl_w39 : ∀ n : Fin 50, centF (n.val + 54450) < 23 := by decide
private theorem bd_w39 : ∀ n : Fin 50, densSupG (n.val + 54450) < 2 ^ 1771 := by decide
private theorem cs_w40 : ∀ n : Fin 50, centredStar (densSupG (n.val + 54500)) (centF (n.val + 54500)) = true := by decide
private theorem cl_w40 : ∀ n : Fin 50, centF (n.val + 54500) < 23 := by decide
private theorem bd_w40 : ∀ n : Fin 50, densSupG (n.val + 54500) < 2 ^ 1771 := by decide
private theorem cs_w41 : ∀ n : Fin 50, centredStar (densSupG (n.val + 54550)) (centF (n.val + 54550)) = true := by decide
private theorem cl_w41 : ∀ n : Fin 50, centF (n.val + 54550) < 23 := by decide
private theorem bd_w41 : ∀ n : Fin 50, densSupG (n.val + 54550) < 2 ^ 1771 := by decide
private theorem cs_w42 : ∀ n : Fin 50, centredStar (densSupG (n.val + 54600)) (centF (n.val + 54600)) = true := by decide
private theorem cl_w42 : ∀ n : Fin 50, centF (n.val + 54600) < 23 := by decide
private theorem bd_w42 : ∀ n : Fin 50, densSupG (n.val + 54600) < 2 ^ 1771 := by decide
private theorem cs_w43 : ∀ n : Fin 50, centredStar (densSupG (n.val + 54650)) (centF (n.val + 54650)) = true := by decide
private theorem cl_w43 : ∀ n : Fin 50, centF (n.val + 54650) < 23 := by decide
private theorem bd_w43 : ∀ n : Fin 50, densSupG (n.val + 54650) < 2 ^ 1771 := by decide
private theorem cs_w44 : ∀ n : Fin 50, centredStar (densSupG (n.val + 54700)) (centF (n.val + 54700)) = true := by decide
private theorem cl_w44 : ∀ n : Fin 50, centF (n.val + 54700) < 23 := by decide
private theorem bd_w44 : ∀ n : Fin 50, densSupG (n.val + 54700) < 2 ^ 1771 := by decide
private theorem cs_w45 : ∀ n : Fin 50, centredStar (densSupG (n.val + 54750)) (centF (n.val + 54750)) = true := by decide
private theorem cl_w45 : ∀ n : Fin 50, centF (n.val + 54750) < 23 := by decide
private theorem bd_w45 : ∀ n : Fin 50, densSupG (n.val + 54750) < 2 ^ 1771 := by decide
private theorem cs_w46 : ∀ n : Fin 50, centredStar (densSupG (n.val + 54800)) (centF (n.val + 54800)) = true := by decide
private theorem cl_w46 : ∀ n : Fin 50, centF (n.val + 54800) < 23 := by decide
private theorem bd_w46 : ∀ n : Fin 50, densSupG (n.val + 54800) < 2 ^ 1771 := by decide
private theorem cs_w47 : ∀ n : Fin 50, centredStar (densSupG (n.val + 54850)) (centF (n.val + 54850)) = true := by decide
private theorem cl_w47 : ∀ n : Fin 50, centF (n.val + 54850) < 23 := by decide
private theorem bd_w47 : ∀ n : Fin 50, densSupG (n.val + 54850) < 2 ^ 1771 := by decide
private theorem cs_w48 : ∀ n : Fin 50, centredStar (densSupG (n.val + 54900)) (centF (n.val + 54900)) = true := by decide
private theorem cl_w48 : ∀ n : Fin 50, centF (n.val + 54900) < 23 := by decide
private theorem bd_w48 : ∀ n : Fin 50, densSupG (n.val + 54900) < 2 ^ 1771 := by decide
private theorem cs_w49 : ∀ n : Fin 50, centredStar (densSupG (n.val + 54950)) (centF (n.val + 54950)) = true := by decide
private theorem cl_w49 : ∀ n : Fin 50, centF (n.val + 54950) < 23 := by decide
private theorem bd_w49 : ∀ n : Fin 50, densSupG (n.val + 54950) < 2 ^ 1771 := by decide
theorem centredStar_range : ∀ n, 52500 ≤ n → n < 55000 → centredStar (densSupG n) (centF n) = true := by
  intro n hlo hhi
  by_cases h0 : n < 52550
  · have hr : n - 52500 < 50 := by omega
    have heq : n = (n - 52500) + 52500 := by omega
    rw [heq]
    exact cs_w0 ⟨n - 52500, hr⟩
  ·
    by_cases h1 : n < 52600
    ·
      have hr : n - 52550 < 50 := by omega
      have heq : n = (n - 52550) + 52550 := by omega
      rw [heq]
      exact cs_w1 ⟨n - 52550, hr⟩
    ·
      by_cases h2 : n < 52650
      ·
        have hr : n - 52600 < 50 := by omega
        have heq : n = (n - 52600) + 52600 := by omega
        rw [heq]
        exact cs_w2 ⟨n - 52600, hr⟩
      ·
        by_cases h3 : n < 52700
        ·
          have hr : n - 52650 < 50 := by omega
          have heq : n = (n - 52650) + 52650 := by omega
          rw [heq]
          exact cs_w3 ⟨n - 52650, hr⟩
        ·
          by_cases h4 : n < 52750
          ·
            have hr : n - 52700 < 50 := by omega
            have heq : n = (n - 52700) + 52700 := by omega
            rw [heq]
            exact cs_w4 ⟨n - 52700, hr⟩
          ·
            by_cases h5 : n < 52800
            ·
              have hr : n - 52750 < 50 := by omega
              have heq : n = (n - 52750) + 52750 := by omega
              rw [heq]
              exact cs_w5 ⟨n - 52750, hr⟩
            ·
              by_cases h6 : n < 52850
              ·
                have hr : n - 52800 < 50 := by omega
                have heq : n = (n - 52800) + 52800 := by omega
                rw [heq]
                exact cs_w6 ⟨n - 52800, hr⟩
              ·
                by_cases h7 : n < 52900
                ·
                  have hr : n - 52850 < 50 := by omega
                  have heq : n = (n - 52850) + 52850 := by omega
                  rw [heq]
                  exact cs_w7 ⟨n - 52850, hr⟩
                ·
                  by_cases h8 : n < 52950
                  ·
                    have hr : n - 52900 < 50 := by omega
                    have heq : n = (n - 52900) + 52900 := by omega
                    rw [heq]
                    exact cs_w8 ⟨n - 52900, hr⟩
                  ·
                    by_cases h9 : n < 53000
                    ·
                      have hr : n - 52950 < 50 := by omega
                      have heq : n = (n - 52950) + 52950 := by omega
                      rw [heq]
                      exact cs_w9 ⟨n - 52950, hr⟩
                    ·
                      by_cases h10 : n < 53050
                      ·
                        have hr : n - 53000 < 50 := by omega
                        have heq : n = (n - 53000) + 53000 := by omega
                        rw [heq]
                        exact cs_w10 ⟨n - 53000, hr⟩
                      ·
                        by_cases h11 : n < 53100
                        ·
                          have hr : n - 53050 < 50 := by omega
                          have heq : n = (n - 53050) + 53050 := by omega
                          rw [heq]
                          exact cs_w11 ⟨n - 53050, hr⟩
                        ·
                          by_cases h12 : n < 53150
                          ·
                            have hr : n - 53100 < 50 := by omega
                            have heq : n = (n - 53100) + 53100 := by omega
                            rw [heq]
                            exact cs_w12 ⟨n - 53100, hr⟩
                          ·
                            by_cases h13 : n < 53200
                            ·
                              have hr : n - 53150 < 50 := by omega
                              have heq : n = (n - 53150) + 53150 := by omega
                              rw [heq]
                              exact cs_w13 ⟨n - 53150, hr⟩
                            ·
                              by_cases h14 : n < 53250
                              ·
                                have hr : n - 53200 < 50 := by omega
                                have heq : n = (n - 53200) + 53200 := by omega
                                rw [heq]
                                exact cs_w14 ⟨n - 53200, hr⟩
                              ·
                                by_cases h15 : n < 53300
                                ·
                                  have hr : n - 53250 < 50 := by omega
                                  have heq : n = (n - 53250) + 53250 := by omega
                                  rw [heq]
                                  exact cs_w15 ⟨n - 53250, hr⟩
                                ·
                                  by_cases h16 : n < 53350
                                  ·
                                    have hr : n - 53300 < 50 := by omega
                                    have heq : n = (n - 53300) + 53300 := by omega
                                    rw [heq]
                                    exact cs_w16 ⟨n - 53300, hr⟩
                                  ·
                                    by_cases h17 : n < 53400
                                    ·
                                      have hr : n - 53350 < 50 := by omega
                                      have heq : n = (n - 53350) + 53350 := by omega
                                      rw [heq]
                                      exact cs_w17 ⟨n - 53350, hr⟩
                                    ·
                                      by_cases h18 : n < 53450
                                      ·
                                        have hr : n - 53400 < 50 := by omega
                                        have heq : n = (n - 53400) + 53400 := by omega
                                        rw [heq]
                                        exact cs_w18 ⟨n - 53400, hr⟩
                                      ·
                                        by_cases h19 : n < 53500
                                        ·
                                          have hr : n - 53450 < 50 := by omega
                                          have heq : n = (n - 53450) + 53450 := by omega
                                          rw [heq]
                                          exact cs_w19 ⟨n - 53450, hr⟩
                                        ·
                                          by_cases h20 : n < 53550
                                          ·
                                            have hr : n - 53500 < 50 := by omega
                                            have heq : n = (n - 53500) + 53500 := by omega
                                            rw [heq]
                                            exact cs_w20 ⟨n - 53500, hr⟩
                                          ·
                                            by_cases h21 : n < 53600
                                            ·
                                              have hr : n - 53550 < 50 := by omega
                                              have heq : n = (n - 53550) + 53550 := by omega
                                              rw [heq]
                                              exact cs_w21 ⟨n - 53550, hr⟩
                                            ·
                                              by_cases h22 : n < 53650
                                              ·
                                                have hr : n - 53600 < 50 := by omega
                                                have heq : n = (n - 53600) + 53600 := by omega
                                                rw [heq]
                                                exact cs_w22 ⟨n - 53600, hr⟩
                                              ·
                                                by_cases h23 : n < 53700
                                                ·
                                                  have hr : n - 53650 < 50 := by omega
                                                  have heq : n = (n - 53650) + 53650 := by omega
                                                  rw [heq]
                                                  exact cs_w23 ⟨n - 53650, hr⟩
                                                ·
                                                  by_cases h24 : n < 53750
                                                  ·
                                                    have hr : n - 53700 < 50 := by omega
                                                    have heq : n = (n - 53700) + 53700 := by omega
                                                    rw [heq]
                                                    exact cs_w24 ⟨n - 53700, hr⟩
                                                  ·
                                                    by_cases h25 : n < 53800
                                                    ·
                                                      have hr : n - 53750 < 50 := by omega
                                                      have heq : n = (n - 53750) + 53750 := by omega
                                                      rw [heq]
                                                      exact cs_w25 ⟨n - 53750, hr⟩
                                                    ·
                                                      by_cases h26 : n < 53850
                                                      ·
                                                        have hr : n - 53800 < 50 := by omega
                                                        have heq : n = (n - 53800) + 53800 := by omega
                                                        rw [heq]
                                                        exact cs_w26 ⟨n - 53800, hr⟩
                                                      ·
                                                        by_cases h27 : n < 53900
                                                        ·
                                                          have hr : n - 53850 < 50 := by omega
                                                          have heq : n = (n - 53850) + 53850 := by omega
                                                          rw [heq]
                                                          exact cs_w27 ⟨n - 53850, hr⟩
                                                        ·
                                                          by_cases h28 : n < 53950
                                                          ·
                                                            have hr : n - 53900 < 50 := by omega
                                                            have heq : n = (n - 53900) + 53900 := by omega
                                                            rw [heq]
                                                            exact cs_w28 ⟨n - 53900, hr⟩
                                                          ·
                                                            by_cases h29 : n < 54000
                                                            ·
                                                              have hr : n - 53950 < 50 := by omega
                                                              have heq : n = (n - 53950) + 53950 := by omega
                                                              rw [heq]
                                                              exact cs_w29 ⟨n - 53950, hr⟩
                                                            ·
                                                              by_cases h30 : n < 54050
                                                              ·
                                                                have hr : n - 54000 < 50 := by omega
                                                                have heq : n = (n - 54000) + 54000 := by omega
                                                                rw [heq]
                                                                exact cs_w30 ⟨n - 54000, hr⟩
                                                              ·
                                                                by_cases h31 : n < 54100
                                                                ·
                                                                  have hr : n - 54050 < 50 := by omega
                                                                  have heq : n = (n - 54050) + 54050 := by omega
                                                                  rw [heq]
                                                                  exact cs_w31 ⟨n - 54050, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 54150
                                                                  ·
                                                                    have hr : n - 54100 < 50 := by omega
                                                                    have heq : n = (n - 54100) + 54100 := by omega
                                                                    rw [heq]
                                                                    exact cs_w32 ⟨n - 54100, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 54200
                                                                    ·
                                                                      have hr : n - 54150 < 50 := by omega
                                                                      have heq : n = (n - 54150) + 54150 := by omega
                                                                      rw [heq]
                                                                      exact cs_w33 ⟨n - 54150, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 54250
                                                                      ·
                                                                        have hr : n - 54200 < 50 := by omega
                                                                        have heq : n = (n - 54200) + 54200 := by omega
                                                                        rw [heq]
                                                                        exact cs_w34 ⟨n - 54200, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 54300
                                                                        ·
                                                                          have hr : n - 54250 < 50 := by omega
                                                                          have heq : n = (n - 54250) + 54250 := by omega
                                                                          rw [heq]
                                                                          exact cs_w35 ⟨n - 54250, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 54350
                                                                          ·
                                                                            have hr : n - 54300 < 50 := by omega
                                                                            have heq : n = (n - 54300) + 54300 := by omega
                                                                            rw [heq]
                                                                            exact cs_w36 ⟨n - 54300, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 54400
                                                                            ·
                                                                              have hr : n - 54350 < 50 := by omega
                                                                              have heq : n = (n - 54350) + 54350 := by omega
                                                                              rw [heq]
                                                                              exact cs_w37 ⟨n - 54350, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 54450
                                                                              ·
                                                                                have hr : n - 54400 < 50 := by omega
                                                                                have heq : n = (n - 54400) + 54400 := by omega
                                                                                rw [heq]
                                                                                exact cs_w38 ⟨n - 54400, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 54500
                                                                                ·
                                                                                  have hr : n - 54450 < 50 := by omega
                                                                                  have heq : n = (n - 54450) + 54450 := by omega
                                                                                  rw [heq]
                                                                                  exact cs_w39 ⟨n - 54450, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 54550
                                                                                  ·
                                                                                    have hr : n - 54500 < 50 := by omega
                                                                                    have heq : n = (n - 54500) + 54500 := by omega
                                                                                    rw [heq]
                                                                                    exact cs_w40 ⟨n - 54500, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 54600
                                                                                    ·
                                                                                      have hr : n - 54550 < 50 := by omega
                                                                                      have heq : n = (n - 54550) + 54550 := by omega
                                                                                      rw [heq]
                                                                                      exact cs_w41 ⟨n - 54550, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 54650
                                                                                      ·
                                                                                        have hr : n - 54600 < 50 := by omega
                                                                                        have heq : n = (n - 54600) + 54600 := by omega
                                                                                        rw [heq]
                                                                                        exact cs_w42 ⟨n - 54600, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 54700
                                                                                        ·
                                                                                          have hr : n - 54650 < 50 := by omega
                                                                                          have heq : n = (n - 54650) + 54650 := by omega
                                                                                          rw [heq]
                                                                                          exact cs_w43 ⟨n - 54650, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 54750
                                                                                          ·
                                                                                            have hr : n - 54700 < 50 := by omega
                                                                                            have heq : n = (n - 54700) + 54700 := by omega
                                                                                            rw [heq]
                                                                                            exact cs_w44 ⟨n - 54700, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 54800
                                                                                            ·
                                                                                              have hr : n - 54750 < 50 := by omega
                                                                                              have heq : n = (n - 54750) + 54750 := by omega
                                                                                              rw [heq]
                                                                                              exact cs_w45 ⟨n - 54750, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 54850
                                                                                              ·
                                                                                                have hr : n - 54800 < 50 := by omega
                                                                                                have heq : n = (n - 54800) + 54800 := by omega
                                                                                                rw [heq]
                                                                                                exact cs_w46 ⟨n - 54800, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 54900
                                                                                                ·
                                                                                                  have hr : n - 54850 < 50 := by omega
                                                                                                  have heq : n = (n - 54850) + 54850 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cs_w47 ⟨n - 54850, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 54950
                                                                                                  ·
                                                                                                    have hr : n - 54900 < 50 := by omega
                                                                                                    have heq : n = (n - 54900) + 54900 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w48 ⟨n - 54900, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 54950 < 50 := by omega
                                                                                                    have heq : n = (n - 54950) + 54950 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w49 ⟨n - 54950, hr⟩


theorem centF_lt_range : ∀ n, 52500 ≤ n → n < 55000 → centF n < 23 := by
  intro n hlo hhi
  by_cases h0 : n < 52550
  · have hr : n - 52500 < 50 := by omega
    have heq : n = (n - 52500) + 52500 := by omega
    rw [heq]
    exact cl_w0 ⟨n - 52500, hr⟩
  ·
    by_cases h1 : n < 52600
    ·
      have hr : n - 52550 < 50 := by omega
      have heq : n = (n - 52550) + 52550 := by omega
      rw [heq]
      exact cl_w1 ⟨n - 52550, hr⟩
    ·
      by_cases h2 : n < 52650
      ·
        have hr : n - 52600 < 50 := by omega
        have heq : n = (n - 52600) + 52600 := by omega
        rw [heq]
        exact cl_w2 ⟨n - 52600, hr⟩
      ·
        by_cases h3 : n < 52700
        ·
          have hr : n - 52650 < 50 := by omega
          have heq : n = (n - 52650) + 52650 := by omega
          rw [heq]
          exact cl_w3 ⟨n - 52650, hr⟩
        ·
          by_cases h4 : n < 52750
          ·
            have hr : n - 52700 < 50 := by omega
            have heq : n = (n - 52700) + 52700 := by omega
            rw [heq]
            exact cl_w4 ⟨n - 52700, hr⟩
          ·
            by_cases h5 : n < 52800
            ·
              have hr : n - 52750 < 50 := by omega
              have heq : n = (n - 52750) + 52750 := by omega
              rw [heq]
              exact cl_w5 ⟨n - 52750, hr⟩
            ·
              by_cases h6 : n < 52850
              ·
                have hr : n - 52800 < 50 := by omega
                have heq : n = (n - 52800) + 52800 := by omega
                rw [heq]
                exact cl_w6 ⟨n - 52800, hr⟩
              ·
                by_cases h7 : n < 52900
                ·
                  have hr : n - 52850 < 50 := by omega
                  have heq : n = (n - 52850) + 52850 := by omega
                  rw [heq]
                  exact cl_w7 ⟨n - 52850, hr⟩
                ·
                  by_cases h8 : n < 52950
                  ·
                    have hr : n - 52900 < 50 := by omega
                    have heq : n = (n - 52900) + 52900 := by omega
                    rw [heq]
                    exact cl_w8 ⟨n - 52900, hr⟩
                  ·
                    by_cases h9 : n < 53000
                    ·
                      have hr : n - 52950 < 50 := by omega
                      have heq : n = (n - 52950) + 52950 := by omega
                      rw [heq]
                      exact cl_w9 ⟨n - 52950, hr⟩
                    ·
                      by_cases h10 : n < 53050
                      ·
                        have hr : n - 53000 < 50 := by omega
                        have heq : n = (n - 53000) + 53000 := by omega
                        rw [heq]
                        exact cl_w10 ⟨n - 53000, hr⟩
                      ·
                        by_cases h11 : n < 53100
                        ·
                          have hr : n - 53050 < 50 := by omega
                          have heq : n = (n - 53050) + 53050 := by omega
                          rw [heq]
                          exact cl_w11 ⟨n - 53050, hr⟩
                        ·
                          by_cases h12 : n < 53150
                          ·
                            have hr : n - 53100 < 50 := by omega
                            have heq : n = (n - 53100) + 53100 := by omega
                            rw [heq]
                            exact cl_w12 ⟨n - 53100, hr⟩
                          ·
                            by_cases h13 : n < 53200
                            ·
                              have hr : n - 53150 < 50 := by omega
                              have heq : n = (n - 53150) + 53150 := by omega
                              rw [heq]
                              exact cl_w13 ⟨n - 53150, hr⟩
                            ·
                              by_cases h14 : n < 53250
                              ·
                                have hr : n - 53200 < 50 := by omega
                                have heq : n = (n - 53200) + 53200 := by omega
                                rw [heq]
                                exact cl_w14 ⟨n - 53200, hr⟩
                              ·
                                by_cases h15 : n < 53300
                                ·
                                  have hr : n - 53250 < 50 := by omega
                                  have heq : n = (n - 53250) + 53250 := by omega
                                  rw [heq]
                                  exact cl_w15 ⟨n - 53250, hr⟩
                                ·
                                  by_cases h16 : n < 53350
                                  ·
                                    have hr : n - 53300 < 50 := by omega
                                    have heq : n = (n - 53300) + 53300 := by omega
                                    rw [heq]
                                    exact cl_w16 ⟨n - 53300, hr⟩
                                  ·
                                    by_cases h17 : n < 53400
                                    ·
                                      have hr : n - 53350 < 50 := by omega
                                      have heq : n = (n - 53350) + 53350 := by omega
                                      rw [heq]
                                      exact cl_w17 ⟨n - 53350, hr⟩
                                    ·
                                      by_cases h18 : n < 53450
                                      ·
                                        have hr : n - 53400 < 50 := by omega
                                        have heq : n = (n - 53400) + 53400 := by omega
                                        rw [heq]
                                        exact cl_w18 ⟨n - 53400, hr⟩
                                      ·
                                        by_cases h19 : n < 53500
                                        ·
                                          have hr : n - 53450 < 50 := by omega
                                          have heq : n = (n - 53450) + 53450 := by omega
                                          rw [heq]
                                          exact cl_w19 ⟨n - 53450, hr⟩
                                        ·
                                          by_cases h20 : n < 53550
                                          ·
                                            have hr : n - 53500 < 50 := by omega
                                            have heq : n = (n - 53500) + 53500 := by omega
                                            rw [heq]
                                            exact cl_w20 ⟨n - 53500, hr⟩
                                          ·
                                            by_cases h21 : n < 53600
                                            ·
                                              have hr : n - 53550 < 50 := by omega
                                              have heq : n = (n - 53550) + 53550 := by omega
                                              rw [heq]
                                              exact cl_w21 ⟨n - 53550, hr⟩
                                            ·
                                              by_cases h22 : n < 53650
                                              ·
                                                have hr : n - 53600 < 50 := by omega
                                                have heq : n = (n - 53600) + 53600 := by omega
                                                rw [heq]
                                                exact cl_w22 ⟨n - 53600, hr⟩
                                              ·
                                                by_cases h23 : n < 53700
                                                ·
                                                  have hr : n - 53650 < 50 := by omega
                                                  have heq : n = (n - 53650) + 53650 := by omega
                                                  rw [heq]
                                                  exact cl_w23 ⟨n - 53650, hr⟩
                                                ·
                                                  by_cases h24 : n < 53750
                                                  ·
                                                    have hr : n - 53700 < 50 := by omega
                                                    have heq : n = (n - 53700) + 53700 := by omega
                                                    rw [heq]
                                                    exact cl_w24 ⟨n - 53700, hr⟩
                                                  ·
                                                    by_cases h25 : n < 53800
                                                    ·
                                                      have hr : n - 53750 < 50 := by omega
                                                      have heq : n = (n - 53750) + 53750 := by omega
                                                      rw [heq]
                                                      exact cl_w25 ⟨n - 53750, hr⟩
                                                    ·
                                                      by_cases h26 : n < 53850
                                                      ·
                                                        have hr : n - 53800 < 50 := by omega
                                                        have heq : n = (n - 53800) + 53800 := by omega
                                                        rw [heq]
                                                        exact cl_w26 ⟨n - 53800, hr⟩
                                                      ·
                                                        by_cases h27 : n < 53900
                                                        ·
                                                          have hr : n - 53850 < 50 := by omega
                                                          have heq : n = (n - 53850) + 53850 := by omega
                                                          rw [heq]
                                                          exact cl_w27 ⟨n - 53850, hr⟩
                                                        ·
                                                          by_cases h28 : n < 53950
                                                          ·
                                                            have hr : n - 53900 < 50 := by omega
                                                            have heq : n = (n - 53900) + 53900 := by omega
                                                            rw [heq]
                                                            exact cl_w28 ⟨n - 53900, hr⟩
                                                          ·
                                                            by_cases h29 : n < 54000
                                                            ·
                                                              have hr : n - 53950 < 50 := by omega
                                                              have heq : n = (n - 53950) + 53950 := by omega
                                                              rw [heq]
                                                              exact cl_w29 ⟨n - 53950, hr⟩
                                                            ·
                                                              by_cases h30 : n < 54050
                                                              ·
                                                                have hr : n - 54000 < 50 := by omega
                                                                have heq : n = (n - 54000) + 54000 := by omega
                                                                rw [heq]
                                                                exact cl_w30 ⟨n - 54000, hr⟩
                                                              ·
                                                                by_cases h31 : n < 54100
                                                                ·
                                                                  have hr : n - 54050 < 50 := by omega
                                                                  have heq : n = (n - 54050) + 54050 := by omega
                                                                  rw [heq]
                                                                  exact cl_w31 ⟨n - 54050, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 54150
                                                                  ·
                                                                    have hr : n - 54100 < 50 := by omega
                                                                    have heq : n = (n - 54100) + 54100 := by omega
                                                                    rw [heq]
                                                                    exact cl_w32 ⟨n - 54100, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 54200
                                                                    ·
                                                                      have hr : n - 54150 < 50 := by omega
                                                                      have heq : n = (n - 54150) + 54150 := by omega
                                                                      rw [heq]
                                                                      exact cl_w33 ⟨n - 54150, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 54250
                                                                      ·
                                                                        have hr : n - 54200 < 50 := by omega
                                                                        have heq : n = (n - 54200) + 54200 := by omega
                                                                        rw [heq]
                                                                        exact cl_w34 ⟨n - 54200, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 54300
                                                                        ·
                                                                          have hr : n - 54250 < 50 := by omega
                                                                          have heq : n = (n - 54250) + 54250 := by omega
                                                                          rw [heq]
                                                                          exact cl_w35 ⟨n - 54250, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 54350
                                                                          ·
                                                                            have hr : n - 54300 < 50 := by omega
                                                                            have heq : n = (n - 54300) + 54300 := by omega
                                                                            rw [heq]
                                                                            exact cl_w36 ⟨n - 54300, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 54400
                                                                            ·
                                                                              have hr : n - 54350 < 50 := by omega
                                                                              have heq : n = (n - 54350) + 54350 := by omega
                                                                              rw [heq]
                                                                              exact cl_w37 ⟨n - 54350, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 54450
                                                                              ·
                                                                                have hr : n - 54400 < 50 := by omega
                                                                                have heq : n = (n - 54400) + 54400 := by omega
                                                                                rw [heq]
                                                                                exact cl_w38 ⟨n - 54400, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 54500
                                                                                ·
                                                                                  have hr : n - 54450 < 50 := by omega
                                                                                  have heq : n = (n - 54450) + 54450 := by omega
                                                                                  rw [heq]
                                                                                  exact cl_w39 ⟨n - 54450, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 54550
                                                                                  ·
                                                                                    have hr : n - 54500 < 50 := by omega
                                                                                    have heq : n = (n - 54500) + 54500 := by omega
                                                                                    rw [heq]
                                                                                    exact cl_w40 ⟨n - 54500, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 54600
                                                                                    ·
                                                                                      have hr : n - 54550 < 50 := by omega
                                                                                      have heq : n = (n - 54550) + 54550 := by omega
                                                                                      rw [heq]
                                                                                      exact cl_w41 ⟨n - 54550, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 54650
                                                                                      ·
                                                                                        have hr : n - 54600 < 50 := by omega
                                                                                        have heq : n = (n - 54600) + 54600 := by omega
                                                                                        rw [heq]
                                                                                        exact cl_w42 ⟨n - 54600, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 54700
                                                                                        ·
                                                                                          have hr : n - 54650 < 50 := by omega
                                                                                          have heq : n = (n - 54650) + 54650 := by omega
                                                                                          rw [heq]
                                                                                          exact cl_w43 ⟨n - 54650, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 54750
                                                                                          ·
                                                                                            have hr : n - 54700 < 50 := by omega
                                                                                            have heq : n = (n - 54700) + 54700 := by omega
                                                                                            rw [heq]
                                                                                            exact cl_w44 ⟨n - 54700, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 54800
                                                                                            ·
                                                                                              have hr : n - 54750 < 50 := by omega
                                                                                              have heq : n = (n - 54750) + 54750 := by omega
                                                                                              rw [heq]
                                                                                              exact cl_w45 ⟨n - 54750, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 54850
                                                                                              ·
                                                                                                have hr : n - 54800 < 50 := by omega
                                                                                                have heq : n = (n - 54800) + 54800 := by omega
                                                                                                rw [heq]
                                                                                                exact cl_w46 ⟨n - 54800, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 54900
                                                                                                ·
                                                                                                  have hr : n - 54850 < 50 := by omega
                                                                                                  have heq : n = (n - 54850) + 54850 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cl_w47 ⟨n - 54850, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 54950
                                                                                                  ·
                                                                                                    have hr : n - 54900 < 50 := by omega
                                                                                                    have heq : n = (n - 54900) + 54900 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w48 ⟨n - 54900, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 54950 < 50 := by omega
                                                                                                    have heq : n = (n - 54950) + 54950 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w49 ⟨n - 54950, hr⟩


theorem densSupG_lt_range : ∀ n, 52500 ≤ n → n < 55000 → densSupG n < 2 ^ 1771 := by
  intro n hlo hhi
  by_cases h0 : n < 52550
  · have hr : n - 52500 < 50 := by omega
    have heq : n = (n - 52500) + 52500 := by omega
    rw [heq]
    exact bd_w0 ⟨n - 52500, hr⟩
  ·
    by_cases h1 : n < 52600
    ·
      have hr : n - 52550 < 50 := by omega
      have heq : n = (n - 52550) + 52550 := by omega
      rw [heq]
      exact bd_w1 ⟨n - 52550, hr⟩
    ·
      by_cases h2 : n < 52650
      ·
        have hr : n - 52600 < 50 := by omega
        have heq : n = (n - 52600) + 52600 := by omega
        rw [heq]
        exact bd_w2 ⟨n - 52600, hr⟩
      ·
        by_cases h3 : n < 52700
        ·
          have hr : n - 52650 < 50 := by omega
          have heq : n = (n - 52650) + 52650 := by omega
          rw [heq]
          exact bd_w3 ⟨n - 52650, hr⟩
        ·
          by_cases h4 : n < 52750
          ·
            have hr : n - 52700 < 50 := by omega
            have heq : n = (n - 52700) + 52700 := by omega
            rw [heq]
            exact bd_w4 ⟨n - 52700, hr⟩
          ·
            by_cases h5 : n < 52800
            ·
              have hr : n - 52750 < 50 := by omega
              have heq : n = (n - 52750) + 52750 := by omega
              rw [heq]
              exact bd_w5 ⟨n - 52750, hr⟩
            ·
              by_cases h6 : n < 52850
              ·
                have hr : n - 52800 < 50 := by omega
                have heq : n = (n - 52800) + 52800 := by omega
                rw [heq]
                exact bd_w6 ⟨n - 52800, hr⟩
              ·
                by_cases h7 : n < 52900
                ·
                  have hr : n - 52850 < 50 := by omega
                  have heq : n = (n - 52850) + 52850 := by omega
                  rw [heq]
                  exact bd_w7 ⟨n - 52850, hr⟩
                ·
                  by_cases h8 : n < 52950
                  ·
                    have hr : n - 52900 < 50 := by omega
                    have heq : n = (n - 52900) + 52900 := by omega
                    rw [heq]
                    exact bd_w8 ⟨n - 52900, hr⟩
                  ·
                    by_cases h9 : n < 53000
                    ·
                      have hr : n - 52950 < 50 := by omega
                      have heq : n = (n - 52950) + 52950 := by omega
                      rw [heq]
                      exact bd_w9 ⟨n - 52950, hr⟩
                    ·
                      by_cases h10 : n < 53050
                      ·
                        have hr : n - 53000 < 50 := by omega
                        have heq : n = (n - 53000) + 53000 := by omega
                        rw [heq]
                        exact bd_w10 ⟨n - 53000, hr⟩
                      ·
                        by_cases h11 : n < 53100
                        ·
                          have hr : n - 53050 < 50 := by omega
                          have heq : n = (n - 53050) + 53050 := by omega
                          rw [heq]
                          exact bd_w11 ⟨n - 53050, hr⟩
                        ·
                          by_cases h12 : n < 53150
                          ·
                            have hr : n - 53100 < 50 := by omega
                            have heq : n = (n - 53100) + 53100 := by omega
                            rw [heq]
                            exact bd_w12 ⟨n - 53100, hr⟩
                          ·
                            by_cases h13 : n < 53200
                            ·
                              have hr : n - 53150 < 50 := by omega
                              have heq : n = (n - 53150) + 53150 := by omega
                              rw [heq]
                              exact bd_w13 ⟨n - 53150, hr⟩
                            ·
                              by_cases h14 : n < 53250
                              ·
                                have hr : n - 53200 < 50 := by omega
                                have heq : n = (n - 53200) + 53200 := by omega
                                rw [heq]
                                exact bd_w14 ⟨n - 53200, hr⟩
                              ·
                                by_cases h15 : n < 53300
                                ·
                                  have hr : n - 53250 < 50 := by omega
                                  have heq : n = (n - 53250) + 53250 := by omega
                                  rw [heq]
                                  exact bd_w15 ⟨n - 53250, hr⟩
                                ·
                                  by_cases h16 : n < 53350
                                  ·
                                    have hr : n - 53300 < 50 := by omega
                                    have heq : n = (n - 53300) + 53300 := by omega
                                    rw [heq]
                                    exact bd_w16 ⟨n - 53300, hr⟩
                                  ·
                                    by_cases h17 : n < 53400
                                    ·
                                      have hr : n - 53350 < 50 := by omega
                                      have heq : n = (n - 53350) + 53350 := by omega
                                      rw [heq]
                                      exact bd_w17 ⟨n - 53350, hr⟩
                                    ·
                                      by_cases h18 : n < 53450
                                      ·
                                        have hr : n - 53400 < 50 := by omega
                                        have heq : n = (n - 53400) + 53400 := by omega
                                        rw [heq]
                                        exact bd_w18 ⟨n - 53400, hr⟩
                                      ·
                                        by_cases h19 : n < 53500
                                        ·
                                          have hr : n - 53450 < 50 := by omega
                                          have heq : n = (n - 53450) + 53450 := by omega
                                          rw [heq]
                                          exact bd_w19 ⟨n - 53450, hr⟩
                                        ·
                                          by_cases h20 : n < 53550
                                          ·
                                            have hr : n - 53500 < 50 := by omega
                                            have heq : n = (n - 53500) + 53500 := by omega
                                            rw [heq]
                                            exact bd_w20 ⟨n - 53500, hr⟩
                                          ·
                                            by_cases h21 : n < 53600
                                            ·
                                              have hr : n - 53550 < 50 := by omega
                                              have heq : n = (n - 53550) + 53550 := by omega
                                              rw [heq]
                                              exact bd_w21 ⟨n - 53550, hr⟩
                                            ·
                                              by_cases h22 : n < 53650
                                              ·
                                                have hr : n - 53600 < 50 := by omega
                                                have heq : n = (n - 53600) + 53600 := by omega
                                                rw [heq]
                                                exact bd_w22 ⟨n - 53600, hr⟩
                                              ·
                                                by_cases h23 : n < 53700
                                                ·
                                                  have hr : n - 53650 < 50 := by omega
                                                  have heq : n = (n - 53650) + 53650 := by omega
                                                  rw [heq]
                                                  exact bd_w23 ⟨n - 53650, hr⟩
                                                ·
                                                  by_cases h24 : n < 53750
                                                  ·
                                                    have hr : n - 53700 < 50 := by omega
                                                    have heq : n = (n - 53700) + 53700 := by omega
                                                    rw [heq]
                                                    exact bd_w24 ⟨n - 53700, hr⟩
                                                  ·
                                                    by_cases h25 : n < 53800
                                                    ·
                                                      have hr : n - 53750 < 50 := by omega
                                                      have heq : n = (n - 53750) + 53750 := by omega
                                                      rw [heq]
                                                      exact bd_w25 ⟨n - 53750, hr⟩
                                                    ·
                                                      by_cases h26 : n < 53850
                                                      ·
                                                        have hr : n - 53800 < 50 := by omega
                                                        have heq : n = (n - 53800) + 53800 := by omega
                                                        rw [heq]
                                                        exact bd_w26 ⟨n - 53800, hr⟩
                                                      ·
                                                        by_cases h27 : n < 53900
                                                        ·
                                                          have hr : n - 53850 < 50 := by omega
                                                          have heq : n = (n - 53850) + 53850 := by omega
                                                          rw [heq]
                                                          exact bd_w27 ⟨n - 53850, hr⟩
                                                        ·
                                                          by_cases h28 : n < 53950
                                                          ·
                                                            have hr : n - 53900 < 50 := by omega
                                                            have heq : n = (n - 53900) + 53900 := by omega
                                                            rw [heq]
                                                            exact bd_w28 ⟨n - 53900, hr⟩
                                                          ·
                                                            by_cases h29 : n < 54000
                                                            ·
                                                              have hr : n - 53950 < 50 := by omega
                                                              have heq : n = (n - 53950) + 53950 := by omega
                                                              rw [heq]
                                                              exact bd_w29 ⟨n - 53950, hr⟩
                                                            ·
                                                              by_cases h30 : n < 54050
                                                              ·
                                                                have hr : n - 54000 < 50 := by omega
                                                                have heq : n = (n - 54000) + 54000 := by omega
                                                                rw [heq]
                                                                exact bd_w30 ⟨n - 54000, hr⟩
                                                              ·
                                                                by_cases h31 : n < 54100
                                                                ·
                                                                  have hr : n - 54050 < 50 := by omega
                                                                  have heq : n = (n - 54050) + 54050 := by omega
                                                                  rw [heq]
                                                                  exact bd_w31 ⟨n - 54050, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 54150
                                                                  ·
                                                                    have hr : n - 54100 < 50 := by omega
                                                                    have heq : n = (n - 54100) + 54100 := by omega
                                                                    rw [heq]
                                                                    exact bd_w32 ⟨n - 54100, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 54200
                                                                    ·
                                                                      have hr : n - 54150 < 50 := by omega
                                                                      have heq : n = (n - 54150) + 54150 := by omega
                                                                      rw [heq]
                                                                      exact bd_w33 ⟨n - 54150, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 54250
                                                                      ·
                                                                        have hr : n - 54200 < 50 := by omega
                                                                        have heq : n = (n - 54200) + 54200 := by omega
                                                                        rw [heq]
                                                                        exact bd_w34 ⟨n - 54200, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 54300
                                                                        ·
                                                                          have hr : n - 54250 < 50 := by omega
                                                                          have heq : n = (n - 54250) + 54250 := by omega
                                                                          rw [heq]
                                                                          exact bd_w35 ⟨n - 54250, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 54350
                                                                          ·
                                                                            have hr : n - 54300 < 50 := by omega
                                                                            have heq : n = (n - 54300) + 54300 := by omega
                                                                            rw [heq]
                                                                            exact bd_w36 ⟨n - 54300, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 54400
                                                                            ·
                                                                              have hr : n - 54350 < 50 := by omega
                                                                              have heq : n = (n - 54350) + 54350 := by omega
                                                                              rw [heq]
                                                                              exact bd_w37 ⟨n - 54350, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 54450
                                                                              ·
                                                                                have hr : n - 54400 < 50 := by omega
                                                                                have heq : n = (n - 54400) + 54400 := by omega
                                                                                rw [heq]
                                                                                exact bd_w38 ⟨n - 54400, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 54500
                                                                                ·
                                                                                  have hr : n - 54450 < 50 := by omega
                                                                                  have heq : n = (n - 54450) + 54450 := by omega
                                                                                  rw [heq]
                                                                                  exact bd_w39 ⟨n - 54450, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 54550
                                                                                  ·
                                                                                    have hr : n - 54500 < 50 := by omega
                                                                                    have heq : n = (n - 54500) + 54500 := by omega
                                                                                    rw [heq]
                                                                                    exact bd_w40 ⟨n - 54500, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 54600
                                                                                    ·
                                                                                      have hr : n - 54550 < 50 := by omega
                                                                                      have heq : n = (n - 54550) + 54550 := by omega
                                                                                      rw [heq]
                                                                                      exact bd_w41 ⟨n - 54550, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 54650
                                                                                      ·
                                                                                        have hr : n - 54600 < 50 := by omega
                                                                                        have heq : n = (n - 54600) + 54600 := by omega
                                                                                        rw [heq]
                                                                                        exact bd_w42 ⟨n - 54600, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 54700
                                                                                        ·
                                                                                          have hr : n - 54650 < 50 := by omega
                                                                                          have heq : n = (n - 54650) + 54650 := by omega
                                                                                          rw [heq]
                                                                                          exact bd_w43 ⟨n - 54650, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 54750
                                                                                          ·
                                                                                            have hr : n - 54700 < 50 := by omega
                                                                                            have heq : n = (n - 54700) + 54700 := by omega
                                                                                            rw [heq]
                                                                                            exact bd_w44 ⟨n - 54700, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 54800
                                                                                            ·
                                                                                              have hr : n - 54750 < 50 := by omega
                                                                                              have heq : n = (n - 54750) + 54750 := by omega
                                                                                              rw [heq]
                                                                                              exact bd_w45 ⟨n - 54750, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 54850
                                                                                              ·
                                                                                                have hr : n - 54800 < 50 := by omega
                                                                                                have heq : n = (n - 54800) + 54800 := by omega
                                                                                                rw [heq]
                                                                                                exact bd_w46 ⟨n - 54800, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 54900
                                                                                                ·
                                                                                                  have hr : n - 54850 < 50 := by omega
                                                                                                  have heq : n = (n - 54850) + 54850 := by omega
                                                                                                  rw [heq]
                                                                                                  exact bd_w47 ⟨n - 54850, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 54950
                                                                                                  ·
                                                                                                    have hr : n - 54900 < 50 := by omega
                                                                                                    have heq : n = (n - 54900) + 54900 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w48 ⟨n - 54900, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 54950 < 50 := by omega
                                                                                                    have heq : n = (n - 54950) + 54950 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w49 ⟨n - 54950, hr⟩


end IntMul.Kappa.R8.Bit.Oppbank.CentBound10b


