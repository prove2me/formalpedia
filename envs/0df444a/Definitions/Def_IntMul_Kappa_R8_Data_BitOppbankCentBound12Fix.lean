-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound12Fix
-- name    : IntMul_Kappa_R8_Data_BitOppbankCentBound12Fix
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T22:19:56.616997+00:00
-- url     : https://prove2.me/theorems/58848450-ac2e-4e5e-8df3-cc2bde463855
-- title:
--   IntMul Kappa R8 Data BitOppbankCentBound12Fix
-- statement:
--   Densified HasCentre support certificates (IntMul_Kappa_R8_Data_BitOppbankCentBound12Fix) retargeted to PndFix/CentFix.

-- CentBound12Fix: PndFix retarget
-- CentBound pack 12: densified HasCentre certificates on n ∈ [60000, 62478)
-- Generated for AllDensCentred (star-mask land + centF).

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPndFix
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentFix
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
set_option exponentiation.threshold 2000

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open IntMul.Kappa.R8.Bit.Oppbank.Cent

namespace IntMul.Kappa.R8.Bit.Oppbank.CentBound12Fix

private theorem cs_w0 : ∀ n : Fin 50, centredStar (densSupG (n.val + 60000)) (centF (n.val + 60000)) = true := by decide
private theorem cl_w0 : ∀ n : Fin 50, centF (n.val + 60000) < 23 := by decide
private theorem bd_w0 : ∀ n : Fin 50, densSupG (n.val + 60000) < 2 ^ 1771 := by decide
private theorem cs_w1 : ∀ n : Fin 50, centredStar (densSupG (n.val + 60050)) (centF (n.val + 60050)) = true := by decide
private theorem cl_w1 : ∀ n : Fin 50, centF (n.val + 60050) < 23 := by decide
private theorem bd_w1 : ∀ n : Fin 50, densSupG (n.val + 60050) < 2 ^ 1771 := by decide
private theorem cs_w2 : ∀ n : Fin 50, centredStar (densSupG (n.val + 60100)) (centF (n.val + 60100)) = true := by decide
private theorem cl_w2 : ∀ n : Fin 50, centF (n.val + 60100) < 23 := by decide
private theorem bd_w2 : ∀ n : Fin 50, densSupG (n.val + 60100) < 2 ^ 1771 := by decide
private theorem cs_w3 : ∀ n : Fin 50, centredStar (densSupG (n.val + 60150)) (centF (n.val + 60150)) = true := by decide
private theorem cl_w3 : ∀ n : Fin 50, centF (n.val + 60150) < 23 := by decide
private theorem bd_w3 : ∀ n : Fin 50, densSupG (n.val + 60150) < 2 ^ 1771 := by decide
private theorem cs_w4 : ∀ n : Fin 50, centredStar (densSupG (n.val + 60200)) (centF (n.val + 60200)) = true := by decide
private theorem cl_w4 : ∀ n : Fin 50, centF (n.val + 60200) < 23 := by decide
private theorem bd_w4 : ∀ n : Fin 50, densSupG (n.val + 60200) < 2 ^ 1771 := by decide
private theorem cs_w5 : ∀ n : Fin 50, centredStar (densSupG (n.val + 60250)) (centF (n.val + 60250)) = true := by decide
private theorem cl_w5 : ∀ n : Fin 50, centF (n.val + 60250) < 23 := by decide
private theorem bd_w5 : ∀ n : Fin 50, densSupG (n.val + 60250) < 2 ^ 1771 := by decide
private theorem cs_w6 : ∀ n : Fin 50, centredStar (densSupG (n.val + 60300)) (centF (n.val + 60300)) = true := by decide
private theorem cl_w6 : ∀ n : Fin 50, centF (n.val + 60300) < 23 := by decide
private theorem bd_w6 : ∀ n : Fin 50, densSupG (n.val + 60300) < 2 ^ 1771 := by decide
private theorem cs_w7 : ∀ n : Fin 50, centredStar (densSupG (n.val + 60350)) (centF (n.val + 60350)) = true := by decide
private theorem cl_w7 : ∀ n : Fin 50, centF (n.val + 60350) < 23 := by decide
private theorem bd_w7 : ∀ n : Fin 50, densSupG (n.val + 60350) < 2 ^ 1771 := by decide
private theorem cs_w8 : ∀ n : Fin 50, centredStar (densSupG (n.val + 60400)) (centF (n.val + 60400)) = true := by decide
private theorem cl_w8 : ∀ n : Fin 50, centF (n.val + 60400) < 23 := by decide
private theorem bd_w8 : ∀ n : Fin 50, densSupG (n.val + 60400) < 2 ^ 1771 := by decide
private theorem cs_w9 : ∀ n : Fin 50, centredStar (densSupG (n.val + 60450)) (centF (n.val + 60450)) = true := by decide
private theorem cl_w9 : ∀ n : Fin 50, centF (n.val + 60450) < 23 := by decide
private theorem bd_w9 : ∀ n : Fin 50, densSupG (n.val + 60450) < 2 ^ 1771 := by decide
private theorem cs_w10 : ∀ n : Fin 50, centredStar (densSupG (n.val + 60500)) (centF (n.val + 60500)) = true := by decide
private theorem cl_w10 : ∀ n : Fin 50, centF (n.val + 60500) < 23 := by decide
private theorem bd_w10 : ∀ n : Fin 50, densSupG (n.val + 60500) < 2 ^ 1771 := by decide
private theorem cs_w11 : ∀ n : Fin 50, centredStar (densSupG (n.val + 60550)) (centF (n.val + 60550)) = true := by decide
private theorem cl_w11 : ∀ n : Fin 50, centF (n.val + 60550) < 23 := by decide
private theorem bd_w11 : ∀ n : Fin 50, densSupG (n.val + 60550) < 2 ^ 1771 := by decide
private theorem cs_w12 : ∀ n : Fin 50, centredStar (densSupG (n.val + 60600)) (centF (n.val + 60600)) = true := by decide
private theorem cl_w12 : ∀ n : Fin 50, centF (n.val + 60600) < 23 := by decide
private theorem bd_w12 : ∀ n : Fin 50, densSupG (n.val + 60600) < 2 ^ 1771 := by decide
private theorem cs_w13 : ∀ n : Fin 50, centredStar (densSupG (n.val + 60650)) (centF (n.val + 60650)) = true := by decide
private theorem cl_w13 : ∀ n : Fin 50, centF (n.val + 60650) < 23 := by decide
private theorem bd_w13 : ∀ n : Fin 50, densSupG (n.val + 60650) < 2 ^ 1771 := by decide
private theorem cs_w14 : ∀ n : Fin 50, centredStar (densSupG (n.val + 60700)) (centF (n.val + 60700)) = true := by decide
private theorem cl_w14 : ∀ n : Fin 50, centF (n.val + 60700) < 23 := by decide
private theorem bd_w14 : ∀ n : Fin 50, densSupG (n.val + 60700) < 2 ^ 1771 := by decide
private theorem cs_w15 : ∀ n : Fin 50, centredStar (densSupG (n.val + 60750)) (centF (n.val + 60750)) = true := by decide
private theorem cl_w15 : ∀ n : Fin 50, centF (n.val + 60750) < 23 := by decide
private theorem bd_w15 : ∀ n : Fin 50, densSupG (n.val + 60750) < 2 ^ 1771 := by decide
private theorem cs_w16 : ∀ n : Fin 50, centredStar (densSupG (n.val + 60800)) (centF (n.val + 60800)) = true := by decide
private theorem cl_w16 : ∀ n : Fin 50, centF (n.val + 60800) < 23 := by decide
private theorem bd_w16 : ∀ n : Fin 50, densSupG (n.val + 60800) < 2 ^ 1771 := by decide
private theorem cs_w17 : ∀ n : Fin 50, centredStar (densSupG (n.val + 60850)) (centF (n.val + 60850)) = true := by decide
private theorem cl_w17 : ∀ n : Fin 50, centF (n.val + 60850) < 23 := by decide
private theorem bd_w17 : ∀ n : Fin 50, densSupG (n.val + 60850) < 2 ^ 1771 := by decide
private theorem cs_w18 : ∀ n : Fin 50, centredStar (densSupG (n.val + 60900)) (centF (n.val + 60900)) = true := by decide
private theorem cl_w18 : ∀ n : Fin 50, centF (n.val + 60900) < 23 := by decide
private theorem bd_w18 : ∀ n : Fin 50, densSupG (n.val + 60900) < 2 ^ 1771 := by decide
private theorem cs_w19 : ∀ n : Fin 50, centredStar (densSupG (n.val + 60950)) (centF (n.val + 60950)) = true := by decide
private theorem cl_w19 : ∀ n : Fin 50, centF (n.val + 60950) < 23 := by decide
private theorem bd_w19 : ∀ n : Fin 50, densSupG (n.val + 60950) < 2 ^ 1771 := by decide
private theorem cs_w20 : ∀ n : Fin 50, centredStar (densSupG (n.val + 61000)) (centF (n.val + 61000)) = true := by decide
private theorem cl_w20 : ∀ n : Fin 50, centF (n.val + 61000) < 23 := by decide
private theorem bd_w20 : ∀ n : Fin 50, densSupG (n.val + 61000) < 2 ^ 1771 := by decide
private theorem cs_w21 : ∀ n : Fin 50, centredStar (densSupG (n.val + 61050)) (centF (n.val + 61050)) = true := by decide
private theorem cl_w21 : ∀ n : Fin 50, centF (n.val + 61050) < 23 := by decide
private theorem bd_w21 : ∀ n : Fin 50, densSupG (n.val + 61050) < 2 ^ 1771 := by decide
private theorem cs_w22 : ∀ n : Fin 50, centredStar (densSupG (n.val + 61100)) (centF (n.val + 61100)) = true := by decide
private theorem cl_w22 : ∀ n : Fin 50, centF (n.val + 61100) < 23 := by decide
private theorem bd_w22 : ∀ n : Fin 50, densSupG (n.val + 61100) < 2 ^ 1771 := by decide
private theorem cs_w23 : ∀ n : Fin 50, centredStar (densSupG (n.val + 61150)) (centF (n.val + 61150)) = true := by decide
private theorem cl_w23 : ∀ n : Fin 50, centF (n.val + 61150) < 23 := by decide
private theorem bd_w23 : ∀ n : Fin 50, densSupG (n.val + 61150) < 2 ^ 1771 := by decide
private theorem cs_w24 : ∀ n : Fin 50, centredStar (densSupG (n.val + 61200)) (centF (n.val + 61200)) = true := by decide
private theorem cl_w24 : ∀ n : Fin 50, centF (n.val + 61200) < 23 := by decide
private theorem bd_w24 : ∀ n : Fin 50, densSupG (n.val + 61200) < 2 ^ 1771 := by decide
private theorem cs_w25 : ∀ n : Fin 50, centredStar (densSupG (n.val + 61250)) (centF (n.val + 61250)) = true := by decide
private theorem cl_w25 : ∀ n : Fin 50, centF (n.val + 61250) < 23 := by decide
private theorem bd_w25 : ∀ n : Fin 50, densSupG (n.val + 61250) < 2 ^ 1771 := by decide
private theorem cs_w26 : ∀ n : Fin 50, centredStar (densSupG (n.val + 61300)) (centF (n.val + 61300)) = true := by decide
private theorem cl_w26 : ∀ n : Fin 50, centF (n.val + 61300) < 23 := by decide
private theorem bd_w26 : ∀ n : Fin 50, densSupG (n.val + 61300) < 2 ^ 1771 := by decide
private theorem cs_w27 : ∀ n : Fin 50, centredStar (densSupG (n.val + 61350)) (centF (n.val + 61350)) = true := by decide
private theorem cl_w27 : ∀ n : Fin 50, centF (n.val + 61350) < 23 := by decide
private theorem bd_w27 : ∀ n : Fin 50, densSupG (n.val + 61350) < 2 ^ 1771 := by decide
private theorem cs_w28 : ∀ n : Fin 50, centredStar (densSupG (n.val + 61400)) (centF (n.val + 61400)) = true := by decide
private theorem cl_w28 : ∀ n : Fin 50, centF (n.val + 61400) < 23 := by decide
private theorem bd_w28 : ∀ n : Fin 50, densSupG (n.val + 61400) < 2 ^ 1771 := by decide
private theorem cs_w29 : ∀ n : Fin 50, centredStar (densSupG (n.val + 61450)) (centF (n.val + 61450)) = true := by decide
private theorem cl_w29 : ∀ n : Fin 50, centF (n.val + 61450) < 23 := by decide
private theorem bd_w29 : ∀ n : Fin 50, densSupG (n.val + 61450) < 2 ^ 1771 := by decide
private theorem cs_w30 : ∀ n : Fin 50, centredStar (densSupG (n.val + 61500)) (centF (n.val + 61500)) = true := by decide
private theorem cl_w30 : ∀ n : Fin 50, centF (n.val + 61500) < 23 := by decide
private theorem bd_w30 : ∀ n : Fin 50, densSupG (n.val + 61500) < 2 ^ 1771 := by decide
private theorem cs_w31 : ∀ n : Fin 50, centredStar (densSupG (n.val + 61550)) (centF (n.val + 61550)) = true := by decide
private theorem cl_w31 : ∀ n : Fin 50, centF (n.val + 61550) < 23 := by decide
private theorem bd_w31 : ∀ n : Fin 50, densSupG (n.val + 61550) < 2 ^ 1771 := by decide
private theorem cs_w32 : ∀ n : Fin 50, centredStar (densSupG (n.val + 61600)) (centF (n.val + 61600)) = true := by decide
private theorem cl_w32 : ∀ n : Fin 50, centF (n.val + 61600) < 23 := by decide
private theorem bd_w32 : ∀ n : Fin 50, densSupG (n.val + 61600) < 2 ^ 1771 := by decide
private theorem cs_w33 : ∀ n : Fin 50, centredStar (densSupG (n.val + 61650)) (centF (n.val + 61650)) = true := by decide
private theorem cl_w33 : ∀ n : Fin 50, centF (n.val + 61650) < 23 := by decide
private theorem bd_w33 : ∀ n : Fin 50, densSupG (n.val + 61650) < 2 ^ 1771 := by decide
private theorem cs_w34 : ∀ n : Fin 50, centredStar (densSupG (n.val + 61700)) (centF (n.val + 61700)) = true := by decide
private theorem cl_w34 : ∀ n : Fin 50, centF (n.val + 61700) < 23 := by decide
private theorem bd_w34 : ∀ n : Fin 50, densSupG (n.val + 61700) < 2 ^ 1771 := by decide
private theorem cs_w35 : ∀ n : Fin 50, centredStar (densSupG (n.val + 61750)) (centF (n.val + 61750)) = true := by decide
private theorem cl_w35 : ∀ n : Fin 50, centF (n.val + 61750) < 23 := by decide
private theorem bd_w35 : ∀ n : Fin 50, densSupG (n.val + 61750) < 2 ^ 1771 := by decide
private theorem cs_w36 : ∀ n : Fin 50, centredStar (densSupG (n.val + 61800)) (centF (n.val + 61800)) = true := by decide
private theorem cl_w36 : ∀ n : Fin 50, centF (n.val + 61800) < 23 := by decide
private theorem bd_w36 : ∀ n : Fin 50, densSupG (n.val + 61800) < 2 ^ 1771 := by decide
private theorem cs_w37 : ∀ n : Fin 50, centredStar (densSupG (n.val + 61850)) (centF (n.val + 61850)) = true := by decide
private theorem cl_w37 : ∀ n : Fin 50, centF (n.val + 61850) < 23 := by decide
private theorem bd_w37 : ∀ n : Fin 50, densSupG (n.val + 61850) < 2 ^ 1771 := by decide
private theorem cs_w38 : ∀ n : Fin 50, centredStar (densSupG (n.val + 61900)) (centF (n.val + 61900)) = true := by decide
private theorem cl_w38 : ∀ n : Fin 50, centF (n.val + 61900) < 23 := by decide
private theorem bd_w38 : ∀ n : Fin 50, densSupG (n.val + 61900) < 2 ^ 1771 := by decide
private theorem cs_w39 : ∀ n : Fin 50, centredStar (densSupG (n.val + 61950)) (centF (n.val + 61950)) = true := by decide
private theorem cl_w39 : ∀ n : Fin 50, centF (n.val + 61950) < 23 := by decide
private theorem bd_w39 : ∀ n : Fin 50, densSupG (n.val + 61950) < 2 ^ 1771 := by decide
private theorem cs_w40 : ∀ n : Fin 50, centredStar (densSupG (n.val + 62000)) (centF (n.val + 62000)) = true := by decide
private theorem cl_w40 : ∀ n : Fin 50, centF (n.val + 62000) < 23 := by decide
private theorem bd_w40 : ∀ n : Fin 50, densSupG (n.val + 62000) < 2 ^ 1771 := by decide
private theorem cs_w41 : ∀ n : Fin 50, centredStar (densSupG (n.val + 62050)) (centF (n.val + 62050)) = true := by decide
private theorem cl_w41 : ∀ n : Fin 50, centF (n.val + 62050) < 23 := by decide
private theorem bd_w41 : ∀ n : Fin 50, densSupG (n.val + 62050) < 2 ^ 1771 := by decide
private theorem cs_w42 : ∀ n : Fin 50, centredStar (densSupG (n.val + 62100)) (centF (n.val + 62100)) = true := by decide
private theorem cl_w42 : ∀ n : Fin 50, centF (n.val + 62100) < 23 := by decide
private theorem bd_w42 : ∀ n : Fin 50, densSupG (n.val + 62100) < 2 ^ 1771 := by decide
private theorem cs_w43 : ∀ n : Fin 50, centredStar (densSupG (n.val + 62150)) (centF (n.val + 62150)) = true := by decide
private theorem cl_w43 : ∀ n : Fin 50, centF (n.val + 62150) < 23 := by decide
private theorem bd_w43 : ∀ n : Fin 50, densSupG (n.val + 62150) < 2 ^ 1771 := by decide
private theorem cs_w44 : ∀ n : Fin 50, centredStar (densSupG (n.val + 62200)) (centF (n.val + 62200)) = true := by decide
private theorem cl_w44 : ∀ n : Fin 50, centF (n.val + 62200) < 23 := by decide
private theorem bd_w44 : ∀ n : Fin 50, densSupG (n.val + 62200) < 2 ^ 1771 := by decide
private theorem cs_w45 : ∀ n : Fin 50, centredStar (densSupG (n.val + 62250)) (centF (n.val + 62250)) = true := by decide
private theorem cl_w45 : ∀ n : Fin 50, centF (n.val + 62250) < 23 := by decide
private theorem bd_w45 : ∀ n : Fin 50, densSupG (n.val + 62250) < 2 ^ 1771 := by decide
private theorem cs_w46 : ∀ n : Fin 50, centredStar (densSupG (n.val + 62300)) (centF (n.val + 62300)) = true := by decide
private theorem cl_w46 : ∀ n : Fin 50, centF (n.val + 62300) < 23 := by decide
private theorem bd_w46 : ∀ n : Fin 50, densSupG (n.val + 62300) < 2 ^ 1771 := by decide
private theorem cs_w47 : ∀ n : Fin 50, centredStar (densSupG (n.val + 62350)) (centF (n.val + 62350)) = true := by decide
private theorem cl_w47 : ∀ n : Fin 50, centF (n.val + 62350) < 23 := by decide
private theorem bd_w47 : ∀ n : Fin 50, densSupG (n.val + 62350) < 2 ^ 1771 := by decide
private theorem cs_w48 : ∀ n : Fin 50, centredStar (densSupG (n.val + 62400)) (centF (n.val + 62400)) = true := by decide
private theorem cl_w48 : ∀ n : Fin 50, centF (n.val + 62400) < 23 := by decide
private theorem bd_w48 : ∀ n : Fin 50, densSupG (n.val + 62400) < 2 ^ 1771 := by decide
private theorem cs_w49 : ∀ n : Fin 28, centredStar (densSupG (n.val + 62450)) (centF (n.val + 62450)) = true := by decide
private theorem cl_w49 : ∀ n : Fin 28, centF (n.val + 62450) < 23 := by decide
private theorem bd_w49 : ∀ n : Fin 28, densSupG (n.val + 62450) < 2 ^ 1771 := by decide

theorem centredStar_range : ∀ n, 60000 ≤ n → n < 62478 → centredStar (densSupG n) (centF n) = true := by
  intro n hlo hhi
  by_cases h0 : n < 60050
  · have hr : n - 60000 < 50 := by omega
    have heq : n = (n - 60000) + 60000 := by omega
    rw [heq]
    exact cs_w0 ⟨n - 60000, hr⟩
  ·
    by_cases h1 : n < 60100
    · have hr : n - 60050 < 50 := by omega
      have heq : n = (n - 60050) + 60050 := by omega
      rw [heq]
      exact cs_w1 ⟨n - 60050, hr⟩
    ·
      by_cases h2 : n < 60150
      · have hr : n - 60100 < 50 := by omega
        have heq : n = (n - 60100) + 60100 := by omega
        rw [heq]
        exact cs_w2 ⟨n - 60100, hr⟩
      ·
        by_cases h3 : n < 60200
        · have hr : n - 60150 < 50 := by omega
          have heq : n = (n - 60150) + 60150 := by omega
          rw [heq]
          exact cs_w3 ⟨n - 60150, hr⟩
        ·
          by_cases h4 : n < 60250
          · have hr : n - 60200 < 50 := by omega
            have heq : n = (n - 60200) + 60200 := by omega
            rw [heq]
            exact cs_w4 ⟨n - 60200, hr⟩
          ·
            by_cases h5 : n < 60300
            · have hr : n - 60250 < 50 := by omega
              have heq : n = (n - 60250) + 60250 := by omega
              rw [heq]
              exact cs_w5 ⟨n - 60250, hr⟩
            ·
              by_cases h6 : n < 60350
              · have hr : n - 60300 < 50 := by omega
                have heq : n = (n - 60300) + 60300 := by omega
                rw [heq]
                exact cs_w6 ⟨n - 60300, hr⟩
              ·
                by_cases h7 : n < 60400
                · have hr : n - 60350 < 50 := by omega
                  have heq : n = (n - 60350) + 60350 := by omega
                  rw [heq]
                  exact cs_w7 ⟨n - 60350, hr⟩
                ·
                  by_cases h8 : n < 60450
                  · have hr : n - 60400 < 50 := by omega
                    have heq : n = (n - 60400) + 60400 := by omega
                    rw [heq]
                    exact cs_w8 ⟨n - 60400, hr⟩
                  ·
                    by_cases h9 : n < 60500
                    · have hr : n - 60450 < 50 := by omega
                      have heq : n = (n - 60450) + 60450 := by omega
                      rw [heq]
                      exact cs_w9 ⟨n - 60450, hr⟩
                    ·
                      by_cases h10 : n < 60550
                      · have hr : n - 60500 < 50 := by omega
                        have heq : n = (n - 60500) + 60500 := by omega
                        rw [heq]
                        exact cs_w10 ⟨n - 60500, hr⟩
                      ·
                        by_cases h11 : n < 60600
                        · have hr : n - 60550 < 50 := by omega
                          have heq : n = (n - 60550) + 60550 := by omega
                          rw [heq]
                          exact cs_w11 ⟨n - 60550, hr⟩
                        ·
                          by_cases h12 : n < 60650
                          · have hr : n - 60600 < 50 := by omega
                            have heq : n = (n - 60600) + 60600 := by omega
                            rw [heq]
                            exact cs_w12 ⟨n - 60600, hr⟩
                          ·
                            by_cases h13 : n < 60700
                            · have hr : n - 60650 < 50 := by omega
                              have heq : n = (n - 60650) + 60650 := by omega
                              rw [heq]
                              exact cs_w13 ⟨n - 60650, hr⟩
                            ·
                              by_cases h14 : n < 60750
                              · have hr : n - 60700 < 50 := by omega
                                have heq : n = (n - 60700) + 60700 := by omega
                                rw [heq]
                                exact cs_w14 ⟨n - 60700, hr⟩
                              ·
                                by_cases h15 : n < 60800
                                · have hr : n - 60750 < 50 := by omega
                                  have heq : n = (n - 60750) + 60750 := by omega
                                  rw [heq]
                                  exact cs_w15 ⟨n - 60750, hr⟩
                                ·
                                  by_cases h16 : n < 60850
                                  · have hr : n - 60800 < 50 := by omega
                                    have heq : n = (n - 60800) + 60800 := by omega
                                    rw [heq]
                                    exact cs_w16 ⟨n - 60800, hr⟩
                                  ·
                                    by_cases h17 : n < 60900
                                    · have hr : n - 60850 < 50 := by omega
                                      have heq : n = (n - 60850) + 60850 := by omega
                                      rw [heq]
                                      exact cs_w17 ⟨n - 60850, hr⟩
                                    ·
                                      by_cases h18 : n < 60950
                                      · have hr : n - 60900 < 50 := by omega
                                        have heq : n = (n - 60900) + 60900 := by omega
                                        rw [heq]
                                        exact cs_w18 ⟨n - 60900, hr⟩
                                      ·
                                        by_cases h19 : n < 61000
                                        · have hr : n - 60950 < 50 := by omega
                                          have heq : n = (n - 60950) + 60950 := by omega
                                          rw [heq]
                                          exact cs_w19 ⟨n - 60950, hr⟩
                                        ·
                                          by_cases h20 : n < 61050
                                          · have hr : n - 61000 < 50 := by omega
                                            have heq : n = (n - 61000) + 61000 := by omega
                                            rw [heq]
                                            exact cs_w20 ⟨n - 61000, hr⟩
                                          ·
                                            by_cases h21 : n < 61100
                                            · have hr : n - 61050 < 50 := by omega
                                              have heq : n = (n - 61050) + 61050 := by omega
                                              rw [heq]
                                              exact cs_w21 ⟨n - 61050, hr⟩
                                            ·
                                              by_cases h22 : n < 61150
                                              · have hr : n - 61100 < 50 := by omega
                                                have heq : n = (n - 61100) + 61100 := by omega
                                                rw [heq]
                                                exact cs_w22 ⟨n - 61100, hr⟩
                                              ·
                                                by_cases h23 : n < 61200
                                                · have hr : n - 61150 < 50 := by omega
                                                  have heq : n = (n - 61150) + 61150 := by omega
                                                  rw [heq]
                                                  exact cs_w23 ⟨n - 61150, hr⟩
                                                ·
                                                  by_cases h24 : n < 61250
                                                  · have hr : n - 61200 < 50 := by omega
                                                    have heq : n = (n - 61200) + 61200 := by omega
                                                    rw [heq]
                                                    exact cs_w24 ⟨n - 61200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 61300
                                                    · have hr : n - 61250 < 50 := by omega
                                                      have heq : n = (n - 61250) + 61250 := by omega
                                                      rw [heq]
                                                      exact cs_w25 ⟨n - 61250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 61350
                                                      · have hr : n - 61300 < 50 := by omega
                                                        have heq : n = (n - 61300) + 61300 := by omega
                                                        rw [heq]
                                                        exact cs_w26 ⟨n - 61300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 61400
                                                        · have hr : n - 61350 < 50 := by omega
                                                          have heq : n = (n - 61350) + 61350 := by omega
                                                          rw [heq]
                                                          exact cs_w27 ⟨n - 61350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 61450
                                                          · have hr : n - 61400 < 50 := by omega
                                                            have heq : n = (n - 61400) + 61400 := by omega
                                                            rw [heq]
                                                            exact cs_w28 ⟨n - 61400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 61500
                                                            · have hr : n - 61450 < 50 := by omega
                                                              have heq : n = (n - 61450) + 61450 := by omega
                                                              rw [heq]
                                                              exact cs_w29 ⟨n - 61450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 61550
                                                              · have hr : n - 61500 < 50 := by omega
                                                                have heq : n = (n - 61500) + 61500 := by omega
                                                                rw [heq]
                                                                exact cs_w30 ⟨n - 61500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 61600
                                                                · have hr : n - 61550 < 50 := by omega
                                                                  have heq : n = (n - 61550) + 61550 := by omega
                                                                  rw [heq]
                                                                  exact cs_w31 ⟨n - 61550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 61650
                                                                  · have hr : n - 61600 < 50 := by omega
                                                                    have heq : n = (n - 61600) + 61600 := by omega
                                                                    rw [heq]
                                                                    exact cs_w32 ⟨n - 61600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 61700
                                                                    · have hr : n - 61650 < 50 := by omega
                                                                      have heq : n = (n - 61650) + 61650 := by omega
                                                                      rw [heq]
                                                                      exact cs_w33 ⟨n - 61650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 61750
                                                                      · have hr : n - 61700 < 50 := by omega
                                                                        have heq : n = (n - 61700) + 61700 := by omega
                                                                        rw [heq]
                                                                        exact cs_w34 ⟨n - 61700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 61800
                                                                        · have hr : n - 61750 < 50 := by omega
                                                                          have heq : n = (n - 61750) + 61750 := by omega
                                                                          rw [heq]
                                                                          exact cs_w35 ⟨n - 61750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 61850
                                                                          · have hr : n - 61800 < 50 := by omega
                                                                            have heq : n = (n - 61800) + 61800 := by omega
                                                                            rw [heq]
                                                                            exact cs_w36 ⟨n - 61800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 61900
                                                                            · have hr : n - 61850 < 50 := by omega
                                                                              have heq : n = (n - 61850) + 61850 := by omega
                                                                              rw [heq]
                                                                              exact cs_w37 ⟨n - 61850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 61950
                                                                              · have hr : n - 61900 < 50 := by omega
                                                                                have heq : n = (n - 61900) + 61900 := by omega
                                                                                rw [heq]
                                                                                exact cs_w38 ⟨n - 61900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 62000
                                                                                · have hr : n - 61950 < 50 := by omega
                                                                                  have heq : n = (n - 61950) + 61950 := by omega
                                                                                  rw [heq]
                                                                                  exact cs_w39 ⟨n - 61950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 62050
                                                                                  · have hr : n - 62000 < 50 := by omega
                                                                                    have heq : n = (n - 62000) + 62000 := by omega
                                                                                    rw [heq]
                                                                                    exact cs_w40 ⟨n - 62000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 62100
                                                                                    · have hr : n - 62050 < 50 := by omega
                                                                                      have heq : n = (n - 62050) + 62050 := by omega
                                                                                      rw [heq]
                                                                                      exact cs_w41 ⟨n - 62050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 62150
                                                                                      · have hr : n - 62100 < 50 := by omega
                                                                                        have heq : n = (n - 62100) + 62100 := by omega
                                                                                        rw [heq]
                                                                                        exact cs_w42 ⟨n - 62100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 62200
                                                                                        · have hr : n - 62150 < 50 := by omega
                                                                                          have heq : n = (n - 62150) + 62150 := by omega
                                                                                          rw [heq]
                                                                                          exact cs_w43 ⟨n - 62150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 62250
                                                                                          · have hr : n - 62200 < 50 := by omega
                                                                                            have heq : n = (n - 62200) + 62200 := by omega
                                                                                            rw [heq]
                                                                                            exact cs_w44 ⟨n - 62200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 62300
                                                                                            · have hr : n - 62250 < 50 := by omega
                                                                                              have heq : n = (n - 62250) + 62250 := by omega
                                                                                              rw [heq]
                                                                                              exact cs_w45 ⟨n - 62250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 62350
                                                                                              · have hr : n - 62300 < 50 := by omega
                                                                                                have heq : n = (n - 62300) + 62300 := by omega
                                                                                                rw [heq]
                                                                                                exact cs_w46 ⟨n - 62300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 62400
                                                                                                · have hr : n - 62350 < 50 := by omega
                                                                                                  have heq : n = (n - 62350) + 62350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cs_w47 ⟨n - 62350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 62450
                                                                                                  · have hr : n - 62400 < 50 := by omega
                                                                                                    have heq : n = (n - 62400) + 62400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w48 ⟨n - 62400, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 62450 < 28 := by omega
                                                                                                    have heq : n = (n - 62450) + 62450 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w49 ⟨n - 62450, hr⟩

theorem centF_lt_range : ∀ n, 60000 ≤ n → n < 62478 → centF n < 23 := by
  intro n hlo hhi
  by_cases h0 : n < 60050
  · have hr : n - 60000 < 50 := by omega
    have heq : n = (n - 60000) + 60000 := by omega
    rw [heq]
    exact cl_w0 ⟨n - 60000, hr⟩
  ·
    by_cases h1 : n < 60100
    · have hr : n - 60050 < 50 := by omega
      have heq : n = (n - 60050) + 60050 := by omega
      rw [heq]
      exact cl_w1 ⟨n - 60050, hr⟩
    ·
      by_cases h2 : n < 60150
      · have hr : n - 60100 < 50 := by omega
        have heq : n = (n - 60100) + 60100 := by omega
        rw [heq]
        exact cl_w2 ⟨n - 60100, hr⟩
      ·
        by_cases h3 : n < 60200
        · have hr : n - 60150 < 50 := by omega
          have heq : n = (n - 60150) + 60150 := by omega
          rw [heq]
          exact cl_w3 ⟨n - 60150, hr⟩
        ·
          by_cases h4 : n < 60250
          · have hr : n - 60200 < 50 := by omega
            have heq : n = (n - 60200) + 60200 := by omega
            rw [heq]
            exact cl_w4 ⟨n - 60200, hr⟩
          ·
            by_cases h5 : n < 60300
            · have hr : n - 60250 < 50 := by omega
              have heq : n = (n - 60250) + 60250 := by omega
              rw [heq]
              exact cl_w5 ⟨n - 60250, hr⟩
            ·
              by_cases h6 : n < 60350
              · have hr : n - 60300 < 50 := by omega
                have heq : n = (n - 60300) + 60300 := by omega
                rw [heq]
                exact cl_w6 ⟨n - 60300, hr⟩
              ·
                by_cases h7 : n < 60400
                · have hr : n - 60350 < 50 := by omega
                  have heq : n = (n - 60350) + 60350 := by omega
                  rw [heq]
                  exact cl_w7 ⟨n - 60350, hr⟩
                ·
                  by_cases h8 : n < 60450
                  · have hr : n - 60400 < 50 := by omega
                    have heq : n = (n - 60400) + 60400 := by omega
                    rw [heq]
                    exact cl_w8 ⟨n - 60400, hr⟩
                  ·
                    by_cases h9 : n < 60500
                    · have hr : n - 60450 < 50 := by omega
                      have heq : n = (n - 60450) + 60450 := by omega
                      rw [heq]
                      exact cl_w9 ⟨n - 60450, hr⟩
                    ·
                      by_cases h10 : n < 60550
                      · have hr : n - 60500 < 50 := by omega
                        have heq : n = (n - 60500) + 60500 := by omega
                        rw [heq]
                        exact cl_w10 ⟨n - 60500, hr⟩
                      ·
                        by_cases h11 : n < 60600
                        · have hr : n - 60550 < 50 := by omega
                          have heq : n = (n - 60550) + 60550 := by omega
                          rw [heq]
                          exact cl_w11 ⟨n - 60550, hr⟩
                        ·
                          by_cases h12 : n < 60650
                          · have hr : n - 60600 < 50 := by omega
                            have heq : n = (n - 60600) + 60600 := by omega
                            rw [heq]
                            exact cl_w12 ⟨n - 60600, hr⟩
                          ·
                            by_cases h13 : n < 60700
                            · have hr : n - 60650 < 50 := by omega
                              have heq : n = (n - 60650) + 60650 := by omega
                              rw [heq]
                              exact cl_w13 ⟨n - 60650, hr⟩
                            ·
                              by_cases h14 : n < 60750
                              · have hr : n - 60700 < 50 := by omega
                                have heq : n = (n - 60700) + 60700 := by omega
                                rw [heq]
                                exact cl_w14 ⟨n - 60700, hr⟩
                              ·
                                by_cases h15 : n < 60800
                                · have hr : n - 60750 < 50 := by omega
                                  have heq : n = (n - 60750) + 60750 := by omega
                                  rw [heq]
                                  exact cl_w15 ⟨n - 60750, hr⟩
                                ·
                                  by_cases h16 : n < 60850
                                  · have hr : n - 60800 < 50 := by omega
                                    have heq : n = (n - 60800) + 60800 := by omega
                                    rw [heq]
                                    exact cl_w16 ⟨n - 60800, hr⟩
                                  ·
                                    by_cases h17 : n < 60900
                                    · have hr : n - 60850 < 50 := by omega
                                      have heq : n = (n - 60850) + 60850 := by omega
                                      rw [heq]
                                      exact cl_w17 ⟨n - 60850, hr⟩
                                    ·
                                      by_cases h18 : n < 60950
                                      · have hr : n - 60900 < 50 := by omega
                                        have heq : n = (n - 60900) + 60900 := by omega
                                        rw [heq]
                                        exact cl_w18 ⟨n - 60900, hr⟩
                                      ·
                                        by_cases h19 : n < 61000
                                        · have hr : n - 60950 < 50 := by omega
                                          have heq : n = (n - 60950) + 60950 := by omega
                                          rw [heq]
                                          exact cl_w19 ⟨n - 60950, hr⟩
                                        ·
                                          by_cases h20 : n < 61050
                                          · have hr : n - 61000 < 50 := by omega
                                            have heq : n = (n - 61000) + 61000 := by omega
                                            rw [heq]
                                            exact cl_w20 ⟨n - 61000, hr⟩
                                          ·
                                            by_cases h21 : n < 61100
                                            · have hr : n - 61050 < 50 := by omega
                                              have heq : n = (n - 61050) + 61050 := by omega
                                              rw [heq]
                                              exact cl_w21 ⟨n - 61050, hr⟩
                                            ·
                                              by_cases h22 : n < 61150
                                              · have hr : n - 61100 < 50 := by omega
                                                have heq : n = (n - 61100) + 61100 := by omega
                                                rw [heq]
                                                exact cl_w22 ⟨n - 61100, hr⟩
                                              ·
                                                by_cases h23 : n < 61200
                                                · have hr : n - 61150 < 50 := by omega
                                                  have heq : n = (n - 61150) + 61150 := by omega
                                                  rw [heq]
                                                  exact cl_w23 ⟨n - 61150, hr⟩
                                                ·
                                                  by_cases h24 : n < 61250
                                                  · have hr : n - 61200 < 50 := by omega
                                                    have heq : n = (n - 61200) + 61200 := by omega
                                                    rw [heq]
                                                    exact cl_w24 ⟨n - 61200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 61300
                                                    · have hr : n - 61250 < 50 := by omega
                                                      have heq : n = (n - 61250) + 61250 := by omega
                                                      rw [heq]
                                                      exact cl_w25 ⟨n - 61250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 61350
                                                      · have hr : n - 61300 < 50 := by omega
                                                        have heq : n = (n - 61300) + 61300 := by omega
                                                        rw [heq]
                                                        exact cl_w26 ⟨n - 61300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 61400
                                                        · have hr : n - 61350 < 50 := by omega
                                                          have heq : n = (n - 61350) + 61350 := by omega
                                                          rw [heq]
                                                          exact cl_w27 ⟨n - 61350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 61450
                                                          · have hr : n - 61400 < 50 := by omega
                                                            have heq : n = (n - 61400) + 61400 := by omega
                                                            rw [heq]
                                                            exact cl_w28 ⟨n - 61400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 61500
                                                            · have hr : n - 61450 < 50 := by omega
                                                              have heq : n = (n - 61450) + 61450 := by omega
                                                              rw [heq]
                                                              exact cl_w29 ⟨n - 61450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 61550
                                                              · have hr : n - 61500 < 50 := by omega
                                                                have heq : n = (n - 61500) + 61500 := by omega
                                                                rw [heq]
                                                                exact cl_w30 ⟨n - 61500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 61600
                                                                · have hr : n - 61550 < 50 := by omega
                                                                  have heq : n = (n - 61550) + 61550 := by omega
                                                                  rw [heq]
                                                                  exact cl_w31 ⟨n - 61550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 61650
                                                                  · have hr : n - 61600 < 50 := by omega
                                                                    have heq : n = (n - 61600) + 61600 := by omega
                                                                    rw [heq]
                                                                    exact cl_w32 ⟨n - 61600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 61700
                                                                    · have hr : n - 61650 < 50 := by omega
                                                                      have heq : n = (n - 61650) + 61650 := by omega
                                                                      rw [heq]
                                                                      exact cl_w33 ⟨n - 61650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 61750
                                                                      · have hr : n - 61700 < 50 := by omega
                                                                        have heq : n = (n - 61700) + 61700 := by omega
                                                                        rw [heq]
                                                                        exact cl_w34 ⟨n - 61700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 61800
                                                                        · have hr : n - 61750 < 50 := by omega
                                                                          have heq : n = (n - 61750) + 61750 := by omega
                                                                          rw [heq]
                                                                          exact cl_w35 ⟨n - 61750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 61850
                                                                          · have hr : n - 61800 < 50 := by omega
                                                                            have heq : n = (n - 61800) + 61800 := by omega
                                                                            rw [heq]
                                                                            exact cl_w36 ⟨n - 61800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 61900
                                                                            · have hr : n - 61850 < 50 := by omega
                                                                              have heq : n = (n - 61850) + 61850 := by omega
                                                                              rw [heq]
                                                                              exact cl_w37 ⟨n - 61850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 61950
                                                                              · have hr : n - 61900 < 50 := by omega
                                                                                have heq : n = (n - 61900) + 61900 := by omega
                                                                                rw [heq]
                                                                                exact cl_w38 ⟨n - 61900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 62000
                                                                                · have hr : n - 61950 < 50 := by omega
                                                                                  have heq : n = (n - 61950) + 61950 := by omega
                                                                                  rw [heq]
                                                                                  exact cl_w39 ⟨n - 61950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 62050
                                                                                  · have hr : n - 62000 < 50 := by omega
                                                                                    have heq : n = (n - 62000) + 62000 := by omega
                                                                                    rw [heq]
                                                                                    exact cl_w40 ⟨n - 62000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 62100
                                                                                    · have hr : n - 62050 < 50 := by omega
                                                                                      have heq : n = (n - 62050) + 62050 := by omega
                                                                                      rw [heq]
                                                                                      exact cl_w41 ⟨n - 62050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 62150
                                                                                      · have hr : n - 62100 < 50 := by omega
                                                                                        have heq : n = (n - 62100) + 62100 := by omega
                                                                                        rw [heq]
                                                                                        exact cl_w42 ⟨n - 62100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 62200
                                                                                        · have hr : n - 62150 < 50 := by omega
                                                                                          have heq : n = (n - 62150) + 62150 := by omega
                                                                                          rw [heq]
                                                                                          exact cl_w43 ⟨n - 62150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 62250
                                                                                          · have hr : n - 62200 < 50 := by omega
                                                                                            have heq : n = (n - 62200) + 62200 := by omega
                                                                                            rw [heq]
                                                                                            exact cl_w44 ⟨n - 62200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 62300
                                                                                            · have hr : n - 62250 < 50 := by omega
                                                                                              have heq : n = (n - 62250) + 62250 := by omega
                                                                                              rw [heq]
                                                                                              exact cl_w45 ⟨n - 62250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 62350
                                                                                              · have hr : n - 62300 < 50 := by omega
                                                                                                have heq : n = (n - 62300) + 62300 := by omega
                                                                                                rw [heq]
                                                                                                exact cl_w46 ⟨n - 62300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 62400
                                                                                                · have hr : n - 62350 < 50 := by omega
                                                                                                  have heq : n = (n - 62350) + 62350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cl_w47 ⟨n - 62350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 62450
                                                                                                  · have hr : n - 62400 < 50 := by omega
                                                                                                    have heq : n = (n - 62400) + 62400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w48 ⟨n - 62400, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 62450 < 28 := by omega
                                                                                                    have heq : n = (n - 62450) + 62450 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w49 ⟨n - 62450, hr⟩

theorem densSupG_lt_range : ∀ n, 60000 ≤ n → n < 62478 → densSupG n < 2 ^ 1771 := by
  intro n hlo hhi
  by_cases h0 : n < 60050
  · have hr : n - 60000 < 50 := by omega
    have heq : n = (n - 60000) + 60000 := by omega
    rw [heq]
    exact bd_w0 ⟨n - 60000, hr⟩
  ·
    by_cases h1 : n < 60100
    · have hr : n - 60050 < 50 := by omega
      have heq : n = (n - 60050) + 60050 := by omega
      rw [heq]
      exact bd_w1 ⟨n - 60050, hr⟩
    ·
      by_cases h2 : n < 60150
      · have hr : n - 60100 < 50 := by omega
        have heq : n = (n - 60100) + 60100 := by omega
        rw [heq]
        exact bd_w2 ⟨n - 60100, hr⟩
      ·
        by_cases h3 : n < 60200
        · have hr : n - 60150 < 50 := by omega
          have heq : n = (n - 60150) + 60150 := by omega
          rw [heq]
          exact bd_w3 ⟨n - 60150, hr⟩
        ·
          by_cases h4 : n < 60250
          · have hr : n - 60200 < 50 := by omega
            have heq : n = (n - 60200) + 60200 := by omega
            rw [heq]
            exact bd_w4 ⟨n - 60200, hr⟩
          ·
            by_cases h5 : n < 60300
            · have hr : n - 60250 < 50 := by omega
              have heq : n = (n - 60250) + 60250 := by omega
              rw [heq]
              exact bd_w5 ⟨n - 60250, hr⟩
            ·
              by_cases h6 : n < 60350
              · have hr : n - 60300 < 50 := by omega
                have heq : n = (n - 60300) + 60300 := by omega
                rw [heq]
                exact bd_w6 ⟨n - 60300, hr⟩
              ·
                by_cases h7 : n < 60400
                · have hr : n - 60350 < 50 := by omega
                  have heq : n = (n - 60350) + 60350 := by omega
                  rw [heq]
                  exact bd_w7 ⟨n - 60350, hr⟩
                ·
                  by_cases h8 : n < 60450
                  · have hr : n - 60400 < 50 := by omega
                    have heq : n = (n - 60400) + 60400 := by omega
                    rw [heq]
                    exact bd_w8 ⟨n - 60400, hr⟩
                  ·
                    by_cases h9 : n < 60500
                    · have hr : n - 60450 < 50 := by omega
                      have heq : n = (n - 60450) + 60450 := by omega
                      rw [heq]
                      exact bd_w9 ⟨n - 60450, hr⟩
                    ·
                      by_cases h10 : n < 60550
                      · have hr : n - 60500 < 50 := by omega
                        have heq : n = (n - 60500) + 60500 := by omega
                        rw [heq]
                        exact bd_w10 ⟨n - 60500, hr⟩
                      ·
                        by_cases h11 : n < 60600
                        · have hr : n - 60550 < 50 := by omega
                          have heq : n = (n - 60550) + 60550 := by omega
                          rw [heq]
                          exact bd_w11 ⟨n - 60550, hr⟩
                        ·
                          by_cases h12 : n < 60650
                          · have hr : n - 60600 < 50 := by omega
                            have heq : n = (n - 60600) + 60600 := by omega
                            rw [heq]
                            exact bd_w12 ⟨n - 60600, hr⟩
                          ·
                            by_cases h13 : n < 60700
                            · have hr : n - 60650 < 50 := by omega
                              have heq : n = (n - 60650) + 60650 := by omega
                              rw [heq]
                              exact bd_w13 ⟨n - 60650, hr⟩
                            ·
                              by_cases h14 : n < 60750
                              · have hr : n - 60700 < 50 := by omega
                                have heq : n = (n - 60700) + 60700 := by omega
                                rw [heq]
                                exact bd_w14 ⟨n - 60700, hr⟩
                              ·
                                by_cases h15 : n < 60800
                                · have hr : n - 60750 < 50 := by omega
                                  have heq : n = (n - 60750) + 60750 := by omega
                                  rw [heq]
                                  exact bd_w15 ⟨n - 60750, hr⟩
                                ·
                                  by_cases h16 : n < 60850
                                  · have hr : n - 60800 < 50 := by omega
                                    have heq : n = (n - 60800) + 60800 := by omega
                                    rw [heq]
                                    exact bd_w16 ⟨n - 60800, hr⟩
                                  ·
                                    by_cases h17 : n < 60900
                                    · have hr : n - 60850 < 50 := by omega
                                      have heq : n = (n - 60850) + 60850 := by omega
                                      rw [heq]
                                      exact bd_w17 ⟨n - 60850, hr⟩
                                    ·
                                      by_cases h18 : n < 60950
                                      · have hr : n - 60900 < 50 := by omega
                                        have heq : n = (n - 60900) + 60900 := by omega
                                        rw [heq]
                                        exact bd_w18 ⟨n - 60900, hr⟩
                                      ·
                                        by_cases h19 : n < 61000
                                        · have hr : n - 60950 < 50 := by omega
                                          have heq : n = (n - 60950) + 60950 := by omega
                                          rw [heq]
                                          exact bd_w19 ⟨n - 60950, hr⟩
                                        ·
                                          by_cases h20 : n < 61050
                                          · have hr : n - 61000 < 50 := by omega
                                            have heq : n = (n - 61000) + 61000 := by omega
                                            rw [heq]
                                            exact bd_w20 ⟨n - 61000, hr⟩
                                          ·
                                            by_cases h21 : n < 61100
                                            · have hr : n - 61050 < 50 := by omega
                                              have heq : n = (n - 61050) + 61050 := by omega
                                              rw [heq]
                                              exact bd_w21 ⟨n - 61050, hr⟩
                                            ·
                                              by_cases h22 : n < 61150
                                              · have hr : n - 61100 < 50 := by omega
                                                have heq : n = (n - 61100) + 61100 := by omega
                                                rw [heq]
                                                exact bd_w22 ⟨n - 61100, hr⟩
                                              ·
                                                by_cases h23 : n < 61200
                                                · have hr : n - 61150 < 50 := by omega
                                                  have heq : n = (n - 61150) + 61150 := by omega
                                                  rw [heq]
                                                  exact bd_w23 ⟨n - 61150, hr⟩
                                                ·
                                                  by_cases h24 : n < 61250
                                                  · have hr : n - 61200 < 50 := by omega
                                                    have heq : n = (n - 61200) + 61200 := by omega
                                                    rw [heq]
                                                    exact bd_w24 ⟨n - 61200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 61300
                                                    · have hr : n - 61250 < 50 := by omega
                                                      have heq : n = (n - 61250) + 61250 := by omega
                                                      rw [heq]
                                                      exact bd_w25 ⟨n - 61250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 61350
                                                      · have hr : n - 61300 < 50 := by omega
                                                        have heq : n = (n - 61300) + 61300 := by omega
                                                        rw [heq]
                                                        exact bd_w26 ⟨n - 61300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 61400
                                                        · have hr : n - 61350 < 50 := by omega
                                                          have heq : n = (n - 61350) + 61350 := by omega
                                                          rw [heq]
                                                          exact bd_w27 ⟨n - 61350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 61450
                                                          · have hr : n - 61400 < 50 := by omega
                                                            have heq : n = (n - 61400) + 61400 := by omega
                                                            rw [heq]
                                                            exact bd_w28 ⟨n - 61400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 61500
                                                            · have hr : n - 61450 < 50 := by omega
                                                              have heq : n = (n - 61450) + 61450 := by omega
                                                              rw [heq]
                                                              exact bd_w29 ⟨n - 61450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 61550
                                                              · have hr : n - 61500 < 50 := by omega
                                                                have heq : n = (n - 61500) + 61500 := by omega
                                                                rw [heq]
                                                                exact bd_w30 ⟨n - 61500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 61600
                                                                · have hr : n - 61550 < 50 := by omega
                                                                  have heq : n = (n - 61550) + 61550 := by omega
                                                                  rw [heq]
                                                                  exact bd_w31 ⟨n - 61550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 61650
                                                                  · have hr : n - 61600 < 50 := by omega
                                                                    have heq : n = (n - 61600) + 61600 := by omega
                                                                    rw [heq]
                                                                    exact bd_w32 ⟨n - 61600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 61700
                                                                    · have hr : n - 61650 < 50 := by omega
                                                                      have heq : n = (n - 61650) + 61650 := by omega
                                                                      rw [heq]
                                                                      exact bd_w33 ⟨n - 61650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 61750
                                                                      · have hr : n - 61700 < 50 := by omega
                                                                        have heq : n = (n - 61700) + 61700 := by omega
                                                                        rw [heq]
                                                                        exact bd_w34 ⟨n - 61700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 61800
                                                                        · have hr : n - 61750 < 50 := by omega
                                                                          have heq : n = (n - 61750) + 61750 := by omega
                                                                          rw [heq]
                                                                          exact bd_w35 ⟨n - 61750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 61850
                                                                          · have hr : n - 61800 < 50 := by omega
                                                                            have heq : n = (n - 61800) + 61800 := by omega
                                                                            rw [heq]
                                                                            exact bd_w36 ⟨n - 61800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 61900
                                                                            · have hr : n - 61850 < 50 := by omega
                                                                              have heq : n = (n - 61850) + 61850 := by omega
                                                                              rw [heq]
                                                                              exact bd_w37 ⟨n - 61850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 61950
                                                                              · have hr : n - 61900 < 50 := by omega
                                                                                have heq : n = (n - 61900) + 61900 := by omega
                                                                                rw [heq]
                                                                                exact bd_w38 ⟨n - 61900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 62000
                                                                                · have hr : n - 61950 < 50 := by omega
                                                                                  have heq : n = (n - 61950) + 61950 := by omega
                                                                                  rw [heq]
                                                                                  exact bd_w39 ⟨n - 61950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 62050
                                                                                  · have hr : n - 62000 < 50 := by omega
                                                                                    have heq : n = (n - 62000) + 62000 := by omega
                                                                                    rw [heq]
                                                                                    exact bd_w40 ⟨n - 62000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 62100
                                                                                    · have hr : n - 62050 < 50 := by omega
                                                                                      have heq : n = (n - 62050) + 62050 := by omega
                                                                                      rw [heq]
                                                                                      exact bd_w41 ⟨n - 62050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 62150
                                                                                      · have hr : n - 62100 < 50 := by omega
                                                                                        have heq : n = (n - 62100) + 62100 := by omega
                                                                                        rw [heq]
                                                                                        exact bd_w42 ⟨n - 62100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 62200
                                                                                        · have hr : n - 62150 < 50 := by omega
                                                                                          have heq : n = (n - 62150) + 62150 := by omega
                                                                                          rw [heq]
                                                                                          exact bd_w43 ⟨n - 62150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 62250
                                                                                          · have hr : n - 62200 < 50 := by omega
                                                                                            have heq : n = (n - 62200) + 62200 := by omega
                                                                                            rw [heq]
                                                                                            exact bd_w44 ⟨n - 62200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 62300
                                                                                            · have hr : n - 62250 < 50 := by omega
                                                                                              have heq : n = (n - 62250) + 62250 := by omega
                                                                                              rw [heq]
                                                                                              exact bd_w45 ⟨n - 62250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 62350
                                                                                              · have hr : n - 62300 < 50 := by omega
                                                                                                have heq : n = (n - 62300) + 62300 := by omega
                                                                                                rw [heq]
                                                                                                exact bd_w46 ⟨n - 62300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 62400
                                                                                                · have hr : n - 62350 < 50 := by omega
                                                                                                  have heq : n = (n - 62350) + 62350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact bd_w47 ⟨n - 62350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 62450
                                                                                                  · have hr : n - 62400 < 50 := by omega
                                                                                                    have heq : n = (n - 62400) + 62400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w48 ⟨n - 62400, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 62450 < 28 := by omega
                                                                                                    have heq : n = (n - 62450) + 62450 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w49 ⟨n - 62450, hr⟩

end IntMul.Kappa.R8.Bit.Oppbank.CentBound12Fix


