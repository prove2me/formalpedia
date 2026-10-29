-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound8bFix
-- name    : IntMul_Kappa_R8_Data_BitOppbankCentBound8bFix
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T22:21:39.041975+00:00
-- url     : https://prove2.me/theorems/12d7a3d3-833f-4900-b4e4-5163f753c4e0
-- title:
--   IntMul Kappa R8 Data BitOppbankCentBound8bFix
-- statement:
--   Densified HasCentre support certificates (IntMul_Kappa_R8_Data_BitOppbankCentBound8bFix) retargeted to PndFix/CentFix.

-- CentBound8bFix: PndFix retarget
-- CentBound pack 8b: densified HasCentre certificates on n ∈ [42500, 45000)
-- Half-pack for server 300s compile budget.

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

namespace IntMul.Kappa.R8.Bit.Oppbank.CentBound8bFix


private theorem cs_w0 : ∀ n : Fin 50, centredStar (densSupG (n.val + 42500)) (centF (n.val + 42500)) = true := by decide
private theorem cl_w0 : ∀ n : Fin 50, centF (n.val + 42500) < 23 := by decide
private theorem bd_w0 : ∀ n : Fin 50, densSupG (n.val + 42500) < 2 ^ 1771 := by decide
private theorem cs_w1 : ∀ n : Fin 50, centredStar (densSupG (n.val + 42550)) (centF (n.val + 42550)) = true := by decide
private theorem cl_w1 : ∀ n : Fin 50, centF (n.val + 42550) < 23 := by decide
private theorem bd_w1 : ∀ n : Fin 50, densSupG (n.val + 42550) < 2 ^ 1771 := by decide
private theorem cs_w2 : ∀ n : Fin 50, centredStar (densSupG (n.val + 42600)) (centF (n.val + 42600)) = true := by decide
private theorem cl_w2 : ∀ n : Fin 50, centF (n.val + 42600) < 23 := by decide
private theorem bd_w2 : ∀ n : Fin 50, densSupG (n.val + 42600) < 2 ^ 1771 := by decide
private theorem cs_w3 : ∀ n : Fin 50, centredStar (densSupG (n.val + 42650)) (centF (n.val + 42650)) = true := by decide
private theorem cl_w3 : ∀ n : Fin 50, centF (n.val + 42650) < 23 := by decide
private theorem bd_w3 : ∀ n : Fin 50, densSupG (n.val + 42650) < 2 ^ 1771 := by decide
private theorem cs_w4 : ∀ n : Fin 50, centredStar (densSupG (n.val + 42700)) (centF (n.val + 42700)) = true := by decide
private theorem cl_w4 : ∀ n : Fin 50, centF (n.val + 42700) < 23 := by decide
private theorem bd_w4 : ∀ n : Fin 50, densSupG (n.val + 42700) < 2 ^ 1771 := by decide
private theorem cs_w5 : ∀ n : Fin 50, centredStar (densSupG (n.val + 42750)) (centF (n.val + 42750)) = true := by decide
private theorem cl_w5 : ∀ n : Fin 50, centF (n.val + 42750) < 23 := by decide
private theorem bd_w5 : ∀ n : Fin 50, densSupG (n.val + 42750) < 2 ^ 1771 := by decide
private theorem cs_w6 : ∀ n : Fin 50, centredStar (densSupG (n.val + 42800)) (centF (n.val + 42800)) = true := by decide
private theorem cl_w6 : ∀ n : Fin 50, centF (n.val + 42800) < 23 := by decide
private theorem bd_w6 : ∀ n : Fin 50, densSupG (n.val + 42800) < 2 ^ 1771 := by decide
private theorem cs_w7 : ∀ n : Fin 50, centredStar (densSupG (n.val + 42850)) (centF (n.val + 42850)) = true := by decide
private theorem cl_w7 : ∀ n : Fin 50, centF (n.val + 42850) < 23 := by decide
private theorem bd_w7 : ∀ n : Fin 50, densSupG (n.val + 42850) < 2 ^ 1771 := by decide
private theorem cs_w8 : ∀ n : Fin 50, centredStar (densSupG (n.val + 42900)) (centF (n.val + 42900)) = true := by decide
private theorem cl_w8 : ∀ n : Fin 50, centF (n.val + 42900) < 23 := by decide
private theorem bd_w8 : ∀ n : Fin 50, densSupG (n.val + 42900) < 2 ^ 1771 := by decide
private theorem cs_w9 : ∀ n : Fin 50, centredStar (densSupG (n.val + 42950)) (centF (n.val + 42950)) = true := by decide
private theorem cl_w9 : ∀ n : Fin 50, centF (n.val + 42950) < 23 := by decide
private theorem bd_w9 : ∀ n : Fin 50, densSupG (n.val + 42950) < 2 ^ 1771 := by decide
private theorem cs_w10 : ∀ n : Fin 50, centredStar (densSupG (n.val + 43000)) (centF (n.val + 43000)) = true := by decide
private theorem cl_w10 : ∀ n : Fin 50, centF (n.val + 43000) < 23 := by decide
private theorem bd_w10 : ∀ n : Fin 50, densSupG (n.val + 43000) < 2 ^ 1771 := by decide
private theorem cs_w11 : ∀ n : Fin 50, centredStar (densSupG (n.val + 43050)) (centF (n.val + 43050)) = true := by decide
private theorem cl_w11 : ∀ n : Fin 50, centF (n.val + 43050) < 23 := by decide
private theorem bd_w11 : ∀ n : Fin 50, densSupG (n.val + 43050) < 2 ^ 1771 := by decide
private theorem cs_w12 : ∀ n : Fin 50, centredStar (densSupG (n.val + 43100)) (centF (n.val + 43100)) = true := by decide
private theorem cl_w12 : ∀ n : Fin 50, centF (n.val + 43100) < 23 := by decide
private theorem bd_w12 : ∀ n : Fin 50, densSupG (n.val + 43100) < 2 ^ 1771 := by decide
private theorem cs_w13 : ∀ n : Fin 50, centredStar (densSupG (n.val + 43150)) (centF (n.val + 43150)) = true := by decide
private theorem cl_w13 : ∀ n : Fin 50, centF (n.val + 43150) < 23 := by decide
private theorem bd_w13 : ∀ n : Fin 50, densSupG (n.val + 43150) < 2 ^ 1771 := by decide
private theorem cs_w14 : ∀ n : Fin 50, centredStar (densSupG (n.val + 43200)) (centF (n.val + 43200)) = true := by decide
private theorem cl_w14 : ∀ n : Fin 50, centF (n.val + 43200) < 23 := by decide
private theorem bd_w14 : ∀ n : Fin 50, densSupG (n.val + 43200) < 2 ^ 1771 := by decide
private theorem cs_w15 : ∀ n : Fin 50, centredStar (densSupG (n.val + 43250)) (centF (n.val + 43250)) = true := by decide
private theorem cl_w15 : ∀ n : Fin 50, centF (n.val + 43250) < 23 := by decide
private theorem bd_w15 : ∀ n : Fin 50, densSupG (n.val + 43250) < 2 ^ 1771 := by decide
private theorem cs_w16 : ∀ n : Fin 50, centredStar (densSupG (n.val + 43300)) (centF (n.val + 43300)) = true := by decide
private theorem cl_w16 : ∀ n : Fin 50, centF (n.val + 43300) < 23 := by decide
private theorem bd_w16 : ∀ n : Fin 50, densSupG (n.val + 43300) < 2 ^ 1771 := by decide
private theorem cs_w17 : ∀ n : Fin 50, centredStar (densSupG (n.val + 43350)) (centF (n.val + 43350)) = true := by decide
private theorem cl_w17 : ∀ n : Fin 50, centF (n.val + 43350) < 23 := by decide
private theorem bd_w17 : ∀ n : Fin 50, densSupG (n.val + 43350) < 2 ^ 1771 := by decide
private theorem cs_w18 : ∀ n : Fin 50, centredStar (densSupG (n.val + 43400)) (centF (n.val + 43400)) = true := by decide
private theorem cl_w18 : ∀ n : Fin 50, centF (n.val + 43400) < 23 := by decide
private theorem bd_w18 : ∀ n : Fin 50, densSupG (n.val + 43400) < 2 ^ 1771 := by decide
private theorem cs_w19 : ∀ n : Fin 50, centredStar (densSupG (n.val + 43450)) (centF (n.val + 43450)) = true := by decide
private theorem cl_w19 : ∀ n : Fin 50, centF (n.val + 43450) < 23 := by decide
private theorem bd_w19 : ∀ n : Fin 50, densSupG (n.val + 43450) < 2 ^ 1771 := by decide
private theorem cs_w20 : ∀ n : Fin 50, centredStar (densSupG (n.val + 43500)) (centF (n.val + 43500)) = true := by decide
private theorem cl_w20 : ∀ n : Fin 50, centF (n.val + 43500) < 23 := by decide
private theorem bd_w20 : ∀ n : Fin 50, densSupG (n.val + 43500) < 2 ^ 1771 := by decide
private theorem cs_w21 : ∀ n : Fin 50, centredStar (densSupG (n.val + 43550)) (centF (n.val + 43550)) = true := by decide
private theorem cl_w21 : ∀ n : Fin 50, centF (n.val + 43550) < 23 := by decide
private theorem bd_w21 : ∀ n : Fin 50, densSupG (n.val + 43550) < 2 ^ 1771 := by decide
private theorem cs_w22 : ∀ n : Fin 50, centredStar (densSupG (n.val + 43600)) (centF (n.val + 43600)) = true := by decide
private theorem cl_w22 : ∀ n : Fin 50, centF (n.val + 43600) < 23 := by decide
private theorem bd_w22 : ∀ n : Fin 50, densSupG (n.val + 43600) < 2 ^ 1771 := by decide
private theorem cs_w23 : ∀ n : Fin 50, centredStar (densSupG (n.val + 43650)) (centF (n.val + 43650)) = true := by decide
private theorem cl_w23 : ∀ n : Fin 50, centF (n.val + 43650) < 23 := by decide
private theorem bd_w23 : ∀ n : Fin 50, densSupG (n.val + 43650) < 2 ^ 1771 := by decide
private theorem cs_w24 : ∀ n : Fin 50, centredStar (densSupG (n.val + 43700)) (centF (n.val + 43700)) = true := by decide
private theorem cl_w24 : ∀ n : Fin 50, centF (n.val + 43700) < 23 := by decide
private theorem bd_w24 : ∀ n : Fin 50, densSupG (n.val + 43700) < 2 ^ 1771 := by decide
private theorem cs_w25 : ∀ n : Fin 50, centredStar (densSupG (n.val + 43750)) (centF (n.val + 43750)) = true := by decide
private theorem cl_w25 : ∀ n : Fin 50, centF (n.val + 43750) < 23 := by decide
private theorem bd_w25 : ∀ n : Fin 50, densSupG (n.val + 43750) < 2 ^ 1771 := by decide
private theorem cs_w26 : ∀ n : Fin 50, centredStar (densSupG (n.val + 43800)) (centF (n.val + 43800)) = true := by decide
private theorem cl_w26 : ∀ n : Fin 50, centF (n.val + 43800) < 23 := by decide
private theorem bd_w26 : ∀ n : Fin 50, densSupG (n.val + 43800) < 2 ^ 1771 := by decide
private theorem cs_w27 : ∀ n : Fin 50, centredStar (densSupG (n.val + 43850)) (centF (n.val + 43850)) = true := by decide
private theorem cl_w27 : ∀ n : Fin 50, centF (n.val + 43850) < 23 := by decide
private theorem bd_w27 : ∀ n : Fin 50, densSupG (n.val + 43850) < 2 ^ 1771 := by decide
private theorem cs_w28 : ∀ n : Fin 50, centredStar (densSupG (n.val + 43900)) (centF (n.val + 43900)) = true := by decide
private theorem cl_w28 : ∀ n : Fin 50, centF (n.val + 43900) < 23 := by decide
private theorem bd_w28 : ∀ n : Fin 50, densSupG (n.val + 43900) < 2 ^ 1771 := by decide
private theorem cs_w29 : ∀ n : Fin 50, centredStar (densSupG (n.val + 43950)) (centF (n.val + 43950)) = true := by decide
private theorem cl_w29 : ∀ n : Fin 50, centF (n.val + 43950) < 23 := by decide
private theorem bd_w29 : ∀ n : Fin 50, densSupG (n.val + 43950) < 2 ^ 1771 := by decide
private theorem cs_w30 : ∀ n : Fin 50, centredStar (densSupG (n.val + 44000)) (centF (n.val + 44000)) = true := by decide
private theorem cl_w30 : ∀ n : Fin 50, centF (n.val + 44000) < 23 := by decide
private theorem bd_w30 : ∀ n : Fin 50, densSupG (n.val + 44000) < 2 ^ 1771 := by decide
private theorem cs_w31 : ∀ n : Fin 50, centredStar (densSupG (n.val + 44050)) (centF (n.val + 44050)) = true := by decide
private theorem cl_w31 : ∀ n : Fin 50, centF (n.val + 44050) < 23 := by decide
private theorem bd_w31 : ∀ n : Fin 50, densSupG (n.val + 44050) < 2 ^ 1771 := by decide
private theorem cs_w32 : ∀ n : Fin 50, centredStar (densSupG (n.val + 44100)) (centF (n.val + 44100)) = true := by decide
private theorem cl_w32 : ∀ n : Fin 50, centF (n.val + 44100) < 23 := by decide
private theorem bd_w32 : ∀ n : Fin 50, densSupG (n.val + 44100) < 2 ^ 1771 := by decide
private theorem cs_w33 : ∀ n : Fin 50, centredStar (densSupG (n.val + 44150)) (centF (n.val + 44150)) = true := by decide
private theorem cl_w33 : ∀ n : Fin 50, centF (n.val + 44150) < 23 := by decide
private theorem bd_w33 : ∀ n : Fin 50, densSupG (n.val + 44150) < 2 ^ 1771 := by decide
private theorem cs_w34 : ∀ n : Fin 50, centredStar (densSupG (n.val + 44200)) (centF (n.val + 44200)) = true := by decide
private theorem cl_w34 : ∀ n : Fin 50, centF (n.val + 44200) < 23 := by decide
private theorem bd_w34 : ∀ n : Fin 50, densSupG (n.val + 44200) < 2 ^ 1771 := by decide
private theorem cs_w35 : ∀ n : Fin 50, centredStar (densSupG (n.val + 44250)) (centF (n.val + 44250)) = true := by decide
private theorem cl_w35 : ∀ n : Fin 50, centF (n.val + 44250) < 23 := by decide
private theorem bd_w35 : ∀ n : Fin 50, densSupG (n.val + 44250) < 2 ^ 1771 := by decide
private theorem cs_w36 : ∀ n : Fin 50, centredStar (densSupG (n.val + 44300)) (centF (n.val + 44300)) = true := by decide
private theorem cl_w36 : ∀ n : Fin 50, centF (n.val + 44300) < 23 := by decide
private theorem bd_w36 : ∀ n : Fin 50, densSupG (n.val + 44300) < 2 ^ 1771 := by decide
private theorem cs_w37 : ∀ n : Fin 50, centredStar (densSupG (n.val + 44350)) (centF (n.val + 44350)) = true := by decide
private theorem cl_w37 : ∀ n : Fin 50, centF (n.val + 44350) < 23 := by decide
private theorem bd_w37 : ∀ n : Fin 50, densSupG (n.val + 44350) < 2 ^ 1771 := by decide
private theorem cs_w38 : ∀ n : Fin 50, centredStar (densSupG (n.val + 44400)) (centF (n.val + 44400)) = true := by decide
private theorem cl_w38 : ∀ n : Fin 50, centF (n.val + 44400) < 23 := by decide
private theorem bd_w38 : ∀ n : Fin 50, densSupG (n.val + 44400) < 2 ^ 1771 := by decide
private theorem cs_w39 : ∀ n : Fin 50, centredStar (densSupG (n.val + 44450)) (centF (n.val + 44450)) = true := by decide
private theorem cl_w39 : ∀ n : Fin 50, centF (n.val + 44450) < 23 := by decide
private theorem bd_w39 : ∀ n : Fin 50, densSupG (n.val + 44450) < 2 ^ 1771 := by decide
private theorem cs_w40 : ∀ n : Fin 50, centredStar (densSupG (n.val + 44500)) (centF (n.val + 44500)) = true := by decide
private theorem cl_w40 : ∀ n : Fin 50, centF (n.val + 44500) < 23 := by decide
private theorem bd_w40 : ∀ n : Fin 50, densSupG (n.val + 44500) < 2 ^ 1771 := by decide
private theorem cs_w41 : ∀ n : Fin 50, centredStar (densSupG (n.val + 44550)) (centF (n.val + 44550)) = true := by decide
private theorem cl_w41 : ∀ n : Fin 50, centF (n.val + 44550) < 23 := by decide
private theorem bd_w41 : ∀ n : Fin 50, densSupG (n.val + 44550) < 2 ^ 1771 := by decide
private theorem cs_w42 : ∀ n : Fin 50, centredStar (densSupG (n.val + 44600)) (centF (n.val + 44600)) = true := by decide
private theorem cl_w42 : ∀ n : Fin 50, centF (n.val + 44600) < 23 := by decide
private theorem bd_w42 : ∀ n : Fin 50, densSupG (n.val + 44600) < 2 ^ 1771 := by decide
private theorem cs_w43 : ∀ n : Fin 50, centredStar (densSupG (n.val + 44650)) (centF (n.val + 44650)) = true := by decide
private theorem cl_w43 : ∀ n : Fin 50, centF (n.val + 44650) < 23 := by decide
private theorem bd_w43 : ∀ n : Fin 50, densSupG (n.val + 44650) < 2 ^ 1771 := by decide
private theorem cs_w44 : ∀ n : Fin 50, centredStar (densSupG (n.val + 44700)) (centF (n.val + 44700)) = true := by decide
private theorem cl_w44 : ∀ n : Fin 50, centF (n.val + 44700) < 23 := by decide
private theorem bd_w44 : ∀ n : Fin 50, densSupG (n.val + 44700) < 2 ^ 1771 := by decide
private theorem cs_w45 : ∀ n : Fin 50, centredStar (densSupG (n.val + 44750)) (centF (n.val + 44750)) = true := by decide
private theorem cl_w45 : ∀ n : Fin 50, centF (n.val + 44750) < 23 := by decide
private theorem bd_w45 : ∀ n : Fin 50, densSupG (n.val + 44750) < 2 ^ 1771 := by decide
private theorem cs_w46 : ∀ n : Fin 50, centredStar (densSupG (n.val + 44800)) (centF (n.val + 44800)) = true := by decide
private theorem cl_w46 : ∀ n : Fin 50, centF (n.val + 44800) < 23 := by decide
private theorem bd_w46 : ∀ n : Fin 50, densSupG (n.val + 44800) < 2 ^ 1771 := by decide
private theorem cs_w47 : ∀ n : Fin 50, centredStar (densSupG (n.val + 44850)) (centF (n.val + 44850)) = true := by decide
private theorem cl_w47 : ∀ n : Fin 50, centF (n.val + 44850) < 23 := by decide
private theorem bd_w47 : ∀ n : Fin 50, densSupG (n.val + 44850) < 2 ^ 1771 := by decide
private theorem cs_w48 : ∀ n : Fin 50, centredStar (densSupG (n.val + 44900)) (centF (n.val + 44900)) = true := by decide
private theorem cl_w48 : ∀ n : Fin 50, centF (n.val + 44900) < 23 := by decide
private theorem bd_w48 : ∀ n : Fin 50, densSupG (n.val + 44900) < 2 ^ 1771 := by decide
private theorem cs_w49 : ∀ n : Fin 50, centredStar (densSupG (n.val + 44950)) (centF (n.val + 44950)) = true := by decide
private theorem cl_w49 : ∀ n : Fin 50, centF (n.val + 44950) < 23 := by decide
private theorem bd_w49 : ∀ n : Fin 50, densSupG (n.val + 44950) < 2 ^ 1771 := by decide
theorem centredStar_range : ∀ n, 42500 ≤ n → n < 45000 → centredStar (densSupG n) (centF n) = true := by
  intro n hlo hhi
  by_cases h0 : n < 42550
  · have hr : n - 42500 < 50 := by omega
    have heq : n = (n - 42500) + 42500 := by omega
    rw [heq]
    exact cs_w0 ⟨n - 42500, hr⟩
  ·
    by_cases h1 : n < 42600
    ·
      have hr : n - 42550 < 50 := by omega
      have heq : n = (n - 42550) + 42550 := by omega
      rw [heq]
      exact cs_w1 ⟨n - 42550, hr⟩
    ·
      by_cases h2 : n < 42650
      ·
        have hr : n - 42600 < 50 := by omega
        have heq : n = (n - 42600) + 42600 := by omega
        rw [heq]
        exact cs_w2 ⟨n - 42600, hr⟩
      ·
        by_cases h3 : n < 42700
        ·
          have hr : n - 42650 < 50 := by omega
          have heq : n = (n - 42650) + 42650 := by omega
          rw [heq]
          exact cs_w3 ⟨n - 42650, hr⟩
        ·
          by_cases h4 : n < 42750
          ·
            have hr : n - 42700 < 50 := by omega
            have heq : n = (n - 42700) + 42700 := by omega
            rw [heq]
            exact cs_w4 ⟨n - 42700, hr⟩
          ·
            by_cases h5 : n < 42800
            ·
              have hr : n - 42750 < 50 := by omega
              have heq : n = (n - 42750) + 42750 := by omega
              rw [heq]
              exact cs_w5 ⟨n - 42750, hr⟩
            ·
              by_cases h6 : n < 42850
              ·
                have hr : n - 42800 < 50 := by omega
                have heq : n = (n - 42800) + 42800 := by omega
                rw [heq]
                exact cs_w6 ⟨n - 42800, hr⟩
              ·
                by_cases h7 : n < 42900
                ·
                  have hr : n - 42850 < 50 := by omega
                  have heq : n = (n - 42850) + 42850 := by omega
                  rw [heq]
                  exact cs_w7 ⟨n - 42850, hr⟩
                ·
                  by_cases h8 : n < 42950
                  ·
                    have hr : n - 42900 < 50 := by omega
                    have heq : n = (n - 42900) + 42900 := by omega
                    rw [heq]
                    exact cs_w8 ⟨n - 42900, hr⟩
                  ·
                    by_cases h9 : n < 43000
                    ·
                      have hr : n - 42950 < 50 := by omega
                      have heq : n = (n - 42950) + 42950 := by omega
                      rw [heq]
                      exact cs_w9 ⟨n - 42950, hr⟩
                    ·
                      by_cases h10 : n < 43050
                      ·
                        have hr : n - 43000 < 50 := by omega
                        have heq : n = (n - 43000) + 43000 := by omega
                        rw [heq]
                        exact cs_w10 ⟨n - 43000, hr⟩
                      ·
                        by_cases h11 : n < 43100
                        ·
                          have hr : n - 43050 < 50 := by omega
                          have heq : n = (n - 43050) + 43050 := by omega
                          rw [heq]
                          exact cs_w11 ⟨n - 43050, hr⟩
                        ·
                          by_cases h12 : n < 43150
                          ·
                            have hr : n - 43100 < 50 := by omega
                            have heq : n = (n - 43100) + 43100 := by omega
                            rw [heq]
                            exact cs_w12 ⟨n - 43100, hr⟩
                          ·
                            by_cases h13 : n < 43200
                            ·
                              have hr : n - 43150 < 50 := by omega
                              have heq : n = (n - 43150) + 43150 := by omega
                              rw [heq]
                              exact cs_w13 ⟨n - 43150, hr⟩
                            ·
                              by_cases h14 : n < 43250
                              ·
                                have hr : n - 43200 < 50 := by omega
                                have heq : n = (n - 43200) + 43200 := by omega
                                rw [heq]
                                exact cs_w14 ⟨n - 43200, hr⟩
                              ·
                                by_cases h15 : n < 43300
                                ·
                                  have hr : n - 43250 < 50 := by omega
                                  have heq : n = (n - 43250) + 43250 := by omega
                                  rw [heq]
                                  exact cs_w15 ⟨n - 43250, hr⟩
                                ·
                                  by_cases h16 : n < 43350
                                  ·
                                    have hr : n - 43300 < 50 := by omega
                                    have heq : n = (n - 43300) + 43300 := by omega
                                    rw [heq]
                                    exact cs_w16 ⟨n - 43300, hr⟩
                                  ·
                                    by_cases h17 : n < 43400
                                    ·
                                      have hr : n - 43350 < 50 := by omega
                                      have heq : n = (n - 43350) + 43350 := by omega
                                      rw [heq]
                                      exact cs_w17 ⟨n - 43350, hr⟩
                                    ·
                                      by_cases h18 : n < 43450
                                      ·
                                        have hr : n - 43400 < 50 := by omega
                                        have heq : n = (n - 43400) + 43400 := by omega
                                        rw [heq]
                                        exact cs_w18 ⟨n - 43400, hr⟩
                                      ·
                                        by_cases h19 : n < 43500
                                        ·
                                          have hr : n - 43450 < 50 := by omega
                                          have heq : n = (n - 43450) + 43450 := by omega
                                          rw [heq]
                                          exact cs_w19 ⟨n - 43450, hr⟩
                                        ·
                                          by_cases h20 : n < 43550
                                          ·
                                            have hr : n - 43500 < 50 := by omega
                                            have heq : n = (n - 43500) + 43500 := by omega
                                            rw [heq]
                                            exact cs_w20 ⟨n - 43500, hr⟩
                                          ·
                                            by_cases h21 : n < 43600
                                            ·
                                              have hr : n - 43550 < 50 := by omega
                                              have heq : n = (n - 43550) + 43550 := by omega
                                              rw [heq]
                                              exact cs_w21 ⟨n - 43550, hr⟩
                                            ·
                                              by_cases h22 : n < 43650
                                              ·
                                                have hr : n - 43600 < 50 := by omega
                                                have heq : n = (n - 43600) + 43600 := by omega
                                                rw [heq]
                                                exact cs_w22 ⟨n - 43600, hr⟩
                                              ·
                                                by_cases h23 : n < 43700
                                                ·
                                                  have hr : n - 43650 < 50 := by omega
                                                  have heq : n = (n - 43650) + 43650 := by omega
                                                  rw [heq]
                                                  exact cs_w23 ⟨n - 43650, hr⟩
                                                ·
                                                  by_cases h24 : n < 43750
                                                  ·
                                                    have hr : n - 43700 < 50 := by omega
                                                    have heq : n = (n - 43700) + 43700 := by omega
                                                    rw [heq]
                                                    exact cs_w24 ⟨n - 43700, hr⟩
                                                  ·
                                                    by_cases h25 : n < 43800
                                                    ·
                                                      have hr : n - 43750 < 50 := by omega
                                                      have heq : n = (n - 43750) + 43750 := by omega
                                                      rw [heq]
                                                      exact cs_w25 ⟨n - 43750, hr⟩
                                                    ·
                                                      by_cases h26 : n < 43850
                                                      ·
                                                        have hr : n - 43800 < 50 := by omega
                                                        have heq : n = (n - 43800) + 43800 := by omega
                                                        rw [heq]
                                                        exact cs_w26 ⟨n - 43800, hr⟩
                                                      ·
                                                        by_cases h27 : n < 43900
                                                        ·
                                                          have hr : n - 43850 < 50 := by omega
                                                          have heq : n = (n - 43850) + 43850 := by omega
                                                          rw [heq]
                                                          exact cs_w27 ⟨n - 43850, hr⟩
                                                        ·
                                                          by_cases h28 : n < 43950
                                                          ·
                                                            have hr : n - 43900 < 50 := by omega
                                                            have heq : n = (n - 43900) + 43900 := by omega
                                                            rw [heq]
                                                            exact cs_w28 ⟨n - 43900, hr⟩
                                                          ·
                                                            by_cases h29 : n < 44000
                                                            ·
                                                              have hr : n - 43950 < 50 := by omega
                                                              have heq : n = (n - 43950) + 43950 := by omega
                                                              rw [heq]
                                                              exact cs_w29 ⟨n - 43950, hr⟩
                                                            ·
                                                              by_cases h30 : n < 44050
                                                              ·
                                                                have hr : n - 44000 < 50 := by omega
                                                                have heq : n = (n - 44000) + 44000 := by omega
                                                                rw [heq]
                                                                exact cs_w30 ⟨n - 44000, hr⟩
                                                              ·
                                                                by_cases h31 : n < 44100
                                                                ·
                                                                  have hr : n - 44050 < 50 := by omega
                                                                  have heq : n = (n - 44050) + 44050 := by omega
                                                                  rw [heq]
                                                                  exact cs_w31 ⟨n - 44050, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 44150
                                                                  ·
                                                                    have hr : n - 44100 < 50 := by omega
                                                                    have heq : n = (n - 44100) + 44100 := by omega
                                                                    rw [heq]
                                                                    exact cs_w32 ⟨n - 44100, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 44200
                                                                    ·
                                                                      have hr : n - 44150 < 50 := by omega
                                                                      have heq : n = (n - 44150) + 44150 := by omega
                                                                      rw [heq]
                                                                      exact cs_w33 ⟨n - 44150, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 44250
                                                                      ·
                                                                        have hr : n - 44200 < 50 := by omega
                                                                        have heq : n = (n - 44200) + 44200 := by omega
                                                                        rw [heq]
                                                                        exact cs_w34 ⟨n - 44200, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 44300
                                                                        ·
                                                                          have hr : n - 44250 < 50 := by omega
                                                                          have heq : n = (n - 44250) + 44250 := by omega
                                                                          rw [heq]
                                                                          exact cs_w35 ⟨n - 44250, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 44350
                                                                          ·
                                                                            have hr : n - 44300 < 50 := by omega
                                                                            have heq : n = (n - 44300) + 44300 := by omega
                                                                            rw [heq]
                                                                            exact cs_w36 ⟨n - 44300, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 44400
                                                                            ·
                                                                              have hr : n - 44350 < 50 := by omega
                                                                              have heq : n = (n - 44350) + 44350 := by omega
                                                                              rw [heq]
                                                                              exact cs_w37 ⟨n - 44350, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 44450
                                                                              ·
                                                                                have hr : n - 44400 < 50 := by omega
                                                                                have heq : n = (n - 44400) + 44400 := by omega
                                                                                rw [heq]
                                                                                exact cs_w38 ⟨n - 44400, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 44500
                                                                                ·
                                                                                  have hr : n - 44450 < 50 := by omega
                                                                                  have heq : n = (n - 44450) + 44450 := by omega
                                                                                  rw [heq]
                                                                                  exact cs_w39 ⟨n - 44450, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 44550
                                                                                  ·
                                                                                    have hr : n - 44500 < 50 := by omega
                                                                                    have heq : n = (n - 44500) + 44500 := by omega
                                                                                    rw [heq]
                                                                                    exact cs_w40 ⟨n - 44500, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 44600
                                                                                    ·
                                                                                      have hr : n - 44550 < 50 := by omega
                                                                                      have heq : n = (n - 44550) + 44550 := by omega
                                                                                      rw [heq]
                                                                                      exact cs_w41 ⟨n - 44550, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 44650
                                                                                      ·
                                                                                        have hr : n - 44600 < 50 := by omega
                                                                                        have heq : n = (n - 44600) + 44600 := by omega
                                                                                        rw [heq]
                                                                                        exact cs_w42 ⟨n - 44600, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 44700
                                                                                        ·
                                                                                          have hr : n - 44650 < 50 := by omega
                                                                                          have heq : n = (n - 44650) + 44650 := by omega
                                                                                          rw [heq]
                                                                                          exact cs_w43 ⟨n - 44650, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 44750
                                                                                          ·
                                                                                            have hr : n - 44700 < 50 := by omega
                                                                                            have heq : n = (n - 44700) + 44700 := by omega
                                                                                            rw [heq]
                                                                                            exact cs_w44 ⟨n - 44700, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 44800
                                                                                            ·
                                                                                              have hr : n - 44750 < 50 := by omega
                                                                                              have heq : n = (n - 44750) + 44750 := by omega
                                                                                              rw [heq]
                                                                                              exact cs_w45 ⟨n - 44750, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 44850
                                                                                              ·
                                                                                                have hr : n - 44800 < 50 := by omega
                                                                                                have heq : n = (n - 44800) + 44800 := by omega
                                                                                                rw [heq]
                                                                                                exact cs_w46 ⟨n - 44800, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 44900
                                                                                                ·
                                                                                                  have hr : n - 44850 < 50 := by omega
                                                                                                  have heq : n = (n - 44850) + 44850 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cs_w47 ⟨n - 44850, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 44950
                                                                                                  ·
                                                                                                    have hr : n - 44900 < 50 := by omega
                                                                                                    have heq : n = (n - 44900) + 44900 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w48 ⟨n - 44900, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 44950 < 50 := by omega
                                                                                                    have heq : n = (n - 44950) + 44950 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w49 ⟨n - 44950, hr⟩


theorem centF_lt_range : ∀ n, 42500 ≤ n → n < 45000 → centF n < 23 := by
  intro n hlo hhi
  by_cases h0 : n < 42550
  · have hr : n - 42500 < 50 := by omega
    have heq : n = (n - 42500) + 42500 := by omega
    rw [heq]
    exact cl_w0 ⟨n - 42500, hr⟩
  ·
    by_cases h1 : n < 42600
    ·
      have hr : n - 42550 < 50 := by omega
      have heq : n = (n - 42550) + 42550 := by omega
      rw [heq]
      exact cl_w1 ⟨n - 42550, hr⟩
    ·
      by_cases h2 : n < 42650
      ·
        have hr : n - 42600 < 50 := by omega
        have heq : n = (n - 42600) + 42600 := by omega
        rw [heq]
        exact cl_w2 ⟨n - 42600, hr⟩
      ·
        by_cases h3 : n < 42700
        ·
          have hr : n - 42650 < 50 := by omega
          have heq : n = (n - 42650) + 42650 := by omega
          rw [heq]
          exact cl_w3 ⟨n - 42650, hr⟩
        ·
          by_cases h4 : n < 42750
          ·
            have hr : n - 42700 < 50 := by omega
            have heq : n = (n - 42700) + 42700 := by omega
            rw [heq]
            exact cl_w4 ⟨n - 42700, hr⟩
          ·
            by_cases h5 : n < 42800
            ·
              have hr : n - 42750 < 50 := by omega
              have heq : n = (n - 42750) + 42750 := by omega
              rw [heq]
              exact cl_w5 ⟨n - 42750, hr⟩
            ·
              by_cases h6 : n < 42850
              ·
                have hr : n - 42800 < 50 := by omega
                have heq : n = (n - 42800) + 42800 := by omega
                rw [heq]
                exact cl_w6 ⟨n - 42800, hr⟩
              ·
                by_cases h7 : n < 42900
                ·
                  have hr : n - 42850 < 50 := by omega
                  have heq : n = (n - 42850) + 42850 := by omega
                  rw [heq]
                  exact cl_w7 ⟨n - 42850, hr⟩
                ·
                  by_cases h8 : n < 42950
                  ·
                    have hr : n - 42900 < 50 := by omega
                    have heq : n = (n - 42900) + 42900 := by omega
                    rw [heq]
                    exact cl_w8 ⟨n - 42900, hr⟩
                  ·
                    by_cases h9 : n < 43000
                    ·
                      have hr : n - 42950 < 50 := by omega
                      have heq : n = (n - 42950) + 42950 := by omega
                      rw [heq]
                      exact cl_w9 ⟨n - 42950, hr⟩
                    ·
                      by_cases h10 : n < 43050
                      ·
                        have hr : n - 43000 < 50 := by omega
                        have heq : n = (n - 43000) + 43000 := by omega
                        rw [heq]
                        exact cl_w10 ⟨n - 43000, hr⟩
                      ·
                        by_cases h11 : n < 43100
                        ·
                          have hr : n - 43050 < 50 := by omega
                          have heq : n = (n - 43050) + 43050 := by omega
                          rw [heq]
                          exact cl_w11 ⟨n - 43050, hr⟩
                        ·
                          by_cases h12 : n < 43150
                          ·
                            have hr : n - 43100 < 50 := by omega
                            have heq : n = (n - 43100) + 43100 := by omega
                            rw [heq]
                            exact cl_w12 ⟨n - 43100, hr⟩
                          ·
                            by_cases h13 : n < 43200
                            ·
                              have hr : n - 43150 < 50 := by omega
                              have heq : n = (n - 43150) + 43150 := by omega
                              rw [heq]
                              exact cl_w13 ⟨n - 43150, hr⟩
                            ·
                              by_cases h14 : n < 43250
                              ·
                                have hr : n - 43200 < 50 := by omega
                                have heq : n = (n - 43200) + 43200 := by omega
                                rw [heq]
                                exact cl_w14 ⟨n - 43200, hr⟩
                              ·
                                by_cases h15 : n < 43300
                                ·
                                  have hr : n - 43250 < 50 := by omega
                                  have heq : n = (n - 43250) + 43250 := by omega
                                  rw [heq]
                                  exact cl_w15 ⟨n - 43250, hr⟩
                                ·
                                  by_cases h16 : n < 43350
                                  ·
                                    have hr : n - 43300 < 50 := by omega
                                    have heq : n = (n - 43300) + 43300 := by omega
                                    rw [heq]
                                    exact cl_w16 ⟨n - 43300, hr⟩
                                  ·
                                    by_cases h17 : n < 43400
                                    ·
                                      have hr : n - 43350 < 50 := by omega
                                      have heq : n = (n - 43350) + 43350 := by omega
                                      rw [heq]
                                      exact cl_w17 ⟨n - 43350, hr⟩
                                    ·
                                      by_cases h18 : n < 43450
                                      ·
                                        have hr : n - 43400 < 50 := by omega
                                        have heq : n = (n - 43400) + 43400 := by omega
                                        rw [heq]
                                        exact cl_w18 ⟨n - 43400, hr⟩
                                      ·
                                        by_cases h19 : n < 43500
                                        ·
                                          have hr : n - 43450 < 50 := by omega
                                          have heq : n = (n - 43450) + 43450 := by omega
                                          rw [heq]
                                          exact cl_w19 ⟨n - 43450, hr⟩
                                        ·
                                          by_cases h20 : n < 43550
                                          ·
                                            have hr : n - 43500 < 50 := by omega
                                            have heq : n = (n - 43500) + 43500 := by omega
                                            rw [heq]
                                            exact cl_w20 ⟨n - 43500, hr⟩
                                          ·
                                            by_cases h21 : n < 43600
                                            ·
                                              have hr : n - 43550 < 50 := by omega
                                              have heq : n = (n - 43550) + 43550 := by omega
                                              rw [heq]
                                              exact cl_w21 ⟨n - 43550, hr⟩
                                            ·
                                              by_cases h22 : n < 43650
                                              ·
                                                have hr : n - 43600 < 50 := by omega
                                                have heq : n = (n - 43600) + 43600 := by omega
                                                rw [heq]
                                                exact cl_w22 ⟨n - 43600, hr⟩
                                              ·
                                                by_cases h23 : n < 43700
                                                ·
                                                  have hr : n - 43650 < 50 := by omega
                                                  have heq : n = (n - 43650) + 43650 := by omega
                                                  rw [heq]
                                                  exact cl_w23 ⟨n - 43650, hr⟩
                                                ·
                                                  by_cases h24 : n < 43750
                                                  ·
                                                    have hr : n - 43700 < 50 := by omega
                                                    have heq : n = (n - 43700) + 43700 := by omega
                                                    rw [heq]
                                                    exact cl_w24 ⟨n - 43700, hr⟩
                                                  ·
                                                    by_cases h25 : n < 43800
                                                    ·
                                                      have hr : n - 43750 < 50 := by omega
                                                      have heq : n = (n - 43750) + 43750 := by omega
                                                      rw [heq]
                                                      exact cl_w25 ⟨n - 43750, hr⟩
                                                    ·
                                                      by_cases h26 : n < 43850
                                                      ·
                                                        have hr : n - 43800 < 50 := by omega
                                                        have heq : n = (n - 43800) + 43800 := by omega
                                                        rw [heq]
                                                        exact cl_w26 ⟨n - 43800, hr⟩
                                                      ·
                                                        by_cases h27 : n < 43900
                                                        ·
                                                          have hr : n - 43850 < 50 := by omega
                                                          have heq : n = (n - 43850) + 43850 := by omega
                                                          rw [heq]
                                                          exact cl_w27 ⟨n - 43850, hr⟩
                                                        ·
                                                          by_cases h28 : n < 43950
                                                          ·
                                                            have hr : n - 43900 < 50 := by omega
                                                            have heq : n = (n - 43900) + 43900 := by omega
                                                            rw [heq]
                                                            exact cl_w28 ⟨n - 43900, hr⟩
                                                          ·
                                                            by_cases h29 : n < 44000
                                                            ·
                                                              have hr : n - 43950 < 50 := by omega
                                                              have heq : n = (n - 43950) + 43950 := by omega
                                                              rw [heq]
                                                              exact cl_w29 ⟨n - 43950, hr⟩
                                                            ·
                                                              by_cases h30 : n < 44050
                                                              ·
                                                                have hr : n - 44000 < 50 := by omega
                                                                have heq : n = (n - 44000) + 44000 := by omega
                                                                rw [heq]
                                                                exact cl_w30 ⟨n - 44000, hr⟩
                                                              ·
                                                                by_cases h31 : n < 44100
                                                                ·
                                                                  have hr : n - 44050 < 50 := by omega
                                                                  have heq : n = (n - 44050) + 44050 := by omega
                                                                  rw [heq]
                                                                  exact cl_w31 ⟨n - 44050, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 44150
                                                                  ·
                                                                    have hr : n - 44100 < 50 := by omega
                                                                    have heq : n = (n - 44100) + 44100 := by omega
                                                                    rw [heq]
                                                                    exact cl_w32 ⟨n - 44100, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 44200
                                                                    ·
                                                                      have hr : n - 44150 < 50 := by omega
                                                                      have heq : n = (n - 44150) + 44150 := by omega
                                                                      rw [heq]
                                                                      exact cl_w33 ⟨n - 44150, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 44250
                                                                      ·
                                                                        have hr : n - 44200 < 50 := by omega
                                                                        have heq : n = (n - 44200) + 44200 := by omega
                                                                        rw [heq]
                                                                        exact cl_w34 ⟨n - 44200, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 44300
                                                                        ·
                                                                          have hr : n - 44250 < 50 := by omega
                                                                          have heq : n = (n - 44250) + 44250 := by omega
                                                                          rw [heq]
                                                                          exact cl_w35 ⟨n - 44250, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 44350
                                                                          ·
                                                                            have hr : n - 44300 < 50 := by omega
                                                                            have heq : n = (n - 44300) + 44300 := by omega
                                                                            rw [heq]
                                                                            exact cl_w36 ⟨n - 44300, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 44400
                                                                            ·
                                                                              have hr : n - 44350 < 50 := by omega
                                                                              have heq : n = (n - 44350) + 44350 := by omega
                                                                              rw [heq]
                                                                              exact cl_w37 ⟨n - 44350, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 44450
                                                                              ·
                                                                                have hr : n - 44400 < 50 := by omega
                                                                                have heq : n = (n - 44400) + 44400 := by omega
                                                                                rw [heq]
                                                                                exact cl_w38 ⟨n - 44400, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 44500
                                                                                ·
                                                                                  have hr : n - 44450 < 50 := by omega
                                                                                  have heq : n = (n - 44450) + 44450 := by omega
                                                                                  rw [heq]
                                                                                  exact cl_w39 ⟨n - 44450, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 44550
                                                                                  ·
                                                                                    have hr : n - 44500 < 50 := by omega
                                                                                    have heq : n = (n - 44500) + 44500 := by omega
                                                                                    rw [heq]
                                                                                    exact cl_w40 ⟨n - 44500, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 44600
                                                                                    ·
                                                                                      have hr : n - 44550 < 50 := by omega
                                                                                      have heq : n = (n - 44550) + 44550 := by omega
                                                                                      rw [heq]
                                                                                      exact cl_w41 ⟨n - 44550, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 44650
                                                                                      ·
                                                                                        have hr : n - 44600 < 50 := by omega
                                                                                        have heq : n = (n - 44600) + 44600 := by omega
                                                                                        rw [heq]
                                                                                        exact cl_w42 ⟨n - 44600, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 44700
                                                                                        ·
                                                                                          have hr : n - 44650 < 50 := by omega
                                                                                          have heq : n = (n - 44650) + 44650 := by omega
                                                                                          rw [heq]
                                                                                          exact cl_w43 ⟨n - 44650, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 44750
                                                                                          ·
                                                                                            have hr : n - 44700 < 50 := by omega
                                                                                            have heq : n = (n - 44700) + 44700 := by omega
                                                                                            rw [heq]
                                                                                            exact cl_w44 ⟨n - 44700, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 44800
                                                                                            ·
                                                                                              have hr : n - 44750 < 50 := by omega
                                                                                              have heq : n = (n - 44750) + 44750 := by omega
                                                                                              rw [heq]
                                                                                              exact cl_w45 ⟨n - 44750, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 44850
                                                                                              ·
                                                                                                have hr : n - 44800 < 50 := by omega
                                                                                                have heq : n = (n - 44800) + 44800 := by omega
                                                                                                rw [heq]
                                                                                                exact cl_w46 ⟨n - 44800, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 44900
                                                                                                ·
                                                                                                  have hr : n - 44850 < 50 := by omega
                                                                                                  have heq : n = (n - 44850) + 44850 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cl_w47 ⟨n - 44850, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 44950
                                                                                                  ·
                                                                                                    have hr : n - 44900 < 50 := by omega
                                                                                                    have heq : n = (n - 44900) + 44900 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w48 ⟨n - 44900, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 44950 < 50 := by omega
                                                                                                    have heq : n = (n - 44950) + 44950 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w49 ⟨n - 44950, hr⟩


theorem densSupG_lt_range : ∀ n, 42500 ≤ n → n < 45000 → densSupG n < 2 ^ 1771 := by
  intro n hlo hhi
  by_cases h0 : n < 42550
  · have hr : n - 42500 < 50 := by omega
    have heq : n = (n - 42500) + 42500 := by omega
    rw [heq]
    exact bd_w0 ⟨n - 42500, hr⟩
  ·
    by_cases h1 : n < 42600
    ·
      have hr : n - 42550 < 50 := by omega
      have heq : n = (n - 42550) + 42550 := by omega
      rw [heq]
      exact bd_w1 ⟨n - 42550, hr⟩
    ·
      by_cases h2 : n < 42650
      ·
        have hr : n - 42600 < 50 := by omega
        have heq : n = (n - 42600) + 42600 := by omega
        rw [heq]
        exact bd_w2 ⟨n - 42600, hr⟩
      ·
        by_cases h3 : n < 42700
        ·
          have hr : n - 42650 < 50 := by omega
          have heq : n = (n - 42650) + 42650 := by omega
          rw [heq]
          exact bd_w3 ⟨n - 42650, hr⟩
        ·
          by_cases h4 : n < 42750
          ·
            have hr : n - 42700 < 50 := by omega
            have heq : n = (n - 42700) + 42700 := by omega
            rw [heq]
            exact bd_w4 ⟨n - 42700, hr⟩
          ·
            by_cases h5 : n < 42800
            ·
              have hr : n - 42750 < 50 := by omega
              have heq : n = (n - 42750) + 42750 := by omega
              rw [heq]
              exact bd_w5 ⟨n - 42750, hr⟩
            ·
              by_cases h6 : n < 42850
              ·
                have hr : n - 42800 < 50 := by omega
                have heq : n = (n - 42800) + 42800 := by omega
                rw [heq]
                exact bd_w6 ⟨n - 42800, hr⟩
              ·
                by_cases h7 : n < 42900
                ·
                  have hr : n - 42850 < 50 := by omega
                  have heq : n = (n - 42850) + 42850 := by omega
                  rw [heq]
                  exact bd_w7 ⟨n - 42850, hr⟩
                ·
                  by_cases h8 : n < 42950
                  ·
                    have hr : n - 42900 < 50 := by omega
                    have heq : n = (n - 42900) + 42900 := by omega
                    rw [heq]
                    exact bd_w8 ⟨n - 42900, hr⟩
                  ·
                    by_cases h9 : n < 43000
                    ·
                      have hr : n - 42950 < 50 := by omega
                      have heq : n = (n - 42950) + 42950 := by omega
                      rw [heq]
                      exact bd_w9 ⟨n - 42950, hr⟩
                    ·
                      by_cases h10 : n < 43050
                      ·
                        have hr : n - 43000 < 50 := by omega
                        have heq : n = (n - 43000) + 43000 := by omega
                        rw [heq]
                        exact bd_w10 ⟨n - 43000, hr⟩
                      ·
                        by_cases h11 : n < 43100
                        ·
                          have hr : n - 43050 < 50 := by omega
                          have heq : n = (n - 43050) + 43050 := by omega
                          rw [heq]
                          exact bd_w11 ⟨n - 43050, hr⟩
                        ·
                          by_cases h12 : n < 43150
                          ·
                            have hr : n - 43100 < 50 := by omega
                            have heq : n = (n - 43100) + 43100 := by omega
                            rw [heq]
                            exact bd_w12 ⟨n - 43100, hr⟩
                          ·
                            by_cases h13 : n < 43200
                            ·
                              have hr : n - 43150 < 50 := by omega
                              have heq : n = (n - 43150) + 43150 := by omega
                              rw [heq]
                              exact bd_w13 ⟨n - 43150, hr⟩
                            ·
                              by_cases h14 : n < 43250
                              ·
                                have hr : n - 43200 < 50 := by omega
                                have heq : n = (n - 43200) + 43200 := by omega
                                rw [heq]
                                exact bd_w14 ⟨n - 43200, hr⟩
                              ·
                                by_cases h15 : n < 43300
                                ·
                                  have hr : n - 43250 < 50 := by omega
                                  have heq : n = (n - 43250) + 43250 := by omega
                                  rw [heq]
                                  exact bd_w15 ⟨n - 43250, hr⟩
                                ·
                                  by_cases h16 : n < 43350
                                  ·
                                    have hr : n - 43300 < 50 := by omega
                                    have heq : n = (n - 43300) + 43300 := by omega
                                    rw [heq]
                                    exact bd_w16 ⟨n - 43300, hr⟩
                                  ·
                                    by_cases h17 : n < 43400
                                    ·
                                      have hr : n - 43350 < 50 := by omega
                                      have heq : n = (n - 43350) + 43350 := by omega
                                      rw [heq]
                                      exact bd_w17 ⟨n - 43350, hr⟩
                                    ·
                                      by_cases h18 : n < 43450
                                      ·
                                        have hr : n - 43400 < 50 := by omega
                                        have heq : n = (n - 43400) + 43400 := by omega
                                        rw [heq]
                                        exact bd_w18 ⟨n - 43400, hr⟩
                                      ·
                                        by_cases h19 : n < 43500
                                        ·
                                          have hr : n - 43450 < 50 := by omega
                                          have heq : n = (n - 43450) + 43450 := by omega
                                          rw [heq]
                                          exact bd_w19 ⟨n - 43450, hr⟩
                                        ·
                                          by_cases h20 : n < 43550
                                          ·
                                            have hr : n - 43500 < 50 := by omega
                                            have heq : n = (n - 43500) + 43500 := by omega
                                            rw [heq]
                                            exact bd_w20 ⟨n - 43500, hr⟩
                                          ·
                                            by_cases h21 : n < 43600
                                            ·
                                              have hr : n - 43550 < 50 := by omega
                                              have heq : n = (n - 43550) + 43550 := by omega
                                              rw [heq]
                                              exact bd_w21 ⟨n - 43550, hr⟩
                                            ·
                                              by_cases h22 : n < 43650
                                              ·
                                                have hr : n - 43600 < 50 := by omega
                                                have heq : n = (n - 43600) + 43600 := by omega
                                                rw [heq]
                                                exact bd_w22 ⟨n - 43600, hr⟩
                                              ·
                                                by_cases h23 : n < 43700
                                                ·
                                                  have hr : n - 43650 < 50 := by omega
                                                  have heq : n = (n - 43650) + 43650 := by omega
                                                  rw [heq]
                                                  exact bd_w23 ⟨n - 43650, hr⟩
                                                ·
                                                  by_cases h24 : n < 43750
                                                  ·
                                                    have hr : n - 43700 < 50 := by omega
                                                    have heq : n = (n - 43700) + 43700 := by omega
                                                    rw [heq]
                                                    exact bd_w24 ⟨n - 43700, hr⟩
                                                  ·
                                                    by_cases h25 : n < 43800
                                                    ·
                                                      have hr : n - 43750 < 50 := by omega
                                                      have heq : n = (n - 43750) + 43750 := by omega
                                                      rw [heq]
                                                      exact bd_w25 ⟨n - 43750, hr⟩
                                                    ·
                                                      by_cases h26 : n < 43850
                                                      ·
                                                        have hr : n - 43800 < 50 := by omega
                                                        have heq : n = (n - 43800) + 43800 := by omega
                                                        rw [heq]
                                                        exact bd_w26 ⟨n - 43800, hr⟩
                                                      ·
                                                        by_cases h27 : n < 43900
                                                        ·
                                                          have hr : n - 43850 < 50 := by omega
                                                          have heq : n = (n - 43850) + 43850 := by omega
                                                          rw [heq]
                                                          exact bd_w27 ⟨n - 43850, hr⟩
                                                        ·
                                                          by_cases h28 : n < 43950
                                                          ·
                                                            have hr : n - 43900 < 50 := by omega
                                                            have heq : n = (n - 43900) + 43900 := by omega
                                                            rw [heq]
                                                            exact bd_w28 ⟨n - 43900, hr⟩
                                                          ·
                                                            by_cases h29 : n < 44000
                                                            ·
                                                              have hr : n - 43950 < 50 := by omega
                                                              have heq : n = (n - 43950) + 43950 := by omega
                                                              rw [heq]
                                                              exact bd_w29 ⟨n - 43950, hr⟩
                                                            ·
                                                              by_cases h30 : n < 44050
                                                              ·
                                                                have hr : n - 44000 < 50 := by omega
                                                                have heq : n = (n - 44000) + 44000 := by omega
                                                                rw [heq]
                                                                exact bd_w30 ⟨n - 44000, hr⟩
                                                              ·
                                                                by_cases h31 : n < 44100
                                                                ·
                                                                  have hr : n - 44050 < 50 := by omega
                                                                  have heq : n = (n - 44050) + 44050 := by omega
                                                                  rw [heq]
                                                                  exact bd_w31 ⟨n - 44050, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 44150
                                                                  ·
                                                                    have hr : n - 44100 < 50 := by omega
                                                                    have heq : n = (n - 44100) + 44100 := by omega
                                                                    rw [heq]
                                                                    exact bd_w32 ⟨n - 44100, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 44200
                                                                    ·
                                                                      have hr : n - 44150 < 50 := by omega
                                                                      have heq : n = (n - 44150) + 44150 := by omega
                                                                      rw [heq]
                                                                      exact bd_w33 ⟨n - 44150, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 44250
                                                                      ·
                                                                        have hr : n - 44200 < 50 := by omega
                                                                        have heq : n = (n - 44200) + 44200 := by omega
                                                                        rw [heq]
                                                                        exact bd_w34 ⟨n - 44200, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 44300
                                                                        ·
                                                                          have hr : n - 44250 < 50 := by omega
                                                                          have heq : n = (n - 44250) + 44250 := by omega
                                                                          rw [heq]
                                                                          exact bd_w35 ⟨n - 44250, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 44350
                                                                          ·
                                                                            have hr : n - 44300 < 50 := by omega
                                                                            have heq : n = (n - 44300) + 44300 := by omega
                                                                            rw [heq]
                                                                            exact bd_w36 ⟨n - 44300, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 44400
                                                                            ·
                                                                              have hr : n - 44350 < 50 := by omega
                                                                              have heq : n = (n - 44350) + 44350 := by omega
                                                                              rw [heq]
                                                                              exact bd_w37 ⟨n - 44350, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 44450
                                                                              ·
                                                                                have hr : n - 44400 < 50 := by omega
                                                                                have heq : n = (n - 44400) + 44400 := by omega
                                                                                rw [heq]
                                                                                exact bd_w38 ⟨n - 44400, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 44500
                                                                                ·
                                                                                  have hr : n - 44450 < 50 := by omega
                                                                                  have heq : n = (n - 44450) + 44450 := by omega
                                                                                  rw [heq]
                                                                                  exact bd_w39 ⟨n - 44450, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 44550
                                                                                  ·
                                                                                    have hr : n - 44500 < 50 := by omega
                                                                                    have heq : n = (n - 44500) + 44500 := by omega
                                                                                    rw [heq]
                                                                                    exact bd_w40 ⟨n - 44500, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 44600
                                                                                    ·
                                                                                      have hr : n - 44550 < 50 := by omega
                                                                                      have heq : n = (n - 44550) + 44550 := by omega
                                                                                      rw [heq]
                                                                                      exact bd_w41 ⟨n - 44550, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 44650
                                                                                      ·
                                                                                        have hr : n - 44600 < 50 := by omega
                                                                                        have heq : n = (n - 44600) + 44600 := by omega
                                                                                        rw [heq]
                                                                                        exact bd_w42 ⟨n - 44600, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 44700
                                                                                        ·
                                                                                          have hr : n - 44650 < 50 := by omega
                                                                                          have heq : n = (n - 44650) + 44650 := by omega
                                                                                          rw [heq]
                                                                                          exact bd_w43 ⟨n - 44650, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 44750
                                                                                          ·
                                                                                            have hr : n - 44700 < 50 := by omega
                                                                                            have heq : n = (n - 44700) + 44700 := by omega
                                                                                            rw [heq]
                                                                                            exact bd_w44 ⟨n - 44700, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 44800
                                                                                            ·
                                                                                              have hr : n - 44750 < 50 := by omega
                                                                                              have heq : n = (n - 44750) + 44750 := by omega
                                                                                              rw [heq]
                                                                                              exact bd_w45 ⟨n - 44750, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 44850
                                                                                              ·
                                                                                                have hr : n - 44800 < 50 := by omega
                                                                                                have heq : n = (n - 44800) + 44800 := by omega
                                                                                                rw [heq]
                                                                                                exact bd_w46 ⟨n - 44800, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 44900
                                                                                                ·
                                                                                                  have hr : n - 44850 < 50 := by omega
                                                                                                  have heq : n = (n - 44850) + 44850 := by omega
                                                                                                  rw [heq]
                                                                                                  exact bd_w47 ⟨n - 44850, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 44950
                                                                                                  ·
                                                                                                    have hr : n - 44900 < 50 := by omega
                                                                                                    have heq : n = (n - 44900) + 44900 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w48 ⟨n - 44900, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 44950 < 50 := by omega
                                                                                                    have heq : n = (n - 44950) + 44950 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w49 ⟨n - 44950, hr⟩


end IntMul.Kappa.R8.Bit.Oppbank.CentBound8bFix


