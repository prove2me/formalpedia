-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound11bFix
-- name    : IntMul_Kappa_R8_Data_BitOppbankCentBound11bFix
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T22:20:43.57755+00:00
-- url     : https://prove2.me/theorems/6af297e5-bec0-4d9c-a7e3-f52cc95c0abc
-- title:
--   IntMul Kappa R8 Data BitOppbankCentBound11bFix
-- statement:
--   Densified HasCentre support certificates (IntMul_Kappa_R8_Data_BitOppbankCentBound11bFix) retargeted to PndFix/CentFix.

-- CentBound11bFix: PndFix retarget
-- CentBound pack 11b: densified HasCentre certificates on n ∈ [57500, 60000)
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

namespace IntMul.Kappa.R8.Bit.Oppbank.CentBound11bFix


private theorem cs_w0 : ∀ n : Fin 50, centredStar (densSupG (n.val + 57500)) (centF (n.val + 57500)) = true := by decide
private theorem cl_w0 : ∀ n : Fin 50, centF (n.val + 57500) < 23 := by decide
private theorem bd_w0 : ∀ n : Fin 50, densSupG (n.val + 57500) < 2 ^ 1771 := by decide
private theorem cs_w1 : ∀ n : Fin 50, centredStar (densSupG (n.val + 57550)) (centF (n.val + 57550)) = true := by decide
private theorem cl_w1 : ∀ n : Fin 50, centF (n.val + 57550) < 23 := by decide
private theorem bd_w1 : ∀ n : Fin 50, densSupG (n.val + 57550) < 2 ^ 1771 := by decide
private theorem cs_w2 : ∀ n : Fin 50, centredStar (densSupG (n.val + 57600)) (centF (n.val + 57600)) = true := by decide
private theorem cl_w2 : ∀ n : Fin 50, centF (n.val + 57600) < 23 := by decide
private theorem bd_w2 : ∀ n : Fin 50, densSupG (n.val + 57600) < 2 ^ 1771 := by decide
private theorem cs_w3 : ∀ n : Fin 50, centredStar (densSupG (n.val + 57650)) (centF (n.val + 57650)) = true := by decide
private theorem cl_w3 : ∀ n : Fin 50, centF (n.val + 57650) < 23 := by decide
private theorem bd_w3 : ∀ n : Fin 50, densSupG (n.val + 57650) < 2 ^ 1771 := by decide
private theorem cs_w4 : ∀ n : Fin 50, centredStar (densSupG (n.val + 57700)) (centF (n.val + 57700)) = true := by decide
private theorem cl_w4 : ∀ n : Fin 50, centF (n.val + 57700) < 23 := by decide
private theorem bd_w4 : ∀ n : Fin 50, densSupG (n.val + 57700) < 2 ^ 1771 := by decide
private theorem cs_w5 : ∀ n : Fin 50, centredStar (densSupG (n.val + 57750)) (centF (n.val + 57750)) = true := by decide
private theorem cl_w5 : ∀ n : Fin 50, centF (n.val + 57750) < 23 := by decide
private theorem bd_w5 : ∀ n : Fin 50, densSupG (n.val + 57750) < 2 ^ 1771 := by decide
private theorem cs_w6 : ∀ n : Fin 50, centredStar (densSupG (n.val + 57800)) (centF (n.val + 57800)) = true := by decide
private theorem cl_w6 : ∀ n : Fin 50, centF (n.val + 57800) < 23 := by decide
private theorem bd_w6 : ∀ n : Fin 50, densSupG (n.val + 57800) < 2 ^ 1771 := by decide
private theorem cs_w7 : ∀ n : Fin 50, centredStar (densSupG (n.val + 57850)) (centF (n.val + 57850)) = true := by decide
private theorem cl_w7 : ∀ n : Fin 50, centF (n.val + 57850) < 23 := by decide
private theorem bd_w7 : ∀ n : Fin 50, densSupG (n.val + 57850) < 2 ^ 1771 := by decide
private theorem cs_w8 : ∀ n : Fin 50, centredStar (densSupG (n.val + 57900)) (centF (n.val + 57900)) = true := by decide
private theorem cl_w8 : ∀ n : Fin 50, centF (n.val + 57900) < 23 := by decide
private theorem bd_w8 : ∀ n : Fin 50, densSupG (n.val + 57900) < 2 ^ 1771 := by decide
private theorem cs_w9 : ∀ n : Fin 50, centredStar (densSupG (n.val + 57950)) (centF (n.val + 57950)) = true := by decide
private theorem cl_w9 : ∀ n : Fin 50, centF (n.val + 57950) < 23 := by decide
private theorem bd_w9 : ∀ n : Fin 50, densSupG (n.val + 57950) < 2 ^ 1771 := by decide
private theorem cs_w10 : ∀ n : Fin 50, centredStar (densSupG (n.val + 58000)) (centF (n.val + 58000)) = true := by decide
private theorem cl_w10 : ∀ n : Fin 50, centF (n.val + 58000) < 23 := by decide
private theorem bd_w10 : ∀ n : Fin 50, densSupG (n.val + 58000) < 2 ^ 1771 := by decide
private theorem cs_w11 : ∀ n : Fin 50, centredStar (densSupG (n.val + 58050)) (centF (n.val + 58050)) = true := by decide
private theorem cl_w11 : ∀ n : Fin 50, centF (n.val + 58050) < 23 := by decide
private theorem bd_w11 : ∀ n : Fin 50, densSupG (n.val + 58050) < 2 ^ 1771 := by decide
private theorem cs_w12 : ∀ n : Fin 50, centredStar (densSupG (n.val + 58100)) (centF (n.val + 58100)) = true := by decide
private theorem cl_w12 : ∀ n : Fin 50, centF (n.val + 58100) < 23 := by decide
private theorem bd_w12 : ∀ n : Fin 50, densSupG (n.val + 58100) < 2 ^ 1771 := by decide
private theorem cs_w13 : ∀ n : Fin 50, centredStar (densSupG (n.val + 58150)) (centF (n.val + 58150)) = true := by decide
private theorem cl_w13 : ∀ n : Fin 50, centF (n.val + 58150) < 23 := by decide
private theorem bd_w13 : ∀ n : Fin 50, densSupG (n.val + 58150) < 2 ^ 1771 := by decide
private theorem cs_w14 : ∀ n : Fin 50, centredStar (densSupG (n.val + 58200)) (centF (n.val + 58200)) = true := by decide
private theorem cl_w14 : ∀ n : Fin 50, centF (n.val + 58200) < 23 := by decide
private theorem bd_w14 : ∀ n : Fin 50, densSupG (n.val + 58200) < 2 ^ 1771 := by decide
private theorem cs_w15 : ∀ n : Fin 50, centredStar (densSupG (n.val + 58250)) (centF (n.val + 58250)) = true := by decide
private theorem cl_w15 : ∀ n : Fin 50, centF (n.val + 58250) < 23 := by decide
private theorem bd_w15 : ∀ n : Fin 50, densSupG (n.val + 58250) < 2 ^ 1771 := by decide
private theorem cs_w16 : ∀ n : Fin 50, centredStar (densSupG (n.val + 58300)) (centF (n.val + 58300)) = true := by decide
private theorem cl_w16 : ∀ n : Fin 50, centF (n.val + 58300) < 23 := by decide
private theorem bd_w16 : ∀ n : Fin 50, densSupG (n.val + 58300) < 2 ^ 1771 := by decide
private theorem cs_w17 : ∀ n : Fin 50, centredStar (densSupG (n.val + 58350)) (centF (n.val + 58350)) = true := by decide
private theorem cl_w17 : ∀ n : Fin 50, centF (n.val + 58350) < 23 := by decide
private theorem bd_w17 : ∀ n : Fin 50, densSupG (n.val + 58350) < 2 ^ 1771 := by decide
private theorem cs_w18 : ∀ n : Fin 50, centredStar (densSupG (n.val + 58400)) (centF (n.val + 58400)) = true := by decide
private theorem cl_w18 : ∀ n : Fin 50, centF (n.val + 58400) < 23 := by decide
private theorem bd_w18 : ∀ n : Fin 50, densSupG (n.val + 58400) < 2 ^ 1771 := by decide
private theorem cs_w19 : ∀ n : Fin 50, centredStar (densSupG (n.val + 58450)) (centF (n.val + 58450)) = true := by decide
private theorem cl_w19 : ∀ n : Fin 50, centF (n.val + 58450) < 23 := by decide
private theorem bd_w19 : ∀ n : Fin 50, densSupG (n.val + 58450) < 2 ^ 1771 := by decide
private theorem cs_w20 : ∀ n : Fin 50, centredStar (densSupG (n.val + 58500)) (centF (n.val + 58500)) = true := by decide
private theorem cl_w20 : ∀ n : Fin 50, centF (n.val + 58500) < 23 := by decide
private theorem bd_w20 : ∀ n : Fin 50, densSupG (n.val + 58500) < 2 ^ 1771 := by decide
private theorem cs_w21 : ∀ n : Fin 50, centredStar (densSupG (n.val + 58550)) (centF (n.val + 58550)) = true := by decide
private theorem cl_w21 : ∀ n : Fin 50, centF (n.val + 58550) < 23 := by decide
private theorem bd_w21 : ∀ n : Fin 50, densSupG (n.val + 58550) < 2 ^ 1771 := by decide
private theorem cs_w22 : ∀ n : Fin 50, centredStar (densSupG (n.val + 58600)) (centF (n.val + 58600)) = true := by decide
private theorem cl_w22 : ∀ n : Fin 50, centF (n.val + 58600) < 23 := by decide
private theorem bd_w22 : ∀ n : Fin 50, densSupG (n.val + 58600) < 2 ^ 1771 := by decide
private theorem cs_w23 : ∀ n : Fin 50, centredStar (densSupG (n.val + 58650)) (centF (n.val + 58650)) = true := by decide
private theorem cl_w23 : ∀ n : Fin 50, centF (n.val + 58650) < 23 := by decide
private theorem bd_w23 : ∀ n : Fin 50, densSupG (n.val + 58650) < 2 ^ 1771 := by decide
private theorem cs_w24 : ∀ n : Fin 50, centredStar (densSupG (n.val + 58700)) (centF (n.val + 58700)) = true := by decide
private theorem cl_w24 : ∀ n : Fin 50, centF (n.val + 58700) < 23 := by decide
private theorem bd_w24 : ∀ n : Fin 50, densSupG (n.val + 58700) < 2 ^ 1771 := by decide
private theorem cs_w25 : ∀ n : Fin 50, centredStar (densSupG (n.val + 58750)) (centF (n.val + 58750)) = true := by decide
private theorem cl_w25 : ∀ n : Fin 50, centF (n.val + 58750) < 23 := by decide
private theorem bd_w25 : ∀ n : Fin 50, densSupG (n.val + 58750) < 2 ^ 1771 := by decide
private theorem cs_w26 : ∀ n : Fin 50, centredStar (densSupG (n.val + 58800)) (centF (n.val + 58800)) = true := by decide
private theorem cl_w26 : ∀ n : Fin 50, centF (n.val + 58800) < 23 := by decide
private theorem bd_w26 : ∀ n : Fin 50, densSupG (n.val + 58800) < 2 ^ 1771 := by decide
private theorem cs_w27 : ∀ n : Fin 50, centredStar (densSupG (n.val + 58850)) (centF (n.val + 58850)) = true := by decide
private theorem cl_w27 : ∀ n : Fin 50, centF (n.val + 58850) < 23 := by decide
private theorem bd_w27 : ∀ n : Fin 50, densSupG (n.val + 58850) < 2 ^ 1771 := by decide
private theorem cs_w28 : ∀ n : Fin 50, centredStar (densSupG (n.val + 58900)) (centF (n.val + 58900)) = true := by decide
private theorem cl_w28 : ∀ n : Fin 50, centF (n.val + 58900) < 23 := by decide
private theorem bd_w28 : ∀ n : Fin 50, densSupG (n.val + 58900) < 2 ^ 1771 := by decide
private theorem cs_w29 : ∀ n : Fin 50, centredStar (densSupG (n.val + 58950)) (centF (n.val + 58950)) = true := by decide
private theorem cl_w29 : ∀ n : Fin 50, centF (n.val + 58950) < 23 := by decide
private theorem bd_w29 : ∀ n : Fin 50, densSupG (n.val + 58950) < 2 ^ 1771 := by decide
private theorem cs_w30 : ∀ n : Fin 50, centredStar (densSupG (n.val + 59000)) (centF (n.val + 59000)) = true := by decide
private theorem cl_w30 : ∀ n : Fin 50, centF (n.val + 59000) < 23 := by decide
private theorem bd_w30 : ∀ n : Fin 50, densSupG (n.val + 59000) < 2 ^ 1771 := by decide
private theorem cs_w31 : ∀ n : Fin 50, centredStar (densSupG (n.val + 59050)) (centF (n.val + 59050)) = true := by decide
private theorem cl_w31 : ∀ n : Fin 50, centF (n.val + 59050) < 23 := by decide
private theorem bd_w31 : ∀ n : Fin 50, densSupG (n.val + 59050) < 2 ^ 1771 := by decide
private theorem cs_w32 : ∀ n : Fin 50, centredStar (densSupG (n.val + 59100)) (centF (n.val + 59100)) = true := by decide
private theorem cl_w32 : ∀ n : Fin 50, centF (n.val + 59100) < 23 := by decide
private theorem bd_w32 : ∀ n : Fin 50, densSupG (n.val + 59100) < 2 ^ 1771 := by decide
private theorem cs_w33 : ∀ n : Fin 50, centredStar (densSupG (n.val + 59150)) (centF (n.val + 59150)) = true := by decide
private theorem cl_w33 : ∀ n : Fin 50, centF (n.val + 59150) < 23 := by decide
private theorem bd_w33 : ∀ n : Fin 50, densSupG (n.val + 59150) < 2 ^ 1771 := by decide
private theorem cs_w34 : ∀ n : Fin 50, centredStar (densSupG (n.val + 59200)) (centF (n.val + 59200)) = true := by decide
private theorem cl_w34 : ∀ n : Fin 50, centF (n.val + 59200) < 23 := by decide
private theorem bd_w34 : ∀ n : Fin 50, densSupG (n.val + 59200) < 2 ^ 1771 := by decide
private theorem cs_w35 : ∀ n : Fin 50, centredStar (densSupG (n.val + 59250)) (centF (n.val + 59250)) = true := by decide
private theorem cl_w35 : ∀ n : Fin 50, centF (n.val + 59250) < 23 := by decide
private theorem bd_w35 : ∀ n : Fin 50, densSupG (n.val + 59250) < 2 ^ 1771 := by decide
private theorem cs_w36 : ∀ n : Fin 50, centredStar (densSupG (n.val + 59300)) (centF (n.val + 59300)) = true := by decide
private theorem cl_w36 : ∀ n : Fin 50, centF (n.val + 59300) < 23 := by decide
private theorem bd_w36 : ∀ n : Fin 50, densSupG (n.val + 59300) < 2 ^ 1771 := by decide
private theorem cs_w37 : ∀ n : Fin 50, centredStar (densSupG (n.val + 59350)) (centF (n.val + 59350)) = true := by decide
private theorem cl_w37 : ∀ n : Fin 50, centF (n.val + 59350) < 23 := by decide
private theorem bd_w37 : ∀ n : Fin 50, densSupG (n.val + 59350) < 2 ^ 1771 := by decide
private theorem cs_w38 : ∀ n : Fin 50, centredStar (densSupG (n.val + 59400)) (centF (n.val + 59400)) = true := by decide
private theorem cl_w38 : ∀ n : Fin 50, centF (n.val + 59400) < 23 := by decide
private theorem bd_w38 : ∀ n : Fin 50, densSupG (n.val + 59400) < 2 ^ 1771 := by decide
private theorem cs_w39 : ∀ n : Fin 50, centredStar (densSupG (n.val + 59450)) (centF (n.val + 59450)) = true := by decide
private theorem cl_w39 : ∀ n : Fin 50, centF (n.val + 59450) < 23 := by decide
private theorem bd_w39 : ∀ n : Fin 50, densSupG (n.val + 59450) < 2 ^ 1771 := by decide
private theorem cs_w40 : ∀ n : Fin 50, centredStar (densSupG (n.val + 59500)) (centF (n.val + 59500)) = true := by decide
private theorem cl_w40 : ∀ n : Fin 50, centF (n.val + 59500) < 23 := by decide
private theorem bd_w40 : ∀ n : Fin 50, densSupG (n.val + 59500) < 2 ^ 1771 := by decide
private theorem cs_w41 : ∀ n : Fin 50, centredStar (densSupG (n.val + 59550)) (centF (n.val + 59550)) = true := by decide
private theorem cl_w41 : ∀ n : Fin 50, centF (n.val + 59550) < 23 := by decide
private theorem bd_w41 : ∀ n : Fin 50, densSupG (n.val + 59550) < 2 ^ 1771 := by decide
private theorem cs_w42 : ∀ n : Fin 50, centredStar (densSupG (n.val + 59600)) (centF (n.val + 59600)) = true := by decide
private theorem cl_w42 : ∀ n : Fin 50, centF (n.val + 59600) < 23 := by decide
private theorem bd_w42 : ∀ n : Fin 50, densSupG (n.val + 59600) < 2 ^ 1771 := by decide
private theorem cs_w43 : ∀ n : Fin 50, centredStar (densSupG (n.val + 59650)) (centF (n.val + 59650)) = true := by decide
private theorem cl_w43 : ∀ n : Fin 50, centF (n.val + 59650) < 23 := by decide
private theorem bd_w43 : ∀ n : Fin 50, densSupG (n.val + 59650) < 2 ^ 1771 := by decide
private theorem cs_w44 : ∀ n : Fin 50, centredStar (densSupG (n.val + 59700)) (centF (n.val + 59700)) = true := by decide
private theorem cl_w44 : ∀ n : Fin 50, centF (n.val + 59700) < 23 := by decide
private theorem bd_w44 : ∀ n : Fin 50, densSupG (n.val + 59700) < 2 ^ 1771 := by decide
private theorem cs_w45 : ∀ n : Fin 50, centredStar (densSupG (n.val + 59750)) (centF (n.val + 59750)) = true := by decide
private theorem cl_w45 : ∀ n : Fin 50, centF (n.val + 59750) < 23 := by decide
private theorem bd_w45 : ∀ n : Fin 50, densSupG (n.val + 59750) < 2 ^ 1771 := by decide
private theorem cs_w46 : ∀ n : Fin 50, centredStar (densSupG (n.val + 59800)) (centF (n.val + 59800)) = true := by decide
private theorem cl_w46 : ∀ n : Fin 50, centF (n.val + 59800) < 23 := by decide
private theorem bd_w46 : ∀ n : Fin 50, densSupG (n.val + 59800) < 2 ^ 1771 := by decide
private theorem cs_w47 : ∀ n : Fin 50, centredStar (densSupG (n.val + 59850)) (centF (n.val + 59850)) = true := by decide
private theorem cl_w47 : ∀ n : Fin 50, centF (n.val + 59850) < 23 := by decide
private theorem bd_w47 : ∀ n : Fin 50, densSupG (n.val + 59850) < 2 ^ 1771 := by decide
private theorem cs_w48 : ∀ n : Fin 50, centredStar (densSupG (n.val + 59900)) (centF (n.val + 59900)) = true := by decide
private theorem cl_w48 : ∀ n : Fin 50, centF (n.val + 59900) < 23 := by decide
private theorem bd_w48 : ∀ n : Fin 50, densSupG (n.val + 59900) < 2 ^ 1771 := by decide
private theorem cs_w49 : ∀ n : Fin 50, centredStar (densSupG (n.val + 59950)) (centF (n.val + 59950)) = true := by decide
private theorem cl_w49 : ∀ n : Fin 50, centF (n.val + 59950) < 23 := by decide
private theorem bd_w49 : ∀ n : Fin 50, densSupG (n.val + 59950) < 2 ^ 1771 := by decide
theorem centredStar_range : ∀ n, 57500 ≤ n → n < 60000 → centredStar (densSupG n) (centF n) = true := by
  intro n hlo hhi
  by_cases h0 : n < 57550
  · have hr : n - 57500 < 50 := by omega
    have heq : n = (n - 57500) + 57500 := by omega
    rw [heq]
    exact cs_w0 ⟨n - 57500, hr⟩
  ·
    by_cases h1 : n < 57600
    ·
      have hr : n - 57550 < 50 := by omega
      have heq : n = (n - 57550) + 57550 := by omega
      rw [heq]
      exact cs_w1 ⟨n - 57550, hr⟩
    ·
      by_cases h2 : n < 57650
      ·
        have hr : n - 57600 < 50 := by omega
        have heq : n = (n - 57600) + 57600 := by omega
        rw [heq]
        exact cs_w2 ⟨n - 57600, hr⟩
      ·
        by_cases h3 : n < 57700
        ·
          have hr : n - 57650 < 50 := by omega
          have heq : n = (n - 57650) + 57650 := by omega
          rw [heq]
          exact cs_w3 ⟨n - 57650, hr⟩
        ·
          by_cases h4 : n < 57750
          ·
            have hr : n - 57700 < 50 := by omega
            have heq : n = (n - 57700) + 57700 := by omega
            rw [heq]
            exact cs_w4 ⟨n - 57700, hr⟩
          ·
            by_cases h5 : n < 57800
            ·
              have hr : n - 57750 < 50 := by omega
              have heq : n = (n - 57750) + 57750 := by omega
              rw [heq]
              exact cs_w5 ⟨n - 57750, hr⟩
            ·
              by_cases h6 : n < 57850
              ·
                have hr : n - 57800 < 50 := by omega
                have heq : n = (n - 57800) + 57800 := by omega
                rw [heq]
                exact cs_w6 ⟨n - 57800, hr⟩
              ·
                by_cases h7 : n < 57900
                ·
                  have hr : n - 57850 < 50 := by omega
                  have heq : n = (n - 57850) + 57850 := by omega
                  rw [heq]
                  exact cs_w7 ⟨n - 57850, hr⟩
                ·
                  by_cases h8 : n < 57950
                  ·
                    have hr : n - 57900 < 50 := by omega
                    have heq : n = (n - 57900) + 57900 := by omega
                    rw [heq]
                    exact cs_w8 ⟨n - 57900, hr⟩
                  ·
                    by_cases h9 : n < 58000
                    ·
                      have hr : n - 57950 < 50 := by omega
                      have heq : n = (n - 57950) + 57950 := by omega
                      rw [heq]
                      exact cs_w9 ⟨n - 57950, hr⟩
                    ·
                      by_cases h10 : n < 58050
                      ·
                        have hr : n - 58000 < 50 := by omega
                        have heq : n = (n - 58000) + 58000 := by omega
                        rw [heq]
                        exact cs_w10 ⟨n - 58000, hr⟩
                      ·
                        by_cases h11 : n < 58100
                        ·
                          have hr : n - 58050 < 50 := by omega
                          have heq : n = (n - 58050) + 58050 := by omega
                          rw [heq]
                          exact cs_w11 ⟨n - 58050, hr⟩
                        ·
                          by_cases h12 : n < 58150
                          ·
                            have hr : n - 58100 < 50 := by omega
                            have heq : n = (n - 58100) + 58100 := by omega
                            rw [heq]
                            exact cs_w12 ⟨n - 58100, hr⟩
                          ·
                            by_cases h13 : n < 58200
                            ·
                              have hr : n - 58150 < 50 := by omega
                              have heq : n = (n - 58150) + 58150 := by omega
                              rw [heq]
                              exact cs_w13 ⟨n - 58150, hr⟩
                            ·
                              by_cases h14 : n < 58250
                              ·
                                have hr : n - 58200 < 50 := by omega
                                have heq : n = (n - 58200) + 58200 := by omega
                                rw [heq]
                                exact cs_w14 ⟨n - 58200, hr⟩
                              ·
                                by_cases h15 : n < 58300
                                ·
                                  have hr : n - 58250 < 50 := by omega
                                  have heq : n = (n - 58250) + 58250 := by omega
                                  rw [heq]
                                  exact cs_w15 ⟨n - 58250, hr⟩
                                ·
                                  by_cases h16 : n < 58350
                                  ·
                                    have hr : n - 58300 < 50 := by omega
                                    have heq : n = (n - 58300) + 58300 := by omega
                                    rw [heq]
                                    exact cs_w16 ⟨n - 58300, hr⟩
                                  ·
                                    by_cases h17 : n < 58400
                                    ·
                                      have hr : n - 58350 < 50 := by omega
                                      have heq : n = (n - 58350) + 58350 := by omega
                                      rw [heq]
                                      exact cs_w17 ⟨n - 58350, hr⟩
                                    ·
                                      by_cases h18 : n < 58450
                                      ·
                                        have hr : n - 58400 < 50 := by omega
                                        have heq : n = (n - 58400) + 58400 := by omega
                                        rw [heq]
                                        exact cs_w18 ⟨n - 58400, hr⟩
                                      ·
                                        by_cases h19 : n < 58500
                                        ·
                                          have hr : n - 58450 < 50 := by omega
                                          have heq : n = (n - 58450) + 58450 := by omega
                                          rw [heq]
                                          exact cs_w19 ⟨n - 58450, hr⟩
                                        ·
                                          by_cases h20 : n < 58550
                                          ·
                                            have hr : n - 58500 < 50 := by omega
                                            have heq : n = (n - 58500) + 58500 := by omega
                                            rw [heq]
                                            exact cs_w20 ⟨n - 58500, hr⟩
                                          ·
                                            by_cases h21 : n < 58600
                                            ·
                                              have hr : n - 58550 < 50 := by omega
                                              have heq : n = (n - 58550) + 58550 := by omega
                                              rw [heq]
                                              exact cs_w21 ⟨n - 58550, hr⟩
                                            ·
                                              by_cases h22 : n < 58650
                                              ·
                                                have hr : n - 58600 < 50 := by omega
                                                have heq : n = (n - 58600) + 58600 := by omega
                                                rw [heq]
                                                exact cs_w22 ⟨n - 58600, hr⟩
                                              ·
                                                by_cases h23 : n < 58700
                                                ·
                                                  have hr : n - 58650 < 50 := by omega
                                                  have heq : n = (n - 58650) + 58650 := by omega
                                                  rw [heq]
                                                  exact cs_w23 ⟨n - 58650, hr⟩
                                                ·
                                                  by_cases h24 : n < 58750
                                                  ·
                                                    have hr : n - 58700 < 50 := by omega
                                                    have heq : n = (n - 58700) + 58700 := by omega
                                                    rw [heq]
                                                    exact cs_w24 ⟨n - 58700, hr⟩
                                                  ·
                                                    by_cases h25 : n < 58800
                                                    ·
                                                      have hr : n - 58750 < 50 := by omega
                                                      have heq : n = (n - 58750) + 58750 := by omega
                                                      rw [heq]
                                                      exact cs_w25 ⟨n - 58750, hr⟩
                                                    ·
                                                      by_cases h26 : n < 58850
                                                      ·
                                                        have hr : n - 58800 < 50 := by omega
                                                        have heq : n = (n - 58800) + 58800 := by omega
                                                        rw [heq]
                                                        exact cs_w26 ⟨n - 58800, hr⟩
                                                      ·
                                                        by_cases h27 : n < 58900
                                                        ·
                                                          have hr : n - 58850 < 50 := by omega
                                                          have heq : n = (n - 58850) + 58850 := by omega
                                                          rw [heq]
                                                          exact cs_w27 ⟨n - 58850, hr⟩
                                                        ·
                                                          by_cases h28 : n < 58950
                                                          ·
                                                            have hr : n - 58900 < 50 := by omega
                                                            have heq : n = (n - 58900) + 58900 := by omega
                                                            rw [heq]
                                                            exact cs_w28 ⟨n - 58900, hr⟩
                                                          ·
                                                            by_cases h29 : n < 59000
                                                            ·
                                                              have hr : n - 58950 < 50 := by omega
                                                              have heq : n = (n - 58950) + 58950 := by omega
                                                              rw [heq]
                                                              exact cs_w29 ⟨n - 58950, hr⟩
                                                            ·
                                                              by_cases h30 : n < 59050
                                                              ·
                                                                have hr : n - 59000 < 50 := by omega
                                                                have heq : n = (n - 59000) + 59000 := by omega
                                                                rw [heq]
                                                                exact cs_w30 ⟨n - 59000, hr⟩
                                                              ·
                                                                by_cases h31 : n < 59100
                                                                ·
                                                                  have hr : n - 59050 < 50 := by omega
                                                                  have heq : n = (n - 59050) + 59050 := by omega
                                                                  rw [heq]
                                                                  exact cs_w31 ⟨n - 59050, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 59150
                                                                  ·
                                                                    have hr : n - 59100 < 50 := by omega
                                                                    have heq : n = (n - 59100) + 59100 := by omega
                                                                    rw [heq]
                                                                    exact cs_w32 ⟨n - 59100, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 59200
                                                                    ·
                                                                      have hr : n - 59150 < 50 := by omega
                                                                      have heq : n = (n - 59150) + 59150 := by omega
                                                                      rw [heq]
                                                                      exact cs_w33 ⟨n - 59150, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 59250
                                                                      ·
                                                                        have hr : n - 59200 < 50 := by omega
                                                                        have heq : n = (n - 59200) + 59200 := by omega
                                                                        rw [heq]
                                                                        exact cs_w34 ⟨n - 59200, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 59300
                                                                        ·
                                                                          have hr : n - 59250 < 50 := by omega
                                                                          have heq : n = (n - 59250) + 59250 := by omega
                                                                          rw [heq]
                                                                          exact cs_w35 ⟨n - 59250, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 59350
                                                                          ·
                                                                            have hr : n - 59300 < 50 := by omega
                                                                            have heq : n = (n - 59300) + 59300 := by omega
                                                                            rw [heq]
                                                                            exact cs_w36 ⟨n - 59300, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 59400
                                                                            ·
                                                                              have hr : n - 59350 < 50 := by omega
                                                                              have heq : n = (n - 59350) + 59350 := by omega
                                                                              rw [heq]
                                                                              exact cs_w37 ⟨n - 59350, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 59450
                                                                              ·
                                                                                have hr : n - 59400 < 50 := by omega
                                                                                have heq : n = (n - 59400) + 59400 := by omega
                                                                                rw [heq]
                                                                                exact cs_w38 ⟨n - 59400, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 59500
                                                                                ·
                                                                                  have hr : n - 59450 < 50 := by omega
                                                                                  have heq : n = (n - 59450) + 59450 := by omega
                                                                                  rw [heq]
                                                                                  exact cs_w39 ⟨n - 59450, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 59550
                                                                                  ·
                                                                                    have hr : n - 59500 < 50 := by omega
                                                                                    have heq : n = (n - 59500) + 59500 := by omega
                                                                                    rw [heq]
                                                                                    exact cs_w40 ⟨n - 59500, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 59600
                                                                                    ·
                                                                                      have hr : n - 59550 < 50 := by omega
                                                                                      have heq : n = (n - 59550) + 59550 := by omega
                                                                                      rw [heq]
                                                                                      exact cs_w41 ⟨n - 59550, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 59650
                                                                                      ·
                                                                                        have hr : n - 59600 < 50 := by omega
                                                                                        have heq : n = (n - 59600) + 59600 := by omega
                                                                                        rw [heq]
                                                                                        exact cs_w42 ⟨n - 59600, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 59700
                                                                                        ·
                                                                                          have hr : n - 59650 < 50 := by omega
                                                                                          have heq : n = (n - 59650) + 59650 := by omega
                                                                                          rw [heq]
                                                                                          exact cs_w43 ⟨n - 59650, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 59750
                                                                                          ·
                                                                                            have hr : n - 59700 < 50 := by omega
                                                                                            have heq : n = (n - 59700) + 59700 := by omega
                                                                                            rw [heq]
                                                                                            exact cs_w44 ⟨n - 59700, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 59800
                                                                                            ·
                                                                                              have hr : n - 59750 < 50 := by omega
                                                                                              have heq : n = (n - 59750) + 59750 := by omega
                                                                                              rw [heq]
                                                                                              exact cs_w45 ⟨n - 59750, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 59850
                                                                                              ·
                                                                                                have hr : n - 59800 < 50 := by omega
                                                                                                have heq : n = (n - 59800) + 59800 := by omega
                                                                                                rw [heq]
                                                                                                exact cs_w46 ⟨n - 59800, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 59900
                                                                                                ·
                                                                                                  have hr : n - 59850 < 50 := by omega
                                                                                                  have heq : n = (n - 59850) + 59850 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cs_w47 ⟨n - 59850, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 59950
                                                                                                  ·
                                                                                                    have hr : n - 59900 < 50 := by omega
                                                                                                    have heq : n = (n - 59900) + 59900 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w48 ⟨n - 59900, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 59950 < 50 := by omega
                                                                                                    have heq : n = (n - 59950) + 59950 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w49 ⟨n - 59950, hr⟩


theorem centF_lt_range : ∀ n, 57500 ≤ n → n < 60000 → centF n < 23 := by
  intro n hlo hhi
  by_cases h0 : n < 57550
  · have hr : n - 57500 < 50 := by omega
    have heq : n = (n - 57500) + 57500 := by omega
    rw [heq]
    exact cl_w0 ⟨n - 57500, hr⟩
  ·
    by_cases h1 : n < 57600
    ·
      have hr : n - 57550 < 50 := by omega
      have heq : n = (n - 57550) + 57550 := by omega
      rw [heq]
      exact cl_w1 ⟨n - 57550, hr⟩
    ·
      by_cases h2 : n < 57650
      ·
        have hr : n - 57600 < 50 := by omega
        have heq : n = (n - 57600) + 57600 := by omega
        rw [heq]
        exact cl_w2 ⟨n - 57600, hr⟩
      ·
        by_cases h3 : n < 57700
        ·
          have hr : n - 57650 < 50 := by omega
          have heq : n = (n - 57650) + 57650 := by omega
          rw [heq]
          exact cl_w3 ⟨n - 57650, hr⟩
        ·
          by_cases h4 : n < 57750
          ·
            have hr : n - 57700 < 50 := by omega
            have heq : n = (n - 57700) + 57700 := by omega
            rw [heq]
            exact cl_w4 ⟨n - 57700, hr⟩
          ·
            by_cases h5 : n < 57800
            ·
              have hr : n - 57750 < 50 := by omega
              have heq : n = (n - 57750) + 57750 := by omega
              rw [heq]
              exact cl_w5 ⟨n - 57750, hr⟩
            ·
              by_cases h6 : n < 57850
              ·
                have hr : n - 57800 < 50 := by omega
                have heq : n = (n - 57800) + 57800 := by omega
                rw [heq]
                exact cl_w6 ⟨n - 57800, hr⟩
              ·
                by_cases h7 : n < 57900
                ·
                  have hr : n - 57850 < 50 := by omega
                  have heq : n = (n - 57850) + 57850 := by omega
                  rw [heq]
                  exact cl_w7 ⟨n - 57850, hr⟩
                ·
                  by_cases h8 : n < 57950
                  ·
                    have hr : n - 57900 < 50 := by omega
                    have heq : n = (n - 57900) + 57900 := by omega
                    rw [heq]
                    exact cl_w8 ⟨n - 57900, hr⟩
                  ·
                    by_cases h9 : n < 58000
                    ·
                      have hr : n - 57950 < 50 := by omega
                      have heq : n = (n - 57950) + 57950 := by omega
                      rw [heq]
                      exact cl_w9 ⟨n - 57950, hr⟩
                    ·
                      by_cases h10 : n < 58050
                      ·
                        have hr : n - 58000 < 50 := by omega
                        have heq : n = (n - 58000) + 58000 := by omega
                        rw [heq]
                        exact cl_w10 ⟨n - 58000, hr⟩
                      ·
                        by_cases h11 : n < 58100
                        ·
                          have hr : n - 58050 < 50 := by omega
                          have heq : n = (n - 58050) + 58050 := by omega
                          rw [heq]
                          exact cl_w11 ⟨n - 58050, hr⟩
                        ·
                          by_cases h12 : n < 58150
                          ·
                            have hr : n - 58100 < 50 := by omega
                            have heq : n = (n - 58100) + 58100 := by omega
                            rw [heq]
                            exact cl_w12 ⟨n - 58100, hr⟩
                          ·
                            by_cases h13 : n < 58200
                            ·
                              have hr : n - 58150 < 50 := by omega
                              have heq : n = (n - 58150) + 58150 := by omega
                              rw [heq]
                              exact cl_w13 ⟨n - 58150, hr⟩
                            ·
                              by_cases h14 : n < 58250
                              ·
                                have hr : n - 58200 < 50 := by omega
                                have heq : n = (n - 58200) + 58200 := by omega
                                rw [heq]
                                exact cl_w14 ⟨n - 58200, hr⟩
                              ·
                                by_cases h15 : n < 58300
                                ·
                                  have hr : n - 58250 < 50 := by omega
                                  have heq : n = (n - 58250) + 58250 := by omega
                                  rw [heq]
                                  exact cl_w15 ⟨n - 58250, hr⟩
                                ·
                                  by_cases h16 : n < 58350
                                  ·
                                    have hr : n - 58300 < 50 := by omega
                                    have heq : n = (n - 58300) + 58300 := by omega
                                    rw [heq]
                                    exact cl_w16 ⟨n - 58300, hr⟩
                                  ·
                                    by_cases h17 : n < 58400
                                    ·
                                      have hr : n - 58350 < 50 := by omega
                                      have heq : n = (n - 58350) + 58350 := by omega
                                      rw [heq]
                                      exact cl_w17 ⟨n - 58350, hr⟩
                                    ·
                                      by_cases h18 : n < 58450
                                      ·
                                        have hr : n - 58400 < 50 := by omega
                                        have heq : n = (n - 58400) + 58400 := by omega
                                        rw [heq]
                                        exact cl_w18 ⟨n - 58400, hr⟩
                                      ·
                                        by_cases h19 : n < 58500
                                        ·
                                          have hr : n - 58450 < 50 := by omega
                                          have heq : n = (n - 58450) + 58450 := by omega
                                          rw [heq]
                                          exact cl_w19 ⟨n - 58450, hr⟩
                                        ·
                                          by_cases h20 : n < 58550
                                          ·
                                            have hr : n - 58500 < 50 := by omega
                                            have heq : n = (n - 58500) + 58500 := by omega
                                            rw [heq]
                                            exact cl_w20 ⟨n - 58500, hr⟩
                                          ·
                                            by_cases h21 : n < 58600
                                            ·
                                              have hr : n - 58550 < 50 := by omega
                                              have heq : n = (n - 58550) + 58550 := by omega
                                              rw [heq]
                                              exact cl_w21 ⟨n - 58550, hr⟩
                                            ·
                                              by_cases h22 : n < 58650
                                              ·
                                                have hr : n - 58600 < 50 := by omega
                                                have heq : n = (n - 58600) + 58600 := by omega
                                                rw [heq]
                                                exact cl_w22 ⟨n - 58600, hr⟩
                                              ·
                                                by_cases h23 : n < 58700
                                                ·
                                                  have hr : n - 58650 < 50 := by omega
                                                  have heq : n = (n - 58650) + 58650 := by omega
                                                  rw [heq]
                                                  exact cl_w23 ⟨n - 58650, hr⟩
                                                ·
                                                  by_cases h24 : n < 58750
                                                  ·
                                                    have hr : n - 58700 < 50 := by omega
                                                    have heq : n = (n - 58700) + 58700 := by omega
                                                    rw [heq]
                                                    exact cl_w24 ⟨n - 58700, hr⟩
                                                  ·
                                                    by_cases h25 : n < 58800
                                                    ·
                                                      have hr : n - 58750 < 50 := by omega
                                                      have heq : n = (n - 58750) + 58750 := by omega
                                                      rw [heq]
                                                      exact cl_w25 ⟨n - 58750, hr⟩
                                                    ·
                                                      by_cases h26 : n < 58850
                                                      ·
                                                        have hr : n - 58800 < 50 := by omega
                                                        have heq : n = (n - 58800) + 58800 := by omega
                                                        rw [heq]
                                                        exact cl_w26 ⟨n - 58800, hr⟩
                                                      ·
                                                        by_cases h27 : n < 58900
                                                        ·
                                                          have hr : n - 58850 < 50 := by omega
                                                          have heq : n = (n - 58850) + 58850 := by omega
                                                          rw [heq]
                                                          exact cl_w27 ⟨n - 58850, hr⟩
                                                        ·
                                                          by_cases h28 : n < 58950
                                                          ·
                                                            have hr : n - 58900 < 50 := by omega
                                                            have heq : n = (n - 58900) + 58900 := by omega
                                                            rw [heq]
                                                            exact cl_w28 ⟨n - 58900, hr⟩
                                                          ·
                                                            by_cases h29 : n < 59000
                                                            ·
                                                              have hr : n - 58950 < 50 := by omega
                                                              have heq : n = (n - 58950) + 58950 := by omega
                                                              rw [heq]
                                                              exact cl_w29 ⟨n - 58950, hr⟩
                                                            ·
                                                              by_cases h30 : n < 59050
                                                              ·
                                                                have hr : n - 59000 < 50 := by omega
                                                                have heq : n = (n - 59000) + 59000 := by omega
                                                                rw [heq]
                                                                exact cl_w30 ⟨n - 59000, hr⟩
                                                              ·
                                                                by_cases h31 : n < 59100
                                                                ·
                                                                  have hr : n - 59050 < 50 := by omega
                                                                  have heq : n = (n - 59050) + 59050 := by omega
                                                                  rw [heq]
                                                                  exact cl_w31 ⟨n - 59050, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 59150
                                                                  ·
                                                                    have hr : n - 59100 < 50 := by omega
                                                                    have heq : n = (n - 59100) + 59100 := by omega
                                                                    rw [heq]
                                                                    exact cl_w32 ⟨n - 59100, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 59200
                                                                    ·
                                                                      have hr : n - 59150 < 50 := by omega
                                                                      have heq : n = (n - 59150) + 59150 := by omega
                                                                      rw [heq]
                                                                      exact cl_w33 ⟨n - 59150, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 59250
                                                                      ·
                                                                        have hr : n - 59200 < 50 := by omega
                                                                        have heq : n = (n - 59200) + 59200 := by omega
                                                                        rw [heq]
                                                                        exact cl_w34 ⟨n - 59200, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 59300
                                                                        ·
                                                                          have hr : n - 59250 < 50 := by omega
                                                                          have heq : n = (n - 59250) + 59250 := by omega
                                                                          rw [heq]
                                                                          exact cl_w35 ⟨n - 59250, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 59350
                                                                          ·
                                                                            have hr : n - 59300 < 50 := by omega
                                                                            have heq : n = (n - 59300) + 59300 := by omega
                                                                            rw [heq]
                                                                            exact cl_w36 ⟨n - 59300, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 59400
                                                                            ·
                                                                              have hr : n - 59350 < 50 := by omega
                                                                              have heq : n = (n - 59350) + 59350 := by omega
                                                                              rw [heq]
                                                                              exact cl_w37 ⟨n - 59350, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 59450
                                                                              ·
                                                                                have hr : n - 59400 < 50 := by omega
                                                                                have heq : n = (n - 59400) + 59400 := by omega
                                                                                rw [heq]
                                                                                exact cl_w38 ⟨n - 59400, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 59500
                                                                                ·
                                                                                  have hr : n - 59450 < 50 := by omega
                                                                                  have heq : n = (n - 59450) + 59450 := by omega
                                                                                  rw [heq]
                                                                                  exact cl_w39 ⟨n - 59450, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 59550
                                                                                  ·
                                                                                    have hr : n - 59500 < 50 := by omega
                                                                                    have heq : n = (n - 59500) + 59500 := by omega
                                                                                    rw [heq]
                                                                                    exact cl_w40 ⟨n - 59500, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 59600
                                                                                    ·
                                                                                      have hr : n - 59550 < 50 := by omega
                                                                                      have heq : n = (n - 59550) + 59550 := by omega
                                                                                      rw [heq]
                                                                                      exact cl_w41 ⟨n - 59550, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 59650
                                                                                      ·
                                                                                        have hr : n - 59600 < 50 := by omega
                                                                                        have heq : n = (n - 59600) + 59600 := by omega
                                                                                        rw [heq]
                                                                                        exact cl_w42 ⟨n - 59600, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 59700
                                                                                        ·
                                                                                          have hr : n - 59650 < 50 := by omega
                                                                                          have heq : n = (n - 59650) + 59650 := by omega
                                                                                          rw [heq]
                                                                                          exact cl_w43 ⟨n - 59650, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 59750
                                                                                          ·
                                                                                            have hr : n - 59700 < 50 := by omega
                                                                                            have heq : n = (n - 59700) + 59700 := by omega
                                                                                            rw [heq]
                                                                                            exact cl_w44 ⟨n - 59700, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 59800
                                                                                            ·
                                                                                              have hr : n - 59750 < 50 := by omega
                                                                                              have heq : n = (n - 59750) + 59750 := by omega
                                                                                              rw [heq]
                                                                                              exact cl_w45 ⟨n - 59750, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 59850
                                                                                              ·
                                                                                                have hr : n - 59800 < 50 := by omega
                                                                                                have heq : n = (n - 59800) + 59800 := by omega
                                                                                                rw [heq]
                                                                                                exact cl_w46 ⟨n - 59800, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 59900
                                                                                                ·
                                                                                                  have hr : n - 59850 < 50 := by omega
                                                                                                  have heq : n = (n - 59850) + 59850 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cl_w47 ⟨n - 59850, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 59950
                                                                                                  ·
                                                                                                    have hr : n - 59900 < 50 := by omega
                                                                                                    have heq : n = (n - 59900) + 59900 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w48 ⟨n - 59900, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 59950 < 50 := by omega
                                                                                                    have heq : n = (n - 59950) + 59950 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w49 ⟨n - 59950, hr⟩


theorem densSupG_lt_range : ∀ n, 57500 ≤ n → n < 60000 → densSupG n < 2 ^ 1771 := by
  intro n hlo hhi
  by_cases h0 : n < 57550
  · have hr : n - 57500 < 50 := by omega
    have heq : n = (n - 57500) + 57500 := by omega
    rw [heq]
    exact bd_w0 ⟨n - 57500, hr⟩
  ·
    by_cases h1 : n < 57600
    ·
      have hr : n - 57550 < 50 := by omega
      have heq : n = (n - 57550) + 57550 := by omega
      rw [heq]
      exact bd_w1 ⟨n - 57550, hr⟩
    ·
      by_cases h2 : n < 57650
      ·
        have hr : n - 57600 < 50 := by omega
        have heq : n = (n - 57600) + 57600 := by omega
        rw [heq]
        exact bd_w2 ⟨n - 57600, hr⟩
      ·
        by_cases h3 : n < 57700
        ·
          have hr : n - 57650 < 50 := by omega
          have heq : n = (n - 57650) + 57650 := by omega
          rw [heq]
          exact bd_w3 ⟨n - 57650, hr⟩
        ·
          by_cases h4 : n < 57750
          ·
            have hr : n - 57700 < 50 := by omega
            have heq : n = (n - 57700) + 57700 := by omega
            rw [heq]
            exact bd_w4 ⟨n - 57700, hr⟩
          ·
            by_cases h5 : n < 57800
            ·
              have hr : n - 57750 < 50 := by omega
              have heq : n = (n - 57750) + 57750 := by omega
              rw [heq]
              exact bd_w5 ⟨n - 57750, hr⟩
            ·
              by_cases h6 : n < 57850
              ·
                have hr : n - 57800 < 50 := by omega
                have heq : n = (n - 57800) + 57800 := by omega
                rw [heq]
                exact bd_w6 ⟨n - 57800, hr⟩
              ·
                by_cases h7 : n < 57900
                ·
                  have hr : n - 57850 < 50 := by omega
                  have heq : n = (n - 57850) + 57850 := by omega
                  rw [heq]
                  exact bd_w7 ⟨n - 57850, hr⟩
                ·
                  by_cases h8 : n < 57950
                  ·
                    have hr : n - 57900 < 50 := by omega
                    have heq : n = (n - 57900) + 57900 := by omega
                    rw [heq]
                    exact bd_w8 ⟨n - 57900, hr⟩
                  ·
                    by_cases h9 : n < 58000
                    ·
                      have hr : n - 57950 < 50 := by omega
                      have heq : n = (n - 57950) + 57950 := by omega
                      rw [heq]
                      exact bd_w9 ⟨n - 57950, hr⟩
                    ·
                      by_cases h10 : n < 58050
                      ·
                        have hr : n - 58000 < 50 := by omega
                        have heq : n = (n - 58000) + 58000 := by omega
                        rw [heq]
                        exact bd_w10 ⟨n - 58000, hr⟩
                      ·
                        by_cases h11 : n < 58100
                        ·
                          have hr : n - 58050 < 50 := by omega
                          have heq : n = (n - 58050) + 58050 := by omega
                          rw [heq]
                          exact bd_w11 ⟨n - 58050, hr⟩
                        ·
                          by_cases h12 : n < 58150
                          ·
                            have hr : n - 58100 < 50 := by omega
                            have heq : n = (n - 58100) + 58100 := by omega
                            rw [heq]
                            exact bd_w12 ⟨n - 58100, hr⟩
                          ·
                            by_cases h13 : n < 58200
                            ·
                              have hr : n - 58150 < 50 := by omega
                              have heq : n = (n - 58150) + 58150 := by omega
                              rw [heq]
                              exact bd_w13 ⟨n - 58150, hr⟩
                            ·
                              by_cases h14 : n < 58250
                              ·
                                have hr : n - 58200 < 50 := by omega
                                have heq : n = (n - 58200) + 58200 := by omega
                                rw [heq]
                                exact bd_w14 ⟨n - 58200, hr⟩
                              ·
                                by_cases h15 : n < 58300
                                ·
                                  have hr : n - 58250 < 50 := by omega
                                  have heq : n = (n - 58250) + 58250 := by omega
                                  rw [heq]
                                  exact bd_w15 ⟨n - 58250, hr⟩
                                ·
                                  by_cases h16 : n < 58350
                                  ·
                                    have hr : n - 58300 < 50 := by omega
                                    have heq : n = (n - 58300) + 58300 := by omega
                                    rw [heq]
                                    exact bd_w16 ⟨n - 58300, hr⟩
                                  ·
                                    by_cases h17 : n < 58400
                                    ·
                                      have hr : n - 58350 < 50 := by omega
                                      have heq : n = (n - 58350) + 58350 := by omega
                                      rw [heq]
                                      exact bd_w17 ⟨n - 58350, hr⟩
                                    ·
                                      by_cases h18 : n < 58450
                                      ·
                                        have hr : n - 58400 < 50 := by omega
                                        have heq : n = (n - 58400) + 58400 := by omega
                                        rw [heq]
                                        exact bd_w18 ⟨n - 58400, hr⟩
                                      ·
                                        by_cases h19 : n < 58500
                                        ·
                                          have hr : n - 58450 < 50 := by omega
                                          have heq : n = (n - 58450) + 58450 := by omega
                                          rw [heq]
                                          exact bd_w19 ⟨n - 58450, hr⟩
                                        ·
                                          by_cases h20 : n < 58550
                                          ·
                                            have hr : n - 58500 < 50 := by omega
                                            have heq : n = (n - 58500) + 58500 := by omega
                                            rw [heq]
                                            exact bd_w20 ⟨n - 58500, hr⟩
                                          ·
                                            by_cases h21 : n < 58600
                                            ·
                                              have hr : n - 58550 < 50 := by omega
                                              have heq : n = (n - 58550) + 58550 := by omega
                                              rw [heq]
                                              exact bd_w21 ⟨n - 58550, hr⟩
                                            ·
                                              by_cases h22 : n < 58650
                                              ·
                                                have hr : n - 58600 < 50 := by omega
                                                have heq : n = (n - 58600) + 58600 := by omega
                                                rw [heq]
                                                exact bd_w22 ⟨n - 58600, hr⟩
                                              ·
                                                by_cases h23 : n < 58700
                                                ·
                                                  have hr : n - 58650 < 50 := by omega
                                                  have heq : n = (n - 58650) + 58650 := by omega
                                                  rw [heq]
                                                  exact bd_w23 ⟨n - 58650, hr⟩
                                                ·
                                                  by_cases h24 : n < 58750
                                                  ·
                                                    have hr : n - 58700 < 50 := by omega
                                                    have heq : n = (n - 58700) + 58700 := by omega
                                                    rw [heq]
                                                    exact bd_w24 ⟨n - 58700, hr⟩
                                                  ·
                                                    by_cases h25 : n < 58800
                                                    ·
                                                      have hr : n - 58750 < 50 := by omega
                                                      have heq : n = (n - 58750) + 58750 := by omega
                                                      rw [heq]
                                                      exact bd_w25 ⟨n - 58750, hr⟩
                                                    ·
                                                      by_cases h26 : n < 58850
                                                      ·
                                                        have hr : n - 58800 < 50 := by omega
                                                        have heq : n = (n - 58800) + 58800 := by omega
                                                        rw [heq]
                                                        exact bd_w26 ⟨n - 58800, hr⟩
                                                      ·
                                                        by_cases h27 : n < 58900
                                                        ·
                                                          have hr : n - 58850 < 50 := by omega
                                                          have heq : n = (n - 58850) + 58850 := by omega
                                                          rw [heq]
                                                          exact bd_w27 ⟨n - 58850, hr⟩
                                                        ·
                                                          by_cases h28 : n < 58950
                                                          ·
                                                            have hr : n - 58900 < 50 := by omega
                                                            have heq : n = (n - 58900) + 58900 := by omega
                                                            rw [heq]
                                                            exact bd_w28 ⟨n - 58900, hr⟩
                                                          ·
                                                            by_cases h29 : n < 59000
                                                            ·
                                                              have hr : n - 58950 < 50 := by omega
                                                              have heq : n = (n - 58950) + 58950 := by omega
                                                              rw [heq]
                                                              exact bd_w29 ⟨n - 58950, hr⟩
                                                            ·
                                                              by_cases h30 : n < 59050
                                                              ·
                                                                have hr : n - 59000 < 50 := by omega
                                                                have heq : n = (n - 59000) + 59000 := by omega
                                                                rw [heq]
                                                                exact bd_w30 ⟨n - 59000, hr⟩
                                                              ·
                                                                by_cases h31 : n < 59100
                                                                ·
                                                                  have hr : n - 59050 < 50 := by omega
                                                                  have heq : n = (n - 59050) + 59050 := by omega
                                                                  rw [heq]
                                                                  exact bd_w31 ⟨n - 59050, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 59150
                                                                  ·
                                                                    have hr : n - 59100 < 50 := by omega
                                                                    have heq : n = (n - 59100) + 59100 := by omega
                                                                    rw [heq]
                                                                    exact bd_w32 ⟨n - 59100, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 59200
                                                                    ·
                                                                      have hr : n - 59150 < 50 := by omega
                                                                      have heq : n = (n - 59150) + 59150 := by omega
                                                                      rw [heq]
                                                                      exact bd_w33 ⟨n - 59150, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 59250
                                                                      ·
                                                                        have hr : n - 59200 < 50 := by omega
                                                                        have heq : n = (n - 59200) + 59200 := by omega
                                                                        rw [heq]
                                                                        exact bd_w34 ⟨n - 59200, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 59300
                                                                        ·
                                                                          have hr : n - 59250 < 50 := by omega
                                                                          have heq : n = (n - 59250) + 59250 := by omega
                                                                          rw [heq]
                                                                          exact bd_w35 ⟨n - 59250, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 59350
                                                                          ·
                                                                            have hr : n - 59300 < 50 := by omega
                                                                            have heq : n = (n - 59300) + 59300 := by omega
                                                                            rw [heq]
                                                                            exact bd_w36 ⟨n - 59300, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 59400
                                                                            ·
                                                                              have hr : n - 59350 < 50 := by omega
                                                                              have heq : n = (n - 59350) + 59350 := by omega
                                                                              rw [heq]
                                                                              exact bd_w37 ⟨n - 59350, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 59450
                                                                              ·
                                                                                have hr : n - 59400 < 50 := by omega
                                                                                have heq : n = (n - 59400) + 59400 := by omega
                                                                                rw [heq]
                                                                                exact bd_w38 ⟨n - 59400, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 59500
                                                                                ·
                                                                                  have hr : n - 59450 < 50 := by omega
                                                                                  have heq : n = (n - 59450) + 59450 := by omega
                                                                                  rw [heq]
                                                                                  exact bd_w39 ⟨n - 59450, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 59550
                                                                                  ·
                                                                                    have hr : n - 59500 < 50 := by omega
                                                                                    have heq : n = (n - 59500) + 59500 := by omega
                                                                                    rw [heq]
                                                                                    exact bd_w40 ⟨n - 59500, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 59600
                                                                                    ·
                                                                                      have hr : n - 59550 < 50 := by omega
                                                                                      have heq : n = (n - 59550) + 59550 := by omega
                                                                                      rw [heq]
                                                                                      exact bd_w41 ⟨n - 59550, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 59650
                                                                                      ·
                                                                                        have hr : n - 59600 < 50 := by omega
                                                                                        have heq : n = (n - 59600) + 59600 := by omega
                                                                                        rw [heq]
                                                                                        exact bd_w42 ⟨n - 59600, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 59700
                                                                                        ·
                                                                                          have hr : n - 59650 < 50 := by omega
                                                                                          have heq : n = (n - 59650) + 59650 := by omega
                                                                                          rw [heq]
                                                                                          exact bd_w43 ⟨n - 59650, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 59750
                                                                                          ·
                                                                                            have hr : n - 59700 < 50 := by omega
                                                                                            have heq : n = (n - 59700) + 59700 := by omega
                                                                                            rw [heq]
                                                                                            exact bd_w44 ⟨n - 59700, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 59800
                                                                                            ·
                                                                                              have hr : n - 59750 < 50 := by omega
                                                                                              have heq : n = (n - 59750) + 59750 := by omega
                                                                                              rw [heq]
                                                                                              exact bd_w45 ⟨n - 59750, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 59850
                                                                                              ·
                                                                                                have hr : n - 59800 < 50 := by omega
                                                                                                have heq : n = (n - 59800) + 59800 := by omega
                                                                                                rw [heq]
                                                                                                exact bd_w46 ⟨n - 59800, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 59900
                                                                                                ·
                                                                                                  have hr : n - 59850 < 50 := by omega
                                                                                                  have heq : n = (n - 59850) + 59850 := by omega
                                                                                                  rw [heq]
                                                                                                  exact bd_w47 ⟨n - 59850, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 59950
                                                                                                  ·
                                                                                                    have hr : n - 59900 < 50 := by omega
                                                                                                    have heq : n = (n - 59900) + 59900 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w48 ⟨n - 59900, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 59950 < 50 := by omega
                                                                                                    have heq : n = (n - 59950) + 59950 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w49 ⟨n - 59950, hr⟩


end IntMul.Kappa.R8.Bit.Oppbank.CentBound11bFix


