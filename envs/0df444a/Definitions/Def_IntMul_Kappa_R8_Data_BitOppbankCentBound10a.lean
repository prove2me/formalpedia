-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound10a
-- name    : IntMul_Kappa_R8_Data_BitOppbankCentBound10a
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:12:57.283744+00:00
-- url     : https://prove2.me/theorems/85f85769-be8e-4052-8555-96643e87fa1d
-- title:
--   HasCentre certificates dens nodes [50000,52500)
-- statement:
--   # CentBound10a
--
--   centredStar/centF/densSupG for $50000\le n<52500$ via Fin50 decide (no native_decide).
-- source:
--   R8 BitOppbank AllDensCentred

-- CentBound pack 10a: densified HasCentre certificates on n ∈ [50000, 52500)
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

namespace IntMul.Kappa.R8.Bit.Oppbank.CentBound10a


private theorem cs_w0 : ∀ n : Fin 50, centredStar (densSupG (n.val + 50000)) (centF (n.val + 50000)) = true := by decide
private theorem cl_w0 : ∀ n : Fin 50, centF (n.val + 50000) < 23 := by decide
private theorem bd_w0 : ∀ n : Fin 50, densSupG (n.val + 50000) < 2 ^ 1771 := by decide
private theorem cs_w1 : ∀ n : Fin 50, centredStar (densSupG (n.val + 50050)) (centF (n.val + 50050)) = true := by decide
private theorem cl_w1 : ∀ n : Fin 50, centF (n.val + 50050) < 23 := by decide
private theorem bd_w1 : ∀ n : Fin 50, densSupG (n.val + 50050) < 2 ^ 1771 := by decide
private theorem cs_w2 : ∀ n : Fin 50, centredStar (densSupG (n.val + 50100)) (centF (n.val + 50100)) = true := by decide
private theorem cl_w2 : ∀ n : Fin 50, centF (n.val + 50100) < 23 := by decide
private theorem bd_w2 : ∀ n : Fin 50, densSupG (n.val + 50100) < 2 ^ 1771 := by decide
private theorem cs_w3 : ∀ n : Fin 50, centredStar (densSupG (n.val + 50150)) (centF (n.val + 50150)) = true := by decide
private theorem cl_w3 : ∀ n : Fin 50, centF (n.val + 50150) < 23 := by decide
private theorem bd_w3 : ∀ n : Fin 50, densSupG (n.val + 50150) < 2 ^ 1771 := by decide
private theorem cs_w4 : ∀ n : Fin 50, centredStar (densSupG (n.val + 50200)) (centF (n.val + 50200)) = true := by decide
private theorem cl_w4 : ∀ n : Fin 50, centF (n.val + 50200) < 23 := by decide
private theorem bd_w4 : ∀ n : Fin 50, densSupG (n.val + 50200) < 2 ^ 1771 := by decide
private theorem cs_w5 : ∀ n : Fin 50, centredStar (densSupG (n.val + 50250)) (centF (n.val + 50250)) = true := by decide
private theorem cl_w5 : ∀ n : Fin 50, centF (n.val + 50250) < 23 := by decide
private theorem bd_w5 : ∀ n : Fin 50, densSupG (n.val + 50250) < 2 ^ 1771 := by decide
private theorem cs_w6 : ∀ n : Fin 50, centredStar (densSupG (n.val + 50300)) (centF (n.val + 50300)) = true := by decide
private theorem cl_w6 : ∀ n : Fin 50, centF (n.val + 50300) < 23 := by decide
private theorem bd_w6 : ∀ n : Fin 50, densSupG (n.val + 50300) < 2 ^ 1771 := by decide
private theorem cs_w7 : ∀ n : Fin 50, centredStar (densSupG (n.val + 50350)) (centF (n.val + 50350)) = true := by decide
private theorem cl_w7 : ∀ n : Fin 50, centF (n.val + 50350) < 23 := by decide
private theorem bd_w7 : ∀ n : Fin 50, densSupG (n.val + 50350) < 2 ^ 1771 := by decide
private theorem cs_w8 : ∀ n : Fin 50, centredStar (densSupG (n.val + 50400)) (centF (n.val + 50400)) = true := by decide
private theorem cl_w8 : ∀ n : Fin 50, centF (n.val + 50400) < 23 := by decide
private theorem bd_w8 : ∀ n : Fin 50, densSupG (n.val + 50400) < 2 ^ 1771 := by decide
private theorem cs_w9 : ∀ n : Fin 50, centredStar (densSupG (n.val + 50450)) (centF (n.val + 50450)) = true := by decide
private theorem cl_w9 : ∀ n : Fin 50, centF (n.val + 50450) < 23 := by decide
private theorem bd_w9 : ∀ n : Fin 50, densSupG (n.val + 50450) < 2 ^ 1771 := by decide
private theorem cs_w10 : ∀ n : Fin 50, centredStar (densSupG (n.val + 50500)) (centF (n.val + 50500)) = true := by decide
private theorem cl_w10 : ∀ n : Fin 50, centF (n.val + 50500) < 23 := by decide
private theorem bd_w10 : ∀ n : Fin 50, densSupG (n.val + 50500) < 2 ^ 1771 := by decide
private theorem cs_w11 : ∀ n : Fin 50, centredStar (densSupG (n.val + 50550)) (centF (n.val + 50550)) = true := by decide
private theorem cl_w11 : ∀ n : Fin 50, centF (n.val + 50550) < 23 := by decide
private theorem bd_w11 : ∀ n : Fin 50, densSupG (n.val + 50550) < 2 ^ 1771 := by decide
private theorem cs_w12 : ∀ n : Fin 50, centredStar (densSupG (n.val + 50600)) (centF (n.val + 50600)) = true := by decide
private theorem cl_w12 : ∀ n : Fin 50, centF (n.val + 50600) < 23 := by decide
private theorem bd_w12 : ∀ n : Fin 50, densSupG (n.val + 50600) < 2 ^ 1771 := by decide
private theorem cs_w13 : ∀ n : Fin 50, centredStar (densSupG (n.val + 50650)) (centF (n.val + 50650)) = true := by decide
private theorem cl_w13 : ∀ n : Fin 50, centF (n.val + 50650) < 23 := by decide
private theorem bd_w13 : ∀ n : Fin 50, densSupG (n.val + 50650) < 2 ^ 1771 := by decide
private theorem cs_w14 : ∀ n : Fin 50, centredStar (densSupG (n.val + 50700)) (centF (n.val + 50700)) = true := by decide
private theorem cl_w14 : ∀ n : Fin 50, centF (n.val + 50700) < 23 := by decide
private theorem bd_w14 : ∀ n : Fin 50, densSupG (n.val + 50700) < 2 ^ 1771 := by decide
private theorem cs_w15 : ∀ n : Fin 50, centredStar (densSupG (n.val + 50750)) (centF (n.val + 50750)) = true := by decide
private theorem cl_w15 : ∀ n : Fin 50, centF (n.val + 50750) < 23 := by decide
private theorem bd_w15 : ∀ n : Fin 50, densSupG (n.val + 50750) < 2 ^ 1771 := by decide
private theorem cs_w16 : ∀ n : Fin 50, centredStar (densSupG (n.val + 50800)) (centF (n.val + 50800)) = true := by decide
private theorem cl_w16 : ∀ n : Fin 50, centF (n.val + 50800) < 23 := by decide
private theorem bd_w16 : ∀ n : Fin 50, densSupG (n.val + 50800) < 2 ^ 1771 := by decide
private theorem cs_w17 : ∀ n : Fin 50, centredStar (densSupG (n.val + 50850)) (centF (n.val + 50850)) = true := by decide
private theorem cl_w17 : ∀ n : Fin 50, centF (n.val + 50850) < 23 := by decide
private theorem bd_w17 : ∀ n : Fin 50, densSupG (n.val + 50850) < 2 ^ 1771 := by decide
private theorem cs_w18 : ∀ n : Fin 50, centredStar (densSupG (n.val + 50900)) (centF (n.val + 50900)) = true := by decide
private theorem cl_w18 : ∀ n : Fin 50, centF (n.val + 50900) < 23 := by decide
private theorem bd_w18 : ∀ n : Fin 50, densSupG (n.val + 50900) < 2 ^ 1771 := by decide
private theorem cs_w19 : ∀ n : Fin 50, centredStar (densSupG (n.val + 50950)) (centF (n.val + 50950)) = true := by decide
private theorem cl_w19 : ∀ n : Fin 50, centF (n.val + 50950) < 23 := by decide
private theorem bd_w19 : ∀ n : Fin 50, densSupG (n.val + 50950) < 2 ^ 1771 := by decide
private theorem cs_w20 : ∀ n : Fin 50, centredStar (densSupG (n.val + 51000)) (centF (n.val + 51000)) = true := by decide
private theorem cl_w20 : ∀ n : Fin 50, centF (n.val + 51000) < 23 := by decide
private theorem bd_w20 : ∀ n : Fin 50, densSupG (n.val + 51000) < 2 ^ 1771 := by decide
private theorem cs_w21 : ∀ n : Fin 50, centredStar (densSupG (n.val + 51050)) (centF (n.val + 51050)) = true := by decide
private theorem cl_w21 : ∀ n : Fin 50, centF (n.val + 51050) < 23 := by decide
private theorem bd_w21 : ∀ n : Fin 50, densSupG (n.val + 51050) < 2 ^ 1771 := by decide
private theorem cs_w22 : ∀ n : Fin 50, centredStar (densSupG (n.val + 51100)) (centF (n.val + 51100)) = true := by decide
private theorem cl_w22 : ∀ n : Fin 50, centF (n.val + 51100) < 23 := by decide
private theorem bd_w22 : ∀ n : Fin 50, densSupG (n.val + 51100) < 2 ^ 1771 := by decide
private theorem cs_w23 : ∀ n : Fin 50, centredStar (densSupG (n.val + 51150)) (centF (n.val + 51150)) = true := by decide
private theorem cl_w23 : ∀ n : Fin 50, centF (n.val + 51150) < 23 := by decide
private theorem bd_w23 : ∀ n : Fin 50, densSupG (n.val + 51150) < 2 ^ 1771 := by decide
private theorem cs_w24 : ∀ n : Fin 50, centredStar (densSupG (n.val + 51200)) (centF (n.val + 51200)) = true := by decide
private theorem cl_w24 : ∀ n : Fin 50, centF (n.val + 51200) < 23 := by decide
private theorem bd_w24 : ∀ n : Fin 50, densSupG (n.val + 51200) < 2 ^ 1771 := by decide
private theorem cs_w25 : ∀ n : Fin 50, centredStar (densSupG (n.val + 51250)) (centF (n.val + 51250)) = true := by decide
private theorem cl_w25 : ∀ n : Fin 50, centF (n.val + 51250) < 23 := by decide
private theorem bd_w25 : ∀ n : Fin 50, densSupG (n.val + 51250) < 2 ^ 1771 := by decide
private theorem cs_w26 : ∀ n : Fin 50, centredStar (densSupG (n.val + 51300)) (centF (n.val + 51300)) = true := by decide
private theorem cl_w26 : ∀ n : Fin 50, centF (n.val + 51300) < 23 := by decide
private theorem bd_w26 : ∀ n : Fin 50, densSupG (n.val + 51300) < 2 ^ 1771 := by decide
private theorem cs_w27 : ∀ n : Fin 50, centredStar (densSupG (n.val + 51350)) (centF (n.val + 51350)) = true := by decide
private theorem cl_w27 : ∀ n : Fin 50, centF (n.val + 51350) < 23 := by decide
private theorem bd_w27 : ∀ n : Fin 50, densSupG (n.val + 51350) < 2 ^ 1771 := by decide
private theorem cs_w28 : ∀ n : Fin 50, centredStar (densSupG (n.val + 51400)) (centF (n.val + 51400)) = true := by decide
private theorem cl_w28 : ∀ n : Fin 50, centF (n.val + 51400) < 23 := by decide
private theorem bd_w28 : ∀ n : Fin 50, densSupG (n.val + 51400) < 2 ^ 1771 := by decide
private theorem cs_w29 : ∀ n : Fin 50, centredStar (densSupG (n.val + 51450)) (centF (n.val + 51450)) = true := by decide
private theorem cl_w29 : ∀ n : Fin 50, centF (n.val + 51450) < 23 := by decide
private theorem bd_w29 : ∀ n : Fin 50, densSupG (n.val + 51450) < 2 ^ 1771 := by decide
private theorem cs_w30 : ∀ n : Fin 50, centredStar (densSupG (n.val + 51500)) (centF (n.val + 51500)) = true := by decide
private theorem cl_w30 : ∀ n : Fin 50, centF (n.val + 51500) < 23 := by decide
private theorem bd_w30 : ∀ n : Fin 50, densSupG (n.val + 51500) < 2 ^ 1771 := by decide
private theorem cs_w31 : ∀ n : Fin 50, centredStar (densSupG (n.val + 51550)) (centF (n.val + 51550)) = true := by decide
private theorem cl_w31 : ∀ n : Fin 50, centF (n.val + 51550) < 23 := by decide
private theorem bd_w31 : ∀ n : Fin 50, densSupG (n.val + 51550) < 2 ^ 1771 := by decide
private theorem cs_w32 : ∀ n : Fin 50, centredStar (densSupG (n.val + 51600)) (centF (n.val + 51600)) = true := by decide
private theorem cl_w32 : ∀ n : Fin 50, centF (n.val + 51600) < 23 := by decide
private theorem bd_w32 : ∀ n : Fin 50, densSupG (n.val + 51600) < 2 ^ 1771 := by decide
private theorem cs_w33 : ∀ n : Fin 50, centredStar (densSupG (n.val + 51650)) (centF (n.val + 51650)) = true := by decide
private theorem cl_w33 : ∀ n : Fin 50, centF (n.val + 51650) < 23 := by decide
private theorem bd_w33 : ∀ n : Fin 50, densSupG (n.val + 51650) < 2 ^ 1771 := by decide
private theorem cs_w34 : ∀ n : Fin 50, centredStar (densSupG (n.val + 51700)) (centF (n.val + 51700)) = true := by decide
private theorem cl_w34 : ∀ n : Fin 50, centF (n.val + 51700) < 23 := by decide
private theorem bd_w34 : ∀ n : Fin 50, densSupG (n.val + 51700) < 2 ^ 1771 := by decide
private theorem cs_w35 : ∀ n : Fin 50, centredStar (densSupG (n.val + 51750)) (centF (n.val + 51750)) = true := by decide
private theorem cl_w35 : ∀ n : Fin 50, centF (n.val + 51750) < 23 := by decide
private theorem bd_w35 : ∀ n : Fin 50, densSupG (n.val + 51750) < 2 ^ 1771 := by decide
private theorem cs_w36 : ∀ n : Fin 50, centredStar (densSupG (n.val + 51800)) (centF (n.val + 51800)) = true := by decide
private theorem cl_w36 : ∀ n : Fin 50, centF (n.val + 51800) < 23 := by decide
private theorem bd_w36 : ∀ n : Fin 50, densSupG (n.val + 51800) < 2 ^ 1771 := by decide
private theorem cs_w37 : ∀ n : Fin 50, centredStar (densSupG (n.val + 51850)) (centF (n.val + 51850)) = true := by decide
private theorem cl_w37 : ∀ n : Fin 50, centF (n.val + 51850) < 23 := by decide
private theorem bd_w37 : ∀ n : Fin 50, densSupG (n.val + 51850) < 2 ^ 1771 := by decide
private theorem cs_w38 : ∀ n : Fin 50, centredStar (densSupG (n.val + 51900)) (centF (n.val + 51900)) = true := by decide
private theorem cl_w38 : ∀ n : Fin 50, centF (n.val + 51900) < 23 := by decide
private theorem bd_w38 : ∀ n : Fin 50, densSupG (n.val + 51900) < 2 ^ 1771 := by decide
private theorem cs_w39 : ∀ n : Fin 50, centredStar (densSupG (n.val + 51950)) (centF (n.val + 51950)) = true := by decide
private theorem cl_w39 : ∀ n : Fin 50, centF (n.val + 51950) < 23 := by decide
private theorem bd_w39 : ∀ n : Fin 50, densSupG (n.val + 51950) < 2 ^ 1771 := by decide
private theorem cs_w40 : ∀ n : Fin 50, centredStar (densSupG (n.val + 52000)) (centF (n.val + 52000)) = true := by decide
private theorem cl_w40 : ∀ n : Fin 50, centF (n.val + 52000) < 23 := by decide
private theorem bd_w40 : ∀ n : Fin 50, densSupG (n.val + 52000) < 2 ^ 1771 := by decide
private theorem cs_w41 : ∀ n : Fin 50, centredStar (densSupG (n.val + 52050)) (centF (n.val + 52050)) = true := by decide
private theorem cl_w41 : ∀ n : Fin 50, centF (n.val + 52050) < 23 := by decide
private theorem bd_w41 : ∀ n : Fin 50, densSupG (n.val + 52050) < 2 ^ 1771 := by decide
private theorem cs_w42 : ∀ n : Fin 50, centredStar (densSupG (n.val + 52100)) (centF (n.val + 52100)) = true := by decide
private theorem cl_w42 : ∀ n : Fin 50, centF (n.val + 52100) < 23 := by decide
private theorem bd_w42 : ∀ n : Fin 50, densSupG (n.val + 52100) < 2 ^ 1771 := by decide
private theorem cs_w43 : ∀ n : Fin 50, centredStar (densSupG (n.val + 52150)) (centF (n.val + 52150)) = true := by decide
private theorem cl_w43 : ∀ n : Fin 50, centF (n.val + 52150) < 23 := by decide
private theorem bd_w43 : ∀ n : Fin 50, densSupG (n.val + 52150) < 2 ^ 1771 := by decide
private theorem cs_w44 : ∀ n : Fin 50, centredStar (densSupG (n.val + 52200)) (centF (n.val + 52200)) = true := by decide
private theorem cl_w44 : ∀ n : Fin 50, centF (n.val + 52200) < 23 := by decide
private theorem bd_w44 : ∀ n : Fin 50, densSupG (n.val + 52200) < 2 ^ 1771 := by decide
private theorem cs_w45 : ∀ n : Fin 50, centredStar (densSupG (n.val + 52250)) (centF (n.val + 52250)) = true := by decide
private theorem cl_w45 : ∀ n : Fin 50, centF (n.val + 52250) < 23 := by decide
private theorem bd_w45 : ∀ n : Fin 50, densSupG (n.val + 52250) < 2 ^ 1771 := by decide
private theorem cs_w46 : ∀ n : Fin 50, centredStar (densSupG (n.val + 52300)) (centF (n.val + 52300)) = true := by decide
private theorem cl_w46 : ∀ n : Fin 50, centF (n.val + 52300) < 23 := by decide
private theorem bd_w46 : ∀ n : Fin 50, densSupG (n.val + 52300) < 2 ^ 1771 := by decide
private theorem cs_w47 : ∀ n : Fin 50, centredStar (densSupG (n.val + 52350)) (centF (n.val + 52350)) = true := by decide
private theorem cl_w47 : ∀ n : Fin 50, centF (n.val + 52350) < 23 := by decide
private theorem bd_w47 : ∀ n : Fin 50, densSupG (n.val + 52350) < 2 ^ 1771 := by decide
private theorem cs_w48 : ∀ n : Fin 50, centredStar (densSupG (n.val + 52400)) (centF (n.val + 52400)) = true := by decide
private theorem cl_w48 : ∀ n : Fin 50, centF (n.val + 52400) < 23 := by decide
private theorem bd_w48 : ∀ n : Fin 50, densSupG (n.val + 52400) < 2 ^ 1771 := by decide
private theorem cs_w49 : ∀ n : Fin 50, centredStar (densSupG (n.val + 52450)) (centF (n.val + 52450)) = true := by decide
private theorem cl_w49 : ∀ n : Fin 50, centF (n.val + 52450) < 23 := by decide
private theorem bd_w49 : ∀ n : Fin 50, densSupG (n.val + 52450) < 2 ^ 1771 := by decide
theorem centredStar_range : ∀ n, 50000 ≤ n → n < 52500 → centredStar (densSupG n) (centF n) = true := by
  intro n hlo hhi
  by_cases h0 : n < 50050
  · have hr : n - 50000 < 50 := by omega
    have heq : n = (n - 50000) + 50000 := by omega
    rw [heq]
    exact cs_w0 ⟨n - 50000, hr⟩
  ·
    by_cases h1 : n < 50100
    ·
      have hr : n - 50050 < 50 := by omega
      have heq : n = (n - 50050) + 50050 := by omega
      rw [heq]
      exact cs_w1 ⟨n - 50050, hr⟩
    ·
      by_cases h2 : n < 50150
      ·
        have hr : n - 50100 < 50 := by omega
        have heq : n = (n - 50100) + 50100 := by omega
        rw [heq]
        exact cs_w2 ⟨n - 50100, hr⟩
      ·
        by_cases h3 : n < 50200
        ·
          have hr : n - 50150 < 50 := by omega
          have heq : n = (n - 50150) + 50150 := by omega
          rw [heq]
          exact cs_w3 ⟨n - 50150, hr⟩
        ·
          by_cases h4 : n < 50250
          ·
            have hr : n - 50200 < 50 := by omega
            have heq : n = (n - 50200) + 50200 := by omega
            rw [heq]
            exact cs_w4 ⟨n - 50200, hr⟩
          ·
            by_cases h5 : n < 50300
            ·
              have hr : n - 50250 < 50 := by omega
              have heq : n = (n - 50250) + 50250 := by omega
              rw [heq]
              exact cs_w5 ⟨n - 50250, hr⟩
            ·
              by_cases h6 : n < 50350
              ·
                have hr : n - 50300 < 50 := by omega
                have heq : n = (n - 50300) + 50300 := by omega
                rw [heq]
                exact cs_w6 ⟨n - 50300, hr⟩
              ·
                by_cases h7 : n < 50400
                ·
                  have hr : n - 50350 < 50 := by omega
                  have heq : n = (n - 50350) + 50350 := by omega
                  rw [heq]
                  exact cs_w7 ⟨n - 50350, hr⟩
                ·
                  by_cases h8 : n < 50450
                  ·
                    have hr : n - 50400 < 50 := by omega
                    have heq : n = (n - 50400) + 50400 := by omega
                    rw [heq]
                    exact cs_w8 ⟨n - 50400, hr⟩
                  ·
                    by_cases h9 : n < 50500
                    ·
                      have hr : n - 50450 < 50 := by omega
                      have heq : n = (n - 50450) + 50450 := by omega
                      rw [heq]
                      exact cs_w9 ⟨n - 50450, hr⟩
                    ·
                      by_cases h10 : n < 50550
                      ·
                        have hr : n - 50500 < 50 := by omega
                        have heq : n = (n - 50500) + 50500 := by omega
                        rw [heq]
                        exact cs_w10 ⟨n - 50500, hr⟩
                      ·
                        by_cases h11 : n < 50600
                        ·
                          have hr : n - 50550 < 50 := by omega
                          have heq : n = (n - 50550) + 50550 := by omega
                          rw [heq]
                          exact cs_w11 ⟨n - 50550, hr⟩
                        ·
                          by_cases h12 : n < 50650
                          ·
                            have hr : n - 50600 < 50 := by omega
                            have heq : n = (n - 50600) + 50600 := by omega
                            rw [heq]
                            exact cs_w12 ⟨n - 50600, hr⟩
                          ·
                            by_cases h13 : n < 50700
                            ·
                              have hr : n - 50650 < 50 := by omega
                              have heq : n = (n - 50650) + 50650 := by omega
                              rw [heq]
                              exact cs_w13 ⟨n - 50650, hr⟩
                            ·
                              by_cases h14 : n < 50750
                              ·
                                have hr : n - 50700 < 50 := by omega
                                have heq : n = (n - 50700) + 50700 := by omega
                                rw [heq]
                                exact cs_w14 ⟨n - 50700, hr⟩
                              ·
                                by_cases h15 : n < 50800
                                ·
                                  have hr : n - 50750 < 50 := by omega
                                  have heq : n = (n - 50750) + 50750 := by omega
                                  rw [heq]
                                  exact cs_w15 ⟨n - 50750, hr⟩
                                ·
                                  by_cases h16 : n < 50850
                                  ·
                                    have hr : n - 50800 < 50 := by omega
                                    have heq : n = (n - 50800) + 50800 := by omega
                                    rw [heq]
                                    exact cs_w16 ⟨n - 50800, hr⟩
                                  ·
                                    by_cases h17 : n < 50900
                                    ·
                                      have hr : n - 50850 < 50 := by omega
                                      have heq : n = (n - 50850) + 50850 := by omega
                                      rw [heq]
                                      exact cs_w17 ⟨n - 50850, hr⟩
                                    ·
                                      by_cases h18 : n < 50950
                                      ·
                                        have hr : n - 50900 < 50 := by omega
                                        have heq : n = (n - 50900) + 50900 := by omega
                                        rw [heq]
                                        exact cs_w18 ⟨n - 50900, hr⟩
                                      ·
                                        by_cases h19 : n < 51000
                                        ·
                                          have hr : n - 50950 < 50 := by omega
                                          have heq : n = (n - 50950) + 50950 := by omega
                                          rw [heq]
                                          exact cs_w19 ⟨n - 50950, hr⟩
                                        ·
                                          by_cases h20 : n < 51050
                                          ·
                                            have hr : n - 51000 < 50 := by omega
                                            have heq : n = (n - 51000) + 51000 := by omega
                                            rw [heq]
                                            exact cs_w20 ⟨n - 51000, hr⟩
                                          ·
                                            by_cases h21 : n < 51100
                                            ·
                                              have hr : n - 51050 < 50 := by omega
                                              have heq : n = (n - 51050) + 51050 := by omega
                                              rw [heq]
                                              exact cs_w21 ⟨n - 51050, hr⟩
                                            ·
                                              by_cases h22 : n < 51150
                                              ·
                                                have hr : n - 51100 < 50 := by omega
                                                have heq : n = (n - 51100) + 51100 := by omega
                                                rw [heq]
                                                exact cs_w22 ⟨n - 51100, hr⟩
                                              ·
                                                by_cases h23 : n < 51200
                                                ·
                                                  have hr : n - 51150 < 50 := by omega
                                                  have heq : n = (n - 51150) + 51150 := by omega
                                                  rw [heq]
                                                  exact cs_w23 ⟨n - 51150, hr⟩
                                                ·
                                                  by_cases h24 : n < 51250
                                                  ·
                                                    have hr : n - 51200 < 50 := by omega
                                                    have heq : n = (n - 51200) + 51200 := by omega
                                                    rw [heq]
                                                    exact cs_w24 ⟨n - 51200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 51300
                                                    ·
                                                      have hr : n - 51250 < 50 := by omega
                                                      have heq : n = (n - 51250) + 51250 := by omega
                                                      rw [heq]
                                                      exact cs_w25 ⟨n - 51250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 51350
                                                      ·
                                                        have hr : n - 51300 < 50 := by omega
                                                        have heq : n = (n - 51300) + 51300 := by omega
                                                        rw [heq]
                                                        exact cs_w26 ⟨n - 51300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 51400
                                                        ·
                                                          have hr : n - 51350 < 50 := by omega
                                                          have heq : n = (n - 51350) + 51350 := by omega
                                                          rw [heq]
                                                          exact cs_w27 ⟨n - 51350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 51450
                                                          ·
                                                            have hr : n - 51400 < 50 := by omega
                                                            have heq : n = (n - 51400) + 51400 := by omega
                                                            rw [heq]
                                                            exact cs_w28 ⟨n - 51400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 51500
                                                            ·
                                                              have hr : n - 51450 < 50 := by omega
                                                              have heq : n = (n - 51450) + 51450 := by omega
                                                              rw [heq]
                                                              exact cs_w29 ⟨n - 51450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 51550
                                                              ·
                                                                have hr : n - 51500 < 50 := by omega
                                                                have heq : n = (n - 51500) + 51500 := by omega
                                                                rw [heq]
                                                                exact cs_w30 ⟨n - 51500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 51600
                                                                ·
                                                                  have hr : n - 51550 < 50 := by omega
                                                                  have heq : n = (n - 51550) + 51550 := by omega
                                                                  rw [heq]
                                                                  exact cs_w31 ⟨n - 51550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 51650
                                                                  ·
                                                                    have hr : n - 51600 < 50 := by omega
                                                                    have heq : n = (n - 51600) + 51600 := by omega
                                                                    rw [heq]
                                                                    exact cs_w32 ⟨n - 51600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 51700
                                                                    ·
                                                                      have hr : n - 51650 < 50 := by omega
                                                                      have heq : n = (n - 51650) + 51650 := by omega
                                                                      rw [heq]
                                                                      exact cs_w33 ⟨n - 51650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 51750
                                                                      ·
                                                                        have hr : n - 51700 < 50 := by omega
                                                                        have heq : n = (n - 51700) + 51700 := by omega
                                                                        rw [heq]
                                                                        exact cs_w34 ⟨n - 51700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 51800
                                                                        ·
                                                                          have hr : n - 51750 < 50 := by omega
                                                                          have heq : n = (n - 51750) + 51750 := by omega
                                                                          rw [heq]
                                                                          exact cs_w35 ⟨n - 51750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 51850
                                                                          ·
                                                                            have hr : n - 51800 < 50 := by omega
                                                                            have heq : n = (n - 51800) + 51800 := by omega
                                                                            rw [heq]
                                                                            exact cs_w36 ⟨n - 51800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 51900
                                                                            ·
                                                                              have hr : n - 51850 < 50 := by omega
                                                                              have heq : n = (n - 51850) + 51850 := by omega
                                                                              rw [heq]
                                                                              exact cs_w37 ⟨n - 51850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 51950
                                                                              ·
                                                                                have hr : n - 51900 < 50 := by omega
                                                                                have heq : n = (n - 51900) + 51900 := by omega
                                                                                rw [heq]
                                                                                exact cs_w38 ⟨n - 51900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 52000
                                                                                ·
                                                                                  have hr : n - 51950 < 50 := by omega
                                                                                  have heq : n = (n - 51950) + 51950 := by omega
                                                                                  rw [heq]
                                                                                  exact cs_w39 ⟨n - 51950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 52050
                                                                                  ·
                                                                                    have hr : n - 52000 < 50 := by omega
                                                                                    have heq : n = (n - 52000) + 52000 := by omega
                                                                                    rw [heq]
                                                                                    exact cs_w40 ⟨n - 52000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 52100
                                                                                    ·
                                                                                      have hr : n - 52050 < 50 := by omega
                                                                                      have heq : n = (n - 52050) + 52050 := by omega
                                                                                      rw [heq]
                                                                                      exact cs_w41 ⟨n - 52050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 52150
                                                                                      ·
                                                                                        have hr : n - 52100 < 50 := by omega
                                                                                        have heq : n = (n - 52100) + 52100 := by omega
                                                                                        rw [heq]
                                                                                        exact cs_w42 ⟨n - 52100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 52200
                                                                                        ·
                                                                                          have hr : n - 52150 < 50 := by omega
                                                                                          have heq : n = (n - 52150) + 52150 := by omega
                                                                                          rw [heq]
                                                                                          exact cs_w43 ⟨n - 52150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 52250
                                                                                          ·
                                                                                            have hr : n - 52200 < 50 := by omega
                                                                                            have heq : n = (n - 52200) + 52200 := by omega
                                                                                            rw [heq]
                                                                                            exact cs_w44 ⟨n - 52200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 52300
                                                                                            ·
                                                                                              have hr : n - 52250 < 50 := by omega
                                                                                              have heq : n = (n - 52250) + 52250 := by omega
                                                                                              rw [heq]
                                                                                              exact cs_w45 ⟨n - 52250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 52350
                                                                                              ·
                                                                                                have hr : n - 52300 < 50 := by omega
                                                                                                have heq : n = (n - 52300) + 52300 := by omega
                                                                                                rw [heq]
                                                                                                exact cs_w46 ⟨n - 52300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 52400
                                                                                                ·
                                                                                                  have hr : n - 52350 < 50 := by omega
                                                                                                  have heq : n = (n - 52350) + 52350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cs_w47 ⟨n - 52350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 52450
                                                                                                  ·
                                                                                                    have hr : n - 52400 < 50 := by omega
                                                                                                    have heq : n = (n - 52400) + 52400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w48 ⟨n - 52400, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 52450 < 50 := by omega
                                                                                                    have heq : n = (n - 52450) + 52450 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w49 ⟨n - 52450, hr⟩


theorem centF_lt_range : ∀ n, 50000 ≤ n → n < 52500 → centF n < 23 := by
  intro n hlo hhi
  by_cases h0 : n < 50050
  · have hr : n - 50000 < 50 := by omega
    have heq : n = (n - 50000) + 50000 := by omega
    rw [heq]
    exact cl_w0 ⟨n - 50000, hr⟩
  ·
    by_cases h1 : n < 50100
    ·
      have hr : n - 50050 < 50 := by omega
      have heq : n = (n - 50050) + 50050 := by omega
      rw [heq]
      exact cl_w1 ⟨n - 50050, hr⟩
    ·
      by_cases h2 : n < 50150
      ·
        have hr : n - 50100 < 50 := by omega
        have heq : n = (n - 50100) + 50100 := by omega
        rw [heq]
        exact cl_w2 ⟨n - 50100, hr⟩
      ·
        by_cases h3 : n < 50200
        ·
          have hr : n - 50150 < 50 := by omega
          have heq : n = (n - 50150) + 50150 := by omega
          rw [heq]
          exact cl_w3 ⟨n - 50150, hr⟩
        ·
          by_cases h4 : n < 50250
          ·
            have hr : n - 50200 < 50 := by omega
            have heq : n = (n - 50200) + 50200 := by omega
            rw [heq]
            exact cl_w4 ⟨n - 50200, hr⟩
          ·
            by_cases h5 : n < 50300
            ·
              have hr : n - 50250 < 50 := by omega
              have heq : n = (n - 50250) + 50250 := by omega
              rw [heq]
              exact cl_w5 ⟨n - 50250, hr⟩
            ·
              by_cases h6 : n < 50350
              ·
                have hr : n - 50300 < 50 := by omega
                have heq : n = (n - 50300) + 50300 := by omega
                rw [heq]
                exact cl_w6 ⟨n - 50300, hr⟩
              ·
                by_cases h7 : n < 50400
                ·
                  have hr : n - 50350 < 50 := by omega
                  have heq : n = (n - 50350) + 50350 := by omega
                  rw [heq]
                  exact cl_w7 ⟨n - 50350, hr⟩
                ·
                  by_cases h8 : n < 50450
                  ·
                    have hr : n - 50400 < 50 := by omega
                    have heq : n = (n - 50400) + 50400 := by omega
                    rw [heq]
                    exact cl_w8 ⟨n - 50400, hr⟩
                  ·
                    by_cases h9 : n < 50500
                    ·
                      have hr : n - 50450 < 50 := by omega
                      have heq : n = (n - 50450) + 50450 := by omega
                      rw [heq]
                      exact cl_w9 ⟨n - 50450, hr⟩
                    ·
                      by_cases h10 : n < 50550
                      ·
                        have hr : n - 50500 < 50 := by omega
                        have heq : n = (n - 50500) + 50500 := by omega
                        rw [heq]
                        exact cl_w10 ⟨n - 50500, hr⟩
                      ·
                        by_cases h11 : n < 50600
                        ·
                          have hr : n - 50550 < 50 := by omega
                          have heq : n = (n - 50550) + 50550 := by omega
                          rw [heq]
                          exact cl_w11 ⟨n - 50550, hr⟩
                        ·
                          by_cases h12 : n < 50650
                          ·
                            have hr : n - 50600 < 50 := by omega
                            have heq : n = (n - 50600) + 50600 := by omega
                            rw [heq]
                            exact cl_w12 ⟨n - 50600, hr⟩
                          ·
                            by_cases h13 : n < 50700
                            ·
                              have hr : n - 50650 < 50 := by omega
                              have heq : n = (n - 50650) + 50650 := by omega
                              rw [heq]
                              exact cl_w13 ⟨n - 50650, hr⟩
                            ·
                              by_cases h14 : n < 50750
                              ·
                                have hr : n - 50700 < 50 := by omega
                                have heq : n = (n - 50700) + 50700 := by omega
                                rw [heq]
                                exact cl_w14 ⟨n - 50700, hr⟩
                              ·
                                by_cases h15 : n < 50800
                                ·
                                  have hr : n - 50750 < 50 := by omega
                                  have heq : n = (n - 50750) + 50750 := by omega
                                  rw [heq]
                                  exact cl_w15 ⟨n - 50750, hr⟩
                                ·
                                  by_cases h16 : n < 50850
                                  ·
                                    have hr : n - 50800 < 50 := by omega
                                    have heq : n = (n - 50800) + 50800 := by omega
                                    rw [heq]
                                    exact cl_w16 ⟨n - 50800, hr⟩
                                  ·
                                    by_cases h17 : n < 50900
                                    ·
                                      have hr : n - 50850 < 50 := by omega
                                      have heq : n = (n - 50850) + 50850 := by omega
                                      rw [heq]
                                      exact cl_w17 ⟨n - 50850, hr⟩
                                    ·
                                      by_cases h18 : n < 50950
                                      ·
                                        have hr : n - 50900 < 50 := by omega
                                        have heq : n = (n - 50900) + 50900 := by omega
                                        rw [heq]
                                        exact cl_w18 ⟨n - 50900, hr⟩
                                      ·
                                        by_cases h19 : n < 51000
                                        ·
                                          have hr : n - 50950 < 50 := by omega
                                          have heq : n = (n - 50950) + 50950 := by omega
                                          rw [heq]
                                          exact cl_w19 ⟨n - 50950, hr⟩
                                        ·
                                          by_cases h20 : n < 51050
                                          ·
                                            have hr : n - 51000 < 50 := by omega
                                            have heq : n = (n - 51000) + 51000 := by omega
                                            rw [heq]
                                            exact cl_w20 ⟨n - 51000, hr⟩
                                          ·
                                            by_cases h21 : n < 51100
                                            ·
                                              have hr : n - 51050 < 50 := by omega
                                              have heq : n = (n - 51050) + 51050 := by omega
                                              rw [heq]
                                              exact cl_w21 ⟨n - 51050, hr⟩
                                            ·
                                              by_cases h22 : n < 51150
                                              ·
                                                have hr : n - 51100 < 50 := by omega
                                                have heq : n = (n - 51100) + 51100 := by omega
                                                rw [heq]
                                                exact cl_w22 ⟨n - 51100, hr⟩
                                              ·
                                                by_cases h23 : n < 51200
                                                ·
                                                  have hr : n - 51150 < 50 := by omega
                                                  have heq : n = (n - 51150) + 51150 := by omega
                                                  rw [heq]
                                                  exact cl_w23 ⟨n - 51150, hr⟩
                                                ·
                                                  by_cases h24 : n < 51250
                                                  ·
                                                    have hr : n - 51200 < 50 := by omega
                                                    have heq : n = (n - 51200) + 51200 := by omega
                                                    rw [heq]
                                                    exact cl_w24 ⟨n - 51200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 51300
                                                    ·
                                                      have hr : n - 51250 < 50 := by omega
                                                      have heq : n = (n - 51250) + 51250 := by omega
                                                      rw [heq]
                                                      exact cl_w25 ⟨n - 51250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 51350
                                                      ·
                                                        have hr : n - 51300 < 50 := by omega
                                                        have heq : n = (n - 51300) + 51300 := by omega
                                                        rw [heq]
                                                        exact cl_w26 ⟨n - 51300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 51400
                                                        ·
                                                          have hr : n - 51350 < 50 := by omega
                                                          have heq : n = (n - 51350) + 51350 := by omega
                                                          rw [heq]
                                                          exact cl_w27 ⟨n - 51350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 51450
                                                          ·
                                                            have hr : n - 51400 < 50 := by omega
                                                            have heq : n = (n - 51400) + 51400 := by omega
                                                            rw [heq]
                                                            exact cl_w28 ⟨n - 51400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 51500
                                                            ·
                                                              have hr : n - 51450 < 50 := by omega
                                                              have heq : n = (n - 51450) + 51450 := by omega
                                                              rw [heq]
                                                              exact cl_w29 ⟨n - 51450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 51550
                                                              ·
                                                                have hr : n - 51500 < 50 := by omega
                                                                have heq : n = (n - 51500) + 51500 := by omega
                                                                rw [heq]
                                                                exact cl_w30 ⟨n - 51500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 51600
                                                                ·
                                                                  have hr : n - 51550 < 50 := by omega
                                                                  have heq : n = (n - 51550) + 51550 := by omega
                                                                  rw [heq]
                                                                  exact cl_w31 ⟨n - 51550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 51650
                                                                  ·
                                                                    have hr : n - 51600 < 50 := by omega
                                                                    have heq : n = (n - 51600) + 51600 := by omega
                                                                    rw [heq]
                                                                    exact cl_w32 ⟨n - 51600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 51700
                                                                    ·
                                                                      have hr : n - 51650 < 50 := by omega
                                                                      have heq : n = (n - 51650) + 51650 := by omega
                                                                      rw [heq]
                                                                      exact cl_w33 ⟨n - 51650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 51750
                                                                      ·
                                                                        have hr : n - 51700 < 50 := by omega
                                                                        have heq : n = (n - 51700) + 51700 := by omega
                                                                        rw [heq]
                                                                        exact cl_w34 ⟨n - 51700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 51800
                                                                        ·
                                                                          have hr : n - 51750 < 50 := by omega
                                                                          have heq : n = (n - 51750) + 51750 := by omega
                                                                          rw [heq]
                                                                          exact cl_w35 ⟨n - 51750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 51850
                                                                          ·
                                                                            have hr : n - 51800 < 50 := by omega
                                                                            have heq : n = (n - 51800) + 51800 := by omega
                                                                            rw [heq]
                                                                            exact cl_w36 ⟨n - 51800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 51900
                                                                            ·
                                                                              have hr : n - 51850 < 50 := by omega
                                                                              have heq : n = (n - 51850) + 51850 := by omega
                                                                              rw [heq]
                                                                              exact cl_w37 ⟨n - 51850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 51950
                                                                              ·
                                                                                have hr : n - 51900 < 50 := by omega
                                                                                have heq : n = (n - 51900) + 51900 := by omega
                                                                                rw [heq]
                                                                                exact cl_w38 ⟨n - 51900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 52000
                                                                                ·
                                                                                  have hr : n - 51950 < 50 := by omega
                                                                                  have heq : n = (n - 51950) + 51950 := by omega
                                                                                  rw [heq]
                                                                                  exact cl_w39 ⟨n - 51950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 52050
                                                                                  ·
                                                                                    have hr : n - 52000 < 50 := by omega
                                                                                    have heq : n = (n - 52000) + 52000 := by omega
                                                                                    rw [heq]
                                                                                    exact cl_w40 ⟨n - 52000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 52100
                                                                                    ·
                                                                                      have hr : n - 52050 < 50 := by omega
                                                                                      have heq : n = (n - 52050) + 52050 := by omega
                                                                                      rw [heq]
                                                                                      exact cl_w41 ⟨n - 52050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 52150
                                                                                      ·
                                                                                        have hr : n - 52100 < 50 := by omega
                                                                                        have heq : n = (n - 52100) + 52100 := by omega
                                                                                        rw [heq]
                                                                                        exact cl_w42 ⟨n - 52100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 52200
                                                                                        ·
                                                                                          have hr : n - 52150 < 50 := by omega
                                                                                          have heq : n = (n - 52150) + 52150 := by omega
                                                                                          rw [heq]
                                                                                          exact cl_w43 ⟨n - 52150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 52250
                                                                                          ·
                                                                                            have hr : n - 52200 < 50 := by omega
                                                                                            have heq : n = (n - 52200) + 52200 := by omega
                                                                                            rw [heq]
                                                                                            exact cl_w44 ⟨n - 52200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 52300
                                                                                            ·
                                                                                              have hr : n - 52250 < 50 := by omega
                                                                                              have heq : n = (n - 52250) + 52250 := by omega
                                                                                              rw [heq]
                                                                                              exact cl_w45 ⟨n - 52250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 52350
                                                                                              ·
                                                                                                have hr : n - 52300 < 50 := by omega
                                                                                                have heq : n = (n - 52300) + 52300 := by omega
                                                                                                rw [heq]
                                                                                                exact cl_w46 ⟨n - 52300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 52400
                                                                                                ·
                                                                                                  have hr : n - 52350 < 50 := by omega
                                                                                                  have heq : n = (n - 52350) + 52350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cl_w47 ⟨n - 52350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 52450
                                                                                                  ·
                                                                                                    have hr : n - 52400 < 50 := by omega
                                                                                                    have heq : n = (n - 52400) + 52400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w48 ⟨n - 52400, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 52450 < 50 := by omega
                                                                                                    have heq : n = (n - 52450) + 52450 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w49 ⟨n - 52450, hr⟩


theorem densSupG_lt_range : ∀ n, 50000 ≤ n → n < 52500 → densSupG n < 2 ^ 1771 := by
  intro n hlo hhi
  by_cases h0 : n < 50050
  · have hr : n - 50000 < 50 := by omega
    have heq : n = (n - 50000) + 50000 := by omega
    rw [heq]
    exact bd_w0 ⟨n - 50000, hr⟩
  ·
    by_cases h1 : n < 50100
    ·
      have hr : n - 50050 < 50 := by omega
      have heq : n = (n - 50050) + 50050 := by omega
      rw [heq]
      exact bd_w1 ⟨n - 50050, hr⟩
    ·
      by_cases h2 : n < 50150
      ·
        have hr : n - 50100 < 50 := by omega
        have heq : n = (n - 50100) + 50100 := by omega
        rw [heq]
        exact bd_w2 ⟨n - 50100, hr⟩
      ·
        by_cases h3 : n < 50200
        ·
          have hr : n - 50150 < 50 := by omega
          have heq : n = (n - 50150) + 50150 := by omega
          rw [heq]
          exact bd_w3 ⟨n - 50150, hr⟩
        ·
          by_cases h4 : n < 50250
          ·
            have hr : n - 50200 < 50 := by omega
            have heq : n = (n - 50200) + 50200 := by omega
            rw [heq]
            exact bd_w4 ⟨n - 50200, hr⟩
          ·
            by_cases h5 : n < 50300
            ·
              have hr : n - 50250 < 50 := by omega
              have heq : n = (n - 50250) + 50250 := by omega
              rw [heq]
              exact bd_w5 ⟨n - 50250, hr⟩
            ·
              by_cases h6 : n < 50350
              ·
                have hr : n - 50300 < 50 := by omega
                have heq : n = (n - 50300) + 50300 := by omega
                rw [heq]
                exact bd_w6 ⟨n - 50300, hr⟩
              ·
                by_cases h7 : n < 50400
                ·
                  have hr : n - 50350 < 50 := by omega
                  have heq : n = (n - 50350) + 50350 := by omega
                  rw [heq]
                  exact bd_w7 ⟨n - 50350, hr⟩
                ·
                  by_cases h8 : n < 50450
                  ·
                    have hr : n - 50400 < 50 := by omega
                    have heq : n = (n - 50400) + 50400 := by omega
                    rw [heq]
                    exact bd_w8 ⟨n - 50400, hr⟩
                  ·
                    by_cases h9 : n < 50500
                    ·
                      have hr : n - 50450 < 50 := by omega
                      have heq : n = (n - 50450) + 50450 := by omega
                      rw [heq]
                      exact bd_w9 ⟨n - 50450, hr⟩
                    ·
                      by_cases h10 : n < 50550
                      ·
                        have hr : n - 50500 < 50 := by omega
                        have heq : n = (n - 50500) + 50500 := by omega
                        rw [heq]
                        exact bd_w10 ⟨n - 50500, hr⟩
                      ·
                        by_cases h11 : n < 50600
                        ·
                          have hr : n - 50550 < 50 := by omega
                          have heq : n = (n - 50550) + 50550 := by omega
                          rw [heq]
                          exact bd_w11 ⟨n - 50550, hr⟩
                        ·
                          by_cases h12 : n < 50650
                          ·
                            have hr : n - 50600 < 50 := by omega
                            have heq : n = (n - 50600) + 50600 := by omega
                            rw [heq]
                            exact bd_w12 ⟨n - 50600, hr⟩
                          ·
                            by_cases h13 : n < 50700
                            ·
                              have hr : n - 50650 < 50 := by omega
                              have heq : n = (n - 50650) + 50650 := by omega
                              rw [heq]
                              exact bd_w13 ⟨n - 50650, hr⟩
                            ·
                              by_cases h14 : n < 50750
                              ·
                                have hr : n - 50700 < 50 := by omega
                                have heq : n = (n - 50700) + 50700 := by omega
                                rw [heq]
                                exact bd_w14 ⟨n - 50700, hr⟩
                              ·
                                by_cases h15 : n < 50800
                                ·
                                  have hr : n - 50750 < 50 := by omega
                                  have heq : n = (n - 50750) + 50750 := by omega
                                  rw [heq]
                                  exact bd_w15 ⟨n - 50750, hr⟩
                                ·
                                  by_cases h16 : n < 50850
                                  ·
                                    have hr : n - 50800 < 50 := by omega
                                    have heq : n = (n - 50800) + 50800 := by omega
                                    rw [heq]
                                    exact bd_w16 ⟨n - 50800, hr⟩
                                  ·
                                    by_cases h17 : n < 50900
                                    ·
                                      have hr : n - 50850 < 50 := by omega
                                      have heq : n = (n - 50850) + 50850 := by omega
                                      rw [heq]
                                      exact bd_w17 ⟨n - 50850, hr⟩
                                    ·
                                      by_cases h18 : n < 50950
                                      ·
                                        have hr : n - 50900 < 50 := by omega
                                        have heq : n = (n - 50900) + 50900 := by omega
                                        rw [heq]
                                        exact bd_w18 ⟨n - 50900, hr⟩
                                      ·
                                        by_cases h19 : n < 51000
                                        ·
                                          have hr : n - 50950 < 50 := by omega
                                          have heq : n = (n - 50950) + 50950 := by omega
                                          rw [heq]
                                          exact bd_w19 ⟨n - 50950, hr⟩
                                        ·
                                          by_cases h20 : n < 51050
                                          ·
                                            have hr : n - 51000 < 50 := by omega
                                            have heq : n = (n - 51000) + 51000 := by omega
                                            rw [heq]
                                            exact bd_w20 ⟨n - 51000, hr⟩
                                          ·
                                            by_cases h21 : n < 51100
                                            ·
                                              have hr : n - 51050 < 50 := by omega
                                              have heq : n = (n - 51050) + 51050 := by omega
                                              rw [heq]
                                              exact bd_w21 ⟨n - 51050, hr⟩
                                            ·
                                              by_cases h22 : n < 51150
                                              ·
                                                have hr : n - 51100 < 50 := by omega
                                                have heq : n = (n - 51100) + 51100 := by omega
                                                rw [heq]
                                                exact bd_w22 ⟨n - 51100, hr⟩
                                              ·
                                                by_cases h23 : n < 51200
                                                ·
                                                  have hr : n - 51150 < 50 := by omega
                                                  have heq : n = (n - 51150) + 51150 := by omega
                                                  rw [heq]
                                                  exact bd_w23 ⟨n - 51150, hr⟩
                                                ·
                                                  by_cases h24 : n < 51250
                                                  ·
                                                    have hr : n - 51200 < 50 := by omega
                                                    have heq : n = (n - 51200) + 51200 := by omega
                                                    rw [heq]
                                                    exact bd_w24 ⟨n - 51200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 51300
                                                    ·
                                                      have hr : n - 51250 < 50 := by omega
                                                      have heq : n = (n - 51250) + 51250 := by omega
                                                      rw [heq]
                                                      exact bd_w25 ⟨n - 51250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 51350
                                                      ·
                                                        have hr : n - 51300 < 50 := by omega
                                                        have heq : n = (n - 51300) + 51300 := by omega
                                                        rw [heq]
                                                        exact bd_w26 ⟨n - 51300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 51400
                                                        ·
                                                          have hr : n - 51350 < 50 := by omega
                                                          have heq : n = (n - 51350) + 51350 := by omega
                                                          rw [heq]
                                                          exact bd_w27 ⟨n - 51350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 51450
                                                          ·
                                                            have hr : n - 51400 < 50 := by omega
                                                            have heq : n = (n - 51400) + 51400 := by omega
                                                            rw [heq]
                                                            exact bd_w28 ⟨n - 51400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 51500
                                                            ·
                                                              have hr : n - 51450 < 50 := by omega
                                                              have heq : n = (n - 51450) + 51450 := by omega
                                                              rw [heq]
                                                              exact bd_w29 ⟨n - 51450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 51550
                                                              ·
                                                                have hr : n - 51500 < 50 := by omega
                                                                have heq : n = (n - 51500) + 51500 := by omega
                                                                rw [heq]
                                                                exact bd_w30 ⟨n - 51500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 51600
                                                                ·
                                                                  have hr : n - 51550 < 50 := by omega
                                                                  have heq : n = (n - 51550) + 51550 := by omega
                                                                  rw [heq]
                                                                  exact bd_w31 ⟨n - 51550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 51650
                                                                  ·
                                                                    have hr : n - 51600 < 50 := by omega
                                                                    have heq : n = (n - 51600) + 51600 := by omega
                                                                    rw [heq]
                                                                    exact bd_w32 ⟨n - 51600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 51700
                                                                    ·
                                                                      have hr : n - 51650 < 50 := by omega
                                                                      have heq : n = (n - 51650) + 51650 := by omega
                                                                      rw [heq]
                                                                      exact bd_w33 ⟨n - 51650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 51750
                                                                      ·
                                                                        have hr : n - 51700 < 50 := by omega
                                                                        have heq : n = (n - 51700) + 51700 := by omega
                                                                        rw [heq]
                                                                        exact bd_w34 ⟨n - 51700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 51800
                                                                        ·
                                                                          have hr : n - 51750 < 50 := by omega
                                                                          have heq : n = (n - 51750) + 51750 := by omega
                                                                          rw [heq]
                                                                          exact bd_w35 ⟨n - 51750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 51850
                                                                          ·
                                                                            have hr : n - 51800 < 50 := by omega
                                                                            have heq : n = (n - 51800) + 51800 := by omega
                                                                            rw [heq]
                                                                            exact bd_w36 ⟨n - 51800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 51900
                                                                            ·
                                                                              have hr : n - 51850 < 50 := by omega
                                                                              have heq : n = (n - 51850) + 51850 := by omega
                                                                              rw [heq]
                                                                              exact bd_w37 ⟨n - 51850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 51950
                                                                              ·
                                                                                have hr : n - 51900 < 50 := by omega
                                                                                have heq : n = (n - 51900) + 51900 := by omega
                                                                                rw [heq]
                                                                                exact bd_w38 ⟨n - 51900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 52000
                                                                                ·
                                                                                  have hr : n - 51950 < 50 := by omega
                                                                                  have heq : n = (n - 51950) + 51950 := by omega
                                                                                  rw [heq]
                                                                                  exact bd_w39 ⟨n - 51950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 52050
                                                                                  ·
                                                                                    have hr : n - 52000 < 50 := by omega
                                                                                    have heq : n = (n - 52000) + 52000 := by omega
                                                                                    rw [heq]
                                                                                    exact bd_w40 ⟨n - 52000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 52100
                                                                                    ·
                                                                                      have hr : n - 52050 < 50 := by omega
                                                                                      have heq : n = (n - 52050) + 52050 := by omega
                                                                                      rw [heq]
                                                                                      exact bd_w41 ⟨n - 52050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 52150
                                                                                      ·
                                                                                        have hr : n - 52100 < 50 := by omega
                                                                                        have heq : n = (n - 52100) + 52100 := by omega
                                                                                        rw [heq]
                                                                                        exact bd_w42 ⟨n - 52100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 52200
                                                                                        ·
                                                                                          have hr : n - 52150 < 50 := by omega
                                                                                          have heq : n = (n - 52150) + 52150 := by omega
                                                                                          rw [heq]
                                                                                          exact bd_w43 ⟨n - 52150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 52250
                                                                                          ·
                                                                                            have hr : n - 52200 < 50 := by omega
                                                                                            have heq : n = (n - 52200) + 52200 := by omega
                                                                                            rw [heq]
                                                                                            exact bd_w44 ⟨n - 52200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 52300
                                                                                            ·
                                                                                              have hr : n - 52250 < 50 := by omega
                                                                                              have heq : n = (n - 52250) + 52250 := by omega
                                                                                              rw [heq]
                                                                                              exact bd_w45 ⟨n - 52250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 52350
                                                                                              ·
                                                                                                have hr : n - 52300 < 50 := by omega
                                                                                                have heq : n = (n - 52300) + 52300 := by omega
                                                                                                rw [heq]
                                                                                                exact bd_w46 ⟨n - 52300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 52400
                                                                                                ·
                                                                                                  have hr : n - 52350 < 50 := by omega
                                                                                                  have heq : n = (n - 52350) + 52350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact bd_w47 ⟨n - 52350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 52450
                                                                                                  ·
                                                                                                    have hr : n - 52400 < 50 := by omega
                                                                                                    have heq : n = (n - 52400) + 52400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w48 ⟨n - 52400, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 52450 < 50 := by omega
                                                                                                    have heq : n = (n - 52450) + 52450 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w49 ⟨n - 52450, hr⟩


end IntMul.Kappa.R8.Bit.Oppbank.CentBound10a


