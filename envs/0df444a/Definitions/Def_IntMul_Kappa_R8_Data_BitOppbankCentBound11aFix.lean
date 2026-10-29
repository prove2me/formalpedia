-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound11aFix
-- name    : IntMul_Kappa_R8_Data_BitOppbankCentBound11aFix
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T22:21:08.925291+00:00
-- url     : https://prove2.me/theorems/d665d07d-9d54-47ee-a452-8a21dd026da2
-- title:
--   IntMul Kappa R8 Data BitOppbankCentBound11aFix
-- statement:
--   Densified HasCentre support certificates (IntMul_Kappa_R8_Data_BitOppbankCentBound11aFix) retargeted to PndFix/CentFix.

-- CentBound11aFix: PndFix retarget
-- CentBound pack 11a: densified HasCentre certificates on n ∈ [55000, 57500)
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

namespace IntMul.Kappa.R8.Bit.Oppbank.CentBound11aFix


private theorem cs_w0 : ∀ n : Fin 50, centredStar (densSupG (n.val + 55000)) (centF (n.val + 55000)) = true := by decide
private theorem cl_w0 : ∀ n : Fin 50, centF (n.val + 55000) < 23 := by decide
private theorem bd_w0 : ∀ n : Fin 50, densSupG (n.val + 55000) < 2 ^ 1771 := by decide
private theorem cs_w1 : ∀ n : Fin 50, centredStar (densSupG (n.val + 55050)) (centF (n.val + 55050)) = true := by decide
private theorem cl_w1 : ∀ n : Fin 50, centF (n.val + 55050) < 23 := by decide
private theorem bd_w1 : ∀ n : Fin 50, densSupG (n.val + 55050) < 2 ^ 1771 := by decide
private theorem cs_w2 : ∀ n : Fin 50, centredStar (densSupG (n.val + 55100)) (centF (n.val + 55100)) = true := by decide
private theorem cl_w2 : ∀ n : Fin 50, centF (n.val + 55100) < 23 := by decide
private theorem bd_w2 : ∀ n : Fin 50, densSupG (n.val + 55100) < 2 ^ 1771 := by decide
private theorem cs_w3 : ∀ n : Fin 50, centredStar (densSupG (n.val + 55150)) (centF (n.val + 55150)) = true := by decide
private theorem cl_w3 : ∀ n : Fin 50, centF (n.val + 55150) < 23 := by decide
private theorem bd_w3 : ∀ n : Fin 50, densSupG (n.val + 55150) < 2 ^ 1771 := by decide
private theorem cs_w4 : ∀ n : Fin 50, centredStar (densSupG (n.val + 55200)) (centF (n.val + 55200)) = true := by decide
private theorem cl_w4 : ∀ n : Fin 50, centF (n.val + 55200) < 23 := by decide
private theorem bd_w4 : ∀ n : Fin 50, densSupG (n.val + 55200) < 2 ^ 1771 := by decide
private theorem cs_w5 : ∀ n : Fin 50, centredStar (densSupG (n.val + 55250)) (centF (n.val + 55250)) = true := by decide
private theorem cl_w5 : ∀ n : Fin 50, centF (n.val + 55250) < 23 := by decide
private theorem bd_w5 : ∀ n : Fin 50, densSupG (n.val + 55250) < 2 ^ 1771 := by decide
private theorem cs_w6 : ∀ n : Fin 50, centredStar (densSupG (n.val + 55300)) (centF (n.val + 55300)) = true := by decide
private theorem cl_w6 : ∀ n : Fin 50, centF (n.val + 55300) < 23 := by decide
private theorem bd_w6 : ∀ n : Fin 50, densSupG (n.val + 55300) < 2 ^ 1771 := by decide
private theorem cs_w7 : ∀ n : Fin 50, centredStar (densSupG (n.val + 55350)) (centF (n.val + 55350)) = true := by decide
private theorem cl_w7 : ∀ n : Fin 50, centF (n.val + 55350) < 23 := by decide
private theorem bd_w7 : ∀ n : Fin 50, densSupG (n.val + 55350) < 2 ^ 1771 := by decide
private theorem cs_w8 : ∀ n : Fin 50, centredStar (densSupG (n.val + 55400)) (centF (n.val + 55400)) = true := by decide
private theorem cl_w8 : ∀ n : Fin 50, centF (n.val + 55400) < 23 := by decide
private theorem bd_w8 : ∀ n : Fin 50, densSupG (n.val + 55400) < 2 ^ 1771 := by decide
private theorem cs_w9 : ∀ n : Fin 50, centredStar (densSupG (n.val + 55450)) (centF (n.val + 55450)) = true := by decide
private theorem cl_w9 : ∀ n : Fin 50, centF (n.val + 55450) < 23 := by decide
private theorem bd_w9 : ∀ n : Fin 50, densSupG (n.val + 55450) < 2 ^ 1771 := by decide
private theorem cs_w10 : ∀ n : Fin 50, centredStar (densSupG (n.val + 55500)) (centF (n.val + 55500)) = true := by decide
private theorem cl_w10 : ∀ n : Fin 50, centF (n.val + 55500) < 23 := by decide
private theorem bd_w10 : ∀ n : Fin 50, densSupG (n.val + 55500) < 2 ^ 1771 := by decide
private theorem cs_w11 : ∀ n : Fin 50, centredStar (densSupG (n.val + 55550)) (centF (n.val + 55550)) = true := by decide
private theorem cl_w11 : ∀ n : Fin 50, centF (n.val + 55550) < 23 := by decide
private theorem bd_w11 : ∀ n : Fin 50, densSupG (n.val + 55550) < 2 ^ 1771 := by decide
private theorem cs_w12 : ∀ n : Fin 50, centredStar (densSupG (n.val + 55600)) (centF (n.val + 55600)) = true := by decide
private theorem cl_w12 : ∀ n : Fin 50, centF (n.val + 55600) < 23 := by decide
private theorem bd_w12 : ∀ n : Fin 50, densSupG (n.val + 55600) < 2 ^ 1771 := by decide
private theorem cs_w13 : ∀ n : Fin 50, centredStar (densSupG (n.val + 55650)) (centF (n.val + 55650)) = true := by decide
private theorem cl_w13 : ∀ n : Fin 50, centF (n.val + 55650) < 23 := by decide
private theorem bd_w13 : ∀ n : Fin 50, densSupG (n.val + 55650) < 2 ^ 1771 := by decide
private theorem cs_w14 : ∀ n : Fin 50, centredStar (densSupG (n.val + 55700)) (centF (n.val + 55700)) = true := by decide
private theorem cl_w14 : ∀ n : Fin 50, centF (n.val + 55700) < 23 := by decide
private theorem bd_w14 : ∀ n : Fin 50, densSupG (n.val + 55700) < 2 ^ 1771 := by decide
private theorem cs_w15 : ∀ n : Fin 50, centredStar (densSupG (n.val + 55750)) (centF (n.val + 55750)) = true := by decide
private theorem cl_w15 : ∀ n : Fin 50, centF (n.val + 55750) < 23 := by decide
private theorem bd_w15 : ∀ n : Fin 50, densSupG (n.val + 55750) < 2 ^ 1771 := by decide
private theorem cs_w16 : ∀ n : Fin 50, centredStar (densSupG (n.val + 55800)) (centF (n.val + 55800)) = true := by decide
private theorem cl_w16 : ∀ n : Fin 50, centF (n.val + 55800) < 23 := by decide
private theorem bd_w16 : ∀ n : Fin 50, densSupG (n.val + 55800) < 2 ^ 1771 := by decide
private theorem cs_w17 : ∀ n : Fin 50, centredStar (densSupG (n.val + 55850)) (centF (n.val + 55850)) = true := by decide
private theorem cl_w17 : ∀ n : Fin 50, centF (n.val + 55850) < 23 := by decide
private theorem bd_w17 : ∀ n : Fin 50, densSupG (n.val + 55850) < 2 ^ 1771 := by decide
private theorem cs_w18 : ∀ n : Fin 50, centredStar (densSupG (n.val + 55900)) (centF (n.val + 55900)) = true := by decide
private theorem cl_w18 : ∀ n : Fin 50, centF (n.val + 55900) < 23 := by decide
private theorem bd_w18 : ∀ n : Fin 50, densSupG (n.val + 55900) < 2 ^ 1771 := by decide
private theorem cs_w19 : ∀ n : Fin 50, centredStar (densSupG (n.val + 55950)) (centF (n.val + 55950)) = true := by decide
private theorem cl_w19 : ∀ n : Fin 50, centF (n.val + 55950) < 23 := by decide
private theorem bd_w19 : ∀ n : Fin 50, densSupG (n.val + 55950) < 2 ^ 1771 := by decide
private theorem cs_w20 : ∀ n : Fin 50, centredStar (densSupG (n.val + 56000)) (centF (n.val + 56000)) = true := by decide
private theorem cl_w20 : ∀ n : Fin 50, centF (n.val + 56000) < 23 := by decide
private theorem bd_w20 : ∀ n : Fin 50, densSupG (n.val + 56000) < 2 ^ 1771 := by decide
private theorem cs_w21 : ∀ n : Fin 50, centredStar (densSupG (n.val + 56050)) (centF (n.val + 56050)) = true := by decide
private theorem cl_w21 : ∀ n : Fin 50, centF (n.val + 56050) < 23 := by decide
private theorem bd_w21 : ∀ n : Fin 50, densSupG (n.val + 56050) < 2 ^ 1771 := by decide
private theorem cs_w22 : ∀ n : Fin 50, centredStar (densSupG (n.val + 56100)) (centF (n.val + 56100)) = true := by decide
private theorem cl_w22 : ∀ n : Fin 50, centF (n.val + 56100) < 23 := by decide
private theorem bd_w22 : ∀ n : Fin 50, densSupG (n.val + 56100) < 2 ^ 1771 := by decide
private theorem cs_w23 : ∀ n : Fin 50, centredStar (densSupG (n.val + 56150)) (centF (n.val + 56150)) = true := by decide
private theorem cl_w23 : ∀ n : Fin 50, centF (n.val + 56150) < 23 := by decide
private theorem bd_w23 : ∀ n : Fin 50, densSupG (n.val + 56150) < 2 ^ 1771 := by decide
private theorem cs_w24 : ∀ n : Fin 50, centredStar (densSupG (n.val + 56200)) (centF (n.val + 56200)) = true := by decide
private theorem cl_w24 : ∀ n : Fin 50, centF (n.val + 56200) < 23 := by decide
private theorem bd_w24 : ∀ n : Fin 50, densSupG (n.val + 56200) < 2 ^ 1771 := by decide
private theorem cs_w25 : ∀ n : Fin 50, centredStar (densSupG (n.val + 56250)) (centF (n.val + 56250)) = true := by decide
private theorem cl_w25 : ∀ n : Fin 50, centF (n.val + 56250) < 23 := by decide
private theorem bd_w25 : ∀ n : Fin 50, densSupG (n.val + 56250) < 2 ^ 1771 := by decide
private theorem cs_w26 : ∀ n : Fin 50, centredStar (densSupG (n.val + 56300)) (centF (n.val + 56300)) = true := by decide
private theorem cl_w26 : ∀ n : Fin 50, centF (n.val + 56300) < 23 := by decide
private theorem bd_w26 : ∀ n : Fin 50, densSupG (n.val + 56300) < 2 ^ 1771 := by decide
private theorem cs_w27 : ∀ n : Fin 50, centredStar (densSupG (n.val + 56350)) (centF (n.val + 56350)) = true := by decide
private theorem cl_w27 : ∀ n : Fin 50, centF (n.val + 56350) < 23 := by decide
private theorem bd_w27 : ∀ n : Fin 50, densSupG (n.val + 56350) < 2 ^ 1771 := by decide
private theorem cs_w28 : ∀ n : Fin 50, centredStar (densSupG (n.val + 56400)) (centF (n.val + 56400)) = true := by decide
private theorem cl_w28 : ∀ n : Fin 50, centF (n.val + 56400) < 23 := by decide
private theorem bd_w28 : ∀ n : Fin 50, densSupG (n.val + 56400) < 2 ^ 1771 := by decide
private theorem cs_w29 : ∀ n : Fin 50, centredStar (densSupG (n.val + 56450)) (centF (n.val + 56450)) = true := by decide
private theorem cl_w29 : ∀ n : Fin 50, centF (n.val + 56450) < 23 := by decide
private theorem bd_w29 : ∀ n : Fin 50, densSupG (n.val + 56450) < 2 ^ 1771 := by decide
private theorem cs_w30 : ∀ n : Fin 50, centredStar (densSupG (n.val + 56500)) (centF (n.val + 56500)) = true := by decide
private theorem cl_w30 : ∀ n : Fin 50, centF (n.val + 56500) < 23 := by decide
private theorem bd_w30 : ∀ n : Fin 50, densSupG (n.val + 56500) < 2 ^ 1771 := by decide
private theorem cs_w31 : ∀ n : Fin 50, centredStar (densSupG (n.val + 56550)) (centF (n.val + 56550)) = true := by decide
private theorem cl_w31 : ∀ n : Fin 50, centF (n.val + 56550) < 23 := by decide
private theorem bd_w31 : ∀ n : Fin 50, densSupG (n.val + 56550) < 2 ^ 1771 := by decide
private theorem cs_w32 : ∀ n : Fin 50, centredStar (densSupG (n.val + 56600)) (centF (n.val + 56600)) = true := by decide
private theorem cl_w32 : ∀ n : Fin 50, centF (n.val + 56600) < 23 := by decide
private theorem bd_w32 : ∀ n : Fin 50, densSupG (n.val + 56600) < 2 ^ 1771 := by decide
private theorem cs_w33 : ∀ n : Fin 50, centredStar (densSupG (n.val + 56650)) (centF (n.val + 56650)) = true := by decide
private theorem cl_w33 : ∀ n : Fin 50, centF (n.val + 56650) < 23 := by decide
private theorem bd_w33 : ∀ n : Fin 50, densSupG (n.val + 56650) < 2 ^ 1771 := by decide
private theorem cs_w34 : ∀ n : Fin 50, centredStar (densSupG (n.val + 56700)) (centF (n.val + 56700)) = true := by decide
private theorem cl_w34 : ∀ n : Fin 50, centF (n.val + 56700) < 23 := by decide
private theorem bd_w34 : ∀ n : Fin 50, densSupG (n.val + 56700) < 2 ^ 1771 := by decide
private theorem cs_w35 : ∀ n : Fin 50, centredStar (densSupG (n.val + 56750)) (centF (n.val + 56750)) = true := by decide
private theorem cl_w35 : ∀ n : Fin 50, centF (n.val + 56750) < 23 := by decide
private theorem bd_w35 : ∀ n : Fin 50, densSupG (n.val + 56750) < 2 ^ 1771 := by decide
private theorem cs_w36 : ∀ n : Fin 50, centredStar (densSupG (n.val + 56800)) (centF (n.val + 56800)) = true := by decide
private theorem cl_w36 : ∀ n : Fin 50, centF (n.val + 56800) < 23 := by decide
private theorem bd_w36 : ∀ n : Fin 50, densSupG (n.val + 56800) < 2 ^ 1771 := by decide
private theorem cs_w37 : ∀ n : Fin 50, centredStar (densSupG (n.val + 56850)) (centF (n.val + 56850)) = true := by decide
private theorem cl_w37 : ∀ n : Fin 50, centF (n.val + 56850) < 23 := by decide
private theorem bd_w37 : ∀ n : Fin 50, densSupG (n.val + 56850) < 2 ^ 1771 := by decide
private theorem cs_w38 : ∀ n : Fin 50, centredStar (densSupG (n.val + 56900)) (centF (n.val + 56900)) = true := by decide
private theorem cl_w38 : ∀ n : Fin 50, centF (n.val + 56900) < 23 := by decide
private theorem bd_w38 : ∀ n : Fin 50, densSupG (n.val + 56900) < 2 ^ 1771 := by decide
private theorem cs_w39 : ∀ n : Fin 50, centredStar (densSupG (n.val + 56950)) (centF (n.val + 56950)) = true := by decide
private theorem cl_w39 : ∀ n : Fin 50, centF (n.val + 56950) < 23 := by decide
private theorem bd_w39 : ∀ n : Fin 50, densSupG (n.val + 56950) < 2 ^ 1771 := by decide
private theorem cs_w40 : ∀ n : Fin 50, centredStar (densSupG (n.val + 57000)) (centF (n.val + 57000)) = true := by decide
private theorem cl_w40 : ∀ n : Fin 50, centF (n.val + 57000) < 23 := by decide
private theorem bd_w40 : ∀ n : Fin 50, densSupG (n.val + 57000) < 2 ^ 1771 := by decide
private theorem cs_w41 : ∀ n : Fin 50, centredStar (densSupG (n.val + 57050)) (centF (n.val + 57050)) = true := by decide
private theorem cl_w41 : ∀ n : Fin 50, centF (n.val + 57050) < 23 := by decide
private theorem bd_w41 : ∀ n : Fin 50, densSupG (n.val + 57050) < 2 ^ 1771 := by decide
private theorem cs_w42 : ∀ n : Fin 50, centredStar (densSupG (n.val + 57100)) (centF (n.val + 57100)) = true := by decide
private theorem cl_w42 : ∀ n : Fin 50, centF (n.val + 57100) < 23 := by decide
private theorem bd_w42 : ∀ n : Fin 50, densSupG (n.val + 57100) < 2 ^ 1771 := by decide
private theorem cs_w43 : ∀ n : Fin 50, centredStar (densSupG (n.val + 57150)) (centF (n.val + 57150)) = true := by decide
private theorem cl_w43 : ∀ n : Fin 50, centF (n.val + 57150) < 23 := by decide
private theorem bd_w43 : ∀ n : Fin 50, densSupG (n.val + 57150) < 2 ^ 1771 := by decide
private theorem cs_w44 : ∀ n : Fin 50, centredStar (densSupG (n.val + 57200)) (centF (n.val + 57200)) = true := by decide
private theorem cl_w44 : ∀ n : Fin 50, centF (n.val + 57200) < 23 := by decide
private theorem bd_w44 : ∀ n : Fin 50, densSupG (n.val + 57200) < 2 ^ 1771 := by decide
private theorem cs_w45 : ∀ n : Fin 50, centredStar (densSupG (n.val + 57250)) (centF (n.val + 57250)) = true := by decide
private theorem cl_w45 : ∀ n : Fin 50, centF (n.val + 57250) < 23 := by decide
private theorem bd_w45 : ∀ n : Fin 50, densSupG (n.val + 57250) < 2 ^ 1771 := by decide
private theorem cs_w46 : ∀ n : Fin 50, centredStar (densSupG (n.val + 57300)) (centF (n.val + 57300)) = true := by decide
private theorem cl_w46 : ∀ n : Fin 50, centF (n.val + 57300) < 23 := by decide
private theorem bd_w46 : ∀ n : Fin 50, densSupG (n.val + 57300) < 2 ^ 1771 := by decide
private theorem cs_w47 : ∀ n : Fin 50, centredStar (densSupG (n.val + 57350)) (centF (n.val + 57350)) = true := by decide
private theorem cl_w47 : ∀ n : Fin 50, centF (n.val + 57350) < 23 := by decide
private theorem bd_w47 : ∀ n : Fin 50, densSupG (n.val + 57350) < 2 ^ 1771 := by decide
private theorem cs_w48 : ∀ n : Fin 50, centredStar (densSupG (n.val + 57400)) (centF (n.val + 57400)) = true := by decide
private theorem cl_w48 : ∀ n : Fin 50, centF (n.val + 57400) < 23 := by decide
private theorem bd_w48 : ∀ n : Fin 50, densSupG (n.val + 57400) < 2 ^ 1771 := by decide
private theorem cs_w49 : ∀ n : Fin 50, centredStar (densSupG (n.val + 57450)) (centF (n.val + 57450)) = true := by decide
private theorem cl_w49 : ∀ n : Fin 50, centF (n.val + 57450) < 23 := by decide
private theorem bd_w49 : ∀ n : Fin 50, densSupG (n.val + 57450) < 2 ^ 1771 := by decide
theorem centredStar_range : ∀ n, 55000 ≤ n → n < 57500 → centredStar (densSupG n) (centF n) = true := by
  intro n hlo hhi
  by_cases h0 : n < 55050
  · have hr : n - 55000 < 50 := by omega
    have heq : n = (n - 55000) + 55000 := by omega
    rw [heq]
    exact cs_w0 ⟨n - 55000, hr⟩
  ·
    by_cases h1 : n < 55100
    ·
      have hr : n - 55050 < 50 := by omega
      have heq : n = (n - 55050) + 55050 := by omega
      rw [heq]
      exact cs_w1 ⟨n - 55050, hr⟩
    ·
      by_cases h2 : n < 55150
      ·
        have hr : n - 55100 < 50 := by omega
        have heq : n = (n - 55100) + 55100 := by omega
        rw [heq]
        exact cs_w2 ⟨n - 55100, hr⟩
      ·
        by_cases h3 : n < 55200
        ·
          have hr : n - 55150 < 50 := by omega
          have heq : n = (n - 55150) + 55150 := by omega
          rw [heq]
          exact cs_w3 ⟨n - 55150, hr⟩
        ·
          by_cases h4 : n < 55250
          ·
            have hr : n - 55200 < 50 := by omega
            have heq : n = (n - 55200) + 55200 := by omega
            rw [heq]
            exact cs_w4 ⟨n - 55200, hr⟩
          ·
            by_cases h5 : n < 55300
            ·
              have hr : n - 55250 < 50 := by omega
              have heq : n = (n - 55250) + 55250 := by omega
              rw [heq]
              exact cs_w5 ⟨n - 55250, hr⟩
            ·
              by_cases h6 : n < 55350
              ·
                have hr : n - 55300 < 50 := by omega
                have heq : n = (n - 55300) + 55300 := by omega
                rw [heq]
                exact cs_w6 ⟨n - 55300, hr⟩
              ·
                by_cases h7 : n < 55400
                ·
                  have hr : n - 55350 < 50 := by omega
                  have heq : n = (n - 55350) + 55350 := by omega
                  rw [heq]
                  exact cs_w7 ⟨n - 55350, hr⟩
                ·
                  by_cases h8 : n < 55450
                  ·
                    have hr : n - 55400 < 50 := by omega
                    have heq : n = (n - 55400) + 55400 := by omega
                    rw [heq]
                    exact cs_w8 ⟨n - 55400, hr⟩
                  ·
                    by_cases h9 : n < 55500
                    ·
                      have hr : n - 55450 < 50 := by omega
                      have heq : n = (n - 55450) + 55450 := by omega
                      rw [heq]
                      exact cs_w9 ⟨n - 55450, hr⟩
                    ·
                      by_cases h10 : n < 55550
                      ·
                        have hr : n - 55500 < 50 := by omega
                        have heq : n = (n - 55500) + 55500 := by omega
                        rw [heq]
                        exact cs_w10 ⟨n - 55500, hr⟩
                      ·
                        by_cases h11 : n < 55600
                        ·
                          have hr : n - 55550 < 50 := by omega
                          have heq : n = (n - 55550) + 55550 := by omega
                          rw [heq]
                          exact cs_w11 ⟨n - 55550, hr⟩
                        ·
                          by_cases h12 : n < 55650
                          ·
                            have hr : n - 55600 < 50 := by omega
                            have heq : n = (n - 55600) + 55600 := by omega
                            rw [heq]
                            exact cs_w12 ⟨n - 55600, hr⟩
                          ·
                            by_cases h13 : n < 55700
                            ·
                              have hr : n - 55650 < 50 := by omega
                              have heq : n = (n - 55650) + 55650 := by omega
                              rw [heq]
                              exact cs_w13 ⟨n - 55650, hr⟩
                            ·
                              by_cases h14 : n < 55750
                              ·
                                have hr : n - 55700 < 50 := by omega
                                have heq : n = (n - 55700) + 55700 := by omega
                                rw [heq]
                                exact cs_w14 ⟨n - 55700, hr⟩
                              ·
                                by_cases h15 : n < 55800
                                ·
                                  have hr : n - 55750 < 50 := by omega
                                  have heq : n = (n - 55750) + 55750 := by omega
                                  rw [heq]
                                  exact cs_w15 ⟨n - 55750, hr⟩
                                ·
                                  by_cases h16 : n < 55850
                                  ·
                                    have hr : n - 55800 < 50 := by omega
                                    have heq : n = (n - 55800) + 55800 := by omega
                                    rw [heq]
                                    exact cs_w16 ⟨n - 55800, hr⟩
                                  ·
                                    by_cases h17 : n < 55900
                                    ·
                                      have hr : n - 55850 < 50 := by omega
                                      have heq : n = (n - 55850) + 55850 := by omega
                                      rw [heq]
                                      exact cs_w17 ⟨n - 55850, hr⟩
                                    ·
                                      by_cases h18 : n < 55950
                                      ·
                                        have hr : n - 55900 < 50 := by omega
                                        have heq : n = (n - 55900) + 55900 := by omega
                                        rw [heq]
                                        exact cs_w18 ⟨n - 55900, hr⟩
                                      ·
                                        by_cases h19 : n < 56000
                                        ·
                                          have hr : n - 55950 < 50 := by omega
                                          have heq : n = (n - 55950) + 55950 := by omega
                                          rw [heq]
                                          exact cs_w19 ⟨n - 55950, hr⟩
                                        ·
                                          by_cases h20 : n < 56050
                                          ·
                                            have hr : n - 56000 < 50 := by omega
                                            have heq : n = (n - 56000) + 56000 := by omega
                                            rw [heq]
                                            exact cs_w20 ⟨n - 56000, hr⟩
                                          ·
                                            by_cases h21 : n < 56100
                                            ·
                                              have hr : n - 56050 < 50 := by omega
                                              have heq : n = (n - 56050) + 56050 := by omega
                                              rw [heq]
                                              exact cs_w21 ⟨n - 56050, hr⟩
                                            ·
                                              by_cases h22 : n < 56150
                                              ·
                                                have hr : n - 56100 < 50 := by omega
                                                have heq : n = (n - 56100) + 56100 := by omega
                                                rw [heq]
                                                exact cs_w22 ⟨n - 56100, hr⟩
                                              ·
                                                by_cases h23 : n < 56200
                                                ·
                                                  have hr : n - 56150 < 50 := by omega
                                                  have heq : n = (n - 56150) + 56150 := by omega
                                                  rw [heq]
                                                  exact cs_w23 ⟨n - 56150, hr⟩
                                                ·
                                                  by_cases h24 : n < 56250
                                                  ·
                                                    have hr : n - 56200 < 50 := by omega
                                                    have heq : n = (n - 56200) + 56200 := by omega
                                                    rw [heq]
                                                    exact cs_w24 ⟨n - 56200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 56300
                                                    ·
                                                      have hr : n - 56250 < 50 := by omega
                                                      have heq : n = (n - 56250) + 56250 := by omega
                                                      rw [heq]
                                                      exact cs_w25 ⟨n - 56250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 56350
                                                      ·
                                                        have hr : n - 56300 < 50 := by omega
                                                        have heq : n = (n - 56300) + 56300 := by omega
                                                        rw [heq]
                                                        exact cs_w26 ⟨n - 56300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 56400
                                                        ·
                                                          have hr : n - 56350 < 50 := by omega
                                                          have heq : n = (n - 56350) + 56350 := by omega
                                                          rw [heq]
                                                          exact cs_w27 ⟨n - 56350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 56450
                                                          ·
                                                            have hr : n - 56400 < 50 := by omega
                                                            have heq : n = (n - 56400) + 56400 := by omega
                                                            rw [heq]
                                                            exact cs_w28 ⟨n - 56400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 56500
                                                            ·
                                                              have hr : n - 56450 < 50 := by omega
                                                              have heq : n = (n - 56450) + 56450 := by omega
                                                              rw [heq]
                                                              exact cs_w29 ⟨n - 56450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 56550
                                                              ·
                                                                have hr : n - 56500 < 50 := by omega
                                                                have heq : n = (n - 56500) + 56500 := by omega
                                                                rw [heq]
                                                                exact cs_w30 ⟨n - 56500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 56600
                                                                ·
                                                                  have hr : n - 56550 < 50 := by omega
                                                                  have heq : n = (n - 56550) + 56550 := by omega
                                                                  rw [heq]
                                                                  exact cs_w31 ⟨n - 56550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 56650
                                                                  ·
                                                                    have hr : n - 56600 < 50 := by omega
                                                                    have heq : n = (n - 56600) + 56600 := by omega
                                                                    rw [heq]
                                                                    exact cs_w32 ⟨n - 56600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 56700
                                                                    ·
                                                                      have hr : n - 56650 < 50 := by omega
                                                                      have heq : n = (n - 56650) + 56650 := by omega
                                                                      rw [heq]
                                                                      exact cs_w33 ⟨n - 56650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 56750
                                                                      ·
                                                                        have hr : n - 56700 < 50 := by omega
                                                                        have heq : n = (n - 56700) + 56700 := by omega
                                                                        rw [heq]
                                                                        exact cs_w34 ⟨n - 56700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 56800
                                                                        ·
                                                                          have hr : n - 56750 < 50 := by omega
                                                                          have heq : n = (n - 56750) + 56750 := by omega
                                                                          rw [heq]
                                                                          exact cs_w35 ⟨n - 56750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 56850
                                                                          ·
                                                                            have hr : n - 56800 < 50 := by omega
                                                                            have heq : n = (n - 56800) + 56800 := by omega
                                                                            rw [heq]
                                                                            exact cs_w36 ⟨n - 56800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 56900
                                                                            ·
                                                                              have hr : n - 56850 < 50 := by omega
                                                                              have heq : n = (n - 56850) + 56850 := by omega
                                                                              rw [heq]
                                                                              exact cs_w37 ⟨n - 56850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 56950
                                                                              ·
                                                                                have hr : n - 56900 < 50 := by omega
                                                                                have heq : n = (n - 56900) + 56900 := by omega
                                                                                rw [heq]
                                                                                exact cs_w38 ⟨n - 56900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 57000
                                                                                ·
                                                                                  have hr : n - 56950 < 50 := by omega
                                                                                  have heq : n = (n - 56950) + 56950 := by omega
                                                                                  rw [heq]
                                                                                  exact cs_w39 ⟨n - 56950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 57050
                                                                                  ·
                                                                                    have hr : n - 57000 < 50 := by omega
                                                                                    have heq : n = (n - 57000) + 57000 := by omega
                                                                                    rw [heq]
                                                                                    exact cs_w40 ⟨n - 57000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 57100
                                                                                    ·
                                                                                      have hr : n - 57050 < 50 := by omega
                                                                                      have heq : n = (n - 57050) + 57050 := by omega
                                                                                      rw [heq]
                                                                                      exact cs_w41 ⟨n - 57050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 57150
                                                                                      ·
                                                                                        have hr : n - 57100 < 50 := by omega
                                                                                        have heq : n = (n - 57100) + 57100 := by omega
                                                                                        rw [heq]
                                                                                        exact cs_w42 ⟨n - 57100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 57200
                                                                                        ·
                                                                                          have hr : n - 57150 < 50 := by omega
                                                                                          have heq : n = (n - 57150) + 57150 := by omega
                                                                                          rw [heq]
                                                                                          exact cs_w43 ⟨n - 57150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 57250
                                                                                          ·
                                                                                            have hr : n - 57200 < 50 := by omega
                                                                                            have heq : n = (n - 57200) + 57200 := by omega
                                                                                            rw [heq]
                                                                                            exact cs_w44 ⟨n - 57200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 57300
                                                                                            ·
                                                                                              have hr : n - 57250 < 50 := by omega
                                                                                              have heq : n = (n - 57250) + 57250 := by omega
                                                                                              rw [heq]
                                                                                              exact cs_w45 ⟨n - 57250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 57350
                                                                                              ·
                                                                                                have hr : n - 57300 < 50 := by omega
                                                                                                have heq : n = (n - 57300) + 57300 := by omega
                                                                                                rw [heq]
                                                                                                exact cs_w46 ⟨n - 57300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 57400
                                                                                                ·
                                                                                                  have hr : n - 57350 < 50 := by omega
                                                                                                  have heq : n = (n - 57350) + 57350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cs_w47 ⟨n - 57350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 57450
                                                                                                  ·
                                                                                                    have hr : n - 57400 < 50 := by omega
                                                                                                    have heq : n = (n - 57400) + 57400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w48 ⟨n - 57400, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 57450 < 50 := by omega
                                                                                                    have heq : n = (n - 57450) + 57450 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w49 ⟨n - 57450, hr⟩


theorem centF_lt_range : ∀ n, 55000 ≤ n → n < 57500 → centF n < 23 := by
  intro n hlo hhi
  by_cases h0 : n < 55050
  · have hr : n - 55000 < 50 := by omega
    have heq : n = (n - 55000) + 55000 := by omega
    rw [heq]
    exact cl_w0 ⟨n - 55000, hr⟩
  ·
    by_cases h1 : n < 55100
    ·
      have hr : n - 55050 < 50 := by omega
      have heq : n = (n - 55050) + 55050 := by omega
      rw [heq]
      exact cl_w1 ⟨n - 55050, hr⟩
    ·
      by_cases h2 : n < 55150
      ·
        have hr : n - 55100 < 50 := by omega
        have heq : n = (n - 55100) + 55100 := by omega
        rw [heq]
        exact cl_w2 ⟨n - 55100, hr⟩
      ·
        by_cases h3 : n < 55200
        ·
          have hr : n - 55150 < 50 := by omega
          have heq : n = (n - 55150) + 55150 := by omega
          rw [heq]
          exact cl_w3 ⟨n - 55150, hr⟩
        ·
          by_cases h4 : n < 55250
          ·
            have hr : n - 55200 < 50 := by omega
            have heq : n = (n - 55200) + 55200 := by omega
            rw [heq]
            exact cl_w4 ⟨n - 55200, hr⟩
          ·
            by_cases h5 : n < 55300
            ·
              have hr : n - 55250 < 50 := by omega
              have heq : n = (n - 55250) + 55250 := by omega
              rw [heq]
              exact cl_w5 ⟨n - 55250, hr⟩
            ·
              by_cases h6 : n < 55350
              ·
                have hr : n - 55300 < 50 := by omega
                have heq : n = (n - 55300) + 55300 := by omega
                rw [heq]
                exact cl_w6 ⟨n - 55300, hr⟩
              ·
                by_cases h7 : n < 55400
                ·
                  have hr : n - 55350 < 50 := by omega
                  have heq : n = (n - 55350) + 55350 := by omega
                  rw [heq]
                  exact cl_w7 ⟨n - 55350, hr⟩
                ·
                  by_cases h8 : n < 55450
                  ·
                    have hr : n - 55400 < 50 := by omega
                    have heq : n = (n - 55400) + 55400 := by omega
                    rw [heq]
                    exact cl_w8 ⟨n - 55400, hr⟩
                  ·
                    by_cases h9 : n < 55500
                    ·
                      have hr : n - 55450 < 50 := by omega
                      have heq : n = (n - 55450) + 55450 := by omega
                      rw [heq]
                      exact cl_w9 ⟨n - 55450, hr⟩
                    ·
                      by_cases h10 : n < 55550
                      ·
                        have hr : n - 55500 < 50 := by omega
                        have heq : n = (n - 55500) + 55500 := by omega
                        rw [heq]
                        exact cl_w10 ⟨n - 55500, hr⟩
                      ·
                        by_cases h11 : n < 55600
                        ·
                          have hr : n - 55550 < 50 := by omega
                          have heq : n = (n - 55550) + 55550 := by omega
                          rw [heq]
                          exact cl_w11 ⟨n - 55550, hr⟩
                        ·
                          by_cases h12 : n < 55650
                          ·
                            have hr : n - 55600 < 50 := by omega
                            have heq : n = (n - 55600) + 55600 := by omega
                            rw [heq]
                            exact cl_w12 ⟨n - 55600, hr⟩
                          ·
                            by_cases h13 : n < 55700
                            ·
                              have hr : n - 55650 < 50 := by omega
                              have heq : n = (n - 55650) + 55650 := by omega
                              rw [heq]
                              exact cl_w13 ⟨n - 55650, hr⟩
                            ·
                              by_cases h14 : n < 55750
                              ·
                                have hr : n - 55700 < 50 := by omega
                                have heq : n = (n - 55700) + 55700 := by omega
                                rw [heq]
                                exact cl_w14 ⟨n - 55700, hr⟩
                              ·
                                by_cases h15 : n < 55800
                                ·
                                  have hr : n - 55750 < 50 := by omega
                                  have heq : n = (n - 55750) + 55750 := by omega
                                  rw [heq]
                                  exact cl_w15 ⟨n - 55750, hr⟩
                                ·
                                  by_cases h16 : n < 55850
                                  ·
                                    have hr : n - 55800 < 50 := by omega
                                    have heq : n = (n - 55800) + 55800 := by omega
                                    rw [heq]
                                    exact cl_w16 ⟨n - 55800, hr⟩
                                  ·
                                    by_cases h17 : n < 55900
                                    ·
                                      have hr : n - 55850 < 50 := by omega
                                      have heq : n = (n - 55850) + 55850 := by omega
                                      rw [heq]
                                      exact cl_w17 ⟨n - 55850, hr⟩
                                    ·
                                      by_cases h18 : n < 55950
                                      ·
                                        have hr : n - 55900 < 50 := by omega
                                        have heq : n = (n - 55900) + 55900 := by omega
                                        rw [heq]
                                        exact cl_w18 ⟨n - 55900, hr⟩
                                      ·
                                        by_cases h19 : n < 56000
                                        ·
                                          have hr : n - 55950 < 50 := by omega
                                          have heq : n = (n - 55950) + 55950 := by omega
                                          rw [heq]
                                          exact cl_w19 ⟨n - 55950, hr⟩
                                        ·
                                          by_cases h20 : n < 56050
                                          ·
                                            have hr : n - 56000 < 50 := by omega
                                            have heq : n = (n - 56000) + 56000 := by omega
                                            rw [heq]
                                            exact cl_w20 ⟨n - 56000, hr⟩
                                          ·
                                            by_cases h21 : n < 56100
                                            ·
                                              have hr : n - 56050 < 50 := by omega
                                              have heq : n = (n - 56050) + 56050 := by omega
                                              rw [heq]
                                              exact cl_w21 ⟨n - 56050, hr⟩
                                            ·
                                              by_cases h22 : n < 56150
                                              ·
                                                have hr : n - 56100 < 50 := by omega
                                                have heq : n = (n - 56100) + 56100 := by omega
                                                rw [heq]
                                                exact cl_w22 ⟨n - 56100, hr⟩
                                              ·
                                                by_cases h23 : n < 56200
                                                ·
                                                  have hr : n - 56150 < 50 := by omega
                                                  have heq : n = (n - 56150) + 56150 := by omega
                                                  rw [heq]
                                                  exact cl_w23 ⟨n - 56150, hr⟩
                                                ·
                                                  by_cases h24 : n < 56250
                                                  ·
                                                    have hr : n - 56200 < 50 := by omega
                                                    have heq : n = (n - 56200) + 56200 := by omega
                                                    rw [heq]
                                                    exact cl_w24 ⟨n - 56200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 56300
                                                    ·
                                                      have hr : n - 56250 < 50 := by omega
                                                      have heq : n = (n - 56250) + 56250 := by omega
                                                      rw [heq]
                                                      exact cl_w25 ⟨n - 56250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 56350
                                                      ·
                                                        have hr : n - 56300 < 50 := by omega
                                                        have heq : n = (n - 56300) + 56300 := by omega
                                                        rw [heq]
                                                        exact cl_w26 ⟨n - 56300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 56400
                                                        ·
                                                          have hr : n - 56350 < 50 := by omega
                                                          have heq : n = (n - 56350) + 56350 := by omega
                                                          rw [heq]
                                                          exact cl_w27 ⟨n - 56350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 56450
                                                          ·
                                                            have hr : n - 56400 < 50 := by omega
                                                            have heq : n = (n - 56400) + 56400 := by omega
                                                            rw [heq]
                                                            exact cl_w28 ⟨n - 56400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 56500
                                                            ·
                                                              have hr : n - 56450 < 50 := by omega
                                                              have heq : n = (n - 56450) + 56450 := by omega
                                                              rw [heq]
                                                              exact cl_w29 ⟨n - 56450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 56550
                                                              ·
                                                                have hr : n - 56500 < 50 := by omega
                                                                have heq : n = (n - 56500) + 56500 := by omega
                                                                rw [heq]
                                                                exact cl_w30 ⟨n - 56500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 56600
                                                                ·
                                                                  have hr : n - 56550 < 50 := by omega
                                                                  have heq : n = (n - 56550) + 56550 := by omega
                                                                  rw [heq]
                                                                  exact cl_w31 ⟨n - 56550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 56650
                                                                  ·
                                                                    have hr : n - 56600 < 50 := by omega
                                                                    have heq : n = (n - 56600) + 56600 := by omega
                                                                    rw [heq]
                                                                    exact cl_w32 ⟨n - 56600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 56700
                                                                    ·
                                                                      have hr : n - 56650 < 50 := by omega
                                                                      have heq : n = (n - 56650) + 56650 := by omega
                                                                      rw [heq]
                                                                      exact cl_w33 ⟨n - 56650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 56750
                                                                      ·
                                                                        have hr : n - 56700 < 50 := by omega
                                                                        have heq : n = (n - 56700) + 56700 := by omega
                                                                        rw [heq]
                                                                        exact cl_w34 ⟨n - 56700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 56800
                                                                        ·
                                                                          have hr : n - 56750 < 50 := by omega
                                                                          have heq : n = (n - 56750) + 56750 := by omega
                                                                          rw [heq]
                                                                          exact cl_w35 ⟨n - 56750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 56850
                                                                          ·
                                                                            have hr : n - 56800 < 50 := by omega
                                                                            have heq : n = (n - 56800) + 56800 := by omega
                                                                            rw [heq]
                                                                            exact cl_w36 ⟨n - 56800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 56900
                                                                            ·
                                                                              have hr : n - 56850 < 50 := by omega
                                                                              have heq : n = (n - 56850) + 56850 := by omega
                                                                              rw [heq]
                                                                              exact cl_w37 ⟨n - 56850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 56950
                                                                              ·
                                                                                have hr : n - 56900 < 50 := by omega
                                                                                have heq : n = (n - 56900) + 56900 := by omega
                                                                                rw [heq]
                                                                                exact cl_w38 ⟨n - 56900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 57000
                                                                                ·
                                                                                  have hr : n - 56950 < 50 := by omega
                                                                                  have heq : n = (n - 56950) + 56950 := by omega
                                                                                  rw [heq]
                                                                                  exact cl_w39 ⟨n - 56950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 57050
                                                                                  ·
                                                                                    have hr : n - 57000 < 50 := by omega
                                                                                    have heq : n = (n - 57000) + 57000 := by omega
                                                                                    rw [heq]
                                                                                    exact cl_w40 ⟨n - 57000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 57100
                                                                                    ·
                                                                                      have hr : n - 57050 < 50 := by omega
                                                                                      have heq : n = (n - 57050) + 57050 := by omega
                                                                                      rw [heq]
                                                                                      exact cl_w41 ⟨n - 57050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 57150
                                                                                      ·
                                                                                        have hr : n - 57100 < 50 := by omega
                                                                                        have heq : n = (n - 57100) + 57100 := by omega
                                                                                        rw [heq]
                                                                                        exact cl_w42 ⟨n - 57100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 57200
                                                                                        ·
                                                                                          have hr : n - 57150 < 50 := by omega
                                                                                          have heq : n = (n - 57150) + 57150 := by omega
                                                                                          rw [heq]
                                                                                          exact cl_w43 ⟨n - 57150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 57250
                                                                                          ·
                                                                                            have hr : n - 57200 < 50 := by omega
                                                                                            have heq : n = (n - 57200) + 57200 := by omega
                                                                                            rw [heq]
                                                                                            exact cl_w44 ⟨n - 57200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 57300
                                                                                            ·
                                                                                              have hr : n - 57250 < 50 := by omega
                                                                                              have heq : n = (n - 57250) + 57250 := by omega
                                                                                              rw [heq]
                                                                                              exact cl_w45 ⟨n - 57250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 57350
                                                                                              ·
                                                                                                have hr : n - 57300 < 50 := by omega
                                                                                                have heq : n = (n - 57300) + 57300 := by omega
                                                                                                rw [heq]
                                                                                                exact cl_w46 ⟨n - 57300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 57400
                                                                                                ·
                                                                                                  have hr : n - 57350 < 50 := by omega
                                                                                                  have heq : n = (n - 57350) + 57350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cl_w47 ⟨n - 57350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 57450
                                                                                                  ·
                                                                                                    have hr : n - 57400 < 50 := by omega
                                                                                                    have heq : n = (n - 57400) + 57400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w48 ⟨n - 57400, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 57450 < 50 := by omega
                                                                                                    have heq : n = (n - 57450) + 57450 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w49 ⟨n - 57450, hr⟩


theorem densSupG_lt_range : ∀ n, 55000 ≤ n → n < 57500 → densSupG n < 2 ^ 1771 := by
  intro n hlo hhi
  by_cases h0 : n < 55050
  · have hr : n - 55000 < 50 := by omega
    have heq : n = (n - 55000) + 55000 := by omega
    rw [heq]
    exact bd_w0 ⟨n - 55000, hr⟩
  ·
    by_cases h1 : n < 55100
    ·
      have hr : n - 55050 < 50 := by omega
      have heq : n = (n - 55050) + 55050 := by omega
      rw [heq]
      exact bd_w1 ⟨n - 55050, hr⟩
    ·
      by_cases h2 : n < 55150
      ·
        have hr : n - 55100 < 50 := by omega
        have heq : n = (n - 55100) + 55100 := by omega
        rw [heq]
        exact bd_w2 ⟨n - 55100, hr⟩
      ·
        by_cases h3 : n < 55200
        ·
          have hr : n - 55150 < 50 := by omega
          have heq : n = (n - 55150) + 55150 := by omega
          rw [heq]
          exact bd_w3 ⟨n - 55150, hr⟩
        ·
          by_cases h4 : n < 55250
          ·
            have hr : n - 55200 < 50 := by omega
            have heq : n = (n - 55200) + 55200 := by omega
            rw [heq]
            exact bd_w4 ⟨n - 55200, hr⟩
          ·
            by_cases h5 : n < 55300
            ·
              have hr : n - 55250 < 50 := by omega
              have heq : n = (n - 55250) + 55250 := by omega
              rw [heq]
              exact bd_w5 ⟨n - 55250, hr⟩
            ·
              by_cases h6 : n < 55350
              ·
                have hr : n - 55300 < 50 := by omega
                have heq : n = (n - 55300) + 55300 := by omega
                rw [heq]
                exact bd_w6 ⟨n - 55300, hr⟩
              ·
                by_cases h7 : n < 55400
                ·
                  have hr : n - 55350 < 50 := by omega
                  have heq : n = (n - 55350) + 55350 := by omega
                  rw [heq]
                  exact bd_w7 ⟨n - 55350, hr⟩
                ·
                  by_cases h8 : n < 55450
                  ·
                    have hr : n - 55400 < 50 := by omega
                    have heq : n = (n - 55400) + 55400 := by omega
                    rw [heq]
                    exact bd_w8 ⟨n - 55400, hr⟩
                  ·
                    by_cases h9 : n < 55500
                    ·
                      have hr : n - 55450 < 50 := by omega
                      have heq : n = (n - 55450) + 55450 := by omega
                      rw [heq]
                      exact bd_w9 ⟨n - 55450, hr⟩
                    ·
                      by_cases h10 : n < 55550
                      ·
                        have hr : n - 55500 < 50 := by omega
                        have heq : n = (n - 55500) + 55500 := by omega
                        rw [heq]
                        exact bd_w10 ⟨n - 55500, hr⟩
                      ·
                        by_cases h11 : n < 55600
                        ·
                          have hr : n - 55550 < 50 := by omega
                          have heq : n = (n - 55550) + 55550 := by omega
                          rw [heq]
                          exact bd_w11 ⟨n - 55550, hr⟩
                        ·
                          by_cases h12 : n < 55650
                          ·
                            have hr : n - 55600 < 50 := by omega
                            have heq : n = (n - 55600) + 55600 := by omega
                            rw [heq]
                            exact bd_w12 ⟨n - 55600, hr⟩
                          ·
                            by_cases h13 : n < 55700
                            ·
                              have hr : n - 55650 < 50 := by omega
                              have heq : n = (n - 55650) + 55650 := by omega
                              rw [heq]
                              exact bd_w13 ⟨n - 55650, hr⟩
                            ·
                              by_cases h14 : n < 55750
                              ·
                                have hr : n - 55700 < 50 := by omega
                                have heq : n = (n - 55700) + 55700 := by omega
                                rw [heq]
                                exact bd_w14 ⟨n - 55700, hr⟩
                              ·
                                by_cases h15 : n < 55800
                                ·
                                  have hr : n - 55750 < 50 := by omega
                                  have heq : n = (n - 55750) + 55750 := by omega
                                  rw [heq]
                                  exact bd_w15 ⟨n - 55750, hr⟩
                                ·
                                  by_cases h16 : n < 55850
                                  ·
                                    have hr : n - 55800 < 50 := by omega
                                    have heq : n = (n - 55800) + 55800 := by omega
                                    rw [heq]
                                    exact bd_w16 ⟨n - 55800, hr⟩
                                  ·
                                    by_cases h17 : n < 55900
                                    ·
                                      have hr : n - 55850 < 50 := by omega
                                      have heq : n = (n - 55850) + 55850 := by omega
                                      rw [heq]
                                      exact bd_w17 ⟨n - 55850, hr⟩
                                    ·
                                      by_cases h18 : n < 55950
                                      ·
                                        have hr : n - 55900 < 50 := by omega
                                        have heq : n = (n - 55900) + 55900 := by omega
                                        rw [heq]
                                        exact bd_w18 ⟨n - 55900, hr⟩
                                      ·
                                        by_cases h19 : n < 56000
                                        ·
                                          have hr : n - 55950 < 50 := by omega
                                          have heq : n = (n - 55950) + 55950 := by omega
                                          rw [heq]
                                          exact bd_w19 ⟨n - 55950, hr⟩
                                        ·
                                          by_cases h20 : n < 56050
                                          ·
                                            have hr : n - 56000 < 50 := by omega
                                            have heq : n = (n - 56000) + 56000 := by omega
                                            rw [heq]
                                            exact bd_w20 ⟨n - 56000, hr⟩
                                          ·
                                            by_cases h21 : n < 56100
                                            ·
                                              have hr : n - 56050 < 50 := by omega
                                              have heq : n = (n - 56050) + 56050 := by omega
                                              rw [heq]
                                              exact bd_w21 ⟨n - 56050, hr⟩
                                            ·
                                              by_cases h22 : n < 56150
                                              ·
                                                have hr : n - 56100 < 50 := by omega
                                                have heq : n = (n - 56100) + 56100 := by omega
                                                rw [heq]
                                                exact bd_w22 ⟨n - 56100, hr⟩
                                              ·
                                                by_cases h23 : n < 56200
                                                ·
                                                  have hr : n - 56150 < 50 := by omega
                                                  have heq : n = (n - 56150) + 56150 := by omega
                                                  rw [heq]
                                                  exact bd_w23 ⟨n - 56150, hr⟩
                                                ·
                                                  by_cases h24 : n < 56250
                                                  ·
                                                    have hr : n - 56200 < 50 := by omega
                                                    have heq : n = (n - 56200) + 56200 := by omega
                                                    rw [heq]
                                                    exact bd_w24 ⟨n - 56200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 56300
                                                    ·
                                                      have hr : n - 56250 < 50 := by omega
                                                      have heq : n = (n - 56250) + 56250 := by omega
                                                      rw [heq]
                                                      exact bd_w25 ⟨n - 56250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 56350
                                                      ·
                                                        have hr : n - 56300 < 50 := by omega
                                                        have heq : n = (n - 56300) + 56300 := by omega
                                                        rw [heq]
                                                        exact bd_w26 ⟨n - 56300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 56400
                                                        ·
                                                          have hr : n - 56350 < 50 := by omega
                                                          have heq : n = (n - 56350) + 56350 := by omega
                                                          rw [heq]
                                                          exact bd_w27 ⟨n - 56350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 56450
                                                          ·
                                                            have hr : n - 56400 < 50 := by omega
                                                            have heq : n = (n - 56400) + 56400 := by omega
                                                            rw [heq]
                                                            exact bd_w28 ⟨n - 56400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 56500
                                                            ·
                                                              have hr : n - 56450 < 50 := by omega
                                                              have heq : n = (n - 56450) + 56450 := by omega
                                                              rw [heq]
                                                              exact bd_w29 ⟨n - 56450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 56550
                                                              ·
                                                                have hr : n - 56500 < 50 := by omega
                                                                have heq : n = (n - 56500) + 56500 := by omega
                                                                rw [heq]
                                                                exact bd_w30 ⟨n - 56500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 56600
                                                                ·
                                                                  have hr : n - 56550 < 50 := by omega
                                                                  have heq : n = (n - 56550) + 56550 := by omega
                                                                  rw [heq]
                                                                  exact bd_w31 ⟨n - 56550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 56650
                                                                  ·
                                                                    have hr : n - 56600 < 50 := by omega
                                                                    have heq : n = (n - 56600) + 56600 := by omega
                                                                    rw [heq]
                                                                    exact bd_w32 ⟨n - 56600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 56700
                                                                    ·
                                                                      have hr : n - 56650 < 50 := by omega
                                                                      have heq : n = (n - 56650) + 56650 := by omega
                                                                      rw [heq]
                                                                      exact bd_w33 ⟨n - 56650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 56750
                                                                      ·
                                                                        have hr : n - 56700 < 50 := by omega
                                                                        have heq : n = (n - 56700) + 56700 := by omega
                                                                        rw [heq]
                                                                        exact bd_w34 ⟨n - 56700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 56800
                                                                        ·
                                                                          have hr : n - 56750 < 50 := by omega
                                                                          have heq : n = (n - 56750) + 56750 := by omega
                                                                          rw [heq]
                                                                          exact bd_w35 ⟨n - 56750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 56850
                                                                          ·
                                                                            have hr : n - 56800 < 50 := by omega
                                                                            have heq : n = (n - 56800) + 56800 := by omega
                                                                            rw [heq]
                                                                            exact bd_w36 ⟨n - 56800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 56900
                                                                            ·
                                                                              have hr : n - 56850 < 50 := by omega
                                                                              have heq : n = (n - 56850) + 56850 := by omega
                                                                              rw [heq]
                                                                              exact bd_w37 ⟨n - 56850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 56950
                                                                              ·
                                                                                have hr : n - 56900 < 50 := by omega
                                                                                have heq : n = (n - 56900) + 56900 := by omega
                                                                                rw [heq]
                                                                                exact bd_w38 ⟨n - 56900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 57000
                                                                                ·
                                                                                  have hr : n - 56950 < 50 := by omega
                                                                                  have heq : n = (n - 56950) + 56950 := by omega
                                                                                  rw [heq]
                                                                                  exact bd_w39 ⟨n - 56950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 57050
                                                                                  ·
                                                                                    have hr : n - 57000 < 50 := by omega
                                                                                    have heq : n = (n - 57000) + 57000 := by omega
                                                                                    rw [heq]
                                                                                    exact bd_w40 ⟨n - 57000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 57100
                                                                                    ·
                                                                                      have hr : n - 57050 < 50 := by omega
                                                                                      have heq : n = (n - 57050) + 57050 := by omega
                                                                                      rw [heq]
                                                                                      exact bd_w41 ⟨n - 57050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 57150
                                                                                      ·
                                                                                        have hr : n - 57100 < 50 := by omega
                                                                                        have heq : n = (n - 57100) + 57100 := by omega
                                                                                        rw [heq]
                                                                                        exact bd_w42 ⟨n - 57100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 57200
                                                                                        ·
                                                                                          have hr : n - 57150 < 50 := by omega
                                                                                          have heq : n = (n - 57150) + 57150 := by omega
                                                                                          rw [heq]
                                                                                          exact bd_w43 ⟨n - 57150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 57250
                                                                                          ·
                                                                                            have hr : n - 57200 < 50 := by omega
                                                                                            have heq : n = (n - 57200) + 57200 := by omega
                                                                                            rw [heq]
                                                                                            exact bd_w44 ⟨n - 57200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 57300
                                                                                            ·
                                                                                              have hr : n - 57250 < 50 := by omega
                                                                                              have heq : n = (n - 57250) + 57250 := by omega
                                                                                              rw [heq]
                                                                                              exact bd_w45 ⟨n - 57250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 57350
                                                                                              ·
                                                                                                have hr : n - 57300 < 50 := by omega
                                                                                                have heq : n = (n - 57300) + 57300 := by omega
                                                                                                rw [heq]
                                                                                                exact bd_w46 ⟨n - 57300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 57400
                                                                                                ·
                                                                                                  have hr : n - 57350 < 50 := by omega
                                                                                                  have heq : n = (n - 57350) + 57350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact bd_w47 ⟨n - 57350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 57450
                                                                                                  ·
                                                                                                    have hr : n - 57400 < 50 := by omega
                                                                                                    have heq : n = (n - 57400) + 57400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w48 ⟨n - 57400, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 57450 < 50 := by omega
                                                                                                    have heq : n = (n - 57450) + 57450 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w49 ⟨n - 57450, hr⟩


end IntMul.Kappa.R8.Bit.Oppbank.CentBound11aFix


