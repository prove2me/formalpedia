-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound1b
-- name    : IntMul_Kappa_R8_Data_BitOppbankCentBound1b
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:55:35.81008+00:00
-- url     : https://prove2.me/theorems/07cf705c-90b7-432b-ab46-7134fabd061a
-- title:
--   HasCentre certificates dens nodes [7500,10000)
-- statement:
--   # Densified centre certificates, pack 1b
--
--   For every densified node index $n$ with $7500\le n<10000$,
--   $$
--   \mathrm{centredStar}(\mathrm{densSupG}\,n,\mathrm{centF}\,n)=\mathsf{true},\quad
--   \mathrm{centF}\,n<23,\quad
--   \mathrm{densSupG}\,n < 2^{1771}.
--   $$
--   Proved by decide on Fin 50 windows (no native_decide). Half-pack split of CentBound1 for server compile budget.
-- source:
--   R8 BitOppbank AllDensCentred; jfstack_23 densified supports

-- CentBound pack 1b: densified HasCentre certificates on n ∈ [7500, 10000)
-- Generated for AllDensCentred (star-mask land + centF).

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

namespace IntMul.Kappa.R8.Bit.Oppbank.CentBound1b

private theorem cs_w0 : ∀ n : Fin 50, centredStar (densSupG (n.val + 7500)) (centF (n.val + 7500)) = true := by decide
private theorem cl_w0 : ∀ n : Fin 50, centF (n.val + 7500) < 23 := by decide
private theorem bd_w0 : ∀ n : Fin 50, densSupG (n.val + 7500) < 2 ^ 1771 := by decide
private theorem cs_w1 : ∀ n : Fin 50, centredStar (densSupG (n.val + 7550)) (centF (n.val + 7550)) = true := by decide
private theorem cl_w1 : ∀ n : Fin 50, centF (n.val + 7550) < 23 := by decide
private theorem bd_w1 : ∀ n : Fin 50, densSupG (n.val + 7550) < 2 ^ 1771 := by decide
private theorem cs_w2 : ∀ n : Fin 50, centredStar (densSupG (n.val + 7600)) (centF (n.val + 7600)) = true := by decide
private theorem cl_w2 : ∀ n : Fin 50, centF (n.val + 7600) < 23 := by decide
private theorem bd_w2 : ∀ n : Fin 50, densSupG (n.val + 7600) < 2 ^ 1771 := by decide
private theorem cs_w3 : ∀ n : Fin 50, centredStar (densSupG (n.val + 7650)) (centF (n.val + 7650)) = true := by decide
private theorem cl_w3 : ∀ n : Fin 50, centF (n.val + 7650) < 23 := by decide
private theorem bd_w3 : ∀ n : Fin 50, densSupG (n.val + 7650) < 2 ^ 1771 := by decide
private theorem cs_w4 : ∀ n : Fin 50, centredStar (densSupG (n.val + 7700)) (centF (n.val + 7700)) = true := by decide
private theorem cl_w4 : ∀ n : Fin 50, centF (n.val + 7700) < 23 := by decide
private theorem bd_w4 : ∀ n : Fin 50, densSupG (n.val + 7700) < 2 ^ 1771 := by decide
private theorem cs_w5 : ∀ n : Fin 50, centredStar (densSupG (n.val + 7750)) (centF (n.val + 7750)) = true := by decide
private theorem cl_w5 : ∀ n : Fin 50, centF (n.val + 7750) < 23 := by decide
private theorem bd_w5 : ∀ n : Fin 50, densSupG (n.val + 7750) < 2 ^ 1771 := by decide
private theorem cs_w6 : ∀ n : Fin 50, centredStar (densSupG (n.val + 7800)) (centF (n.val + 7800)) = true := by decide
private theorem cl_w6 : ∀ n : Fin 50, centF (n.val + 7800) < 23 := by decide
private theorem bd_w6 : ∀ n : Fin 50, densSupG (n.val + 7800) < 2 ^ 1771 := by decide
private theorem cs_w7 : ∀ n : Fin 50, centredStar (densSupG (n.val + 7850)) (centF (n.val + 7850)) = true := by decide
private theorem cl_w7 : ∀ n : Fin 50, centF (n.val + 7850) < 23 := by decide
private theorem bd_w7 : ∀ n : Fin 50, densSupG (n.val + 7850) < 2 ^ 1771 := by decide
private theorem cs_w8 : ∀ n : Fin 50, centredStar (densSupG (n.val + 7900)) (centF (n.val + 7900)) = true := by decide
private theorem cl_w8 : ∀ n : Fin 50, centF (n.val + 7900) < 23 := by decide
private theorem bd_w8 : ∀ n : Fin 50, densSupG (n.val + 7900) < 2 ^ 1771 := by decide
private theorem cs_w9 : ∀ n : Fin 50, centredStar (densSupG (n.val + 7950)) (centF (n.val + 7950)) = true := by decide
private theorem cl_w9 : ∀ n : Fin 50, centF (n.val + 7950) < 23 := by decide
private theorem bd_w9 : ∀ n : Fin 50, densSupG (n.val + 7950) < 2 ^ 1771 := by decide
private theorem cs_w10 : ∀ n : Fin 50, centredStar (densSupG (n.val + 8000)) (centF (n.val + 8000)) = true := by decide
private theorem cl_w10 : ∀ n : Fin 50, centF (n.val + 8000) < 23 := by decide
private theorem bd_w10 : ∀ n : Fin 50, densSupG (n.val + 8000) < 2 ^ 1771 := by decide
private theorem cs_w11 : ∀ n : Fin 50, centredStar (densSupG (n.val + 8050)) (centF (n.val + 8050)) = true := by decide
private theorem cl_w11 : ∀ n : Fin 50, centF (n.val + 8050) < 23 := by decide
private theorem bd_w11 : ∀ n : Fin 50, densSupG (n.val + 8050) < 2 ^ 1771 := by decide
private theorem cs_w12 : ∀ n : Fin 50, centredStar (densSupG (n.val + 8100)) (centF (n.val + 8100)) = true := by decide
private theorem cl_w12 : ∀ n : Fin 50, centF (n.val + 8100) < 23 := by decide
private theorem bd_w12 : ∀ n : Fin 50, densSupG (n.val + 8100) < 2 ^ 1771 := by decide
private theorem cs_w13 : ∀ n : Fin 50, centredStar (densSupG (n.val + 8150)) (centF (n.val + 8150)) = true := by decide
private theorem cl_w13 : ∀ n : Fin 50, centF (n.val + 8150) < 23 := by decide
private theorem bd_w13 : ∀ n : Fin 50, densSupG (n.val + 8150) < 2 ^ 1771 := by decide
private theorem cs_w14 : ∀ n : Fin 50, centredStar (densSupG (n.val + 8200)) (centF (n.val + 8200)) = true := by decide
private theorem cl_w14 : ∀ n : Fin 50, centF (n.val + 8200) < 23 := by decide
private theorem bd_w14 : ∀ n : Fin 50, densSupG (n.val + 8200) < 2 ^ 1771 := by decide
private theorem cs_w15 : ∀ n : Fin 50, centredStar (densSupG (n.val + 8250)) (centF (n.val + 8250)) = true := by decide
private theorem cl_w15 : ∀ n : Fin 50, centF (n.val + 8250) < 23 := by decide
private theorem bd_w15 : ∀ n : Fin 50, densSupG (n.val + 8250) < 2 ^ 1771 := by decide
private theorem cs_w16 : ∀ n : Fin 50, centredStar (densSupG (n.val + 8300)) (centF (n.val + 8300)) = true := by decide
private theorem cl_w16 : ∀ n : Fin 50, centF (n.val + 8300) < 23 := by decide
private theorem bd_w16 : ∀ n : Fin 50, densSupG (n.val + 8300) < 2 ^ 1771 := by decide
private theorem cs_w17 : ∀ n : Fin 50, centredStar (densSupG (n.val + 8350)) (centF (n.val + 8350)) = true := by decide
private theorem cl_w17 : ∀ n : Fin 50, centF (n.val + 8350) < 23 := by decide
private theorem bd_w17 : ∀ n : Fin 50, densSupG (n.val + 8350) < 2 ^ 1771 := by decide
private theorem cs_w18 : ∀ n : Fin 50, centredStar (densSupG (n.val + 8400)) (centF (n.val + 8400)) = true := by decide
private theorem cl_w18 : ∀ n : Fin 50, centF (n.val + 8400) < 23 := by decide
private theorem bd_w18 : ∀ n : Fin 50, densSupG (n.val + 8400) < 2 ^ 1771 := by decide
private theorem cs_w19 : ∀ n : Fin 50, centredStar (densSupG (n.val + 8450)) (centF (n.val + 8450)) = true := by decide
private theorem cl_w19 : ∀ n : Fin 50, centF (n.val + 8450) < 23 := by decide
private theorem bd_w19 : ∀ n : Fin 50, densSupG (n.val + 8450) < 2 ^ 1771 := by decide
private theorem cs_w20 : ∀ n : Fin 50, centredStar (densSupG (n.val + 8500)) (centF (n.val + 8500)) = true := by decide
private theorem cl_w20 : ∀ n : Fin 50, centF (n.val + 8500) < 23 := by decide
private theorem bd_w20 : ∀ n : Fin 50, densSupG (n.val + 8500) < 2 ^ 1771 := by decide
private theorem cs_w21 : ∀ n : Fin 50, centredStar (densSupG (n.val + 8550)) (centF (n.val + 8550)) = true := by decide
private theorem cl_w21 : ∀ n : Fin 50, centF (n.val + 8550) < 23 := by decide
private theorem bd_w21 : ∀ n : Fin 50, densSupG (n.val + 8550) < 2 ^ 1771 := by decide
private theorem cs_w22 : ∀ n : Fin 50, centredStar (densSupG (n.val + 8600)) (centF (n.val + 8600)) = true := by decide
private theorem cl_w22 : ∀ n : Fin 50, centF (n.val + 8600) < 23 := by decide
private theorem bd_w22 : ∀ n : Fin 50, densSupG (n.val + 8600) < 2 ^ 1771 := by decide
private theorem cs_w23 : ∀ n : Fin 50, centredStar (densSupG (n.val + 8650)) (centF (n.val + 8650)) = true := by decide
private theorem cl_w23 : ∀ n : Fin 50, centF (n.val + 8650) < 23 := by decide
private theorem bd_w23 : ∀ n : Fin 50, densSupG (n.val + 8650) < 2 ^ 1771 := by decide
private theorem cs_w24 : ∀ n : Fin 50, centredStar (densSupG (n.val + 8700)) (centF (n.val + 8700)) = true := by decide
private theorem cl_w24 : ∀ n : Fin 50, centF (n.val + 8700) < 23 := by decide
private theorem bd_w24 : ∀ n : Fin 50, densSupG (n.val + 8700) < 2 ^ 1771 := by decide
private theorem cs_w25 : ∀ n : Fin 50, centredStar (densSupG (n.val + 8750)) (centF (n.val + 8750)) = true := by decide
private theorem cl_w25 : ∀ n : Fin 50, centF (n.val + 8750) < 23 := by decide
private theorem bd_w25 : ∀ n : Fin 50, densSupG (n.val + 8750) < 2 ^ 1771 := by decide
private theorem cs_w26 : ∀ n : Fin 50, centredStar (densSupG (n.val + 8800)) (centF (n.val + 8800)) = true := by decide
private theorem cl_w26 : ∀ n : Fin 50, centF (n.val + 8800) < 23 := by decide
private theorem bd_w26 : ∀ n : Fin 50, densSupG (n.val + 8800) < 2 ^ 1771 := by decide
private theorem cs_w27 : ∀ n : Fin 50, centredStar (densSupG (n.val + 8850)) (centF (n.val + 8850)) = true := by decide
private theorem cl_w27 : ∀ n : Fin 50, centF (n.val + 8850) < 23 := by decide
private theorem bd_w27 : ∀ n : Fin 50, densSupG (n.val + 8850) < 2 ^ 1771 := by decide
private theorem cs_w28 : ∀ n : Fin 50, centredStar (densSupG (n.val + 8900)) (centF (n.val + 8900)) = true := by decide
private theorem cl_w28 : ∀ n : Fin 50, centF (n.val + 8900) < 23 := by decide
private theorem bd_w28 : ∀ n : Fin 50, densSupG (n.val + 8900) < 2 ^ 1771 := by decide
private theorem cs_w29 : ∀ n : Fin 50, centredStar (densSupG (n.val + 8950)) (centF (n.val + 8950)) = true := by decide
private theorem cl_w29 : ∀ n : Fin 50, centF (n.val + 8950) < 23 := by decide
private theorem bd_w29 : ∀ n : Fin 50, densSupG (n.val + 8950) < 2 ^ 1771 := by decide
private theorem cs_w30 : ∀ n : Fin 50, centredStar (densSupG (n.val + 9000)) (centF (n.val + 9000)) = true := by decide
private theorem cl_w30 : ∀ n : Fin 50, centF (n.val + 9000) < 23 := by decide
private theorem bd_w30 : ∀ n : Fin 50, densSupG (n.val + 9000) < 2 ^ 1771 := by decide
private theorem cs_w31 : ∀ n : Fin 50, centredStar (densSupG (n.val + 9050)) (centF (n.val + 9050)) = true := by decide
private theorem cl_w31 : ∀ n : Fin 50, centF (n.val + 9050) < 23 := by decide
private theorem bd_w31 : ∀ n : Fin 50, densSupG (n.val + 9050) < 2 ^ 1771 := by decide
private theorem cs_w32 : ∀ n : Fin 50, centredStar (densSupG (n.val + 9100)) (centF (n.val + 9100)) = true := by decide
private theorem cl_w32 : ∀ n : Fin 50, centF (n.val + 9100) < 23 := by decide
private theorem bd_w32 : ∀ n : Fin 50, densSupG (n.val + 9100) < 2 ^ 1771 := by decide
private theorem cs_w33 : ∀ n : Fin 50, centredStar (densSupG (n.val + 9150)) (centF (n.val + 9150)) = true := by decide
private theorem cl_w33 : ∀ n : Fin 50, centF (n.val + 9150) < 23 := by decide
private theorem bd_w33 : ∀ n : Fin 50, densSupG (n.val + 9150) < 2 ^ 1771 := by decide
private theorem cs_w34 : ∀ n : Fin 50, centredStar (densSupG (n.val + 9200)) (centF (n.val + 9200)) = true := by decide
private theorem cl_w34 : ∀ n : Fin 50, centF (n.val + 9200) < 23 := by decide
private theorem bd_w34 : ∀ n : Fin 50, densSupG (n.val + 9200) < 2 ^ 1771 := by decide
private theorem cs_w35 : ∀ n : Fin 50, centredStar (densSupG (n.val + 9250)) (centF (n.val + 9250)) = true := by decide
private theorem cl_w35 : ∀ n : Fin 50, centF (n.val + 9250) < 23 := by decide
private theorem bd_w35 : ∀ n : Fin 50, densSupG (n.val + 9250) < 2 ^ 1771 := by decide
private theorem cs_w36 : ∀ n : Fin 50, centredStar (densSupG (n.val + 9300)) (centF (n.val + 9300)) = true := by decide
private theorem cl_w36 : ∀ n : Fin 50, centF (n.val + 9300) < 23 := by decide
private theorem bd_w36 : ∀ n : Fin 50, densSupG (n.val + 9300) < 2 ^ 1771 := by decide
private theorem cs_w37 : ∀ n : Fin 50, centredStar (densSupG (n.val + 9350)) (centF (n.val + 9350)) = true := by decide
private theorem cl_w37 : ∀ n : Fin 50, centF (n.val + 9350) < 23 := by decide
private theorem bd_w37 : ∀ n : Fin 50, densSupG (n.val + 9350) < 2 ^ 1771 := by decide
private theorem cs_w38 : ∀ n : Fin 50, centredStar (densSupG (n.val + 9400)) (centF (n.val + 9400)) = true := by decide
private theorem cl_w38 : ∀ n : Fin 50, centF (n.val + 9400) < 23 := by decide
private theorem bd_w38 : ∀ n : Fin 50, densSupG (n.val + 9400) < 2 ^ 1771 := by decide
private theorem cs_w39 : ∀ n : Fin 50, centredStar (densSupG (n.val + 9450)) (centF (n.val + 9450)) = true := by decide
private theorem cl_w39 : ∀ n : Fin 50, centF (n.val + 9450) < 23 := by decide
private theorem bd_w39 : ∀ n : Fin 50, densSupG (n.val + 9450) < 2 ^ 1771 := by decide
private theorem cs_w40 : ∀ n : Fin 50, centredStar (densSupG (n.val + 9500)) (centF (n.val + 9500)) = true := by decide
private theorem cl_w40 : ∀ n : Fin 50, centF (n.val + 9500) < 23 := by decide
private theorem bd_w40 : ∀ n : Fin 50, densSupG (n.val + 9500) < 2 ^ 1771 := by decide
private theorem cs_w41 : ∀ n : Fin 50, centredStar (densSupG (n.val + 9550)) (centF (n.val + 9550)) = true := by decide
private theorem cl_w41 : ∀ n : Fin 50, centF (n.val + 9550) < 23 := by decide
private theorem bd_w41 : ∀ n : Fin 50, densSupG (n.val + 9550) < 2 ^ 1771 := by decide
private theorem cs_w42 : ∀ n : Fin 50, centredStar (densSupG (n.val + 9600)) (centF (n.val + 9600)) = true := by decide
private theorem cl_w42 : ∀ n : Fin 50, centF (n.val + 9600) < 23 := by decide
private theorem bd_w42 : ∀ n : Fin 50, densSupG (n.val + 9600) < 2 ^ 1771 := by decide
private theorem cs_w43 : ∀ n : Fin 50, centredStar (densSupG (n.val + 9650)) (centF (n.val + 9650)) = true := by decide
private theorem cl_w43 : ∀ n : Fin 50, centF (n.val + 9650) < 23 := by decide
private theorem bd_w43 : ∀ n : Fin 50, densSupG (n.val + 9650) < 2 ^ 1771 := by decide
private theorem cs_w44 : ∀ n : Fin 50, centredStar (densSupG (n.val + 9700)) (centF (n.val + 9700)) = true := by decide
private theorem cl_w44 : ∀ n : Fin 50, centF (n.val + 9700) < 23 := by decide
private theorem bd_w44 : ∀ n : Fin 50, densSupG (n.val + 9700) < 2 ^ 1771 := by decide
private theorem cs_w45 : ∀ n : Fin 50, centredStar (densSupG (n.val + 9750)) (centF (n.val + 9750)) = true := by decide
private theorem cl_w45 : ∀ n : Fin 50, centF (n.val + 9750) < 23 := by decide
private theorem bd_w45 : ∀ n : Fin 50, densSupG (n.val + 9750) < 2 ^ 1771 := by decide
private theorem cs_w46 : ∀ n : Fin 50, centredStar (densSupG (n.val + 9800)) (centF (n.val + 9800)) = true := by decide
private theorem cl_w46 : ∀ n : Fin 50, centF (n.val + 9800) < 23 := by decide
private theorem bd_w46 : ∀ n : Fin 50, densSupG (n.val + 9800) < 2 ^ 1771 := by decide
private theorem cs_w47 : ∀ n : Fin 50, centredStar (densSupG (n.val + 9850)) (centF (n.val + 9850)) = true := by decide
private theorem cl_w47 : ∀ n : Fin 50, centF (n.val + 9850) < 23 := by decide
private theorem bd_w47 : ∀ n : Fin 50, densSupG (n.val + 9850) < 2 ^ 1771 := by decide
private theorem cs_w48 : ∀ n : Fin 50, centredStar (densSupG (n.val + 9900)) (centF (n.val + 9900)) = true := by decide
private theorem cl_w48 : ∀ n : Fin 50, centF (n.val + 9900) < 23 := by decide
private theorem bd_w48 : ∀ n : Fin 50, densSupG (n.val + 9900) < 2 ^ 1771 := by decide
private theorem cs_w49 : ∀ n : Fin 50, centredStar (densSupG (n.val + 9950)) (centF (n.val + 9950)) = true := by decide
private theorem cl_w49 : ∀ n : Fin 50, centF (n.val + 9950) < 23 := by decide
private theorem bd_w49 : ∀ n : Fin 50, densSupG (n.val + 9950) < 2 ^ 1771 := by decide

theorem centredStar_range : ∀ n, 7500 ≤ n → n < 10000 → centredStar (densSupG n) (centF n) = true := by
  intro n hlo hhi
  by_cases h0 : n < 7550
  · have hr : n - 7500 < 50 := by omega
    have heq : n = (n - 7500) + 7500 := by omega
    rw [heq]
    exact cs_w0 ⟨n - 7500, hr⟩
  ·
    by_cases h1 : n < 7600
    ·
      have hr : n - 7550 < 50 := by omega
      have heq : n = (n - 7550) + 7550 := by omega
      rw [heq]
      exact cs_w1 ⟨n - 7550, hr⟩
    ·
      by_cases h2 : n < 7650
      ·
        have hr : n - 7600 < 50 := by omega
        have heq : n = (n - 7600) + 7600 := by omega
        rw [heq]
        exact cs_w2 ⟨n - 7600, hr⟩
      ·
        by_cases h3 : n < 7700
        ·
          have hr : n - 7650 < 50 := by omega
          have heq : n = (n - 7650) + 7650 := by omega
          rw [heq]
          exact cs_w3 ⟨n - 7650, hr⟩
        ·
          by_cases h4 : n < 7750
          ·
            have hr : n - 7700 < 50 := by omega
            have heq : n = (n - 7700) + 7700 := by omega
            rw [heq]
            exact cs_w4 ⟨n - 7700, hr⟩
          ·
            by_cases h5 : n < 7800
            ·
              have hr : n - 7750 < 50 := by omega
              have heq : n = (n - 7750) + 7750 := by omega
              rw [heq]
              exact cs_w5 ⟨n - 7750, hr⟩
            ·
              by_cases h6 : n < 7850
              ·
                have hr : n - 7800 < 50 := by omega
                have heq : n = (n - 7800) + 7800 := by omega
                rw [heq]
                exact cs_w6 ⟨n - 7800, hr⟩
              ·
                by_cases h7 : n < 7900
                ·
                  have hr : n - 7850 < 50 := by omega
                  have heq : n = (n - 7850) + 7850 := by omega
                  rw [heq]
                  exact cs_w7 ⟨n - 7850, hr⟩
                ·
                  by_cases h8 : n < 7950
                  ·
                    have hr : n - 7900 < 50 := by omega
                    have heq : n = (n - 7900) + 7900 := by omega
                    rw [heq]
                    exact cs_w8 ⟨n - 7900, hr⟩
                  ·
                    by_cases h9 : n < 8000
                    ·
                      have hr : n - 7950 < 50 := by omega
                      have heq : n = (n - 7950) + 7950 := by omega
                      rw [heq]
                      exact cs_w9 ⟨n - 7950, hr⟩
                    ·
                      by_cases h10 : n < 8050
                      ·
                        have hr : n - 8000 < 50 := by omega
                        have heq : n = (n - 8000) + 8000 := by omega
                        rw [heq]
                        exact cs_w10 ⟨n - 8000, hr⟩
                      ·
                        by_cases h11 : n < 8100
                        ·
                          have hr : n - 8050 < 50 := by omega
                          have heq : n = (n - 8050) + 8050 := by omega
                          rw [heq]
                          exact cs_w11 ⟨n - 8050, hr⟩
                        ·
                          by_cases h12 : n < 8150
                          ·
                            have hr : n - 8100 < 50 := by omega
                            have heq : n = (n - 8100) + 8100 := by omega
                            rw [heq]
                            exact cs_w12 ⟨n - 8100, hr⟩
                          ·
                            by_cases h13 : n < 8200
                            ·
                              have hr : n - 8150 < 50 := by omega
                              have heq : n = (n - 8150) + 8150 := by omega
                              rw [heq]
                              exact cs_w13 ⟨n - 8150, hr⟩
                            ·
                              by_cases h14 : n < 8250
                              ·
                                have hr : n - 8200 < 50 := by omega
                                have heq : n = (n - 8200) + 8200 := by omega
                                rw [heq]
                                exact cs_w14 ⟨n - 8200, hr⟩
                              ·
                                by_cases h15 : n < 8300
                                ·
                                  have hr : n - 8250 < 50 := by omega
                                  have heq : n = (n - 8250) + 8250 := by omega
                                  rw [heq]
                                  exact cs_w15 ⟨n - 8250, hr⟩
                                ·
                                  by_cases h16 : n < 8350
                                  ·
                                    have hr : n - 8300 < 50 := by omega
                                    have heq : n = (n - 8300) + 8300 := by omega
                                    rw [heq]
                                    exact cs_w16 ⟨n - 8300, hr⟩
                                  ·
                                    by_cases h17 : n < 8400
                                    ·
                                      have hr : n - 8350 < 50 := by omega
                                      have heq : n = (n - 8350) + 8350 := by omega
                                      rw [heq]
                                      exact cs_w17 ⟨n - 8350, hr⟩
                                    ·
                                      by_cases h18 : n < 8450
                                      ·
                                        have hr : n - 8400 < 50 := by omega
                                        have heq : n = (n - 8400) + 8400 := by omega
                                        rw [heq]
                                        exact cs_w18 ⟨n - 8400, hr⟩
                                      ·
                                        by_cases h19 : n < 8500
                                        ·
                                          have hr : n - 8450 < 50 := by omega
                                          have heq : n = (n - 8450) + 8450 := by omega
                                          rw [heq]
                                          exact cs_w19 ⟨n - 8450, hr⟩
                                        ·
                                          by_cases h20 : n < 8550
                                          ·
                                            have hr : n - 8500 < 50 := by omega
                                            have heq : n = (n - 8500) + 8500 := by omega
                                            rw [heq]
                                            exact cs_w20 ⟨n - 8500, hr⟩
                                          ·
                                            by_cases h21 : n < 8600
                                            ·
                                              have hr : n - 8550 < 50 := by omega
                                              have heq : n = (n - 8550) + 8550 := by omega
                                              rw [heq]
                                              exact cs_w21 ⟨n - 8550, hr⟩
                                            ·
                                              by_cases h22 : n < 8650
                                              ·
                                                have hr : n - 8600 < 50 := by omega
                                                have heq : n = (n - 8600) + 8600 := by omega
                                                rw [heq]
                                                exact cs_w22 ⟨n - 8600, hr⟩
                                              ·
                                                by_cases h23 : n < 8700
                                                ·
                                                  have hr : n - 8650 < 50 := by omega
                                                  have heq : n = (n - 8650) + 8650 := by omega
                                                  rw [heq]
                                                  exact cs_w23 ⟨n - 8650, hr⟩
                                                ·
                                                  by_cases h24 : n < 8750
                                                  ·
                                                    have hr : n - 8700 < 50 := by omega
                                                    have heq : n = (n - 8700) + 8700 := by omega
                                                    rw [heq]
                                                    exact cs_w24 ⟨n - 8700, hr⟩
                                                  ·
                                                    by_cases h25 : n < 8800
                                                    ·
                                                      have hr : n - 8750 < 50 := by omega
                                                      have heq : n = (n - 8750) + 8750 := by omega
                                                      rw [heq]
                                                      exact cs_w25 ⟨n - 8750, hr⟩
                                                    ·
                                                      by_cases h26 : n < 8850
                                                      ·
                                                        have hr : n - 8800 < 50 := by omega
                                                        have heq : n = (n - 8800) + 8800 := by omega
                                                        rw [heq]
                                                        exact cs_w26 ⟨n - 8800, hr⟩
                                                      ·
                                                        by_cases h27 : n < 8900
                                                        ·
                                                          have hr : n - 8850 < 50 := by omega
                                                          have heq : n = (n - 8850) + 8850 := by omega
                                                          rw [heq]
                                                          exact cs_w27 ⟨n - 8850, hr⟩
                                                        ·
                                                          by_cases h28 : n < 8950
                                                          ·
                                                            have hr : n - 8900 < 50 := by omega
                                                            have heq : n = (n - 8900) + 8900 := by omega
                                                            rw [heq]
                                                            exact cs_w28 ⟨n - 8900, hr⟩
                                                          ·
                                                            by_cases h29 : n < 9000
                                                            ·
                                                              have hr : n - 8950 < 50 := by omega
                                                              have heq : n = (n - 8950) + 8950 := by omega
                                                              rw [heq]
                                                              exact cs_w29 ⟨n - 8950, hr⟩
                                                            ·
                                                              by_cases h30 : n < 9050
                                                              ·
                                                                have hr : n - 9000 < 50 := by omega
                                                                have heq : n = (n - 9000) + 9000 := by omega
                                                                rw [heq]
                                                                exact cs_w30 ⟨n - 9000, hr⟩
                                                              ·
                                                                by_cases h31 : n < 9100
                                                                ·
                                                                  have hr : n - 9050 < 50 := by omega
                                                                  have heq : n = (n - 9050) + 9050 := by omega
                                                                  rw [heq]
                                                                  exact cs_w31 ⟨n - 9050, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 9150
                                                                  ·
                                                                    have hr : n - 9100 < 50 := by omega
                                                                    have heq : n = (n - 9100) + 9100 := by omega
                                                                    rw [heq]
                                                                    exact cs_w32 ⟨n - 9100, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 9200
                                                                    ·
                                                                      have hr : n - 9150 < 50 := by omega
                                                                      have heq : n = (n - 9150) + 9150 := by omega
                                                                      rw [heq]
                                                                      exact cs_w33 ⟨n - 9150, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 9250
                                                                      ·
                                                                        have hr : n - 9200 < 50 := by omega
                                                                        have heq : n = (n - 9200) + 9200 := by omega
                                                                        rw [heq]
                                                                        exact cs_w34 ⟨n - 9200, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 9300
                                                                        ·
                                                                          have hr : n - 9250 < 50 := by omega
                                                                          have heq : n = (n - 9250) + 9250 := by omega
                                                                          rw [heq]
                                                                          exact cs_w35 ⟨n - 9250, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 9350
                                                                          ·
                                                                            have hr : n - 9300 < 50 := by omega
                                                                            have heq : n = (n - 9300) + 9300 := by omega
                                                                            rw [heq]
                                                                            exact cs_w36 ⟨n - 9300, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 9400
                                                                            ·
                                                                              have hr : n - 9350 < 50 := by omega
                                                                              have heq : n = (n - 9350) + 9350 := by omega
                                                                              rw [heq]
                                                                              exact cs_w37 ⟨n - 9350, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 9450
                                                                              ·
                                                                                have hr : n - 9400 < 50 := by omega
                                                                                have heq : n = (n - 9400) + 9400 := by omega
                                                                                rw [heq]
                                                                                exact cs_w38 ⟨n - 9400, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 9500
                                                                                ·
                                                                                  have hr : n - 9450 < 50 := by omega
                                                                                  have heq : n = (n - 9450) + 9450 := by omega
                                                                                  rw [heq]
                                                                                  exact cs_w39 ⟨n - 9450, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 9550
                                                                                  ·
                                                                                    have hr : n - 9500 < 50 := by omega
                                                                                    have heq : n = (n - 9500) + 9500 := by omega
                                                                                    rw [heq]
                                                                                    exact cs_w40 ⟨n - 9500, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 9600
                                                                                    ·
                                                                                      have hr : n - 9550 < 50 := by omega
                                                                                      have heq : n = (n - 9550) + 9550 := by omega
                                                                                      rw [heq]
                                                                                      exact cs_w41 ⟨n - 9550, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 9650
                                                                                      ·
                                                                                        have hr : n - 9600 < 50 := by omega
                                                                                        have heq : n = (n - 9600) + 9600 := by omega
                                                                                        rw [heq]
                                                                                        exact cs_w42 ⟨n - 9600, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 9700
                                                                                        ·
                                                                                          have hr : n - 9650 < 50 := by omega
                                                                                          have heq : n = (n - 9650) + 9650 := by omega
                                                                                          rw [heq]
                                                                                          exact cs_w43 ⟨n - 9650, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 9750
                                                                                          ·
                                                                                            have hr : n - 9700 < 50 := by omega
                                                                                            have heq : n = (n - 9700) + 9700 := by omega
                                                                                            rw [heq]
                                                                                            exact cs_w44 ⟨n - 9700, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 9800
                                                                                            ·
                                                                                              have hr : n - 9750 < 50 := by omega
                                                                                              have heq : n = (n - 9750) + 9750 := by omega
                                                                                              rw [heq]
                                                                                              exact cs_w45 ⟨n - 9750, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 9850
                                                                                              ·
                                                                                                have hr : n - 9800 < 50 := by omega
                                                                                                have heq : n = (n - 9800) + 9800 := by omega
                                                                                                rw [heq]
                                                                                                exact cs_w46 ⟨n - 9800, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 9900
                                                                                                ·
                                                                                                  have hr : n - 9850 < 50 := by omega
                                                                                                  have heq : n = (n - 9850) + 9850 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cs_w47 ⟨n - 9850, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 9950
                                                                                                  ·
                                                                                                    have hr : n - 9900 < 50 := by omega
                                                                                                    have heq : n = (n - 9900) + 9900 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w48 ⟨n - 9900, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 9950 < 50 := by omega
                                                                                                    have heq : n = (n - 9950) + 9950 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w49 ⟨n - 9950, hr⟩

theorem centF_lt_range : ∀ n, 7500 ≤ n → n < 10000 → centF n < 23 := by
  intro n hlo hhi
  by_cases h0 : n < 7550
  · have hr : n - 7500 < 50 := by omega
    have heq : n = (n - 7500) + 7500 := by omega
    rw [heq]
    exact cl_w0 ⟨n - 7500, hr⟩
  ·
    by_cases h1 : n < 7600
    ·
      have hr : n - 7550 < 50 := by omega
      have heq : n = (n - 7550) + 7550 := by omega
      rw [heq]
      exact cl_w1 ⟨n - 7550, hr⟩
    ·
      by_cases h2 : n < 7650
      ·
        have hr : n - 7600 < 50 := by omega
        have heq : n = (n - 7600) + 7600 := by omega
        rw [heq]
        exact cl_w2 ⟨n - 7600, hr⟩
      ·
        by_cases h3 : n < 7700
        ·
          have hr : n - 7650 < 50 := by omega
          have heq : n = (n - 7650) + 7650 := by omega
          rw [heq]
          exact cl_w3 ⟨n - 7650, hr⟩
        ·
          by_cases h4 : n < 7750
          ·
            have hr : n - 7700 < 50 := by omega
            have heq : n = (n - 7700) + 7700 := by omega
            rw [heq]
            exact cl_w4 ⟨n - 7700, hr⟩
          ·
            by_cases h5 : n < 7800
            ·
              have hr : n - 7750 < 50 := by omega
              have heq : n = (n - 7750) + 7750 := by omega
              rw [heq]
              exact cl_w5 ⟨n - 7750, hr⟩
            ·
              by_cases h6 : n < 7850
              ·
                have hr : n - 7800 < 50 := by omega
                have heq : n = (n - 7800) + 7800 := by omega
                rw [heq]
                exact cl_w6 ⟨n - 7800, hr⟩
              ·
                by_cases h7 : n < 7900
                ·
                  have hr : n - 7850 < 50 := by omega
                  have heq : n = (n - 7850) + 7850 := by omega
                  rw [heq]
                  exact cl_w7 ⟨n - 7850, hr⟩
                ·
                  by_cases h8 : n < 7950
                  ·
                    have hr : n - 7900 < 50 := by omega
                    have heq : n = (n - 7900) + 7900 := by omega
                    rw [heq]
                    exact cl_w8 ⟨n - 7900, hr⟩
                  ·
                    by_cases h9 : n < 8000
                    ·
                      have hr : n - 7950 < 50 := by omega
                      have heq : n = (n - 7950) + 7950 := by omega
                      rw [heq]
                      exact cl_w9 ⟨n - 7950, hr⟩
                    ·
                      by_cases h10 : n < 8050
                      ·
                        have hr : n - 8000 < 50 := by omega
                        have heq : n = (n - 8000) + 8000 := by omega
                        rw [heq]
                        exact cl_w10 ⟨n - 8000, hr⟩
                      ·
                        by_cases h11 : n < 8100
                        ·
                          have hr : n - 8050 < 50 := by omega
                          have heq : n = (n - 8050) + 8050 := by omega
                          rw [heq]
                          exact cl_w11 ⟨n - 8050, hr⟩
                        ·
                          by_cases h12 : n < 8150
                          ·
                            have hr : n - 8100 < 50 := by omega
                            have heq : n = (n - 8100) + 8100 := by omega
                            rw [heq]
                            exact cl_w12 ⟨n - 8100, hr⟩
                          ·
                            by_cases h13 : n < 8200
                            ·
                              have hr : n - 8150 < 50 := by omega
                              have heq : n = (n - 8150) + 8150 := by omega
                              rw [heq]
                              exact cl_w13 ⟨n - 8150, hr⟩
                            ·
                              by_cases h14 : n < 8250
                              ·
                                have hr : n - 8200 < 50 := by omega
                                have heq : n = (n - 8200) + 8200 := by omega
                                rw [heq]
                                exact cl_w14 ⟨n - 8200, hr⟩
                              ·
                                by_cases h15 : n < 8300
                                ·
                                  have hr : n - 8250 < 50 := by omega
                                  have heq : n = (n - 8250) + 8250 := by omega
                                  rw [heq]
                                  exact cl_w15 ⟨n - 8250, hr⟩
                                ·
                                  by_cases h16 : n < 8350
                                  ·
                                    have hr : n - 8300 < 50 := by omega
                                    have heq : n = (n - 8300) + 8300 := by omega
                                    rw [heq]
                                    exact cl_w16 ⟨n - 8300, hr⟩
                                  ·
                                    by_cases h17 : n < 8400
                                    ·
                                      have hr : n - 8350 < 50 := by omega
                                      have heq : n = (n - 8350) + 8350 := by omega
                                      rw [heq]
                                      exact cl_w17 ⟨n - 8350, hr⟩
                                    ·
                                      by_cases h18 : n < 8450
                                      ·
                                        have hr : n - 8400 < 50 := by omega
                                        have heq : n = (n - 8400) + 8400 := by omega
                                        rw [heq]
                                        exact cl_w18 ⟨n - 8400, hr⟩
                                      ·
                                        by_cases h19 : n < 8500
                                        ·
                                          have hr : n - 8450 < 50 := by omega
                                          have heq : n = (n - 8450) + 8450 := by omega
                                          rw [heq]
                                          exact cl_w19 ⟨n - 8450, hr⟩
                                        ·
                                          by_cases h20 : n < 8550
                                          ·
                                            have hr : n - 8500 < 50 := by omega
                                            have heq : n = (n - 8500) + 8500 := by omega
                                            rw [heq]
                                            exact cl_w20 ⟨n - 8500, hr⟩
                                          ·
                                            by_cases h21 : n < 8600
                                            ·
                                              have hr : n - 8550 < 50 := by omega
                                              have heq : n = (n - 8550) + 8550 := by omega
                                              rw [heq]
                                              exact cl_w21 ⟨n - 8550, hr⟩
                                            ·
                                              by_cases h22 : n < 8650
                                              ·
                                                have hr : n - 8600 < 50 := by omega
                                                have heq : n = (n - 8600) + 8600 := by omega
                                                rw [heq]
                                                exact cl_w22 ⟨n - 8600, hr⟩
                                              ·
                                                by_cases h23 : n < 8700
                                                ·
                                                  have hr : n - 8650 < 50 := by omega
                                                  have heq : n = (n - 8650) + 8650 := by omega
                                                  rw [heq]
                                                  exact cl_w23 ⟨n - 8650, hr⟩
                                                ·
                                                  by_cases h24 : n < 8750
                                                  ·
                                                    have hr : n - 8700 < 50 := by omega
                                                    have heq : n = (n - 8700) + 8700 := by omega
                                                    rw [heq]
                                                    exact cl_w24 ⟨n - 8700, hr⟩
                                                  ·
                                                    by_cases h25 : n < 8800
                                                    ·
                                                      have hr : n - 8750 < 50 := by omega
                                                      have heq : n = (n - 8750) + 8750 := by omega
                                                      rw [heq]
                                                      exact cl_w25 ⟨n - 8750, hr⟩
                                                    ·
                                                      by_cases h26 : n < 8850
                                                      ·
                                                        have hr : n - 8800 < 50 := by omega
                                                        have heq : n = (n - 8800) + 8800 := by omega
                                                        rw [heq]
                                                        exact cl_w26 ⟨n - 8800, hr⟩
                                                      ·
                                                        by_cases h27 : n < 8900
                                                        ·
                                                          have hr : n - 8850 < 50 := by omega
                                                          have heq : n = (n - 8850) + 8850 := by omega
                                                          rw [heq]
                                                          exact cl_w27 ⟨n - 8850, hr⟩
                                                        ·
                                                          by_cases h28 : n < 8950
                                                          ·
                                                            have hr : n - 8900 < 50 := by omega
                                                            have heq : n = (n - 8900) + 8900 := by omega
                                                            rw [heq]
                                                            exact cl_w28 ⟨n - 8900, hr⟩
                                                          ·
                                                            by_cases h29 : n < 9000
                                                            ·
                                                              have hr : n - 8950 < 50 := by omega
                                                              have heq : n = (n - 8950) + 8950 := by omega
                                                              rw [heq]
                                                              exact cl_w29 ⟨n - 8950, hr⟩
                                                            ·
                                                              by_cases h30 : n < 9050
                                                              ·
                                                                have hr : n - 9000 < 50 := by omega
                                                                have heq : n = (n - 9000) + 9000 := by omega
                                                                rw [heq]
                                                                exact cl_w30 ⟨n - 9000, hr⟩
                                                              ·
                                                                by_cases h31 : n < 9100
                                                                ·
                                                                  have hr : n - 9050 < 50 := by omega
                                                                  have heq : n = (n - 9050) + 9050 := by omega
                                                                  rw [heq]
                                                                  exact cl_w31 ⟨n - 9050, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 9150
                                                                  ·
                                                                    have hr : n - 9100 < 50 := by omega
                                                                    have heq : n = (n - 9100) + 9100 := by omega
                                                                    rw [heq]
                                                                    exact cl_w32 ⟨n - 9100, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 9200
                                                                    ·
                                                                      have hr : n - 9150 < 50 := by omega
                                                                      have heq : n = (n - 9150) + 9150 := by omega
                                                                      rw [heq]
                                                                      exact cl_w33 ⟨n - 9150, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 9250
                                                                      ·
                                                                        have hr : n - 9200 < 50 := by omega
                                                                        have heq : n = (n - 9200) + 9200 := by omega
                                                                        rw [heq]
                                                                        exact cl_w34 ⟨n - 9200, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 9300
                                                                        ·
                                                                          have hr : n - 9250 < 50 := by omega
                                                                          have heq : n = (n - 9250) + 9250 := by omega
                                                                          rw [heq]
                                                                          exact cl_w35 ⟨n - 9250, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 9350
                                                                          ·
                                                                            have hr : n - 9300 < 50 := by omega
                                                                            have heq : n = (n - 9300) + 9300 := by omega
                                                                            rw [heq]
                                                                            exact cl_w36 ⟨n - 9300, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 9400
                                                                            ·
                                                                              have hr : n - 9350 < 50 := by omega
                                                                              have heq : n = (n - 9350) + 9350 := by omega
                                                                              rw [heq]
                                                                              exact cl_w37 ⟨n - 9350, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 9450
                                                                              ·
                                                                                have hr : n - 9400 < 50 := by omega
                                                                                have heq : n = (n - 9400) + 9400 := by omega
                                                                                rw [heq]
                                                                                exact cl_w38 ⟨n - 9400, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 9500
                                                                                ·
                                                                                  have hr : n - 9450 < 50 := by omega
                                                                                  have heq : n = (n - 9450) + 9450 := by omega
                                                                                  rw [heq]
                                                                                  exact cl_w39 ⟨n - 9450, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 9550
                                                                                  ·
                                                                                    have hr : n - 9500 < 50 := by omega
                                                                                    have heq : n = (n - 9500) + 9500 := by omega
                                                                                    rw [heq]
                                                                                    exact cl_w40 ⟨n - 9500, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 9600
                                                                                    ·
                                                                                      have hr : n - 9550 < 50 := by omega
                                                                                      have heq : n = (n - 9550) + 9550 := by omega
                                                                                      rw [heq]
                                                                                      exact cl_w41 ⟨n - 9550, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 9650
                                                                                      ·
                                                                                        have hr : n - 9600 < 50 := by omega
                                                                                        have heq : n = (n - 9600) + 9600 := by omega
                                                                                        rw [heq]
                                                                                        exact cl_w42 ⟨n - 9600, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 9700
                                                                                        ·
                                                                                          have hr : n - 9650 < 50 := by omega
                                                                                          have heq : n = (n - 9650) + 9650 := by omega
                                                                                          rw [heq]
                                                                                          exact cl_w43 ⟨n - 9650, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 9750
                                                                                          ·
                                                                                            have hr : n - 9700 < 50 := by omega
                                                                                            have heq : n = (n - 9700) + 9700 := by omega
                                                                                            rw [heq]
                                                                                            exact cl_w44 ⟨n - 9700, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 9800
                                                                                            ·
                                                                                              have hr : n - 9750 < 50 := by omega
                                                                                              have heq : n = (n - 9750) + 9750 := by omega
                                                                                              rw [heq]
                                                                                              exact cl_w45 ⟨n - 9750, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 9850
                                                                                              ·
                                                                                                have hr : n - 9800 < 50 := by omega
                                                                                                have heq : n = (n - 9800) + 9800 := by omega
                                                                                                rw [heq]
                                                                                                exact cl_w46 ⟨n - 9800, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 9900
                                                                                                ·
                                                                                                  have hr : n - 9850 < 50 := by omega
                                                                                                  have heq : n = (n - 9850) + 9850 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cl_w47 ⟨n - 9850, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 9950
                                                                                                  ·
                                                                                                    have hr : n - 9900 < 50 := by omega
                                                                                                    have heq : n = (n - 9900) + 9900 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w48 ⟨n - 9900, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 9950 < 50 := by omega
                                                                                                    have heq : n = (n - 9950) + 9950 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w49 ⟨n - 9950, hr⟩

theorem densSupG_lt_range : ∀ n, 7500 ≤ n → n < 10000 → densSupG n < 2 ^ 1771 := by
  intro n hlo hhi
  by_cases h0 : n < 7550
  · have hr : n - 7500 < 50 := by omega
    have heq : n = (n - 7500) + 7500 := by omega
    rw [heq]
    exact bd_w0 ⟨n - 7500, hr⟩
  ·
    by_cases h1 : n < 7600
    ·
      have hr : n - 7550 < 50 := by omega
      have heq : n = (n - 7550) + 7550 := by omega
      rw [heq]
      exact bd_w1 ⟨n - 7550, hr⟩
    ·
      by_cases h2 : n < 7650
      ·
        have hr : n - 7600 < 50 := by omega
        have heq : n = (n - 7600) + 7600 := by omega
        rw [heq]
        exact bd_w2 ⟨n - 7600, hr⟩
      ·
        by_cases h3 : n < 7700
        ·
          have hr : n - 7650 < 50 := by omega
          have heq : n = (n - 7650) + 7650 := by omega
          rw [heq]
          exact bd_w3 ⟨n - 7650, hr⟩
        ·
          by_cases h4 : n < 7750
          ·
            have hr : n - 7700 < 50 := by omega
            have heq : n = (n - 7700) + 7700 := by omega
            rw [heq]
            exact bd_w4 ⟨n - 7700, hr⟩
          ·
            by_cases h5 : n < 7800
            ·
              have hr : n - 7750 < 50 := by omega
              have heq : n = (n - 7750) + 7750 := by omega
              rw [heq]
              exact bd_w5 ⟨n - 7750, hr⟩
            ·
              by_cases h6 : n < 7850
              ·
                have hr : n - 7800 < 50 := by omega
                have heq : n = (n - 7800) + 7800 := by omega
                rw [heq]
                exact bd_w6 ⟨n - 7800, hr⟩
              ·
                by_cases h7 : n < 7900
                ·
                  have hr : n - 7850 < 50 := by omega
                  have heq : n = (n - 7850) + 7850 := by omega
                  rw [heq]
                  exact bd_w7 ⟨n - 7850, hr⟩
                ·
                  by_cases h8 : n < 7950
                  ·
                    have hr : n - 7900 < 50 := by omega
                    have heq : n = (n - 7900) + 7900 := by omega
                    rw [heq]
                    exact bd_w8 ⟨n - 7900, hr⟩
                  ·
                    by_cases h9 : n < 8000
                    ·
                      have hr : n - 7950 < 50 := by omega
                      have heq : n = (n - 7950) + 7950 := by omega
                      rw [heq]
                      exact bd_w9 ⟨n - 7950, hr⟩
                    ·
                      by_cases h10 : n < 8050
                      ·
                        have hr : n - 8000 < 50 := by omega
                        have heq : n = (n - 8000) + 8000 := by omega
                        rw [heq]
                        exact bd_w10 ⟨n - 8000, hr⟩
                      ·
                        by_cases h11 : n < 8100
                        ·
                          have hr : n - 8050 < 50 := by omega
                          have heq : n = (n - 8050) + 8050 := by omega
                          rw [heq]
                          exact bd_w11 ⟨n - 8050, hr⟩
                        ·
                          by_cases h12 : n < 8150
                          ·
                            have hr : n - 8100 < 50 := by omega
                            have heq : n = (n - 8100) + 8100 := by omega
                            rw [heq]
                            exact bd_w12 ⟨n - 8100, hr⟩
                          ·
                            by_cases h13 : n < 8200
                            ·
                              have hr : n - 8150 < 50 := by omega
                              have heq : n = (n - 8150) + 8150 := by omega
                              rw [heq]
                              exact bd_w13 ⟨n - 8150, hr⟩
                            ·
                              by_cases h14 : n < 8250
                              ·
                                have hr : n - 8200 < 50 := by omega
                                have heq : n = (n - 8200) + 8200 := by omega
                                rw [heq]
                                exact bd_w14 ⟨n - 8200, hr⟩
                              ·
                                by_cases h15 : n < 8300
                                ·
                                  have hr : n - 8250 < 50 := by omega
                                  have heq : n = (n - 8250) + 8250 := by omega
                                  rw [heq]
                                  exact bd_w15 ⟨n - 8250, hr⟩
                                ·
                                  by_cases h16 : n < 8350
                                  ·
                                    have hr : n - 8300 < 50 := by omega
                                    have heq : n = (n - 8300) + 8300 := by omega
                                    rw [heq]
                                    exact bd_w16 ⟨n - 8300, hr⟩
                                  ·
                                    by_cases h17 : n < 8400
                                    ·
                                      have hr : n - 8350 < 50 := by omega
                                      have heq : n = (n - 8350) + 8350 := by omega
                                      rw [heq]
                                      exact bd_w17 ⟨n - 8350, hr⟩
                                    ·
                                      by_cases h18 : n < 8450
                                      ·
                                        have hr : n - 8400 < 50 := by omega
                                        have heq : n = (n - 8400) + 8400 := by omega
                                        rw [heq]
                                        exact bd_w18 ⟨n - 8400, hr⟩
                                      ·
                                        by_cases h19 : n < 8500
                                        ·
                                          have hr : n - 8450 < 50 := by omega
                                          have heq : n = (n - 8450) + 8450 := by omega
                                          rw [heq]
                                          exact bd_w19 ⟨n - 8450, hr⟩
                                        ·
                                          by_cases h20 : n < 8550
                                          ·
                                            have hr : n - 8500 < 50 := by omega
                                            have heq : n = (n - 8500) + 8500 := by omega
                                            rw [heq]
                                            exact bd_w20 ⟨n - 8500, hr⟩
                                          ·
                                            by_cases h21 : n < 8600
                                            ·
                                              have hr : n - 8550 < 50 := by omega
                                              have heq : n = (n - 8550) + 8550 := by omega
                                              rw [heq]
                                              exact bd_w21 ⟨n - 8550, hr⟩
                                            ·
                                              by_cases h22 : n < 8650
                                              ·
                                                have hr : n - 8600 < 50 := by omega
                                                have heq : n = (n - 8600) + 8600 := by omega
                                                rw [heq]
                                                exact bd_w22 ⟨n - 8600, hr⟩
                                              ·
                                                by_cases h23 : n < 8700
                                                ·
                                                  have hr : n - 8650 < 50 := by omega
                                                  have heq : n = (n - 8650) + 8650 := by omega
                                                  rw [heq]
                                                  exact bd_w23 ⟨n - 8650, hr⟩
                                                ·
                                                  by_cases h24 : n < 8750
                                                  ·
                                                    have hr : n - 8700 < 50 := by omega
                                                    have heq : n = (n - 8700) + 8700 := by omega
                                                    rw [heq]
                                                    exact bd_w24 ⟨n - 8700, hr⟩
                                                  ·
                                                    by_cases h25 : n < 8800
                                                    ·
                                                      have hr : n - 8750 < 50 := by omega
                                                      have heq : n = (n - 8750) + 8750 := by omega
                                                      rw [heq]
                                                      exact bd_w25 ⟨n - 8750, hr⟩
                                                    ·
                                                      by_cases h26 : n < 8850
                                                      ·
                                                        have hr : n - 8800 < 50 := by omega
                                                        have heq : n = (n - 8800) + 8800 := by omega
                                                        rw [heq]
                                                        exact bd_w26 ⟨n - 8800, hr⟩
                                                      ·
                                                        by_cases h27 : n < 8900
                                                        ·
                                                          have hr : n - 8850 < 50 := by omega
                                                          have heq : n = (n - 8850) + 8850 := by omega
                                                          rw [heq]
                                                          exact bd_w27 ⟨n - 8850, hr⟩
                                                        ·
                                                          by_cases h28 : n < 8950
                                                          ·
                                                            have hr : n - 8900 < 50 := by omega
                                                            have heq : n = (n - 8900) + 8900 := by omega
                                                            rw [heq]
                                                            exact bd_w28 ⟨n - 8900, hr⟩
                                                          ·
                                                            by_cases h29 : n < 9000
                                                            ·
                                                              have hr : n - 8950 < 50 := by omega
                                                              have heq : n = (n - 8950) + 8950 := by omega
                                                              rw [heq]
                                                              exact bd_w29 ⟨n - 8950, hr⟩
                                                            ·
                                                              by_cases h30 : n < 9050
                                                              ·
                                                                have hr : n - 9000 < 50 := by omega
                                                                have heq : n = (n - 9000) + 9000 := by omega
                                                                rw [heq]
                                                                exact bd_w30 ⟨n - 9000, hr⟩
                                                              ·
                                                                by_cases h31 : n < 9100
                                                                ·
                                                                  have hr : n - 9050 < 50 := by omega
                                                                  have heq : n = (n - 9050) + 9050 := by omega
                                                                  rw [heq]
                                                                  exact bd_w31 ⟨n - 9050, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 9150
                                                                  ·
                                                                    have hr : n - 9100 < 50 := by omega
                                                                    have heq : n = (n - 9100) + 9100 := by omega
                                                                    rw [heq]
                                                                    exact bd_w32 ⟨n - 9100, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 9200
                                                                    ·
                                                                      have hr : n - 9150 < 50 := by omega
                                                                      have heq : n = (n - 9150) + 9150 := by omega
                                                                      rw [heq]
                                                                      exact bd_w33 ⟨n - 9150, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 9250
                                                                      ·
                                                                        have hr : n - 9200 < 50 := by omega
                                                                        have heq : n = (n - 9200) + 9200 := by omega
                                                                        rw [heq]
                                                                        exact bd_w34 ⟨n - 9200, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 9300
                                                                        ·
                                                                          have hr : n - 9250 < 50 := by omega
                                                                          have heq : n = (n - 9250) + 9250 := by omega
                                                                          rw [heq]
                                                                          exact bd_w35 ⟨n - 9250, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 9350
                                                                          ·
                                                                            have hr : n - 9300 < 50 := by omega
                                                                            have heq : n = (n - 9300) + 9300 := by omega
                                                                            rw [heq]
                                                                            exact bd_w36 ⟨n - 9300, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 9400
                                                                            ·
                                                                              have hr : n - 9350 < 50 := by omega
                                                                              have heq : n = (n - 9350) + 9350 := by omega
                                                                              rw [heq]
                                                                              exact bd_w37 ⟨n - 9350, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 9450
                                                                              ·
                                                                                have hr : n - 9400 < 50 := by omega
                                                                                have heq : n = (n - 9400) + 9400 := by omega
                                                                                rw [heq]
                                                                                exact bd_w38 ⟨n - 9400, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 9500
                                                                                ·
                                                                                  have hr : n - 9450 < 50 := by omega
                                                                                  have heq : n = (n - 9450) + 9450 := by omega
                                                                                  rw [heq]
                                                                                  exact bd_w39 ⟨n - 9450, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 9550
                                                                                  ·
                                                                                    have hr : n - 9500 < 50 := by omega
                                                                                    have heq : n = (n - 9500) + 9500 := by omega
                                                                                    rw [heq]
                                                                                    exact bd_w40 ⟨n - 9500, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 9600
                                                                                    ·
                                                                                      have hr : n - 9550 < 50 := by omega
                                                                                      have heq : n = (n - 9550) + 9550 := by omega
                                                                                      rw [heq]
                                                                                      exact bd_w41 ⟨n - 9550, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 9650
                                                                                      ·
                                                                                        have hr : n - 9600 < 50 := by omega
                                                                                        have heq : n = (n - 9600) + 9600 := by omega
                                                                                        rw [heq]
                                                                                        exact bd_w42 ⟨n - 9600, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 9700
                                                                                        ·
                                                                                          have hr : n - 9650 < 50 := by omega
                                                                                          have heq : n = (n - 9650) + 9650 := by omega
                                                                                          rw [heq]
                                                                                          exact bd_w43 ⟨n - 9650, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 9750
                                                                                          ·
                                                                                            have hr : n - 9700 < 50 := by omega
                                                                                            have heq : n = (n - 9700) + 9700 := by omega
                                                                                            rw [heq]
                                                                                            exact bd_w44 ⟨n - 9700, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 9800
                                                                                            ·
                                                                                              have hr : n - 9750 < 50 := by omega
                                                                                              have heq : n = (n - 9750) + 9750 := by omega
                                                                                              rw [heq]
                                                                                              exact bd_w45 ⟨n - 9750, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 9850
                                                                                              ·
                                                                                                have hr : n - 9800 < 50 := by omega
                                                                                                have heq : n = (n - 9800) + 9800 := by omega
                                                                                                rw [heq]
                                                                                                exact bd_w46 ⟨n - 9800, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 9900
                                                                                                ·
                                                                                                  have hr : n - 9850 < 50 := by omega
                                                                                                  have heq : n = (n - 9850) + 9850 := by omega
                                                                                                  rw [heq]
                                                                                                  exact bd_w47 ⟨n - 9850, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 9950
                                                                                                  ·
                                                                                                    have hr : n - 9900 < 50 := by omega
                                                                                                    have heq : n = (n - 9900) + 9900 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w48 ⟨n - 9900, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 9950 < 50 := by omega
                                                                                                    have heq : n = (n - 9950) + 9950 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w49 ⟨n - 9950, hr⟩


end IntMul.Kappa.R8.Bit.Oppbank.CentBound1b


