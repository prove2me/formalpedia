-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound1a
-- name    : IntMul_Kappa_R8_Data_BitOppbankCentBound1a
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:55:21.951853+00:00
-- url     : https://prove2.me/theorems/165db59d-ac3e-447b-96cd-41cf0089e3d4
-- title:
--   HasCentre certificates dens nodes [5000,7500)
-- statement:
--   # Densified centre certificates, pack 1a
--
--   For every densified node index $n$ with $5000\le n<7500$,
--   $$
--   \mathrm{centredStar}(\mathrm{densSupG}\,n,\mathrm{centF}\,n)=\mathsf{true},\quad
--   \mathrm{centF}\,n<23,\quad
--   \mathrm{densSupG}\,n < 2^{1771}.
--   $$
--   Proved by decide on Fin 50 windows (no native_decide). Half-pack split of CentBound1 for server compile budget.
-- source:
--   R8 BitOppbank AllDensCentred; jfstack_23 densified supports

-- CentBound pack 1a: densified HasCentre certificates on n ∈ [5000, 7500)
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

namespace IntMul.Kappa.R8.Bit.Oppbank.CentBound1a

private theorem cs_w0 : ∀ n : Fin 50, centredStar (densSupG (n.val + 5000)) (centF (n.val + 5000)) = true := by decide
private theorem cl_w0 : ∀ n : Fin 50, centF (n.val + 5000) < 23 := by decide
private theorem bd_w0 : ∀ n : Fin 50, densSupG (n.val + 5000) < 2 ^ 1771 := by decide
private theorem cs_w1 : ∀ n : Fin 50, centredStar (densSupG (n.val + 5050)) (centF (n.val + 5050)) = true := by decide
private theorem cl_w1 : ∀ n : Fin 50, centF (n.val + 5050) < 23 := by decide
private theorem bd_w1 : ∀ n : Fin 50, densSupG (n.val + 5050) < 2 ^ 1771 := by decide
private theorem cs_w2 : ∀ n : Fin 50, centredStar (densSupG (n.val + 5100)) (centF (n.val + 5100)) = true := by decide
private theorem cl_w2 : ∀ n : Fin 50, centF (n.val + 5100) < 23 := by decide
private theorem bd_w2 : ∀ n : Fin 50, densSupG (n.val + 5100) < 2 ^ 1771 := by decide
private theorem cs_w3 : ∀ n : Fin 50, centredStar (densSupG (n.val + 5150)) (centF (n.val + 5150)) = true := by decide
private theorem cl_w3 : ∀ n : Fin 50, centF (n.val + 5150) < 23 := by decide
private theorem bd_w3 : ∀ n : Fin 50, densSupG (n.val + 5150) < 2 ^ 1771 := by decide
private theorem cs_w4 : ∀ n : Fin 50, centredStar (densSupG (n.val + 5200)) (centF (n.val + 5200)) = true := by decide
private theorem cl_w4 : ∀ n : Fin 50, centF (n.val + 5200) < 23 := by decide
private theorem bd_w4 : ∀ n : Fin 50, densSupG (n.val + 5200) < 2 ^ 1771 := by decide
private theorem cs_w5 : ∀ n : Fin 50, centredStar (densSupG (n.val + 5250)) (centF (n.val + 5250)) = true := by decide
private theorem cl_w5 : ∀ n : Fin 50, centF (n.val + 5250) < 23 := by decide
private theorem bd_w5 : ∀ n : Fin 50, densSupG (n.val + 5250) < 2 ^ 1771 := by decide
private theorem cs_w6 : ∀ n : Fin 50, centredStar (densSupG (n.val + 5300)) (centF (n.val + 5300)) = true := by decide
private theorem cl_w6 : ∀ n : Fin 50, centF (n.val + 5300) < 23 := by decide
private theorem bd_w6 : ∀ n : Fin 50, densSupG (n.val + 5300) < 2 ^ 1771 := by decide
private theorem cs_w7 : ∀ n : Fin 50, centredStar (densSupG (n.val + 5350)) (centF (n.val + 5350)) = true := by decide
private theorem cl_w7 : ∀ n : Fin 50, centF (n.val + 5350) < 23 := by decide
private theorem bd_w7 : ∀ n : Fin 50, densSupG (n.val + 5350) < 2 ^ 1771 := by decide
private theorem cs_w8 : ∀ n : Fin 50, centredStar (densSupG (n.val + 5400)) (centF (n.val + 5400)) = true := by decide
private theorem cl_w8 : ∀ n : Fin 50, centF (n.val + 5400) < 23 := by decide
private theorem bd_w8 : ∀ n : Fin 50, densSupG (n.val + 5400) < 2 ^ 1771 := by decide
private theorem cs_w9 : ∀ n : Fin 50, centredStar (densSupG (n.val + 5450)) (centF (n.val + 5450)) = true := by decide
private theorem cl_w9 : ∀ n : Fin 50, centF (n.val + 5450) < 23 := by decide
private theorem bd_w9 : ∀ n : Fin 50, densSupG (n.val + 5450) < 2 ^ 1771 := by decide
private theorem cs_w10 : ∀ n : Fin 50, centredStar (densSupG (n.val + 5500)) (centF (n.val + 5500)) = true := by decide
private theorem cl_w10 : ∀ n : Fin 50, centF (n.val + 5500) < 23 := by decide
private theorem bd_w10 : ∀ n : Fin 50, densSupG (n.val + 5500) < 2 ^ 1771 := by decide
private theorem cs_w11 : ∀ n : Fin 50, centredStar (densSupG (n.val + 5550)) (centF (n.val + 5550)) = true := by decide
private theorem cl_w11 : ∀ n : Fin 50, centF (n.val + 5550) < 23 := by decide
private theorem bd_w11 : ∀ n : Fin 50, densSupG (n.val + 5550) < 2 ^ 1771 := by decide
private theorem cs_w12 : ∀ n : Fin 50, centredStar (densSupG (n.val + 5600)) (centF (n.val + 5600)) = true := by decide
private theorem cl_w12 : ∀ n : Fin 50, centF (n.val + 5600) < 23 := by decide
private theorem bd_w12 : ∀ n : Fin 50, densSupG (n.val + 5600) < 2 ^ 1771 := by decide
private theorem cs_w13 : ∀ n : Fin 50, centredStar (densSupG (n.val + 5650)) (centF (n.val + 5650)) = true := by decide
private theorem cl_w13 : ∀ n : Fin 50, centF (n.val + 5650) < 23 := by decide
private theorem bd_w13 : ∀ n : Fin 50, densSupG (n.val + 5650) < 2 ^ 1771 := by decide
private theorem cs_w14 : ∀ n : Fin 50, centredStar (densSupG (n.val + 5700)) (centF (n.val + 5700)) = true := by decide
private theorem cl_w14 : ∀ n : Fin 50, centF (n.val + 5700) < 23 := by decide
private theorem bd_w14 : ∀ n : Fin 50, densSupG (n.val + 5700) < 2 ^ 1771 := by decide
private theorem cs_w15 : ∀ n : Fin 50, centredStar (densSupG (n.val + 5750)) (centF (n.val + 5750)) = true := by decide
private theorem cl_w15 : ∀ n : Fin 50, centF (n.val + 5750) < 23 := by decide
private theorem bd_w15 : ∀ n : Fin 50, densSupG (n.val + 5750) < 2 ^ 1771 := by decide
private theorem cs_w16 : ∀ n : Fin 50, centredStar (densSupG (n.val + 5800)) (centF (n.val + 5800)) = true := by decide
private theorem cl_w16 : ∀ n : Fin 50, centF (n.val + 5800) < 23 := by decide
private theorem bd_w16 : ∀ n : Fin 50, densSupG (n.val + 5800) < 2 ^ 1771 := by decide
private theorem cs_w17 : ∀ n : Fin 50, centredStar (densSupG (n.val + 5850)) (centF (n.val + 5850)) = true := by decide
private theorem cl_w17 : ∀ n : Fin 50, centF (n.val + 5850) < 23 := by decide
private theorem bd_w17 : ∀ n : Fin 50, densSupG (n.val + 5850) < 2 ^ 1771 := by decide
private theorem cs_w18 : ∀ n : Fin 50, centredStar (densSupG (n.val + 5900)) (centF (n.val + 5900)) = true := by decide
private theorem cl_w18 : ∀ n : Fin 50, centF (n.val + 5900) < 23 := by decide
private theorem bd_w18 : ∀ n : Fin 50, densSupG (n.val + 5900) < 2 ^ 1771 := by decide
private theorem cs_w19 : ∀ n : Fin 50, centredStar (densSupG (n.val + 5950)) (centF (n.val + 5950)) = true := by decide
private theorem cl_w19 : ∀ n : Fin 50, centF (n.val + 5950) < 23 := by decide
private theorem bd_w19 : ∀ n : Fin 50, densSupG (n.val + 5950) < 2 ^ 1771 := by decide
private theorem cs_w20 : ∀ n : Fin 50, centredStar (densSupG (n.val + 6000)) (centF (n.val + 6000)) = true := by decide
private theorem cl_w20 : ∀ n : Fin 50, centF (n.val + 6000) < 23 := by decide
private theorem bd_w20 : ∀ n : Fin 50, densSupG (n.val + 6000) < 2 ^ 1771 := by decide
private theorem cs_w21 : ∀ n : Fin 50, centredStar (densSupG (n.val + 6050)) (centF (n.val + 6050)) = true := by decide
private theorem cl_w21 : ∀ n : Fin 50, centF (n.val + 6050) < 23 := by decide
private theorem bd_w21 : ∀ n : Fin 50, densSupG (n.val + 6050) < 2 ^ 1771 := by decide
private theorem cs_w22 : ∀ n : Fin 50, centredStar (densSupG (n.val + 6100)) (centF (n.val + 6100)) = true := by decide
private theorem cl_w22 : ∀ n : Fin 50, centF (n.val + 6100) < 23 := by decide
private theorem bd_w22 : ∀ n : Fin 50, densSupG (n.val + 6100) < 2 ^ 1771 := by decide
private theorem cs_w23 : ∀ n : Fin 50, centredStar (densSupG (n.val + 6150)) (centF (n.val + 6150)) = true := by decide
private theorem cl_w23 : ∀ n : Fin 50, centF (n.val + 6150) < 23 := by decide
private theorem bd_w23 : ∀ n : Fin 50, densSupG (n.val + 6150) < 2 ^ 1771 := by decide
private theorem cs_w24 : ∀ n : Fin 50, centredStar (densSupG (n.val + 6200)) (centF (n.val + 6200)) = true := by decide
private theorem cl_w24 : ∀ n : Fin 50, centF (n.val + 6200) < 23 := by decide
private theorem bd_w24 : ∀ n : Fin 50, densSupG (n.val + 6200) < 2 ^ 1771 := by decide
private theorem cs_w25 : ∀ n : Fin 50, centredStar (densSupG (n.val + 6250)) (centF (n.val + 6250)) = true := by decide
private theorem cl_w25 : ∀ n : Fin 50, centF (n.val + 6250) < 23 := by decide
private theorem bd_w25 : ∀ n : Fin 50, densSupG (n.val + 6250) < 2 ^ 1771 := by decide
private theorem cs_w26 : ∀ n : Fin 50, centredStar (densSupG (n.val + 6300)) (centF (n.val + 6300)) = true := by decide
private theorem cl_w26 : ∀ n : Fin 50, centF (n.val + 6300) < 23 := by decide
private theorem bd_w26 : ∀ n : Fin 50, densSupG (n.val + 6300) < 2 ^ 1771 := by decide
private theorem cs_w27 : ∀ n : Fin 50, centredStar (densSupG (n.val + 6350)) (centF (n.val + 6350)) = true := by decide
private theorem cl_w27 : ∀ n : Fin 50, centF (n.val + 6350) < 23 := by decide
private theorem bd_w27 : ∀ n : Fin 50, densSupG (n.val + 6350) < 2 ^ 1771 := by decide
private theorem cs_w28 : ∀ n : Fin 50, centredStar (densSupG (n.val + 6400)) (centF (n.val + 6400)) = true := by decide
private theorem cl_w28 : ∀ n : Fin 50, centF (n.val + 6400) < 23 := by decide
private theorem bd_w28 : ∀ n : Fin 50, densSupG (n.val + 6400) < 2 ^ 1771 := by decide
private theorem cs_w29 : ∀ n : Fin 50, centredStar (densSupG (n.val + 6450)) (centF (n.val + 6450)) = true := by decide
private theorem cl_w29 : ∀ n : Fin 50, centF (n.val + 6450) < 23 := by decide
private theorem bd_w29 : ∀ n : Fin 50, densSupG (n.val + 6450) < 2 ^ 1771 := by decide
private theorem cs_w30 : ∀ n : Fin 50, centredStar (densSupG (n.val + 6500)) (centF (n.val + 6500)) = true := by decide
private theorem cl_w30 : ∀ n : Fin 50, centF (n.val + 6500) < 23 := by decide
private theorem bd_w30 : ∀ n : Fin 50, densSupG (n.val + 6500) < 2 ^ 1771 := by decide
private theorem cs_w31 : ∀ n : Fin 50, centredStar (densSupG (n.val + 6550)) (centF (n.val + 6550)) = true := by decide
private theorem cl_w31 : ∀ n : Fin 50, centF (n.val + 6550) < 23 := by decide
private theorem bd_w31 : ∀ n : Fin 50, densSupG (n.val + 6550) < 2 ^ 1771 := by decide
private theorem cs_w32 : ∀ n : Fin 50, centredStar (densSupG (n.val + 6600)) (centF (n.val + 6600)) = true := by decide
private theorem cl_w32 : ∀ n : Fin 50, centF (n.val + 6600) < 23 := by decide
private theorem bd_w32 : ∀ n : Fin 50, densSupG (n.val + 6600) < 2 ^ 1771 := by decide
private theorem cs_w33 : ∀ n : Fin 50, centredStar (densSupG (n.val + 6650)) (centF (n.val + 6650)) = true := by decide
private theorem cl_w33 : ∀ n : Fin 50, centF (n.val + 6650) < 23 := by decide
private theorem bd_w33 : ∀ n : Fin 50, densSupG (n.val + 6650) < 2 ^ 1771 := by decide
private theorem cs_w34 : ∀ n : Fin 50, centredStar (densSupG (n.val + 6700)) (centF (n.val + 6700)) = true := by decide
private theorem cl_w34 : ∀ n : Fin 50, centF (n.val + 6700) < 23 := by decide
private theorem bd_w34 : ∀ n : Fin 50, densSupG (n.val + 6700) < 2 ^ 1771 := by decide
private theorem cs_w35 : ∀ n : Fin 50, centredStar (densSupG (n.val + 6750)) (centF (n.val + 6750)) = true := by decide
private theorem cl_w35 : ∀ n : Fin 50, centF (n.val + 6750) < 23 := by decide
private theorem bd_w35 : ∀ n : Fin 50, densSupG (n.val + 6750) < 2 ^ 1771 := by decide
private theorem cs_w36 : ∀ n : Fin 50, centredStar (densSupG (n.val + 6800)) (centF (n.val + 6800)) = true := by decide
private theorem cl_w36 : ∀ n : Fin 50, centF (n.val + 6800) < 23 := by decide
private theorem bd_w36 : ∀ n : Fin 50, densSupG (n.val + 6800) < 2 ^ 1771 := by decide
private theorem cs_w37 : ∀ n : Fin 50, centredStar (densSupG (n.val + 6850)) (centF (n.val + 6850)) = true := by decide
private theorem cl_w37 : ∀ n : Fin 50, centF (n.val + 6850) < 23 := by decide
private theorem bd_w37 : ∀ n : Fin 50, densSupG (n.val + 6850) < 2 ^ 1771 := by decide
private theorem cs_w38 : ∀ n : Fin 50, centredStar (densSupG (n.val + 6900)) (centF (n.val + 6900)) = true := by decide
private theorem cl_w38 : ∀ n : Fin 50, centF (n.val + 6900) < 23 := by decide
private theorem bd_w38 : ∀ n : Fin 50, densSupG (n.val + 6900) < 2 ^ 1771 := by decide
private theorem cs_w39 : ∀ n : Fin 50, centredStar (densSupG (n.val + 6950)) (centF (n.val + 6950)) = true := by decide
private theorem cl_w39 : ∀ n : Fin 50, centF (n.val + 6950) < 23 := by decide
private theorem bd_w39 : ∀ n : Fin 50, densSupG (n.val + 6950) < 2 ^ 1771 := by decide
private theorem cs_w40 : ∀ n : Fin 50, centredStar (densSupG (n.val + 7000)) (centF (n.val + 7000)) = true := by decide
private theorem cl_w40 : ∀ n : Fin 50, centF (n.val + 7000) < 23 := by decide
private theorem bd_w40 : ∀ n : Fin 50, densSupG (n.val + 7000) < 2 ^ 1771 := by decide
private theorem cs_w41 : ∀ n : Fin 50, centredStar (densSupG (n.val + 7050)) (centF (n.val + 7050)) = true := by decide
private theorem cl_w41 : ∀ n : Fin 50, centF (n.val + 7050) < 23 := by decide
private theorem bd_w41 : ∀ n : Fin 50, densSupG (n.val + 7050) < 2 ^ 1771 := by decide
private theorem cs_w42 : ∀ n : Fin 50, centredStar (densSupG (n.val + 7100)) (centF (n.val + 7100)) = true := by decide
private theorem cl_w42 : ∀ n : Fin 50, centF (n.val + 7100) < 23 := by decide
private theorem bd_w42 : ∀ n : Fin 50, densSupG (n.val + 7100) < 2 ^ 1771 := by decide
private theorem cs_w43 : ∀ n : Fin 50, centredStar (densSupG (n.val + 7150)) (centF (n.val + 7150)) = true := by decide
private theorem cl_w43 : ∀ n : Fin 50, centF (n.val + 7150) < 23 := by decide
private theorem bd_w43 : ∀ n : Fin 50, densSupG (n.val + 7150) < 2 ^ 1771 := by decide
private theorem cs_w44 : ∀ n : Fin 50, centredStar (densSupG (n.val + 7200)) (centF (n.val + 7200)) = true := by decide
private theorem cl_w44 : ∀ n : Fin 50, centF (n.val + 7200) < 23 := by decide
private theorem bd_w44 : ∀ n : Fin 50, densSupG (n.val + 7200) < 2 ^ 1771 := by decide
private theorem cs_w45 : ∀ n : Fin 50, centredStar (densSupG (n.val + 7250)) (centF (n.val + 7250)) = true := by decide
private theorem cl_w45 : ∀ n : Fin 50, centF (n.val + 7250) < 23 := by decide
private theorem bd_w45 : ∀ n : Fin 50, densSupG (n.val + 7250) < 2 ^ 1771 := by decide
private theorem cs_w46 : ∀ n : Fin 50, centredStar (densSupG (n.val + 7300)) (centF (n.val + 7300)) = true := by decide
private theorem cl_w46 : ∀ n : Fin 50, centF (n.val + 7300) < 23 := by decide
private theorem bd_w46 : ∀ n : Fin 50, densSupG (n.val + 7300) < 2 ^ 1771 := by decide
private theorem cs_w47 : ∀ n : Fin 50, centredStar (densSupG (n.val + 7350)) (centF (n.val + 7350)) = true := by decide
private theorem cl_w47 : ∀ n : Fin 50, centF (n.val + 7350) < 23 := by decide
private theorem bd_w47 : ∀ n : Fin 50, densSupG (n.val + 7350) < 2 ^ 1771 := by decide
private theorem cs_w48 : ∀ n : Fin 50, centredStar (densSupG (n.val + 7400)) (centF (n.val + 7400)) = true := by decide
private theorem cl_w48 : ∀ n : Fin 50, centF (n.val + 7400) < 23 := by decide
private theorem bd_w48 : ∀ n : Fin 50, densSupG (n.val + 7400) < 2 ^ 1771 := by decide
private theorem cs_w49 : ∀ n : Fin 50, centredStar (densSupG (n.val + 7450)) (centF (n.val + 7450)) = true := by decide
private theorem cl_w49 : ∀ n : Fin 50, centF (n.val + 7450) < 23 := by decide
private theorem bd_w49 : ∀ n : Fin 50, densSupG (n.val + 7450) < 2 ^ 1771 := by decide

theorem centredStar_range : ∀ n, 5000 ≤ n → n < 7500 → centredStar (densSupG n) (centF n) = true := by
  intro n hlo hhi
  by_cases h0 : n < 5050
  · have hr : n - 5000 < 50 := by omega
    have heq : n = (n - 5000) + 5000 := by omega
    rw [heq]
    exact cs_w0 ⟨n - 5000, hr⟩
  ·
    by_cases h1 : n < 5100
    ·
      have hr : n - 5050 < 50 := by omega
      have heq : n = (n - 5050) + 5050 := by omega
      rw [heq]
      exact cs_w1 ⟨n - 5050, hr⟩
    ·
      by_cases h2 : n < 5150
      ·
        have hr : n - 5100 < 50 := by omega
        have heq : n = (n - 5100) + 5100 := by omega
        rw [heq]
        exact cs_w2 ⟨n - 5100, hr⟩
      ·
        by_cases h3 : n < 5200
        ·
          have hr : n - 5150 < 50 := by omega
          have heq : n = (n - 5150) + 5150 := by omega
          rw [heq]
          exact cs_w3 ⟨n - 5150, hr⟩
        ·
          by_cases h4 : n < 5250
          ·
            have hr : n - 5200 < 50 := by omega
            have heq : n = (n - 5200) + 5200 := by omega
            rw [heq]
            exact cs_w4 ⟨n - 5200, hr⟩
          ·
            by_cases h5 : n < 5300
            ·
              have hr : n - 5250 < 50 := by omega
              have heq : n = (n - 5250) + 5250 := by omega
              rw [heq]
              exact cs_w5 ⟨n - 5250, hr⟩
            ·
              by_cases h6 : n < 5350
              ·
                have hr : n - 5300 < 50 := by omega
                have heq : n = (n - 5300) + 5300 := by omega
                rw [heq]
                exact cs_w6 ⟨n - 5300, hr⟩
              ·
                by_cases h7 : n < 5400
                ·
                  have hr : n - 5350 < 50 := by omega
                  have heq : n = (n - 5350) + 5350 := by omega
                  rw [heq]
                  exact cs_w7 ⟨n - 5350, hr⟩
                ·
                  by_cases h8 : n < 5450
                  ·
                    have hr : n - 5400 < 50 := by omega
                    have heq : n = (n - 5400) + 5400 := by omega
                    rw [heq]
                    exact cs_w8 ⟨n - 5400, hr⟩
                  ·
                    by_cases h9 : n < 5500
                    ·
                      have hr : n - 5450 < 50 := by omega
                      have heq : n = (n - 5450) + 5450 := by omega
                      rw [heq]
                      exact cs_w9 ⟨n - 5450, hr⟩
                    ·
                      by_cases h10 : n < 5550
                      ·
                        have hr : n - 5500 < 50 := by omega
                        have heq : n = (n - 5500) + 5500 := by omega
                        rw [heq]
                        exact cs_w10 ⟨n - 5500, hr⟩
                      ·
                        by_cases h11 : n < 5600
                        ·
                          have hr : n - 5550 < 50 := by omega
                          have heq : n = (n - 5550) + 5550 := by omega
                          rw [heq]
                          exact cs_w11 ⟨n - 5550, hr⟩
                        ·
                          by_cases h12 : n < 5650
                          ·
                            have hr : n - 5600 < 50 := by omega
                            have heq : n = (n - 5600) + 5600 := by omega
                            rw [heq]
                            exact cs_w12 ⟨n - 5600, hr⟩
                          ·
                            by_cases h13 : n < 5700
                            ·
                              have hr : n - 5650 < 50 := by omega
                              have heq : n = (n - 5650) + 5650 := by omega
                              rw [heq]
                              exact cs_w13 ⟨n - 5650, hr⟩
                            ·
                              by_cases h14 : n < 5750
                              ·
                                have hr : n - 5700 < 50 := by omega
                                have heq : n = (n - 5700) + 5700 := by omega
                                rw [heq]
                                exact cs_w14 ⟨n - 5700, hr⟩
                              ·
                                by_cases h15 : n < 5800
                                ·
                                  have hr : n - 5750 < 50 := by omega
                                  have heq : n = (n - 5750) + 5750 := by omega
                                  rw [heq]
                                  exact cs_w15 ⟨n - 5750, hr⟩
                                ·
                                  by_cases h16 : n < 5850
                                  ·
                                    have hr : n - 5800 < 50 := by omega
                                    have heq : n = (n - 5800) + 5800 := by omega
                                    rw [heq]
                                    exact cs_w16 ⟨n - 5800, hr⟩
                                  ·
                                    by_cases h17 : n < 5900
                                    ·
                                      have hr : n - 5850 < 50 := by omega
                                      have heq : n = (n - 5850) + 5850 := by omega
                                      rw [heq]
                                      exact cs_w17 ⟨n - 5850, hr⟩
                                    ·
                                      by_cases h18 : n < 5950
                                      ·
                                        have hr : n - 5900 < 50 := by omega
                                        have heq : n = (n - 5900) + 5900 := by omega
                                        rw [heq]
                                        exact cs_w18 ⟨n - 5900, hr⟩
                                      ·
                                        by_cases h19 : n < 6000
                                        ·
                                          have hr : n - 5950 < 50 := by omega
                                          have heq : n = (n - 5950) + 5950 := by omega
                                          rw [heq]
                                          exact cs_w19 ⟨n - 5950, hr⟩
                                        ·
                                          by_cases h20 : n < 6050
                                          ·
                                            have hr : n - 6000 < 50 := by omega
                                            have heq : n = (n - 6000) + 6000 := by omega
                                            rw [heq]
                                            exact cs_w20 ⟨n - 6000, hr⟩
                                          ·
                                            by_cases h21 : n < 6100
                                            ·
                                              have hr : n - 6050 < 50 := by omega
                                              have heq : n = (n - 6050) + 6050 := by omega
                                              rw [heq]
                                              exact cs_w21 ⟨n - 6050, hr⟩
                                            ·
                                              by_cases h22 : n < 6150
                                              ·
                                                have hr : n - 6100 < 50 := by omega
                                                have heq : n = (n - 6100) + 6100 := by omega
                                                rw [heq]
                                                exact cs_w22 ⟨n - 6100, hr⟩
                                              ·
                                                by_cases h23 : n < 6200
                                                ·
                                                  have hr : n - 6150 < 50 := by omega
                                                  have heq : n = (n - 6150) + 6150 := by omega
                                                  rw [heq]
                                                  exact cs_w23 ⟨n - 6150, hr⟩
                                                ·
                                                  by_cases h24 : n < 6250
                                                  ·
                                                    have hr : n - 6200 < 50 := by omega
                                                    have heq : n = (n - 6200) + 6200 := by omega
                                                    rw [heq]
                                                    exact cs_w24 ⟨n - 6200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 6300
                                                    ·
                                                      have hr : n - 6250 < 50 := by omega
                                                      have heq : n = (n - 6250) + 6250 := by omega
                                                      rw [heq]
                                                      exact cs_w25 ⟨n - 6250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 6350
                                                      ·
                                                        have hr : n - 6300 < 50 := by omega
                                                        have heq : n = (n - 6300) + 6300 := by omega
                                                        rw [heq]
                                                        exact cs_w26 ⟨n - 6300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 6400
                                                        ·
                                                          have hr : n - 6350 < 50 := by omega
                                                          have heq : n = (n - 6350) + 6350 := by omega
                                                          rw [heq]
                                                          exact cs_w27 ⟨n - 6350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 6450
                                                          ·
                                                            have hr : n - 6400 < 50 := by omega
                                                            have heq : n = (n - 6400) + 6400 := by omega
                                                            rw [heq]
                                                            exact cs_w28 ⟨n - 6400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 6500
                                                            ·
                                                              have hr : n - 6450 < 50 := by omega
                                                              have heq : n = (n - 6450) + 6450 := by omega
                                                              rw [heq]
                                                              exact cs_w29 ⟨n - 6450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 6550
                                                              ·
                                                                have hr : n - 6500 < 50 := by omega
                                                                have heq : n = (n - 6500) + 6500 := by omega
                                                                rw [heq]
                                                                exact cs_w30 ⟨n - 6500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 6600
                                                                ·
                                                                  have hr : n - 6550 < 50 := by omega
                                                                  have heq : n = (n - 6550) + 6550 := by omega
                                                                  rw [heq]
                                                                  exact cs_w31 ⟨n - 6550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 6650
                                                                  ·
                                                                    have hr : n - 6600 < 50 := by omega
                                                                    have heq : n = (n - 6600) + 6600 := by omega
                                                                    rw [heq]
                                                                    exact cs_w32 ⟨n - 6600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 6700
                                                                    ·
                                                                      have hr : n - 6650 < 50 := by omega
                                                                      have heq : n = (n - 6650) + 6650 := by omega
                                                                      rw [heq]
                                                                      exact cs_w33 ⟨n - 6650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 6750
                                                                      ·
                                                                        have hr : n - 6700 < 50 := by omega
                                                                        have heq : n = (n - 6700) + 6700 := by omega
                                                                        rw [heq]
                                                                        exact cs_w34 ⟨n - 6700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 6800
                                                                        ·
                                                                          have hr : n - 6750 < 50 := by omega
                                                                          have heq : n = (n - 6750) + 6750 := by omega
                                                                          rw [heq]
                                                                          exact cs_w35 ⟨n - 6750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 6850
                                                                          ·
                                                                            have hr : n - 6800 < 50 := by omega
                                                                            have heq : n = (n - 6800) + 6800 := by omega
                                                                            rw [heq]
                                                                            exact cs_w36 ⟨n - 6800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 6900
                                                                            ·
                                                                              have hr : n - 6850 < 50 := by omega
                                                                              have heq : n = (n - 6850) + 6850 := by omega
                                                                              rw [heq]
                                                                              exact cs_w37 ⟨n - 6850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 6950
                                                                              ·
                                                                                have hr : n - 6900 < 50 := by omega
                                                                                have heq : n = (n - 6900) + 6900 := by omega
                                                                                rw [heq]
                                                                                exact cs_w38 ⟨n - 6900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 7000
                                                                                ·
                                                                                  have hr : n - 6950 < 50 := by omega
                                                                                  have heq : n = (n - 6950) + 6950 := by omega
                                                                                  rw [heq]
                                                                                  exact cs_w39 ⟨n - 6950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 7050
                                                                                  ·
                                                                                    have hr : n - 7000 < 50 := by omega
                                                                                    have heq : n = (n - 7000) + 7000 := by omega
                                                                                    rw [heq]
                                                                                    exact cs_w40 ⟨n - 7000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 7100
                                                                                    ·
                                                                                      have hr : n - 7050 < 50 := by omega
                                                                                      have heq : n = (n - 7050) + 7050 := by omega
                                                                                      rw [heq]
                                                                                      exact cs_w41 ⟨n - 7050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 7150
                                                                                      ·
                                                                                        have hr : n - 7100 < 50 := by omega
                                                                                        have heq : n = (n - 7100) + 7100 := by omega
                                                                                        rw [heq]
                                                                                        exact cs_w42 ⟨n - 7100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 7200
                                                                                        ·
                                                                                          have hr : n - 7150 < 50 := by omega
                                                                                          have heq : n = (n - 7150) + 7150 := by omega
                                                                                          rw [heq]
                                                                                          exact cs_w43 ⟨n - 7150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 7250
                                                                                          ·
                                                                                            have hr : n - 7200 < 50 := by omega
                                                                                            have heq : n = (n - 7200) + 7200 := by omega
                                                                                            rw [heq]
                                                                                            exact cs_w44 ⟨n - 7200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 7300
                                                                                            ·
                                                                                              have hr : n - 7250 < 50 := by omega
                                                                                              have heq : n = (n - 7250) + 7250 := by omega
                                                                                              rw [heq]
                                                                                              exact cs_w45 ⟨n - 7250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 7350
                                                                                              ·
                                                                                                have hr : n - 7300 < 50 := by omega
                                                                                                have heq : n = (n - 7300) + 7300 := by omega
                                                                                                rw [heq]
                                                                                                exact cs_w46 ⟨n - 7300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 7400
                                                                                                ·
                                                                                                  have hr : n - 7350 < 50 := by omega
                                                                                                  have heq : n = (n - 7350) + 7350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cs_w47 ⟨n - 7350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 7450
                                                                                                  ·
                                                                                                    have hr : n - 7400 < 50 := by omega
                                                                                                    have heq : n = (n - 7400) + 7400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w48 ⟨n - 7400, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 7450 < 50 := by omega
                                                                                                    have heq : n = (n - 7450) + 7450 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w49 ⟨n - 7450, hr⟩

theorem centF_lt_range : ∀ n, 5000 ≤ n → n < 7500 → centF n < 23 := by
  intro n hlo hhi
  by_cases h0 : n < 5050
  · have hr : n - 5000 < 50 := by omega
    have heq : n = (n - 5000) + 5000 := by omega
    rw [heq]
    exact cl_w0 ⟨n - 5000, hr⟩
  ·
    by_cases h1 : n < 5100
    ·
      have hr : n - 5050 < 50 := by omega
      have heq : n = (n - 5050) + 5050 := by omega
      rw [heq]
      exact cl_w1 ⟨n - 5050, hr⟩
    ·
      by_cases h2 : n < 5150
      ·
        have hr : n - 5100 < 50 := by omega
        have heq : n = (n - 5100) + 5100 := by omega
        rw [heq]
        exact cl_w2 ⟨n - 5100, hr⟩
      ·
        by_cases h3 : n < 5200
        ·
          have hr : n - 5150 < 50 := by omega
          have heq : n = (n - 5150) + 5150 := by omega
          rw [heq]
          exact cl_w3 ⟨n - 5150, hr⟩
        ·
          by_cases h4 : n < 5250
          ·
            have hr : n - 5200 < 50 := by omega
            have heq : n = (n - 5200) + 5200 := by omega
            rw [heq]
            exact cl_w4 ⟨n - 5200, hr⟩
          ·
            by_cases h5 : n < 5300
            ·
              have hr : n - 5250 < 50 := by omega
              have heq : n = (n - 5250) + 5250 := by omega
              rw [heq]
              exact cl_w5 ⟨n - 5250, hr⟩
            ·
              by_cases h6 : n < 5350
              ·
                have hr : n - 5300 < 50 := by omega
                have heq : n = (n - 5300) + 5300 := by omega
                rw [heq]
                exact cl_w6 ⟨n - 5300, hr⟩
              ·
                by_cases h7 : n < 5400
                ·
                  have hr : n - 5350 < 50 := by omega
                  have heq : n = (n - 5350) + 5350 := by omega
                  rw [heq]
                  exact cl_w7 ⟨n - 5350, hr⟩
                ·
                  by_cases h8 : n < 5450
                  ·
                    have hr : n - 5400 < 50 := by omega
                    have heq : n = (n - 5400) + 5400 := by omega
                    rw [heq]
                    exact cl_w8 ⟨n - 5400, hr⟩
                  ·
                    by_cases h9 : n < 5500
                    ·
                      have hr : n - 5450 < 50 := by omega
                      have heq : n = (n - 5450) + 5450 := by omega
                      rw [heq]
                      exact cl_w9 ⟨n - 5450, hr⟩
                    ·
                      by_cases h10 : n < 5550
                      ·
                        have hr : n - 5500 < 50 := by omega
                        have heq : n = (n - 5500) + 5500 := by omega
                        rw [heq]
                        exact cl_w10 ⟨n - 5500, hr⟩
                      ·
                        by_cases h11 : n < 5600
                        ·
                          have hr : n - 5550 < 50 := by omega
                          have heq : n = (n - 5550) + 5550 := by omega
                          rw [heq]
                          exact cl_w11 ⟨n - 5550, hr⟩
                        ·
                          by_cases h12 : n < 5650
                          ·
                            have hr : n - 5600 < 50 := by omega
                            have heq : n = (n - 5600) + 5600 := by omega
                            rw [heq]
                            exact cl_w12 ⟨n - 5600, hr⟩
                          ·
                            by_cases h13 : n < 5700
                            ·
                              have hr : n - 5650 < 50 := by omega
                              have heq : n = (n - 5650) + 5650 := by omega
                              rw [heq]
                              exact cl_w13 ⟨n - 5650, hr⟩
                            ·
                              by_cases h14 : n < 5750
                              ·
                                have hr : n - 5700 < 50 := by omega
                                have heq : n = (n - 5700) + 5700 := by omega
                                rw [heq]
                                exact cl_w14 ⟨n - 5700, hr⟩
                              ·
                                by_cases h15 : n < 5800
                                ·
                                  have hr : n - 5750 < 50 := by omega
                                  have heq : n = (n - 5750) + 5750 := by omega
                                  rw [heq]
                                  exact cl_w15 ⟨n - 5750, hr⟩
                                ·
                                  by_cases h16 : n < 5850
                                  ·
                                    have hr : n - 5800 < 50 := by omega
                                    have heq : n = (n - 5800) + 5800 := by omega
                                    rw [heq]
                                    exact cl_w16 ⟨n - 5800, hr⟩
                                  ·
                                    by_cases h17 : n < 5900
                                    ·
                                      have hr : n - 5850 < 50 := by omega
                                      have heq : n = (n - 5850) + 5850 := by omega
                                      rw [heq]
                                      exact cl_w17 ⟨n - 5850, hr⟩
                                    ·
                                      by_cases h18 : n < 5950
                                      ·
                                        have hr : n - 5900 < 50 := by omega
                                        have heq : n = (n - 5900) + 5900 := by omega
                                        rw [heq]
                                        exact cl_w18 ⟨n - 5900, hr⟩
                                      ·
                                        by_cases h19 : n < 6000
                                        ·
                                          have hr : n - 5950 < 50 := by omega
                                          have heq : n = (n - 5950) + 5950 := by omega
                                          rw [heq]
                                          exact cl_w19 ⟨n - 5950, hr⟩
                                        ·
                                          by_cases h20 : n < 6050
                                          ·
                                            have hr : n - 6000 < 50 := by omega
                                            have heq : n = (n - 6000) + 6000 := by omega
                                            rw [heq]
                                            exact cl_w20 ⟨n - 6000, hr⟩
                                          ·
                                            by_cases h21 : n < 6100
                                            ·
                                              have hr : n - 6050 < 50 := by omega
                                              have heq : n = (n - 6050) + 6050 := by omega
                                              rw [heq]
                                              exact cl_w21 ⟨n - 6050, hr⟩
                                            ·
                                              by_cases h22 : n < 6150
                                              ·
                                                have hr : n - 6100 < 50 := by omega
                                                have heq : n = (n - 6100) + 6100 := by omega
                                                rw [heq]
                                                exact cl_w22 ⟨n - 6100, hr⟩
                                              ·
                                                by_cases h23 : n < 6200
                                                ·
                                                  have hr : n - 6150 < 50 := by omega
                                                  have heq : n = (n - 6150) + 6150 := by omega
                                                  rw [heq]
                                                  exact cl_w23 ⟨n - 6150, hr⟩
                                                ·
                                                  by_cases h24 : n < 6250
                                                  ·
                                                    have hr : n - 6200 < 50 := by omega
                                                    have heq : n = (n - 6200) + 6200 := by omega
                                                    rw [heq]
                                                    exact cl_w24 ⟨n - 6200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 6300
                                                    ·
                                                      have hr : n - 6250 < 50 := by omega
                                                      have heq : n = (n - 6250) + 6250 := by omega
                                                      rw [heq]
                                                      exact cl_w25 ⟨n - 6250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 6350
                                                      ·
                                                        have hr : n - 6300 < 50 := by omega
                                                        have heq : n = (n - 6300) + 6300 := by omega
                                                        rw [heq]
                                                        exact cl_w26 ⟨n - 6300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 6400
                                                        ·
                                                          have hr : n - 6350 < 50 := by omega
                                                          have heq : n = (n - 6350) + 6350 := by omega
                                                          rw [heq]
                                                          exact cl_w27 ⟨n - 6350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 6450
                                                          ·
                                                            have hr : n - 6400 < 50 := by omega
                                                            have heq : n = (n - 6400) + 6400 := by omega
                                                            rw [heq]
                                                            exact cl_w28 ⟨n - 6400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 6500
                                                            ·
                                                              have hr : n - 6450 < 50 := by omega
                                                              have heq : n = (n - 6450) + 6450 := by omega
                                                              rw [heq]
                                                              exact cl_w29 ⟨n - 6450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 6550
                                                              ·
                                                                have hr : n - 6500 < 50 := by omega
                                                                have heq : n = (n - 6500) + 6500 := by omega
                                                                rw [heq]
                                                                exact cl_w30 ⟨n - 6500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 6600
                                                                ·
                                                                  have hr : n - 6550 < 50 := by omega
                                                                  have heq : n = (n - 6550) + 6550 := by omega
                                                                  rw [heq]
                                                                  exact cl_w31 ⟨n - 6550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 6650
                                                                  ·
                                                                    have hr : n - 6600 < 50 := by omega
                                                                    have heq : n = (n - 6600) + 6600 := by omega
                                                                    rw [heq]
                                                                    exact cl_w32 ⟨n - 6600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 6700
                                                                    ·
                                                                      have hr : n - 6650 < 50 := by omega
                                                                      have heq : n = (n - 6650) + 6650 := by omega
                                                                      rw [heq]
                                                                      exact cl_w33 ⟨n - 6650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 6750
                                                                      ·
                                                                        have hr : n - 6700 < 50 := by omega
                                                                        have heq : n = (n - 6700) + 6700 := by omega
                                                                        rw [heq]
                                                                        exact cl_w34 ⟨n - 6700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 6800
                                                                        ·
                                                                          have hr : n - 6750 < 50 := by omega
                                                                          have heq : n = (n - 6750) + 6750 := by omega
                                                                          rw [heq]
                                                                          exact cl_w35 ⟨n - 6750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 6850
                                                                          ·
                                                                            have hr : n - 6800 < 50 := by omega
                                                                            have heq : n = (n - 6800) + 6800 := by omega
                                                                            rw [heq]
                                                                            exact cl_w36 ⟨n - 6800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 6900
                                                                            ·
                                                                              have hr : n - 6850 < 50 := by omega
                                                                              have heq : n = (n - 6850) + 6850 := by omega
                                                                              rw [heq]
                                                                              exact cl_w37 ⟨n - 6850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 6950
                                                                              ·
                                                                                have hr : n - 6900 < 50 := by omega
                                                                                have heq : n = (n - 6900) + 6900 := by omega
                                                                                rw [heq]
                                                                                exact cl_w38 ⟨n - 6900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 7000
                                                                                ·
                                                                                  have hr : n - 6950 < 50 := by omega
                                                                                  have heq : n = (n - 6950) + 6950 := by omega
                                                                                  rw [heq]
                                                                                  exact cl_w39 ⟨n - 6950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 7050
                                                                                  ·
                                                                                    have hr : n - 7000 < 50 := by omega
                                                                                    have heq : n = (n - 7000) + 7000 := by omega
                                                                                    rw [heq]
                                                                                    exact cl_w40 ⟨n - 7000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 7100
                                                                                    ·
                                                                                      have hr : n - 7050 < 50 := by omega
                                                                                      have heq : n = (n - 7050) + 7050 := by omega
                                                                                      rw [heq]
                                                                                      exact cl_w41 ⟨n - 7050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 7150
                                                                                      ·
                                                                                        have hr : n - 7100 < 50 := by omega
                                                                                        have heq : n = (n - 7100) + 7100 := by omega
                                                                                        rw [heq]
                                                                                        exact cl_w42 ⟨n - 7100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 7200
                                                                                        ·
                                                                                          have hr : n - 7150 < 50 := by omega
                                                                                          have heq : n = (n - 7150) + 7150 := by omega
                                                                                          rw [heq]
                                                                                          exact cl_w43 ⟨n - 7150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 7250
                                                                                          ·
                                                                                            have hr : n - 7200 < 50 := by omega
                                                                                            have heq : n = (n - 7200) + 7200 := by omega
                                                                                            rw [heq]
                                                                                            exact cl_w44 ⟨n - 7200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 7300
                                                                                            ·
                                                                                              have hr : n - 7250 < 50 := by omega
                                                                                              have heq : n = (n - 7250) + 7250 := by omega
                                                                                              rw [heq]
                                                                                              exact cl_w45 ⟨n - 7250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 7350
                                                                                              ·
                                                                                                have hr : n - 7300 < 50 := by omega
                                                                                                have heq : n = (n - 7300) + 7300 := by omega
                                                                                                rw [heq]
                                                                                                exact cl_w46 ⟨n - 7300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 7400
                                                                                                ·
                                                                                                  have hr : n - 7350 < 50 := by omega
                                                                                                  have heq : n = (n - 7350) + 7350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cl_w47 ⟨n - 7350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 7450
                                                                                                  ·
                                                                                                    have hr : n - 7400 < 50 := by omega
                                                                                                    have heq : n = (n - 7400) + 7400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w48 ⟨n - 7400, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 7450 < 50 := by omega
                                                                                                    have heq : n = (n - 7450) + 7450 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w49 ⟨n - 7450, hr⟩

theorem densSupG_lt_range : ∀ n, 5000 ≤ n → n < 7500 → densSupG n < 2 ^ 1771 := by
  intro n hlo hhi
  by_cases h0 : n < 5050
  · have hr : n - 5000 < 50 := by omega
    have heq : n = (n - 5000) + 5000 := by omega
    rw [heq]
    exact bd_w0 ⟨n - 5000, hr⟩
  ·
    by_cases h1 : n < 5100
    ·
      have hr : n - 5050 < 50 := by omega
      have heq : n = (n - 5050) + 5050 := by omega
      rw [heq]
      exact bd_w1 ⟨n - 5050, hr⟩
    ·
      by_cases h2 : n < 5150
      ·
        have hr : n - 5100 < 50 := by omega
        have heq : n = (n - 5100) + 5100 := by omega
        rw [heq]
        exact bd_w2 ⟨n - 5100, hr⟩
      ·
        by_cases h3 : n < 5200
        ·
          have hr : n - 5150 < 50 := by omega
          have heq : n = (n - 5150) + 5150 := by omega
          rw [heq]
          exact bd_w3 ⟨n - 5150, hr⟩
        ·
          by_cases h4 : n < 5250
          ·
            have hr : n - 5200 < 50 := by omega
            have heq : n = (n - 5200) + 5200 := by omega
            rw [heq]
            exact bd_w4 ⟨n - 5200, hr⟩
          ·
            by_cases h5 : n < 5300
            ·
              have hr : n - 5250 < 50 := by omega
              have heq : n = (n - 5250) + 5250 := by omega
              rw [heq]
              exact bd_w5 ⟨n - 5250, hr⟩
            ·
              by_cases h6 : n < 5350
              ·
                have hr : n - 5300 < 50 := by omega
                have heq : n = (n - 5300) + 5300 := by omega
                rw [heq]
                exact bd_w6 ⟨n - 5300, hr⟩
              ·
                by_cases h7 : n < 5400
                ·
                  have hr : n - 5350 < 50 := by omega
                  have heq : n = (n - 5350) + 5350 := by omega
                  rw [heq]
                  exact bd_w7 ⟨n - 5350, hr⟩
                ·
                  by_cases h8 : n < 5450
                  ·
                    have hr : n - 5400 < 50 := by omega
                    have heq : n = (n - 5400) + 5400 := by omega
                    rw [heq]
                    exact bd_w8 ⟨n - 5400, hr⟩
                  ·
                    by_cases h9 : n < 5500
                    ·
                      have hr : n - 5450 < 50 := by omega
                      have heq : n = (n - 5450) + 5450 := by omega
                      rw [heq]
                      exact bd_w9 ⟨n - 5450, hr⟩
                    ·
                      by_cases h10 : n < 5550
                      ·
                        have hr : n - 5500 < 50 := by omega
                        have heq : n = (n - 5500) + 5500 := by omega
                        rw [heq]
                        exact bd_w10 ⟨n - 5500, hr⟩
                      ·
                        by_cases h11 : n < 5600
                        ·
                          have hr : n - 5550 < 50 := by omega
                          have heq : n = (n - 5550) + 5550 := by omega
                          rw [heq]
                          exact bd_w11 ⟨n - 5550, hr⟩
                        ·
                          by_cases h12 : n < 5650
                          ·
                            have hr : n - 5600 < 50 := by omega
                            have heq : n = (n - 5600) + 5600 := by omega
                            rw [heq]
                            exact bd_w12 ⟨n - 5600, hr⟩
                          ·
                            by_cases h13 : n < 5700
                            ·
                              have hr : n - 5650 < 50 := by omega
                              have heq : n = (n - 5650) + 5650 := by omega
                              rw [heq]
                              exact bd_w13 ⟨n - 5650, hr⟩
                            ·
                              by_cases h14 : n < 5750
                              ·
                                have hr : n - 5700 < 50 := by omega
                                have heq : n = (n - 5700) + 5700 := by omega
                                rw [heq]
                                exact bd_w14 ⟨n - 5700, hr⟩
                              ·
                                by_cases h15 : n < 5800
                                ·
                                  have hr : n - 5750 < 50 := by omega
                                  have heq : n = (n - 5750) + 5750 := by omega
                                  rw [heq]
                                  exact bd_w15 ⟨n - 5750, hr⟩
                                ·
                                  by_cases h16 : n < 5850
                                  ·
                                    have hr : n - 5800 < 50 := by omega
                                    have heq : n = (n - 5800) + 5800 := by omega
                                    rw [heq]
                                    exact bd_w16 ⟨n - 5800, hr⟩
                                  ·
                                    by_cases h17 : n < 5900
                                    ·
                                      have hr : n - 5850 < 50 := by omega
                                      have heq : n = (n - 5850) + 5850 := by omega
                                      rw [heq]
                                      exact bd_w17 ⟨n - 5850, hr⟩
                                    ·
                                      by_cases h18 : n < 5950
                                      ·
                                        have hr : n - 5900 < 50 := by omega
                                        have heq : n = (n - 5900) + 5900 := by omega
                                        rw [heq]
                                        exact bd_w18 ⟨n - 5900, hr⟩
                                      ·
                                        by_cases h19 : n < 6000
                                        ·
                                          have hr : n - 5950 < 50 := by omega
                                          have heq : n = (n - 5950) + 5950 := by omega
                                          rw [heq]
                                          exact bd_w19 ⟨n - 5950, hr⟩
                                        ·
                                          by_cases h20 : n < 6050
                                          ·
                                            have hr : n - 6000 < 50 := by omega
                                            have heq : n = (n - 6000) + 6000 := by omega
                                            rw [heq]
                                            exact bd_w20 ⟨n - 6000, hr⟩
                                          ·
                                            by_cases h21 : n < 6100
                                            ·
                                              have hr : n - 6050 < 50 := by omega
                                              have heq : n = (n - 6050) + 6050 := by omega
                                              rw [heq]
                                              exact bd_w21 ⟨n - 6050, hr⟩
                                            ·
                                              by_cases h22 : n < 6150
                                              ·
                                                have hr : n - 6100 < 50 := by omega
                                                have heq : n = (n - 6100) + 6100 := by omega
                                                rw [heq]
                                                exact bd_w22 ⟨n - 6100, hr⟩
                                              ·
                                                by_cases h23 : n < 6200
                                                ·
                                                  have hr : n - 6150 < 50 := by omega
                                                  have heq : n = (n - 6150) + 6150 := by omega
                                                  rw [heq]
                                                  exact bd_w23 ⟨n - 6150, hr⟩
                                                ·
                                                  by_cases h24 : n < 6250
                                                  ·
                                                    have hr : n - 6200 < 50 := by omega
                                                    have heq : n = (n - 6200) + 6200 := by omega
                                                    rw [heq]
                                                    exact bd_w24 ⟨n - 6200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 6300
                                                    ·
                                                      have hr : n - 6250 < 50 := by omega
                                                      have heq : n = (n - 6250) + 6250 := by omega
                                                      rw [heq]
                                                      exact bd_w25 ⟨n - 6250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 6350
                                                      ·
                                                        have hr : n - 6300 < 50 := by omega
                                                        have heq : n = (n - 6300) + 6300 := by omega
                                                        rw [heq]
                                                        exact bd_w26 ⟨n - 6300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 6400
                                                        ·
                                                          have hr : n - 6350 < 50 := by omega
                                                          have heq : n = (n - 6350) + 6350 := by omega
                                                          rw [heq]
                                                          exact bd_w27 ⟨n - 6350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 6450
                                                          ·
                                                            have hr : n - 6400 < 50 := by omega
                                                            have heq : n = (n - 6400) + 6400 := by omega
                                                            rw [heq]
                                                            exact bd_w28 ⟨n - 6400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 6500
                                                            ·
                                                              have hr : n - 6450 < 50 := by omega
                                                              have heq : n = (n - 6450) + 6450 := by omega
                                                              rw [heq]
                                                              exact bd_w29 ⟨n - 6450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 6550
                                                              ·
                                                                have hr : n - 6500 < 50 := by omega
                                                                have heq : n = (n - 6500) + 6500 := by omega
                                                                rw [heq]
                                                                exact bd_w30 ⟨n - 6500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 6600
                                                                ·
                                                                  have hr : n - 6550 < 50 := by omega
                                                                  have heq : n = (n - 6550) + 6550 := by omega
                                                                  rw [heq]
                                                                  exact bd_w31 ⟨n - 6550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 6650
                                                                  ·
                                                                    have hr : n - 6600 < 50 := by omega
                                                                    have heq : n = (n - 6600) + 6600 := by omega
                                                                    rw [heq]
                                                                    exact bd_w32 ⟨n - 6600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 6700
                                                                    ·
                                                                      have hr : n - 6650 < 50 := by omega
                                                                      have heq : n = (n - 6650) + 6650 := by omega
                                                                      rw [heq]
                                                                      exact bd_w33 ⟨n - 6650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 6750
                                                                      ·
                                                                        have hr : n - 6700 < 50 := by omega
                                                                        have heq : n = (n - 6700) + 6700 := by omega
                                                                        rw [heq]
                                                                        exact bd_w34 ⟨n - 6700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 6800
                                                                        ·
                                                                          have hr : n - 6750 < 50 := by omega
                                                                          have heq : n = (n - 6750) + 6750 := by omega
                                                                          rw [heq]
                                                                          exact bd_w35 ⟨n - 6750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 6850
                                                                          ·
                                                                            have hr : n - 6800 < 50 := by omega
                                                                            have heq : n = (n - 6800) + 6800 := by omega
                                                                            rw [heq]
                                                                            exact bd_w36 ⟨n - 6800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 6900
                                                                            ·
                                                                              have hr : n - 6850 < 50 := by omega
                                                                              have heq : n = (n - 6850) + 6850 := by omega
                                                                              rw [heq]
                                                                              exact bd_w37 ⟨n - 6850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 6950
                                                                              ·
                                                                                have hr : n - 6900 < 50 := by omega
                                                                                have heq : n = (n - 6900) + 6900 := by omega
                                                                                rw [heq]
                                                                                exact bd_w38 ⟨n - 6900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 7000
                                                                                ·
                                                                                  have hr : n - 6950 < 50 := by omega
                                                                                  have heq : n = (n - 6950) + 6950 := by omega
                                                                                  rw [heq]
                                                                                  exact bd_w39 ⟨n - 6950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 7050
                                                                                  ·
                                                                                    have hr : n - 7000 < 50 := by omega
                                                                                    have heq : n = (n - 7000) + 7000 := by omega
                                                                                    rw [heq]
                                                                                    exact bd_w40 ⟨n - 7000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 7100
                                                                                    ·
                                                                                      have hr : n - 7050 < 50 := by omega
                                                                                      have heq : n = (n - 7050) + 7050 := by omega
                                                                                      rw [heq]
                                                                                      exact bd_w41 ⟨n - 7050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 7150
                                                                                      ·
                                                                                        have hr : n - 7100 < 50 := by omega
                                                                                        have heq : n = (n - 7100) + 7100 := by omega
                                                                                        rw [heq]
                                                                                        exact bd_w42 ⟨n - 7100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 7200
                                                                                        ·
                                                                                          have hr : n - 7150 < 50 := by omega
                                                                                          have heq : n = (n - 7150) + 7150 := by omega
                                                                                          rw [heq]
                                                                                          exact bd_w43 ⟨n - 7150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 7250
                                                                                          ·
                                                                                            have hr : n - 7200 < 50 := by omega
                                                                                            have heq : n = (n - 7200) + 7200 := by omega
                                                                                            rw [heq]
                                                                                            exact bd_w44 ⟨n - 7200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 7300
                                                                                            ·
                                                                                              have hr : n - 7250 < 50 := by omega
                                                                                              have heq : n = (n - 7250) + 7250 := by omega
                                                                                              rw [heq]
                                                                                              exact bd_w45 ⟨n - 7250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 7350
                                                                                              ·
                                                                                                have hr : n - 7300 < 50 := by omega
                                                                                                have heq : n = (n - 7300) + 7300 := by omega
                                                                                                rw [heq]
                                                                                                exact bd_w46 ⟨n - 7300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 7400
                                                                                                ·
                                                                                                  have hr : n - 7350 < 50 := by omega
                                                                                                  have heq : n = (n - 7350) + 7350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact bd_w47 ⟨n - 7350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 7450
                                                                                                  ·
                                                                                                    have hr : n - 7400 < 50 := by omega
                                                                                                    have heq : n = (n - 7400) + 7400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w48 ⟨n - 7400, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 7450 < 50 := by omega
                                                                                                    have heq : n = (n - 7450) + 7450 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w49 ⟨n - 7450, hr⟩


end IntMul.Kappa.R8.Bit.Oppbank.CentBound1a


