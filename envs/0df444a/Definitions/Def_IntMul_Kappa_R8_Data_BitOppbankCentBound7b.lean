-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound7b
-- name    : IntMul_Kappa_R8_Data_BitOppbankCentBound7b
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:04:15.196761+00:00
-- url     : https://prove2.me/theorems/c215ea29-9b05-41a9-a1ca-695498f3d829
-- title:
--   HasCentre certificates dens nodes [37500,40000)
-- statement:
--   # Densified centre certificates, pack 7b
--
--   For every densified node index $n$ with $37500\le n<40000$,
--   $$
--   \mathrm{centredStar}(\mathrm{densSupG}\,n,\mathrm{centF}\,n)=\mathsf{true},\quad
--   \mathrm{centF}\,n<23,\quad
--   \mathrm{densSupG}\,n < 2^{1771}.
--   $$
--   Proved by decide on Fin 50 windows (no native_decide). Half-pack for 300s server budget.
-- source:
--   R8 BitOppbank AllDensCentred; jfstack_23 densified supports

-- CentBound pack 7b: densified HasCentre certificates on n ∈ [37500, 40000)
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

namespace IntMul.Kappa.R8.Bit.Oppbank.CentBound7b


private theorem cs_w0 : ∀ n : Fin 50, centredStar (densSupG (n.val + 37500)) (centF (n.val + 37500)) = true := by decide
private theorem cl_w0 : ∀ n : Fin 50, centF (n.val + 37500) < 23 := by decide
private theorem bd_w0 : ∀ n : Fin 50, densSupG (n.val + 37500) < 2 ^ 1771 := by decide
private theorem cs_w1 : ∀ n : Fin 50, centredStar (densSupG (n.val + 37550)) (centF (n.val + 37550)) = true := by decide
private theorem cl_w1 : ∀ n : Fin 50, centF (n.val + 37550) < 23 := by decide
private theorem bd_w1 : ∀ n : Fin 50, densSupG (n.val + 37550) < 2 ^ 1771 := by decide
private theorem cs_w2 : ∀ n : Fin 50, centredStar (densSupG (n.val + 37600)) (centF (n.val + 37600)) = true := by decide
private theorem cl_w2 : ∀ n : Fin 50, centF (n.val + 37600) < 23 := by decide
private theorem bd_w2 : ∀ n : Fin 50, densSupG (n.val + 37600) < 2 ^ 1771 := by decide
private theorem cs_w3 : ∀ n : Fin 50, centredStar (densSupG (n.val + 37650)) (centF (n.val + 37650)) = true := by decide
private theorem cl_w3 : ∀ n : Fin 50, centF (n.val + 37650) < 23 := by decide
private theorem bd_w3 : ∀ n : Fin 50, densSupG (n.val + 37650) < 2 ^ 1771 := by decide
private theorem cs_w4 : ∀ n : Fin 50, centredStar (densSupG (n.val + 37700)) (centF (n.val + 37700)) = true := by decide
private theorem cl_w4 : ∀ n : Fin 50, centF (n.val + 37700) < 23 := by decide
private theorem bd_w4 : ∀ n : Fin 50, densSupG (n.val + 37700) < 2 ^ 1771 := by decide
private theorem cs_w5 : ∀ n : Fin 50, centredStar (densSupG (n.val + 37750)) (centF (n.val + 37750)) = true := by decide
private theorem cl_w5 : ∀ n : Fin 50, centF (n.val + 37750) < 23 := by decide
private theorem bd_w5 : ∀ n : Fin 50, densSupG (n.val + 37750) < 2 ^ 1771 := by decide
private theorem cs_w6 : ∀ n : Fin 50, centredStar (densSupG (n.val + 37800)) (centF (n.val + 37800)) = true := by decide
private theorem cl_w6 : ∀ n : Fin 50, centF (n.val + 37800) < 23 := by decide
private theorem bd_w6 : ∀ n : Fin 50, densSupG (n.val + 37800) < 2 ^ 1771 := by decide
private theorem cs_w7 : ∀ n : Fin 50, centredStar (densSupG (n.val + 37850)) (centF (n.val + 37850)) = true := by decide
private theorem cl_w7 : ∀ n : Fin 50, centF (n.val + 37850) < 23 := by decide
private theorem bd_w7 : ∀ n : Fin 50, densSupG (n.val + 37850) < 2 ^ 1771 := by decide
private theorem cs_w8 : ∀ n : Fin 50, centredStar (densSupG (n.val + 37900)) (centF (n.val + 37900)) = true := by decide
private theorem cl_w8 : ∀ n : Fin 50, centF (n.val + 37900) < 23 := by decide
private theorem bd_w8 : ∀ n : Fin 50, densSupG (n.val + 37900) < 2 ^ 1771 := by decide
private theorem cs_w9 : ∀ n : Fin 50, centredStar (densSupG (n.val + 37950)) (centF (n.val + 37950)) = true := by decide
private theorem cl_w9 : ∀ n : Fin 50, centF (n.val + 37950) < 23 := by decide
private theorem bd_w9 : ∀ n : Fin 50, densSupG (n.val + 37950) < 2 ^ 1771 := by decide
private theorem cs_w10 : ∀ n : Fin 50, centredStar (densSupG (n.val + 38000)) (centF (n.val + 38000)) = true := by decide
private theorem cl_w10 : ∀ n : Fin 50, centF (n.val + 38000) < 23 := by decide
private theorem bd_w10 : ∀ n : Fin 50, densSupG (n.val + 38000) < 2 ^ 1771 := by decide
private theorem cs_w11 : ∀ n : Fin 50, centredStar (densSupG (n.val + 38050)) (centF (n.val + 38050)) = true := by decide
private theorem cl_w11 : ∀ n : Fin 50, centF (n.val + 38050) < 23 := by decide
private theorem bd_w11 : ∀ n : Fin 50, densSupG (n.val + 38050) < 2 ^ 1771 := by decide
private theorem cs_w12 : ∀ n : Fin 50, centredStar (densSupG (n.val + 38100)) (centF (n.val + 38100)) = true := by decide
private theorem cl_w12 : ∀ n : Fin 50, centF (n.val + 38100) < 23 := by decide
private theorem bd_w12 : ∀ n : Fin 50, densSupG (n.val + 38100) < 2 ^ 1771 := by decide
private theorem cs_w13 : ∀ n : Fin 50, centredStar (densSupG (n.val + 38150)) (centF (n.val + 38150)) = true := by decide
private theorem cl_w13 : ∀ n : Fin 50, centF (n.val + 38150) < 23 := by decide
private theorem bd_w13 : ∀ n : Fin 50, densSupG (n.val + 38150) < 2 ^ 1771 := by decide
private theorem cs_w14 : ∀ n : Fin 50, centredStar (densSupG (n.val + 38200)) (centF (n.val + 38200)) = true := by decide
private theorem cl_w14 : ∀ n : Fin 50, centF (n.val + 38200) < 23 := by decide
private theorem bd_w14 : ∀ n : Fin 50, densSupG (n.val + 38200) < 2 ^ 1771 := by decide
private theorem cs_w15 : ∀ n : Fin 50, centredStar (densSupG (n.val + 38250)) (centF (n.val + 38250)) = true := by decide
private theorem cl_w15 : ∀ n : Fin 50, centF (n.val + 38250) < 23 := by decide
private theorem bd_w15 : ∀ n : Fin 50, densSupG (n.val + 38250) < 2 ^ 1771 := by decide
private theorem cs_w16 : ∀ n : Fin 50, centredStar (densSupG (n.val + 38300)) (centF (n.val + 38300)) = true := by decide
private theorem cl_w16 : ∀ n : Fin 50, centF (n.val + 38300) < 23 := by decide
private theorem bd_w16 : ∀ n : Fin 50, densSupG (n.val + 38300) < 2 ^ 1771 := by decide
private theorem cs_w17 : ∀ n : Fin 50, centredStar (densSupG (n.val + 38350)) (centF (n.val + 38350)) = true := by decide
private theorem cl_w17 : ∀ n : Fin 50, centF (n.val + 38350) < 23 := by decide
private theorem bd_w17 : ∀ n : Fin 50, densSupG (n.val + 38350) < 2 ^ 1771 := by decide
private theorem cs_w18 : ∀ n : Fin 50, centredStar (densSupG (n.val + 38400)) (centF (n.val + 38400)) = true := by decide
private theorem cl_w18 : ∀ n : Fin 50, centF (n.val + 38400) < 23 := by decide
private theorem bd_w18 : ∀ n : Fin 50, densSupG (n.val + 38400) < 2 ^ 1771 := by decide
private theorem cs_w19 : ∀ n : Fin 50, centredStar (densSupG (n.val + 38450)) (centF (n.val + 38450)) = true := by decide
private theorem cl_w19 : ∀ n : Fin 50, centF (n.val + 38450) < 23 := by decide
private theorem bd_w19 : ∀ n : Fin 50, densSupG (n.val + 38450) < 2 ^ 1771 := by decide
private theorem cs_w20 : ∀ n : Fin 50, centredStar (densSupG (n.val + 38500)) (centF (n.val + 38500)) = true := by decide
private theorem cl_w20 : ∀ n : Fin 50, centF (n.val + 38500) < 23 := by decide
private theorem bd_w20 : ∀ n : Fin 50, densSupG (n.val + 38500) < 2 ^ 1771 := by decide
private theorem cs_w21 : ∀ n : Fin 50, centredStar (densSupG (n.val + 38550)) (centF (n.val + 38550)) = true := by decide
private theorem cl_w21 : ∀ n : Fin 50, centF (n.val + 38550) < 23 := by decide
private theorem bd_w21 : ∀ n : Fin 50, densSupG (n.val + 38550) < 2 ^ 1771 := by decide
private theorem cs_w22 : ∀ n : Fin 50, centredStar (densSupG (n.val + 38600)) (centF (n.val + 38600)) = true := by decide
private theorem cl_w22 : ∀ n : Fin 50, centF (n.val + 38600) < 23 := by decide
private theorem bd_w22 : ∀ n : Fin 50, densSupG (n.val + 38600) < 2 ^ 1771 := by decide
private theorem cs_w23 : ∀ n : Fin 50, centredStar (densSupG (n.val + 38650)) (centF (n.val + 38650)) = true := by decide
private theorem cl_w23 : ∀ n : Fin 50, centF (n.val + 38650) < 23 := by decide
private theorem bd_w23 : ∀ n : Fin 50, densSupG (n.val + 38650) < 2 ^ 1771 := by decide
private theorem cs_w24 : ∀ n : Fin 50, centredStar (densSupG (n.val + 38700)) (centF (n.val + 38700)) = true := by decide
private theorem cl_w24 : ∀ n : Fin 50, centF (n.val + 38700) < 23 := by decide
private theorem bd_w24 : ∀ n : Fin 50, densSupG (n.val + 38700) < 2 ^ 1771 := by decide
private theorem cs_w25 : ∀ n : Fin 50, centredStar (densSupG (n.val + 38750)) (centF (n.val + 38750)) = true := by decide
private theorem cl_w25 : ∀ n : Fin 50, centF (n.val + 38750) < 23 := by decide
private theorem bd_w25 : ∀ n : Fin 50, densSupG (n.val + 38750) < 2 ^ 1771 := by decide
private theorem cs_w26 : ∀ n : Fin 50, centredStar (densSupG (n.val + 38800)) (centF (n.val + 38800)) = true := by decide
private theorem cl_w26 : ∀ n : Fin 50, centF (n.val + 38800) < 23 := by decide
private theorem bd_w26 : ∀ n : Fin 50, densSupG (n.val + 38800) < 2 ^ 1771 := by decide
private theorem cs_w27 : ∀ n : Fin 50, centredStar (densSupG (n.val + 38850)) (centF (n.val + 38850)) = true := by decide
private theorem cl_w27 : ∀ n : Fin 50, centF (n.val + 38850) < 23 := by decide
private theorem bd_w27 : ∀ n : Fin 50, densSupG (n.val + 38850) < 2 ^ 1771 := by decide
private theorem cs_w28 : ∀ n : Fin 50, centredStar (densSupG (n.val + 38900)) (centF (n.val + 38900)) = true := by decide
private theorem cl_w28 : ∀ n : Fin 50, centF (n.val + 38900) < 23 := by decide
private theorem bd_w28 : ∀ n : Fin 50, densSupG (n.val + 38900) < 2 ^ 1771 := by decide
private theorem cs_w29 : ∀ n : Fin 50, centredStar (densSupG (n.val + 38950)) (centF (n.val + 38950)) = true := by decide
private theorem cl_w29 : ∀ n : Fin 50, centF (n.val + 38950) < 23 := by decide
private theorem bd_w29 : ∀ n : Fin 50, densSupG (n.val + 38950) < 2 ^ 1771 := by decide
private theorem cs_w30 : ∀ n : Fin 50, centredStar (densSupG (n.val + 39000)) (centF (n.val + 39000)) = true := by decide
private theorem cl_w30 : ∀ n : Fin 50, centF (n.val + 39000) < 23 := by decide
private theorem bd_w30 : ∀ n : Fin 50, densSupG (n.val + 39000) < 2 ^ 1771 := by decide
private theorem cs_w31 : ∀ n : Fin 50, centredStar (densSupG (n.val + 39050)) (centF (n.val + 39050)) = true := by decide
private theorem cl_w31 : ∀ n : Fin 50, centF (n.val + 39050) < 23 := by decide
private theorem bd_w31 : ∀ n : Fin 50, densSupG (n.val + 39050) < 2 ^ 1771 := by decide
private theorem cs_w32 : ∀ n : Fin 50, centredStar (densSupG (n.val + 39100)) (centF (n.val + 39100)) = true := by decide
private theorem cl_w32 : ∀ n : Fin 50, centF (n.val + 39100) < 23 := by decide
private theorem bd_w32 : ∀ n : Fin 50, densSupG (n.val + 39100) < 2 ^ 1771 := by decide
private theorem cs_w33 : ∀ n : Fin 50, centredStar (densSupG (n.val + 39150)) (centF (n.val + 39150)) = true := by decide
private theorem cl_w33 : ∀ n : Fin 50, centF (n.val + 39150) < 23 := by decide
private theorem bd_w33 : ∀ n : Fin 50, densSupG (n.val + 39150) < 2 ^ 1771 := by decide
private theorem cs_w34 : ∀ n : Fin 50, centredStar (densSupG (n.val + 39200)) (centF (n.val + 39200)) = true := by decide
private theorem cl_w34 : ∀ n : Fin 50, centF (n.val + 39200) < 23 := by decide
private theorem bd_w34 : ∀ n : Fin 50, densSupG (n.val + 39200) < 2 ^ 1771 := by decide
private theorem cs_w35 : ∀ n : Fin 50, centredStar (densSupG (n.val + 39250)) (centF (n.val + 39250)) = true := by decide
private theorem cl_w35 : ∀ n : Fin 50, centF (n.val + 39250) < 23 := by decide
private theorem bd_w35 : ∀ n : Fin 50, densSupG (n.val + 39250) < 2 ^ 1771 := by decide
private theorem cs_w36 : ∀ n : Fin 50, centredStar (densSupG (n.val + 39300)) (centF (n.val + 39300)) = true := by decide
private theorem cl_w36 : ∀ n : Fin 50, centF (n.val + 39300) < 23 := by decide
private theorem bd_w36 : ∀ n : Fin 50, densSupG (n.val + 39300) < 2 ^ 1771 := by decide
private theorem cs_w37 : ∀ n : Fin 50, centredStar (densSupG (n.val + 39350)) (centF (n.val + 39350)) = true := by decide
private theorem cl_w37 : ∀ n : Fin 50, centF (n.val + 39350) < 23 := by decide
private theorem bd_w37 : ∀ n : Fin 50, densSupG (n.val + 39350) < 2 ^ 1771 := by decide
private theorem cs_w38 : ∀ n : Fin 50, centredStar (densSupG (n.val + 39400)) (centF (n.val + 39400)) = true := by decide
private theorem cl_w38 : ∀ n : Fin 50, centF (n.val + 39400) < 23 := by decide
private theorem bd_w38 : ∀ n : Fin 50, densSupG (n.val + 39400) < 2 ^ 1771 := by decide
private theorem cs_w39 : ∀ n : Fin 50, centredStar (densSupG (n.val + 39450)) (centF (n.val + 39450)) = true := by decide
private theorem cl_w39 : ∀ n : Fin 50, centF (n.val + 39450) < 23 := by decide
private theorem bd_w39 : ∀ n : Fin 50, densSupG (n.val + 39450) < 2 ^ 1771 := by decide
private theorem cs_w40 : ∀ n : Fin 50, centredStar (densSupG (n.val + 39500)) (centF (n.val + 39500)) = true := by decide
private theorem cl_w40 : ∀ n : Fin 50, centF (n.val + 39500) < 23 := by decide
private theorem bd_w40 : ∀ n : Fin 50, densSupG (n.val + 39500) < 2 ^ 1771 := by decide
private theorem cs_w41 : ∀ n : Fin 50, centredStar (densSupG (n.val + 39550)) (centF (n.val + 39550)) = true := by decide
private theorem cl_w41 : ∀ n : Fin 50, centF (n.val + 39550) < 23 := by decide
private theorem bd_w41 : ∀ n : Fin 50, densSupG (n.val + 39550) < 2 ^ 1771 := by decide
private theorem cs_w42 : ∀ n : Fin 50, centredStar (densSupG (n.val + 39600)) (centF (n.val + 39600)) = true := by decide
private theorem cl_w42 : ∀ n : Fin 50, centF (n.val + 39600) < 23 := by decide
private theorem bd_w42 : ∀ n : Fin 50, densSupG (n.val + 39600) < 2 ^ 1771 := by decide
private theorem cs_w43 : ∀ n : Fin 50, centredStar (densSupG (n.val + 39650)) (centF (n.val + 39650)) = true := by decide
private theorem cl_w43 : ∀ n : Fin 50, centF (n.val + 39650) < 23 := by decide
private theorem bd_w43 : ∀ n : Fin 50, densSupG (n.val + 39650) < 2 ^ 1771 := by decide
private theorem cs_w44 : ∀ n : Fin 50, centredStar (densSupG (n.val + 39700)) (centF (n.val + 39700)) = true := by decide
private theorem cl_w44 : ∀ n : Fin 50, centF (n.val + 39700) < 23 := by decide
private theorem bd_w44 : ∀ n : Fin 50, densSupG (n.val + 39700) < 2 ^ 1771 := by decide
private theorem cs_w45 : ∀ n : Fin 50, centredStar (densSupG (n.val + 39750)) (centF (n.val + 39750)) = true := by decide
private theorem cl_w45 : ∀ n : Fin 50, centF (n.val + 39750) < 23 := by decide
private theorem bd_w45 : ∀ n : Fin 50, densSupG (n.val + 39750) < 2 ^ 1771 := by decide
private theorem cs_w46 : ∀ n : Fin 50, centredStar (densSupG (n.val + 39800)) (centF (n.val + 39800)) = true := by decide
private theorem cl_w46 : ∀ n : Fin 50, centF (n.val + 39800) < 23 := by decide
private theorem bd_w46 : ∀ n : Fin 50, densSupG (n.val + 39800) < 2 ^ 1771 := by decide
private theorem cs_w47 : ∀ n : Fin 50, centredStar (densSupG (n.val + 39850)) (centF (n.val + 39850)) = true := by decide
private theorem cl_w47 : ∀ n : Fin 50, centF (n.val + 39850) < 23 := by decide
private theorem bd_w47 : ∀ n : Fin 50, densSupG (n.val + 39850) < 2 ^ 1771 := by decide
private theorem cs_w48 : ∀ n : Fin 50, centredStar (densSupG (n.val + 39900)) (centF (n.val + 39900)) = true := by decide
private theorem cl_w48 : ∀ n : Fin 50, centF (n.val + 39900) < 23 := by decide
private theorem bd_w48 : ∀ n : Fin 50, densSupG (n.val + 39900) < 2 ^ 1771 := by decide
private theorem cs_w49 : ∀ n : Fin 50, centredStar (densSupG (n.val + 39950)) (centF (n.val + 39950)) = true := by decide
private theorem cl_w49 : ∀ n : Fin 50, centF (n.val + 39950) < 23 := by decide
private theorem bd_w49 : ∀ n : Fin 50, densSupG (n.val + 39950) < 2 ^ 1771 := by decide
theorem centredStar_range : ∀ n, 37500 ≤ n → n < 40000 → centredStar (densSupG n) (centF n) = true := by
  intro n hlo hhi
  by_cases h0 : n < 37550
  · have hr : n - 37500 < 50 := by omega
    have heq : n = (n - 37500) + 37500 := by omega
    rw [heq]
    exact cs_w0 ⟨n - 37500, hr⟩
  ·
    by_cases h1 : n < 37600
    ·
      have hr : n - 37550 < 50 := by omega
      have heq : n = (n - 37550) + 37550 := by omega
      rw [heq]
      exact cs_w1 ⟨n - 37550, hr⟩
    ·
      by_cases h2 : n < 37650
      ·
        have hr : n - 37600 < 50 := by omega
        have heq : n = (n - 37600) + 37600 := by omega
        rw [heq]
        exact cs_w2 ⟨n - 37600, hr⟩
      ·
        by_cases h3 : n < 37700
        ·
          have hr : n - 37650 < 50 := by omega
          have heq : n = (n - 37650) + 37650 := by omega
          rw [heq]
          exact cs_w3 ⟨n - 37650, hr⟩
        ·
          by_cases h4 : n < 37750
          ·
            have hr : n - 37700 < 50 := by omega
            have heq : n = (n - 37700) + 37700 := by omega
            rw [heq]
            exact cs_w4 ⟨n - 37700, hr⟩
          ·
            by_cases h5 : n < 37800
            ·
              have hr : n - 37750 < 50 := by omega
              have heq : n = (n - 37750) + 37750 := by omega
              rw [heq]
              exact cs_w5 ⟨n - 37750, hr⟩
            ·
              by_cases h6 : n < 37850
              ·
                have hr : n - 37800 < 50 := by omega
                have heq : n = (n - 37800) + 37800 := by omega
                rw [heq]
                exact cs_w6 ⟨n - 37800, hr⟩
              ·
                by_cases h7 : n < 37900
                ·
                  have hr : n - 37850 < 50 := by omega
                  have heq : n = (n - 37850) + 37850 := by omega
                  rw [heq]
                  exact cs_w7 ⟨n - 37850, hr⟩
                ·
                  by_cases h8 : n < 37950
                  ·
                    have hr : n - 37900 < 50 := by omega
                    have heq : n = (n - 37900) + 37900 := by omega
                    rw [heq]
                    exact cs_w8 ⟨n - 37900, hr⟩
                  ·
                    by_cases h9 : n < 38000
                    ·
                      have hr : n - 37950 < 50 := by omega
                      have heq : n = (n - 37950) + 37950 := by omega
                      rw [heq]
                      exact cs_w9 ⟨n - 37950, hr⟩
                    ·
                      by_cases h10 : n < 38050
                      ·
                        have hr : n - 38000 < 50 := by omega
                        have heq : n = (n - 38000) + 38000 := by omega
                        rw [heq]
                        exact cs_w10 ⟨n - 38000, hr⟩
                      ·
                        by_cases h11 : n < 38100
                        ·
                          have hr : n - 38050 < 50 := by omega
                          have heq : n = (n - 38050) + 38050 := by omega
                          rw [heq]
                          exact cs_w11 ⟨n - 38050, hr⟩
                        ·
                          by_cases h12 : n < 38150
                          ·
                            have hr : n - 38100 < 50 := by omega
                            have heq : n = (n - 38100) + 38100 := by omega
                            rw [heq]
                            exact cs_w12 ⟨n - 38100, hr⟩
                          ·
                            by_cases h13 : n < 38200
                            ·
                              have hr : n - 38150 < 50 := by omega
                              have heq : n = (n - 38150) + 38150 := by omega
                              rw [heq]
                              exact cs_w13 ⟨n - 38150, hr⟩
                            ·
                              by_cases h14 : n < 38250
                              ·
                                have hr : n - 38200 < 50 := by omega
                                have heq : n = (n - 38200) + 38200 := by omega
                                rw [heq]
                                exact cs_w14 ⟨n - 38200, hr⟩
                              ·
                                by_cases h15 : n < 38300
                                ·
                                  have hr : n - 38250 < 50 := by omega
                                  have heq : n = (n - 38250) + 38250 := by omega
                                  rw [heq]
                                  exact cs_w15 ⟨n - 38250, hr⟩
                                ·
                                  by_cases h16 : n < 38350
                                  ·
                                    have hr : n - 38300 < 50 := by omega
                                    have heq : n = (n - 38300) + 38300 := by omega
                                    rw [heq]
                                    exact cs_w16 ⟨n - 38300, hr⟩
                                  ·
                                    by_cases h17 : n < 38400
                                    ·
                                      have hr : n - 38350 < 50 := by omega
                                      have heq : n = (n - 38350) + 38350 := by omega
                                      rw [heq]
                                      exact cs_w17 ⟨n - 38350, hr⟩
                                    ·
                                      by_cases h18 : n < 38450
                                      ·
                                        have hr : n - 38400 < 50 := by omega
                                        have heq : n = (n - 38400) + 38400 := by omega
                                        rw [heq]
                                        exact cs_w18 ⟨n - 38400, hr⟩
                                      ·
                                        by_cases h19 : n < 38500
                                        ·
                                          have hr : n - 38450 < 50 := by omega
                                          have heq : n = (n - 38450) + 38450 := by omega
                                          rw [heq]
                                          exact cs_w19 ⟨n - 38450, hr⟩
                                        ·
                                          by_cases h20 : n < 38550
                                          ·
                                            have hr : n - 38500 < 50 := by omega
                                            have heq : n = (n - 38500) + 38500 := by omega
                                            rw [heq]
                                            exact cs_w20 ⟨n - 38500, hr⟩
                                          ·
                                            by_cases h21 : n < 38600
                                            ·
                                              have hr : n - 38550 < 50 := by omega
                                              have heq : n = (n - 38550) + 38550 := by omega
                                              rw [heq]
                                              exact cs_w21 ⟨n - 38550, hr⟩
                                            ·
                                              by_cases h22 : n < 38650
                                              ·
                                                have hr : n - 38600 < 50 := by omega
                                                have heq : n = (n - 38600) + 38600 := by omega
                                                rw [heq]
                                                exact cs_w22 ⟨n - 38600, hr⟩
                                              ·
                                                by_cases h23 : n < 38700
                                                ·
                                                  have hr : n - 38650 < 50 := by omega
                                                  have heq : n = (n - 38650) + 38650 := by omega
                                                  rw [heq]
                                                  exact cs_w23 ⟨n - 38650, hr⟩
                                                ·
                                                  by_cases h24 : n < 38750
                                                  ·
                                                    have hr : n - 38700 < 50 := by omega
                                                    have heq : n = (n - 38700) + 38700 := by omega
                                                    rw [heq]
                                                    exact cs_w24 ⟨n - 38700, hr⟩
                                                  ·
                                                    by_cases h25 : n < 38800
                                                    ·
                                                      have hr : n - 38750 < 50 := by omega
                                                      have heq : n = (n - 38750) + 38750 := by omega
                                                      rw [heq]
                                                      exact cs_w25 ⟨n - 38750, hr⟩
                                                    ·
                                                      by_cases h26 : n < 38850
                                                      ·
                                                        have hr : n - 38800 < 50 := by omega
                                                        have heq : n = (n - 38800) + 38800 := by omega
                                                        rw [heq]
                                                        exact cs_w26 ⟨n - 38800, hr⟩
                                                      ·
                                                        by_cases h27 : n < 38900
                                                        ·
                                                          have hr : n - 38850 < 50 := by omega
                                                          have heq : n = (n - 38850) + 38850 := by omega
                                                          rw [heq]
                                                          exact cs_w27 ⟨n - 38850, hr⟩
                                                        ·
                                                          by_cases h28 : n < 38950
                                                          ·
                                                            have hr : n - 38900 < 50 := by omega
                                                            have heq : n = (n - 38900) + 38900 := by omega
                                                            rw [heq]
                                                            exact cs_w28 ⟨n - 38900, hr⟩
                                                          ·
                                                            by_cases h29 : n < 39000
                                                            ·
                                                              have hr : n - 38950 < 50 := by omega
                                                              have heq : n = (n - 38950) + 38950 := by omega
                                                              rw [heq]
                                                              exact cs_w29 ⟨n - 38950, hr⟩
                                                            ·
                                                              by_cases h30 : n < 39050
                                                              ·
                                                                have hr : n - 39000 < 50 := by omega
                                                                have heq : n = (n - 39000) + 39000 := by omega
                                                                rw [heq]
                                                                exact cs_w30 ⟨n - 39000, hr⟩
                                                              ·
                                                                by_cases h31 : n < 39100
                                                                ·
                                                                  have hr : n - 39050 < 50 := by omega
                                                                  have heq : n = (n - 39050) + 39050 := by omega
                                                                  rw [heq]
                                                                  exact cs_w31 ⟨n - 39050, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 39150
                                                                  ·
                                                                    have hr : n - 39100 < 50 := by omega
                                                                    have heq : n = (n - 39100) + 39100 := by omega
                                                                    rw [heq]
                                                                    exact cs_w32 ⟨n - 39100, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 39200
                                                                    ·
                                                                      have hr : n - 39150 < 50 := by omega
                                                                      have heq : n = (n - 39150) + 39150 := by omega
                                                                      rw [heq]
                                                                      exact cs_w33 ⟨n - 39150, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 39250
                                                                      ·
                                                                        have hr : n - 39200 < 50 := by omega
                                                                        have heq : n = (n - 39200) + 39200 := by omega
                                                                        rw [heq]
                                                                        exact cs_w34 ⟨n - 39200, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 39300
                                                                        ·
                                                                          have hr : n - 39250 < 50 := by omega
                                                                          have heq : n = (n - 39250) + 39250 := by omega
                                                                          rw [heq]
                                                                          exact cs_w35 ⟨n - 39250, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 39350
                                                                          ·
                                                                            have hr : n - 39300 < 50 := by omega
                                                                            have heq : n = (n - 39300) + 39300 := by omega
                                                                            rw [heq]
                                                                            exact cs_w36 ⟨n - 39300, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 39400
                                                                            ·
                                                                              have hr : n - 39350 < 50 := by omega
                                                                              have heq : n = (n - 39350) + 39350 := by omega
                                                                              rw [heq]
                                                                              exact cs_w37 ⟨n - 39350, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 39450
                                                                              ·
                                                                                have hr : n - 39400 < 50 := by omega
                                                                                have heq : n = (n - 39400) + 39400 := by omega
                                                                                rw [heq]
                                                                                exact cs_w38 ⟨n - 39400, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 39500
                                                                                ·
                                                                                  have hr : n - 39450 < 50 := by omega
                                                                                  have heq : n = (n - 39450) + 39450 := by omega
                                                                                  rw [heq]
                                                                                  exact cs_w39 ⟨n - 39450, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 39550
                                                                                  ·
                                                                                    have hr : n - 39500 < 50 := by omega
                                                                                    have heq : n = (n - 39500) + 39500 := by omega
                                                                                    rw [heq]
                                                                                    exact cs_w40 ⟨n - 39500, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 39600
                                                                                    ·
                                                                                      have hr : n - 39550 < 50 := by omega
                                                                                      have heq : n = (n - 39550) + 39550 := by omega
                                                                                      rw [heq]
                                                                                      exact cs_w41 ⟨n - 39550, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 39650
                                                                                      ·
                                                                                        have hr : n - 39600 < 50 := by omega
                                                                                        have heq : n = (n - 39600) + 39600 := by omega
                                                                                        rw [heq]
                                                                                        exact cs_w42 ⟨n - 39600, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 39700
                                                                                        ·
                                                                                          have hr : n - 39650 < 50 := by omega
                                                                                          have heq : n = (n - 39650) + 39650 := by omega
                                                                                          rw [heq]
                                                                                          exact cs_w43 ⟨n - 39650, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 39750
                                                                                          ·
                                                                                            have hr : n - 39700 < 50 := by omega
                                                                                            have heq : n = (n - 39700) + 39700 := by omega
                                                                                            rw [heq]
                                                                                            exact cs_w44 ⟨n - 39700, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 39800
                                                                                            ·
                                                                                              have hr : n - 39750 < 50 := by omega
                                                                                              have heq : n = (n - 39750) + 39750 := by omega
                                                                                              rw [heq]
                                                                                              exact cs_w45 ⟨n - 39750, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 39850
                                                                                              ·
                                                                                                have hr : n - 39800 < 50 := by omega
                                                                                                have heq : n = (n - 39800) + 39800 := by omega
                                                                                                rw [heq]
                                                                                                exact cs_w46 ⟨n - 39800, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 39900
                                                                                                ·
                                                                                                  have hr : n - 39850 < 50 := by omega
                                                                                                  have heq : n = (n - 39850) + 39850 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cs_w47 ⟨n - 39850, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 39950
                                                                                                  ·
                                                                                                    have hr : n - 39900 < 50 := by omega
                                                                                                    have heq : n = (n - 39900) + 39900 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w48 ⟨n - 39900, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 39950 < 50 := by omega
                                                                                                    have heq : n = (n - 39950) + 39950 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w49 ⟨n - 39950, hr⟩


theorem centF_lt_range : ∀ n, 37500 ≤ n → n < 40000 → centF n < 23 := by
  intro n hlo hhi
  by_cases h0 : n < 37550
  · have hr : n - 37500 < 50 := by omega
    have heq : n = (n - 37500) + 37500 := by omega
    rw [heq]
    exact cl_w0 ⟨n - 37500, hr⟩
  ·
    by_cases h1 : n < 37600
    ·
      have hr : n - 37550 < 50 := by omega
      have heq : n = (n - 37550) + 37550 := by omega
      rw [heq]
      exact cl_w1 ⟨n - 37550, hr⟩
    ·
      by_cases h2 : n < 37650
      ·
        have hr : n - 37600 < 50 := by omega
        have heq : n = (n - 37600) + 37600 := by omega
        rw [heq]
        exact cl_w2 ⟨n - 37600, hr⟩
      ·
        by_cases h3 : n < 37700
        ·
          have hr : n - 37650 < 50 := by omega
          have heq : n = (n - 37650) + 37650 := by omega
          rw [heq]
          exact cl_w3 ⟨n - 37650, hr⟩
        ·
          by_cases h4 : n < 37750
          ·
            have hr : n - 37700 < 50 := by omega
            have heq : n = (n - 37700) + 37700 := by omega
            rw [heq]
            exact cl_w4 ⟨n - 37700, hr⟩
          ·
            by_cases h5 : n < 37800
            ·
              have hr : n - 37750 < 50 := by omega
              have heq : n = (n - 37750) + 37750 := by omega
              rw [heq]
              exact cl_w5 ⟨n - 37750, hr⟩
            ·
              by_cases h6 : n < 37850
              ·
                have hr : n - 37800 < 50 := by omega
                have heq : n = (n - 37800) + 37800 := by omega
                rw [heq]
                exact cl_w6 ⟨n - 37800, hr⟩
              ·
                by_cases h7 : n < 37900
                ·
                  have hr : n - 37850 < 50 := by omega
                  have heq : n = (n - 37850) + 37850 := by omega
                  rw [heq]
                  exact cl_w7 ⟨n - 37850, hr⟩
                ·
                  by_cases h8 : n < 37950
                  ·
                    have hr : n - 37900 < 50 := by omega
                    have heq : n = (n - 37900) + 37900 := by omega
                    rw [heq]
                    exact cl_w8 ⟨n - 37900, hr⟩
                  ·
                    by_cases h9 : n < 38000
                    ·
                      have hr : n - 37950 < 50 := by omega
                      have heq : n = (n - 37950) + 37950 := by omega
                      rw [heq]
                      exact cl_w9 ⟨n - 37950, hr⟩
                    ·
                      by_cases h10 : n < 38050
                      ·
                        have hr : n - 38000 < 50 := by omega
                        have heq : n = (n - 38000) + 38000 := by omega
                        rw [heq]
                        exact cl_w10 ⟨n - 38000, hr⟩
                      ·
                        by_cases h11 : n < 38100
                        ·
                          have hr : n - 38050 < 50 := by omega
                          have heq : n = (n - 38050) + 38050 := by omega
                          rw [heq]
                          exact cl_w11 ⟨n - 38050, hr⟩
                        ·
                          by_cases h12 : n < 38150
                          ·
                            have hr : n - 38100 < 50 := by omega
                            have heq : n = (n - 38100) + 38100 := by omega
                            rw [heq]
                            exact cl_w12 ⟨n - 38100, hr⟩
                          ·
                            by_cases h13 : n < 38200
                            ·
                              have hr : n - 38150 < 50 := by omega
                              have heq : n = (n - 38150) + 38150 := by omega
                              rw [heq]
                              exact cl_w13 ⟨n - 38150, hr⟩
                            ·
                              by_cases h14 : n < 38250
                              ·
                                have hr : n - 38200 < 50 := by omega
                                have heq : n = (n - 38200) + 38200 := by omega
                                rw [heq]
                                exact cl_w14 ⟨n - 38200, hr⟩
                              ·
                                by_cases h15 : n < 38300
                                ·
                                  have hr : n - 38250 < 50 := by omega
                                  have heq : n = (n - 38250) + 38250 := by omega
                                  rw [heq]
                                  exact cl_w15 ⟨n - 38250, hr⟩
                                ·
                                  by_cases h16 : n < 38350
                                  ·
                                    have hr : n - 38300 < 50 := by omega
                                    have heq : n = (n - 38300) + 38300 := by omega
                                    rw [heq]
                                    exact cl_w16 ⟨n - 38300, hr⟩
                                  ·
                                    by_cases h17 : n < 38400
                                    ·
                                      have hr : n - 38350 < 50 := by omega
                                      have heq : n = (n - 38350) + 38350 := by omega
                                      rw [heq]
                                      exact cl_w17 ⟨n - 38350, hr⟩
                                    ·
                                      by_cases h18 : n < 38450
                                      ·
                                        have hr : n - 38400 < 50 := by omega
                                        have heq : n = (n - 38400) + 38400 := by omega
                                        rw [heq]
                                        exact cl_w18 ⟨n - 38400, hr⟩
                                      ·
                                        by_cases h19 : n < 38500
                                        ·
                                          have hr : n - 38450 < 50 := by omega
                                          have heq : n = (n - 38450) + 38450 := by omega
                                          rw [heq]
                                          exact cl_w19 ⟨n - 38450, hr⟩
                                        ·
                                          by_cases h20 : n < 38550
                                          ·
                                            have hr : n - 38500 < 50 := by omega
                                            have heq : n = (n - 38500) + 38500 := by omega
                                            rw [heq]
                                            exact cl_w20 ⟨n - 38500, hr⟩
                                          ·
                                            by_cases h21 : n < 38600
                                            ·
                                              have hr : n - 38550 < 50 := by omega
                                              have heq : n = (n - 38550) + 38550 := by omega
                                              rw [heq]
                                              exact cl_w21 ⟨n - 38550, hr⟩
                                            ·
                                              by_cases h22 : n < 38650
                                              ·
                                                have hr : n - 38600 < 50 := by omega
                                                have heq : n = (n - 38600) + 38600 := by omega
                                                rw [heq]
                                                exact cl_w22 ⟨n - 38600, hr⟩
                                              ·
                                                by_cases h23 : n < 38700
                                                ·
                                                  have hr : n - 38650 < 50 := by omega
                                                  have heq : n = (n - 38650) + 38650 := by omega
                                                  rw [heq]
                                                  exact cl_w23 ⟨n - 38650, hr⟩
                                                ·
                                                  by_cases h24 : n < 38750
                                                  ·
                                                    have hr : n - 38700 < 50 := by omega
                                                    have heq : n = (n - 38700) + 38700 := by omega
                                                    rw [heq]
                                                    exact cl_w24 ⟨n - 38700, hr⟩
                                                  ·
                                                    by_cases h25 : n < 38800
                                                    ·
                                                      have hr : n - 38750 < 50 := by omega
                                                      have heq : n = (n - 38750) + 38750 := by omega
                                                      rw [heq]
                                                      exact cl_w25 ⟨n - 38750, hr⟩
                                                    ·
                                                      by_cases h26 : n < 38850
                                                      ·
                                                        have hr : n - 38800 < 50 := by omega
                                                        have heq : n = (n - 38800) + 38800 := by omega
                                                        rw [heq]
                                                        exact cl_w26 ⟨n - 38800, hr⟩
                                                      ·
                                                        by_cases h27 : n < 38900
                                                        ·
                                                          have hr : n - 38850 < 50 := by omega
                                                          have heq : n = (n - 38850) + 38850 := by omega
                                                          rw [heq]
                                                          exact cl_w27 ⟨n - 38850, hr⟩
                                                        ·
                                                          by_cases h28 : n < 38950
                                                          ·
                                                            have hr : n - 38900 < 50 := by omega
                                                            have heq : n = (n - 38900) + 38900 := by omega
                                                            rw [heq]
                                                            exact cl_w28 ⟨n - 38900, hr⟩
                                                          ·
                                                            by_cases h29 : n < 39000
                                                            ·
                                                              have hr : n - 38950 < 50 := by omega
                                                              have heq : n = (n - 38950) + 38950 := by omega
                                                              rw [heq]
                                                              exact cl_w29 ⟨n - 38950, hr⟩
                                                            ·
                                                              by_cases h30 : n < 39050
                                                              ·
                                                                have hr : n - 39000 < 50 := by omega
                                                                have heq : n = (n - 39000) + 39000 := by omega
                                                                rw [heq]
                                                                exact cl_w30 ⟨n - 39000, hr⟩
                                                              ·
                                                                by_cases h31 : n < 39100
                                                                ·
                                                                  have hr : n - 39050 < 50 := by omega
                                                                  have heq : n = (n - 39050) + 39050 := by omega
                                                                  rw [heq]
                                                                  exact cl_w31 ⟨n - 39050, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 39150
                                                                  ·
                                                                    have hr : n - 39100 < 50 := by omega
                                                                    have heq : n = (n - 39100) + 39100 := by omega
                                                                    rw [heq]
                                                                    exact cl_w32 ⟨n - 39100, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 39200
                                                                    ·
                                                                      have hr : n - 39150 < 50 := by omega
                                                                      have heq : n = (n - 39150) + 39150 := by omega
                                                                      rw [heq]
                                                                      exact cl_w33 ⟨n - 39150, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 39250
                                                                      ·
                                                                        have hr : n - 39200 < 50 := by omega
                                                                        have heq : n = (n - 39200) + 39200 := by omega
                                                                        rw [heq]
                                                                        exact cl_w34 ⟨n - 39200, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 39300
                                                                        ·
                                                                          have hr : n - 39250 < 50 := by omega
                                                                          have heq : n = (n - 39250) + 39250 := by omega
                                                                          rw [heq]
                                                                          exact cl_w35 ⟨n - 39250, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 39350
                                                                          ·
                                                                            have hr : n - 39300 < 50 := by omega
                                                                            have heq : n = (n - 39300) + 39300 := by omega
                                                                            rw [heq]
                                                                            exact cl_w36 ⟨n - 39300, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 39400
                                                                            ·
                                                                              have hr : n - 39350 < 50 := by omega
                                                                              have heq : n = (n - 39350) + 39350 := by omega
                                                                              rw [heq]
                                                                              exact cl_w37 ⟨n - 39350, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 39450
                                                                              ·
                                                                                have hr : n - 39400 < 50 := by omega
                                                                                have heq : n = (n - 39400) + 39400 := by omega
                                                                                rw [heq]
                                                                                exact cl_w38 ⟨n - 39400, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 39500
                                                                                ·
                                                                                  have hr : n - 39450 < 50 := by omega
                                                                                  have heq : n = (n - 39450) + 39450 := by omega
                                                                                  rw [heq]
                                                                                  exact cl_w39 ⟨n - 39450, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 39550
                                                                                  ·
                                                                                    have hr : n - 39500 < 50 := by omega
                                                                                    have heq : n = (n - 39500) + 39500 := by omega
                                                                                    rw [heq]
                                                                                    exact cl_w40 ⟨n - 39500, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 39600
                                                                                    ·
                                                                                      have hr : n - 39550 < 50 := by omega
                                                                                      have heq : n = (n - 39550) + 39550 := by omega
                                                                                      rw [heq]
                                                                                      exact cl_w41 ⟨n - 39550, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 39650
                                                                                      ·
                                                                                        have hr : n - 39600 < 50 := by omega
                                                                                        have heq : n = (n - 39600) + 39600 := by omega
                                                                                        rw [heq]
                                                                                        exact cl_w42 ⟨n - 39600, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 39700
                                                                                        ·
                                                                                          have hr : n - 39650 < 50 := by omega
                                                                                          have heq : n = (n - 39650) + 39650 := by omega
                                                                                          rw [heq]
                                                                                          exact cl_w43 ⟨n - 39650, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 39750
                                                                                          ·
                                                                                            have hr : n - 39700 < 50 := by omega
                                                                                            have heq : n = (n - 39700) + 39700 := by omega
                                                                                            rw [heq]
                                                                                            exact cl_w44 ⟨n - 39700, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 39800
                                                                                            ·
                                                                                              have hr : n - 39750 < 50 := by omega
                                                                                              have heq : n = (n - 39750) + 39750 := by omega
                                                                                              rw [heq]
                                                                                              exact cl_w45 ⟨n - 39750, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 39850
                                                                                              ·
                                                                                                have hr : n - 39800 < 50 := by omega
                                                                                                have heq : n = (n - 39800) + 39800 := by omega
                                                                                                rw [heq]
                                                                                                exact cl_w46 ⟨n - 39800, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 39900
                                                                                                ·
                                                                                                  have hr : n - 39850 < 50 := by omega
                                                                                                  have heq : n = (n - 39850) + 39850 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cl_w47 ⟨n - 39850, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 39950
                                                                                                  ·
                                                                                                    have hr : n - 39900 < 50 := by omega
                                                                                                    have heq : n = (n - 39900) + 39900 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w48 ⟨n - 39900, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 39950 < 50 := by omega
                                                                                                    have heq : n = (n - 39950) + 39950 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w49 ⟨n - 39950, hr⟩


theorem densSupG_lt_range : ∀ n, 37500 ≤ n → n < 40000 → densSupG n < 2 ^ 1771 := by
  intro n hlo hhi
  by_cases h0 : n < 37550
  · have hr : n - 37500 < 50 := by omega
    have heq : n = (n - 37500) + 37500 := by omega
    rw [heq]
    exact bd_w0 ⟨n - 37500, hr⟩
  ·
    by_cases h1 : n < 37600
    ·
      have hr : n - 37550 < 50 := by omega
      have heq : n = (n - 37550) + 37550 := by omega
      rw [heq]
      exact bd_w1 ⟨n - 37550, hr⟩
    ·
      by_cases h2 : n < 37650
      ·
        have hr : n - 37600 < 50 := by omega
        have heq : n = (n - 37600) + 37600 := by omega
        rw [heq]
        exact bd_w2 ⟨n - 37600, hr⟩
      ·
        by_cases h3 : n < 37700
        ·
          have hr : n - 37650 < 50 := by omega
          have heq : n = (n - 37650) + 37650 := by omega
          rw [heq]
          exact bd_w3 ⟨n - 37650, hr⟩
        ·
          by_cases h4 : n < 37750
          ·
            have hr : n - 37700 < 50 := by omega
            have heq : n = (n - 37700) + 37700 := by omega
            rw [heq]
            exact bd_w4 ⟨n - 37700, hr⟩
          ·
            by_cases h5 : n < 37800
            ·
              have hr : n - 37750 < 50 := by omega
              have heq : n = (n - 37750) + 37750 := by omega
              rw [heq]
              exact bd_w5 ⟨n - 37750, hr⟩
            ·
              by_cases h6 : n < 37850
              ·
                have hr : n - 37800 < 50 := by omega
                have heq : n = (n - 37800) + 37800 := by omega
                rw [heq]
                exact bd_w6 ⟨n - 37800, hr⟩
              ·
                by_cases h7 : n < 37900
                ·
                  have hr : n - 37850 < 50 := by omega
                  have heq : n = (n - 37850) + 37850 := by omega
                  rw [heq]
                  exact bd_w7 ⟨n - 37850, hr⟩
                ·
                  by_cases h8 : n < 37950
                  ·
                    have hr : n - 37900 < 50 := by omega
                    have heq : n = (n - 37900) + 37900 := by omega
                    rw [heq]
                    exact bd_w8 ⟨n - 37900, hr⟩
                  ·
                    by_cases h9 : n < 38000
                    ·
                      have hr : n - 37950 < 50 := by omega
                      have heq : n = (n - 37950) + 37950 := by omega
                      rw [heq]
                      exact bd_w9 ⟨n - 37950, hr⟩
                    ·
                      by_cases h10 : n < 38050
                      ·
                        have hr : n - 38000 < 50 := by omega
                        have heq : n = (n - 38000) + 38000 := by omega
                        rw [heq]
                        exact bd_w10 ⟨n - 38000, hr⟩
                      ·
                        by_cases h11 : n < 38100
                        ·
                          have hr : n - 38050 < 50 := by omega
                          have heq : n = (n - 38050) + 38050 := by omega
                          rw [heq]
                          exact bd_w11 ⟨n - 38050, hr⟩
                        ·
                          by_cases h12 : n < 38150
                          ·
                            have hr : n - 38100 < 50 := by omega
                            have heq : n = (n - 38100) + 38100 := by omega
                            rw [heq]
                            exact bd_w12 ⟨n - 38100, hr⟩
                          ·
                            by_cases h13 : n < 38200
                            ·
                              have hr : n - 38150 < 50 := by omega
                              have heq : n = (n - 38150) + 38150 := by omega
                              rw [heq]
                              exact bd_w13 ⟨n - 38150, hr⟩
                            ·
                              by_cases h14 : n < 38250
                              ·
                                have hr : n - 38200 < 50 := by omega
                                have heq : n = (n - 38200) + 38200 := by omega
                                rw [heq]
                                exact bd_w14 ⟨n - 38200, hr⟩
                              ·
                                by_cases h15 : n < 38300
                                ·
                                  have hr : n - 38250 < 50 := by omega
                                  have heq : n = (n - 38250) + 38250 := by omega
                                  rw [heq]
                                  exact bd_w15 ⟨n - 38250, hr⟩
                                ·
                                  by_cases h16 : n < 38350
                                  ·
                                    have hr : n - 38300 < 50 := by omega
                                    have heq : n = (n - 38300) + 38300 := by omega
                                    rw [heq]
                                    exact bd_w16 ⟨n - 38300, hr⟩
                                  ·
                                    by_cases h17 : n < 38400
                                    ·
                                      have hr : n - 38350 < 50 := by omega
                                      have heq : n = (n - 38350) + 38350 := by omega
                                      rw [heq]
                                      exact bd_w17 ⟨n - 38350, hr⟩
                                    ·
                                      by_cases h18 : n < 38450
                                      ·
                                        have hr : n - 38400 < 50 := by omega
                                        have heq : n = (n - 38400) + 38400 := by omega
                                        rw [heq]
                                        exact bd_w18 ⟨n - 38400, hr⟩
                                      ·
                                        by_cases h19 : n < 38500
                                        ·
                                          have hr : n - 38450 < 50 := by omega
                                          have heq : n = (n - 38450) + 38450 := by omega
                                          rw [heq]
                                          exact bd_w19 ⟨n - 38450, hr⟩
                                        ·
                                          by_cases h20 : n < 38550
                                          ·
                                            have hr : n - 38500 < 50 := by omega
                                            have heq : n = (n - 38500) + 38500 := by omega
                                            rw [heq]
                                            exact bd_w20 ⟨n - 38500, hr⟩
                                          ·
                                            by_cases h21 : n < 38600
                                            ·
                                              have hr : n - 38550 < 50 := by omega
                                              have heq : n = (n - 38550) + 38550 := by omega
                                              rw [heq]
                                              exact bd_w21 ⟨n - 38550, hr⟩
                                            ·
                                              by_cases h22 : n < 38650
                                              ·
                                                have hr : n - 38600 < 50 := by omega
                                                have heq : n = (n - 38600) + 38600 := by omega
                                                rw [heq]
                                                exact bd_w22 ⟨n - 38600, hr⟩
                                              ·
                                                by_cases h23 : n < 38700
                                                ·
                                                  have hr : n - 38650 < 50 := by omega
                                                  have heq : n = (n - 38650) + 38650 := by omega
                                                  rw [heq]
                                                  exact bd_w23 ⟨n - 38650, hr⟩
                                                ·
                                                  by_cases h24 : n < 38750
                                                  ·
                                                    have hr : n - 38700 < 50 := by omega
                                                    have heq : n = (n - 38700) + 38700 := by omega
                                                    rw [heq]
                                                    exact bd_w24 ⟨n - 38700, hr⟩
                                                  ·
                                                    by_cases h25 : n < 38800
                                                    ·
                                                      have hr : n - 38750 < 50 := by omega
                                                      have heq : n = (n - 38750) + 38750 := by omega
                                                      rw [heq]
                                                      exact bd_w25 ⟨n - 38750, hr⟩
                                                    ·
                                                      by_cases h26 : n < 38850
                                                      ·
                                                        have hr : n - 38800 < 50 := by omega
                                                        have heq : n = (n - 38800) + 38800 := by omega
                                                        rw [heq]
                                                        exact bd_w26 ⟨n - 38800, hr⟩
                                                      ·
                                                        by_cases h27 : n < 38900
                                                        ·
                                                          have hr : n - 38850 < 50 := by omega
                                                          have heq : n = (n - 38850) + 38850 := by omega
                                                          rw [heq]
                                                          exact bd_w27 ⟨n - 38850, hr⟩
                                                        ·
                                                          by_cases h28 : n < 38950
                                                          ·
                                                            have hr : n - 38900 < 50 := by omega
                                                            have heq : n = (n - 38900) + 38900 := by omega
                                                            rw [heq]
                                                            exact bd_w28 ⟨n - 38900, hr⟩
                                                          ·
                                                            by_cases h29 : n < 39000
                                                            ·
                                                              have hr : n - 38950 < 50 := by omega
                                                              have heq : n = (n - 38950) + 38950 := by omega
                                                              rw [heq]
                                                              exact bd_w29 ⟨n - 38950, hr⟩
                                                            ·
                                                              by_cases h30 : n < 39050
                                                              ·
                                                                have hr : n - 39000 < 50 := by omega
                                                                have heq : n = (n - 39000) + 39000 := by omega
                                                                rw [heq]
                                                                exact bd_w30 ⟨n - 39000, hr⟩
                                                              ·
                                                                by_cases h31 : n < 39100
                                                                ·
                                                                  have hr : n - 39050 < 50 := by omega
                                                                  have heq : n = (n - 39050) + 39050 := by omega
                                                                  rw [heq]
                                                                  exact bd_w31 ⟨n - 39050, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 39150
                                                                  ·
                                                                    have hr : n - 39100 < 50 := by omega
                                                                    have heq : n = (n - 39100) + 39100 := by omega
                                                                    rw [heq]
                                                                    exact bd_w32 ⟨n - 39100, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 39200
                                                                    ·
                                                                      have hr : n - 39150 < 50 := by omega
                                                                      have heq : n = (n - 39150) + 39150 := by omega
                                                                      rw [heq]
                                                                      exact bd_w33 ⟨n - 39150, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 39250
                                                                      ·
                                                                        have hr : n - 39200 < 50 := by omega
                                                                        have heq : n = (n - 39200) + 39200 := by omega
                                                                        rw [heq]
                                                                        exact bd_w34 ⟨n - 39200, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 39300
                                                                        ·
                                                                          have hr : n - 39250 < 50 := by omega
                                                                          have heq : n = (n - 39250) + 39250 := by omega
                                                                          rw [heq]
                                                                          exact bd_w35 ⟨n - 39250, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 39350
                                                                          ·
                                                                            have hr : n - 39300 < 50 := by omega
                                                                            have heq : n = (n - 39300) + 39300 := by omega
                                                                            rw [heq]
                                                                            exact bd_w36 ⟨n - 39300, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 39400
                                                                            ·
                                                                              have hr : n - 39350 < 50 := by omega
                                                                              have heq : n = (n - 39350) + 39350 := by omega
                                                                              rw [heq]
                                                                              exact bd_w37 ⟨n - 39350, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 39450
                                                                              ·
                                                                                have hr : n - 39400 < 50 := by omega
                                                                                have heq : n = (n - 39400) + 39400 := by omega
                                                                                rw [heq]
                                                                                exact bd_w38 ⟨n - 39400, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 39500
                                                                                ·
                                                                                  have hr : n - 39450 < 50 := by omega
                                                                                  have heq : n = (n - 39450) + 39450 := by omega
                                                                                  rw [heq]
                                                                                  exact bd_w39 ⟨n - 39450, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 39550
                                                                                  ·
                                                                                    have hr : n - 39500 < 50 := by omega
                                                                                    have heq : n = (n - 39500) + 39500 := by omega
                                                                                    rw [heq]
                                                                                    exact bd_w40 ⟨n - 39500, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 39600
                                                                                    ·
                                                                                      have hr : n - 39550 < 50 := by omega
                                                                                      have heq : n = (n - 39550) + 39550 := by omega
                                                                                      rw [heq]
                                                                                      exact bd_w41 ⟨n - 39550, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 39650
                                                                                      ·
                                                                                        have hr : n - 39600 < 50 := by omega
                                                                                        have heq : n = (n - 39600) + 39600 := by omega
                                                                                        rw [heq]
                                                                                        exact bd_w42 ⟨n - 39600, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 39700
                                                                                        ·
                                                                                          have hr : n - 39650 < 50 := by omega
                                                                                          have heq : n = (n - 39650) + 39650 := by omega
                                                                                          rw [heq]
                                                                                          exact bd_w43 ⟨n - 39650, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 39750
                                                                                          ·
                                                                                            have hr : n - 39700 < 50 := by omega
                                                                                            have heq : n = (n - 39700) + 39700 := by omega
                                                                                            rw [heq]
                                                                                            exact bd_w44 ⟨n - 39700, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 39800
                                                                                            ·
                                                                                              have hr : n - 39750 < 50 := by omega
                                                                                              have heq : n = (n - 39750) + 39750 := by omega
                                                                                              rw [heq]
                                                                                              exact bd_w45 ⟨n - 39750, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 39850
                                                                                              ·
                                                                                                have hr : n - 39800 < 50 := by omega
                                                                                                have heq : n = (n - 39800) + 39800 := by omega
                                                                                                rw [heq]
                                                                                                exact bd_w46 ⟨n - 39800, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 39900
                                                                                                ·
                                                                                                  have hr : n - 39850 < 50 := by omega
                                                                                                  have heq : n = (n - 39850) + 39850 := by omega
                                                                                                  rw [heq]
                                                                                                  exact bd_w47 ⟨n - 39850, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 39950
                                                                                                  ·
                                                                                                    have hr : n - 39900 < 50 := by omega
                                                                                                    have heq : n = (n - 39900) + 39900 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w48 ⟨n - 39900, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 39950 < 50 := by omega
                                                                                                    have heq : n = (n - 39950) + 39950 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w49 ⟨n - 39950, hr⟩


end IntMul.Kappa.R8.Bit.Oppbank.CentBound7b


