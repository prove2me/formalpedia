-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound9b
-- name    : IntMul_Kappa_R8_Data_BitOppbankCentBound9b
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:09:44.789049+00:00
-- url     : https://prove2.me/theorems/3f0145b6-91bf-498b-922c-223a9ac9df96
-- title:
--   HasCentre certificates dens nodes [47500,50000)
-- statement:
--   # Densified centre certificates, pack 9b
--
--   For every densified node index $n$ with $47500\le n<50000$,
--   $$
--   \mathrm{centredStar}(\mathrm{densSupG}\,n,\mathrm{centF}\,n)=\mathsf{true},\quad
--   \mathrm{centF}\,n<23,\quad
--   \mathrm{densSupG}\,n < 2^{1771}.
--   $$
--   Proved by decide on Fin 50 windows (no native_decide). Half-pack for 300s server budget.
-- source:
--   R8 BitOppbank AllDensCentred; jfstack_23 densified supports

-- CentBound pack 9b: densified HasCentre certificates on n ∈ [47500, 50000)
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

namespace IntMul.Kappa.R8.Bit.Oppbank.CentBound9b


private theorem cs_w0 : ∀ n : Fin 50, centredStar (densSupG (n.val + 47500)) (centF (n.val + 47500)) = true := by decide
private theorem cl_w0 : ∀ n : Fin 50, centF (n.val + 47500) < 23 := by decide
private theorem bd_w0 : ∀ n : Fin 50, densSupG (n.val + 47500) < 2 ^ 1771 := by decide
private theorem cs_w1 : ∀ n : Fin 50, centredStar (densSupG (n.val + 47550)) (centF (n.val + 47550)) = true := by decide
private theorem cl_w1 : ∀ n : Fin 50, centF (n.val + 47550) < 23 := by decide
private theorem bd_w1 : ∀ n : Fin 50, densSupG (n.val + 47550) < 2 ^ 1771 := by decide
private theorem cs_w2 : ∀ n : Fin 50, centredStar (densSupG (n.val + 47600)) (centF (n.val + 47600)) = true := by decide
private theorem cl_w2 : ∀ n : Fin 50, centF (n.val + 47600) < 23 := by decide
private theorem bd_w2 : ∀ n : Fin 50, densSupG (n.val + 47600) < 2 ^ 1771 := by decide
private theorem cs_w3 : ∀ n : Fin 50, centredStar (densSupG (n.val + 47650)) (centF (n.val + 47650)) = true := by decide
private theorem cl_w3 : ∀ n : Fin 50, centF (n.val + 47650) < 23 := by decide
private theorem bd_w3 : ∀ n : Fin 50, densSupG (n.val + 47650) < 2 ^ 1771 := by decide
private theorem cs_w4 : ∀ n : Fin 50, centredStar (densSupG (n.val + 47700)) (centF (n.val + 47700)) = true := by decide
private theorem cl_w4 : ∀ n : Fin 50, centF (n.val + 47700) < 23 := by decide
private theorem bd_w4 : ∀ n : Fin 50, densSupG (n.val + 47700) < 2 ^ 1771 := by decide
private theorem cs_w5 : ∀ n : Fin 50, centredStar (densSupG (n.val + 47750)) (centF (n.val + 47750)) = true := by decide
private theorem cl_w5 : ∀ n : Fin 50, centF (n.val + 47750) < 23 := by decide
private theorem bd_w5 : ∀ n : Fin 50, densSupG (n.val + 47750) < 2 ^ 1771 := by decide
private theorem cs_w6 : ∀ n : Fin 50, centredStar (densSupG (n.val + 47800)) (centF (n.val + 47800)) = true := by decide
private theorem cl_w6 : ∀ n : Fin 50, centF (n.val + 47800) < 23 := by decide
private theorem bd_w6 : ∀ n : Fin 50, densSupG (n.val + 47800) < 2 ^ 1771 := by decide
private theorem cs_w7 : ∀ n : Fin 50, centredStar (densSupG (n.val + 47850)) (centF (n.val + 47850)) = true := by decide
private theorem cl_w7 : ∀ n : Fin 50, centF (n.val + 47850) < 23 := by decide
private theorem bd_w7 : ∀ n : Fin 50, densSupG (n.val + 47850) < 2 ^ 1771 := by decide
private theorem cs_w8 : ∀ n : Fin 50, centredStar (densSupG (n.val + 47900)) (centF (n.val + 47900)) = true := by decide
private theorem cl_w8 : ∀ n : Fin 50, centF (n.val + 47900) < 23 := by decide
private theorem bd_w8 : ∀ n : Fin 50, densSupG (n.val + 47900) < 2 ^ 1771 := by decide
private theorem cs_w9 : ∀ n : Fin 50, centredStar (densSupG (n.val + 47950)) (centF (n.val + 47950)) = true := by decide
private theorem cl_w9 : ∀ n : Fin 50, centF (n.val + 47950) < 23 := by decide
private theorem bd_w9 : ∀ n : Fin 50, densSupG (n.val + 47950) < 2 ^ 1771 := by decide
private theorem cs_w10 : ∀ n : Fin 50, centredStar (densSupG (n.val + 48000)) (centF (n.val + 48000)) = true := by decide
private theorem cl_w10 : ∀ n : Fin 50, centF (n.val + 48000) < 23 := by decide
private theorem bd_w10 : ∀ n : Fin 50, densSupG (n.val + 48000) < 2 ^ 1771 := by decide
private theorem cs_w11 : ∀ n : Fin 50, centredStar (densSupG (n.val + 48050)) (centF (n.val + 48050)) = true := by decide
private theorem cl_w11 : ∀ n : Fin 50, centF (n.val + 48050) < 23 := by decide
private theorem bd_w11 : ∀ n : Fin 50, densSupG (n.val + 48050) < 2 ^ 1771 := by decide
private theorem cs_w12 : ∀ n : Fin 50, centredStar (densSupG (n.val + 48100)) (centF (n.val + 48100)) = true := by decide
private theorem cl_w12 : ∀ n : Fin 50, centF (n.val + 48100) < 23 := by decide
private theorem bd_w12 : ∀ n : Fin 50, densSupG (n.val + 48100) < 2 ^ 1771 := by decide
private theorem cs_w13 : ∀ n : Fin 50, centredStar (densSupG (n.val + 48150)) (centF (n.val + 48150)) = true := by decide
private theorem cl_w13 : ∀ n : Fin 50, centF (n.val + 48150) < 23 := by decide
private theorem bd_w13 : ∀ n : Fin 50, densSupG (n.val + 48150) < 2 ^ 1771 := by decide
private theorem cs_w14 : ∀ n : Fin 50, centredStar (densSupG (n.val + 48200)) (centF (n.val + 48200)) = true := by decide
private theorem cl_w14 : ∀ n : Fin 50, centF (n.val + 48200) < 23 := by decide
private theorem bd_w14 : ∀ n : Fin 50, densSupG (n.val + 48200) < 2 ^ 1771 := by decide
private theorem cs_w15 : ∀ n : Fin 50, centredStar (densSupG (n.val + 48250)) (centF (n.val + 48250)) = true := by decide
private theorem cl_w15 : ∀ n : Fin 50, centF (n.val + 48250) < 23 := by decide
private theorem bd_w15 : ∀ n : Fin 50, densSupG (n.val + 48250) < 2 ^ 1771 := by decide
private theorem cs_w16 : ∀ n : Fin 50, centredStar (densSupG (n.val + 48300)) (centF (n.val + 48300)) = true := by decide
private theorem cl_w16 : ∀ n : Fin 50, centF (n.val + 48300) < 23 := by decide
private theorem bd_w16 : ∀ n : Fin 50, densSupG (n.val + 48300) < 2 ^ 1771 := by decide
private theorem cs_w17 : ∀ n : Fin 50, centredStar (densSupG (n.val + 48350)) (centF (n.val + 48350)) = true := by decide
private theorem cl_w17 : ∀ n : Fin 50, centF (n.val + 48350) < 23 := by decide
private theorem bd_w17 : ∀ n : Fin 50, densSupG (n.val + 48350) < 2 ^ 1771 := by decide
private theorem cs_w18 : ∀ n : Fin 50, centredStar (densSupG (n.val + 48400)) (centF (n.val + 48400)) = true := by decide
private theorem cl_w18 : ∀ n : Fin 50, centF (n.val + 48400) < 23 := by decide
private theorem bd_w18 : ∀ n : Fin 50, densSupG (n.val + 48400) < 2 ^ 1771 := by decide
private theorem cs_w19 : ∀ n : Fin 50, centredStar (densSupG (n.val + 48450)) (centF (n.val + 48450)) = true := by decide
private theorem cl_w19 : ∀ n : Fin 50, centF (n.val + 48450) < 23 := by decide
private theorem bd_w19 : ∀ n : Fin 50, densSupG (n.val + 48450) < 2 ^ 1771 := by decide
private theorem cs_w20 : ∀ n : Fin 50, centredStar (densSupG (n.val + 48500)) (centF (n.val + 48500)) = true := by decide
private theorem cl_w20 : ∀ n : Fin 50, centF (n.val + 48500) < 23 := by decide
private theorem bd_w20 : ∀ n : Fin 50, densSupG (n.val + 48500) < 2 ^ 1771 := by decide
private theorem cs_w21 : ∀ n : Fin 50, centredStar (densSupG (n.val + 48550)) (centF (n.val + 48550)) = true := by decide
private theorem cl_w21 : ∀ n : Fin 50, centF (n.val + 48550) < 23 := by decide
private theorem bd_w21 : ∀ n : Fin 50, densSupG (n.val + 48550) < 2 ^ 1771 := by decide
private theorem cs_w22 : ∀ n : Fin 50, centredStar (densSupG (n.val + 48600)) (centF (n.val + 48600)) = true := by decide
private theorem cl_w22 : ∀ n : Fin 50, centF (n.val + 48600) < 23 := by decide
private theorem bd_w22 : ∀ n : Fin 50, densSupG (n.val + 48600) < 2 ^ 1771 := by decide
private theorem cs_w23 : ∀ n : Fin 50, centredStar (densSupG (n.val + 48650)) (centF (n.val + 48650)) = true := by decide
private theorem cl_w23 : ∀ n : Fin 50, centF (n.val + 48650) < 23 := by decide
private theorem bd_w23 : ∀ n : Fin 50, densSupG (n.val + 48650) < 2 ^ 1771 := by decide
private theorem cs_w24 : ∀ n : Fin 50, centredStar (densSupG (n.val + 48700)) (centF (n.val + 48700)) = true := by decide
private theorem cl_w24 : ∀ n : Fin 50, centF (n.val + 48700) < 23 := by decide
private theorem bd_w24 : ∀ n : Fin 50, densSupG (n.val + 48700) < 2 ^ 1771 := by decide
private theorem cs_w25 : ∀ n : Fin 50, centredStar (densSupG (n.val + 48750)) (centF (n.val + 48750)) = true := by decide
private theorem cl_w25 : ∀ n : Fin 50, centF (n.val + 48750) < 23 := by decide
private theorem bd_w25 : ∀ n : Fin 50, densSupG (n.val + 48750) < 2 ^ 1771 := by decide
private theorem cs_w26 : ∀ n : Fin 50, centredStar (densSupG (n.val + 48800)) (centF (n.val + 48800)) = true := by decide
private theorem cl_w26 : ∀ n : Fin 50, centF (n.val + 48800) < 23 := by decide
private theorem bd_w26 : ∀ n : Fin 50, densSupG (n.val + 48800) < 2 ^ 1771 := by decide
private theorem cs_w27 : ∀ n : Fin 50, centredStar (densSupG (n.val + 48850)) (centF (n.val + 48850)) = true := by decide
private theorem cl_w27 : ∀ n : Fin 50, centF (n.val + 48850) < 23 := by decide
private theorem bd_w27 : ∀ n : Fin 50, densSupG (n.val + 48850) < 2 ^ 1771 := by decide
private theorem cs_w28 : ∀ n : Fin 50, centredStar (densSupG (n.val + 48900)) (centF (n.val + 48900)) = true := by decide
private theorem cl_w28 : ∀ n : Fin 50, centF (n.val + 48900) < 23 := by decide
private theorem bd_w28 : ∀ n : Fin 50, densSupG (n.val + 48900) < 2 ^ 1771 := by decide
private theorem cs_w29 : ∀ n : Fin 50, centredStar (densSupG (n.val + 48950)) (centF (n.val + 48950)) = true := by decide
private theorem cl_w29 : ∀ n : Fin 50, centF (n.val + 48950) < 23 := by decide
private theorem bd_w29 : ∀ n : Fin 50, densSupG (n.val + 48950) < 2 ^ 1771 := by decide
private theorem cs_w30 : ∀ n : Fin 50, centredStar (densSupG (n.val + 49000)) (centF (n.val + 49000)) = true := by decide
private theorem cl_w30 : ∀ n : Fin 50, centF (n.val + 49000) < 23 := by decide
private theorem bd_w30 : ∀ n : Fin 50, densSupG (n.val + 49000) < 2 ^ 1771 := by decide
private theorem cs_w31 : ∀ n : Fin 50, centredStar (densSupG (n.val + 49050)) (centF (n.val + 49050)) = true := by decide
private theorem cl_w31 : ∀ n : Fin 50, centF (n.val + 49050) < 23 := by decide
private theorem bd_w31 : ∀ n : Fin 50, densSupG (n.val + 49050) < 2 ^ 1771 := by decide
private theorem cs_w32 : ∀ n : Fin 50, centredStar (densSupG (n.val + 49100)) (centF (n.val + 49100)) = true := by decide
private theorem cl_w32 : ∀ n : Fin 50, centF (n.val + 49100) < 23 := by decide
private theorem bd_w32 : ∀ n : Fin 50, densSupG (n.val + 49100) < 2 ^ 1771 := by decide
private theorem cs_w33 : ∀ n : Fin 50, centredStar (densSupG (n.val + 49150)) (centF (n.val + 49150)) = true := by decide
private theorem cl_w33 : ∀ n : Fin 50, centF (n.val + 49150) < 23 := by decide
private theorem bd_w33 : ∀ n : Fin 50, densSupG (n.val + 49150) < 2 ^ 1771 := by decide
private theorem cs_w34 : ∀ n : Fin 50, centredStar (densSupG (n.val + 49200)) (centF (n.val + 49200)) = true := by decide
private theorem cl_w34 : ∀ n : Fin 50, centF (n.val + 49200) < 23 := by decide
private theorem bd_w34 : ∀ n : Fin 50, densSupG (n.val + 49200) < 2 ^ 1771 := by decide
private theorem cs_w35 : ∀ n : Fin 50, centredStar (densSupG (n.val + 49250)) (centF (n.val + 49250)) = true := by decide
private theorem cl_w35 : ∀ n : Fin 50, centF (n.val + 49250) < 23 := by decide
private theorem bd_w35 : ∀ n : Fin 50, densSupG (n.val + 49250) < 2 ^ 1771 := by decide
private theorem cs_w36 : ∀ n : Fin 50, centredStar (densSupG (n.val + 49300)) (centF (n.val + 49300)) = true := by decide
private theorem cl_w36 : ∀ n : Fin 50, centF (n.val + 49300) < 23 := by decide
private theorem bd_w36 : ∀ n : Fin 50, densSupG (n.val + 49300) < 2 ^ 1771 := by decide
private theorem cs_w37 : ∀ n : Fin 50, centredStar (densSupG (n.val + 49350)) (centF (n.val + 49350)) = true := by decide
private theorem cl_w37 : ∀ n : Fin 50, centF (n.val + 49350) < 23 := by decide
private theorem bd_w37 : ∀ n : Fin 50, densSupG (n.val + 49350) < 2 ^ 1771 := by decide
private theorem cs_w38 : ∀ n : Fin 50, centredStar (densSupG (n.val + 49400)) (centF (n.val + 49400)) = true := by decide
private theorem cl_w38 : ∀ n : Fin 50, centF (n.val + 49400) < 23 := by decide
private theorem bd_w38 : ∀ n : Fin 50, densSupG (n.val + 49400) < 2 ^ 1771 := by decide
private theorem cs_w39 : ∀ n : Fin 50, centredStar (densSupG (n.val + 49450)) (centF (n.val + 49450)) = true := by decide
private theorem cl_w39 : ∀ n : Fin 50, centF (n.val + 49450) < 23 := by decide
private theorem bd_w39 : ∀ n : Fin 50, densSupG (n.val + 49450) < 2 ^ 1771 := by decide
private theorem cs_w40 : ∀ n : Fin 50, centredStar (densSupG (n.val + 49500)) (centF (n.val + 49500)) = true := by decide
private theorem cl_w40 : ∀ n : Fin 50, centF (n.val + 49500) < 23 := by decide
private theorem bd_w40 : ∀ n : Fin 50, densSupG (n.val + 49500) < 2 ^ 1771 := by decide
private theorem cs_w41 : ∀ n : Fin 50, centredStar (densSupG (n.val + 49550)) (centF (n.val + 49550)) = true := by decide
private theorem cl_w41 : ∀ n : Fin 50, centF (n.val + 49550) < 23 := by decide
private theorem bd_w41 : ∀ n : Fin 50, densSupG (n.val + 49550) < 2 ^ 1771 := by decide
private theorem cs_w42 : ∀ n : Fin 50, centredStar (densSupG (n.val + 49600)) (centF (n.val + 49600)) = true := by decide
private theorem cl_w42 : ∀ n : Fin 50, centF (n.val + 49600) < 23 := by decide
private theorem bd_w42 : ∀ n : Fin 50, densSupG (n.val + 49600) < 2 ^ 1771 := by decide
private theorem cs_w43 : ∀ n : Fin 50, centredStar (densSupG (n.val + 49650)) (centF (n.val + 49650)) = true := by decide
private theorem cl_w43 : ∀ n : Fin 50, centF (n.val + 49650) < 23 := by decide
private theorem bd_w43 : ∀ n : Fin 50, densSupG (n.val + 49650) < 2 ^ 1771 := by decide
private theorem cs_w44 : ∀ n : Fin 50, centredStar (densSupG (n.val + 49700)) (centF (n.val + 49700)) = true := by decide
private theorem cl_w44 : ∀ n : Fin 50, centF (n.val + 49700) < 23 := by decide
private theorem bd_w44 : ∀ n : Fin 50, densSupG (n.val + 49700) < 2 ^ 1771 := by decide
private theorem cs_w45 : ∀ n : Fin 50, centredStar (densSupG (n.val + 49750)) (centF (n.val + 49750)) = true := by decide
private theorem cl_w45 : ∀ n : Fin 50, centF (n.val + 49750) < 23 := by decide
private theorem bd_w45 : ∀ n : Fin 50, densSupG (n.val + 49750) < 2 ^ 1771 := by decide
private theorem cs_w46 : ∀ n : Fin 50, centredStar (densSupG (n.val + 49800)) (centF (n.val + 49800)) = true := by decide
private theorem cl_w46 : ∀ n : Fin 50, centF (n.val + 49800) < 23 := by decide
private theorem bd_w46 : ∀ n : Fin 50, densSupG (n.val + 49800) < 2 ^ 1771 := by decide
private theorem cs_w47 : ∀ n : Fin 50, centredStar (densSupG (n.val + 49850)) (centF (n.val + 49850)) = true := by decide
private theorem cl_w47 : ∀ n : Fin 50, centF (n.val + 49850) < 23 := by decide
private theorem bd_w47 : ∀ n : Fin 50, densSupG (n.val + 49850) < 2 ^ 1771 := by decide
private theorem cs_w48 : ∀ n : Fin 50, centredStar (densSupG (n.val + 49900)) (centF (n.val + 49900)) = true := by decide
private theorem cl_w48 : ∀ n : Fin 50, centF (n.val + 49900) < 23 := by decide
private theorem bd_w48 : ∀ n : Fin 50, densSupG (n.val + 49900) < 2 ^ 1771 := by decide
private theorem cs_w49 : ∀ n : Fin 50, centredStar (densSupG (n.val + 49950)) (centF (n.val + 49950)) = true := by decide
private theorem cl_w49 : ∀ n : Fin 50, centF (n.val + 49950) < 23 := by decide
private theorem bd_w49 : ∀ n : Fin 50, densSupG (n.val + 49950) < 2 ^ 1771 := by decide
theorem centredStar_range : ∀ n, 47500 ≤ n → n < 50000 → centredStar (densSupG n) (centF n) = true := by
  intro n hlo hhi
  by_cases h0 : n < 47550
  · have hr : n - 47500 < 50 := by omega
    have heq : n = (n - 47500) + 47500 := by omega
    rw [heq]
    exact cs_w0 ⟨n - 47500, hr⟩
  ·
    by_cases h1 : n < 47600
    ·
      have hr : n - 47550 < 50 := by omega
      have heq : n = (n - 47550) + 47550 := by omega
      rw [heq]
      exact cs_w1 ⟨n - 47550, hr⟩
    ·
      by_cases h2 : n < 47650
      ·
        have hr : n - 47600 < 50 := by omega
        have heq : n = (n - 47600) + 47600 := by omega
        rw [heq]
        exact cs_w2 ⟨n - 47600, hr⟩
      ·
        by_cases h3 : n < 47700
        ·
          have hr : n - 47650 < 50 := by omega
          have heq : n = (n - 47650) + 47650 := by omega
          rw [heq]
          exact cs_w3 ⟨n - 47650, hr⟩
        ·
          by_cases h4 : n < 47750
          ·
            have hr : n - 47700 < 50 := by omega
            have heq : n = (n - 47700) + 47700 := by omega
            rw [heq]
            exact cs_w4 ⟨n - 47700, hr⟩
          ·
            by_cases h5 : n < 47800
            ·
              have hr : n - 47750 < 50 := by omega
              have heq : n = (n - 47750) + 47750 := by omega
              rw [heq]
              exact cs_w5 ⟨n - 47750, hr⟩
            ·
              by_cases h6 : n < 47850
              ·
                have hr : n - 47800 < 50 := by omega
                have heq : n = (n - 47800) + 47800 := by omega
                rw [heq]
                exact cs_w6 ⟨n - 47800, hr⟩
              ·
                by_cases h7 : n < 47900
                ·
                  have hr : n - 47850 < 50 := by omega
                  have heq : n = (n - 47850) + 47850 := by omega
                  rw [heq]
                  exact cs_w7 ⟨n - 47850, hr⟩
                ·
                  by_cases h8 : n < 47950
                  ·
                    have hr : n - 47900 < 50 := by omega
                    have heq : n = (n - 47900) + 47900 := by omega
                    rw [heq]
                    exact cs_w8 ⟨n - 47900, hr⟩
                  ·
                    by_cases h9 : n < 48000
                    ·
                      have hr : n - 47950 < 50 := by omega
                      have heq : n = (n - 47950) + 47950 := by omega
                      rw [heq]
                      exact cs_w9 ⟨n - 47950, hr⟩
                    ·
                      by_cases h10 : n < 48050
                      ·
                        have hr : n - 48000 < 50 := by omega
                        have heq : n = (n - 48000) + 48000 := by omega
                        rw [heq]
                        exact cs_w10 ⟨n - 48000, hr⟩
                      ·
                        by_cases h11 : n < 48100
                        ·
                          have hr : n - 48050 < 50 := by omega
                          have heq : n = (n - 48050) + 48050 := by omega
                          rw [heq]
                          exact cs_w11 ⟨n - 48050, hr⟩
                        ·
                          by_cases h12 : n < 48150
                          ·
                            have hr : n - 48100 < 50 := by omega
                            have heq : n = (n - 48100) + 48100 := by omega
                            rw [heq]
                            exact cs_w12 ⟨n - 48100, hr⟩
                          ·
                            by_cases h13 : n < 48200
                            ·
                              have hr : n - 48150 < 50 := by omega
                              have heq : n = (n - 48150) + 48150 := by omega
                              rw [heq]
                              exact cs_w13 ⟨n - 48150, hr⟩
                            ·
                              by_cases h14 : n < 48250
                              ·
                                have hr : n - 48200 < 50 := by omega
                                have heq : n = (n - 48200) + 48200 := by omega
                                rw [heq]
                                exact cs_w14 ⟨n - 48200, hr⟩
                              ·
                                by_cases h15 : n < 48300
                                ·
                                  have hr : n - 48250 < 50 := by omega
                                  have heq : n = (n - 48250) + 48250 := by omega
                                  rw [heq]
                                  exact cs_w15 ⟨n - 48250, hr⟩
                                ·
                                  by_cases h16 : n < 48350
                                  ·
                                    have hr : n - 48300 < 50 := by omega
                                    have heq : n = (n - 48300) + 48300 := by omega
                                    rw [heq]
                                    exact cs_w16 ⟨n - 48300, hr⟩
                                  ·
                                    by_cases h17 : n < 48400
                                    ·
                                      have hr : n - 48350 < 50 := by omega
                                      have heq : n = (n - 48350) + 48350 := by omega
                                      rw [heq]
                                      exact cs_w17 ⟨n - 48350, hr⟩
                                    ·
                                      by_cases h18 : n < 48450
                                      ·
                                        have hr : n - 48400 < 50 := by omega
                                        have heq : n = (n - 48400) + 48400 := by omega
                                        rw [heq]
                                        exact cs_w18 ⟨n - 48400, hr⟩
                                      ·
                                        by_cases h19 : n < 48500
                                        ·
                                          have hr : n - 48450 < 50 := by omega
                                          have heq : n = (n - 48450) + 48450 := by omega
                                          rw [heq]
                                          exact cs_w19 ⟨n - 48450, hr⟩
                                        ·
                                          by_cases h20 : n < 48550
                                          ·
                                            have hr : n - 48500 < 50 := by omega
                                            have heq : n = (n - 48500) + 48500 := by omega
                                            rw [heq]
                                            exact cs_w20 ⟨n - 48500, hr⟩
                                          ·
                                            by_cases h21 : n < 48600
                                            ·
                                              have hr : n - 48550 < 50 := by omega
                                              have heq : n = (n - 48550) + 48550 := by omega
                                              rw [heq]
                                              exact cs_w21 ⟨n - 48550, hr⟩
                                            ·
                                              by_cases h22 : n < 48650
                                              ·
                                                have hr : n - 48600 < 50 := by omega
                                                have heq : n = (n - 48600) + 48600 := by omega
                                                rw [heq]
                                                exact cs_w22 ⟨n - 48600, hr⟩
                                              ·
                                                by_cases h23 : n < 48700
                                                ·
                                                  have hr : n - 48650 < 50 := by omega
                                                  have heq : n = (n - 48650) + 48650 := by omega
                                                  rw [heq]
                                                  exact cs_w23 ⟨n - 48650, hr⟩
                                                ·
                                                  by_cases h24 : n < 48750
                                                  ·
                                                    have hr : n - 48700 < 50 := by omega
                                                    have heq : n = (n - 48700) + 48700 := by omega
                                                    rw [heq]
                                                    exact cs_w24 ⟨n - 48700, hr⟩
                                                  ·
                                                    by_cases h25 : n < 48800
                                                    ·
                                                      have hr : n - 48750 < 50 := by omega
                                                      have heq : n = (n - 48750) + 48750 := by omega
                                                      rw [heq]
                                                      exact cs_w25 ⟨n - 48750, hr⟩
                                                    ·
                                                      by_cases h26 : n < 48850
                                                      ·
                                                        have hr : n - 48800 < 50 := by omega
                                                        have heq : n = (n - 48800) + 48800 := by omega
                                                        rw [heq]
                                                        exact cs_w26 ⟨n - 48800, hr⟩
                                                      ·
                                                        by_cases h27 : n < 48900
                                                        ·
                                                          have hr : n - 48850 < 50 := by omega
                                                          have heq : n = (n - 48850) + 48850 := by omega
                                                          rw [heq]
                                                          exact cs_w27 ⟨n - 48850, hr⟩
                                                        ·
                                                          by_cases h28 : n < 48950
                                                          ·
                                                            have hr : n - 48900 < 50 := by omega
                                                            have heq : n = (n - 48900) + 48900 := by omega
                                                            rw [heq]
                                                            exact cs_w28 ⟨n - 48900, hr⟩
                                                          ·
                                                            by_cases h29 : n < 49000
                                                            ·
                                                              have hr : n - 48950 < 50 := by omega
                                                              have heq : n = (n - 48950) + 48950 := by omega
                                                              rw [heq]
                                                              exact cs_w29 ⟨n - 48950, hr⟩
                                                            ·
                                                              by_cases h30 : n < 49050
                                                              ·
                                                                have hr : n - 49000 < 50 := by omega
                                                                have heq : n = (n - 49000) + 49000 := by omega
                                                                rw [heq]
                                                                exact cs_w30 ⟨n - 49000, hr⟩
                                                              ·
                                                                by_cases h31 : n < 49100
                                                                ·
                                                                  have hr : n - 49050 < 50 := by omega
                                                                  have heq : n = (n - 49050) + 49050 := by omega
                                                                  rw [heq]
                                                                  exact cs_w31 ⟨n - 49050, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 49150
                                                                  ·
                                                                    have hr : n - 49100 < 50 := by omega
                                                                    have heq : n = (n - 49100) + 49100 := by omega
                                                                    rw [heq]
                                                                    exact cs_w32 ⟨n - 49100, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 49200
                                                                    ·
                                                                      have hr : n - 49150 < 50 := by omega
                                                                      have heq : n = (n - 49150) + 49150 := by omega
                                                                      rw [heq]
                                                                      exact cs_w33 ⟨n - 49150, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 49250
                                                                      ·
                                                                        have hr : n - 49200 < 50 := by omega
                                                                        have heq : n = (n - 49200) + 49200 := by omega
                                                                        rw [heq]
                                                                        exact cs_w34 ⟨n - 49200, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 49300
                                                                        ·
                                                                          have hr : n - 49250 < 50 := by omega
                                                                          have heq : n = (n - 49250) + 49250 := by omega
                                                                          rw [heq]
                                                                          exact cs_w35 ⟨n - 49250, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 49350
                                                                          ·
                                                                            have hr : n - 49300 < 50 := by omega
                                                                            have heq : n = (n - 49300) + 49300 := by omega
                                                                            rw [heq]
                                                                            exact cs_w36 ⟨n - 49300, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 49400
                                                                            ·
                                                                              have hr : n - 49350 < 50 := by omega
                                                                              have heq : n = (n - 49350) + 49350 := by omega
                                                                              rw [heq]
                                                                              exact cs_w37 ⟨n - 49350, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 49450
                                                                              ·
                                                                                have hr : n - 49400 < 50 := by omega
                                                                                have heq : n = (n - 49400) + 49400 := by omega
                                                                                rw [heq]
                                                                                exact cs_w38 ⟨n - 49400, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 49500
                                                                                ·
                                                                                  have hr : n - 49450 < 50 := by omega
                                                                                  have heq : n = (n - 49450) + 49450 := by omega
                                                                                  rw [heq]
                                                                                  exact cs_w39 ⟨n - 49450, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 49550
                                                                                  ·
                                                                                    have hr : n - 49500 < 50 := by omega
                                                                                    have heq : n = (n - 49500) + 49500 := by omega
                                                                                    rw [heq]
                                                                                    exact cs_w40 ⟨n - 49500, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 49600
                                                                                    ·
                                                                                      have hr : n - 49550 < 50 := by omega
                                                                                      have heq : n = (n - 49550) + 49550 := by omega
                                                                                      rw [heq]
                                                                                      exact cs_w41 ⟨n - 49550, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 49650
                                                                                      ·
                                                                                        have hr : n - 49600 < 50 := by omega
                                                                                        have heq : n = (n - 49600) + 49600 := by omega
                                                                                        rw [heq]
                                                                                        exact cs_w42 ⟨n - 49600, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 49700
                                                                                        ·
                                                                                          have hr : n - 49650 < 50 := by omega
                                                                                          have heq : n = (n - 49650) + 49650 := by omega
                                                                                          rw [heq]
                                                                                          exact cs_w43 ⟨n - 49650, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 49750
                                                                                          ·
                                                                                            have hr : n - 49700 < 50 := by omega
                                                                                            have heq : n = (n - 49700) + 49700 := by omega
                                                                                            rw [heq]
                                                                                            exact cs_w44 ⟨n - 49700, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 49800
                                                                                            ·
                                                                                              have hr : n - 49750 < 50 := by omega
                                                                                              have heq : n = (n - 49750) + 49750 := by omega
                                                                                              rw [heq]
                                                                                              exact cs_w45 ⟨n - 49750, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 49850
                                                                                              ·
                                                                                                have hr : n - 49800 < 50 := by omega
                                                                                                have heq : n = (n - 49800) + 49800 := by omega
                                                                                                rw [heq]
                                                                                                exact cs_w46 ⟨n - 49800, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 49900
                                                                                                ·
                                                                                                  have hr : n - 49850 < 50 := by omega
                                                                                                  have heq : n = (n - 49850) + 49850 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cs_w47 ⟨n - 49850, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 49950
                                                                                                  ·
                                                                                                    have hr : n - 49900 < 50 := by omega
                                                                                                    have heq : n = (n - 49900) + 49900 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w48 ⟨n - 49900, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 49950 < 50 := by omega
                                                                                                    have heq : n = (n - 49950) + 49950 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w49 ⟨n - 49950, hr⟩


theorem centF_lt_range : ∀ n, 47500 ≤ n → n < 50000 → centF n < 23 := by
  intro n hlo hhi
  by_cases h0 : n < 47550
  · have hr : n - 47500 < 50 := by omega
    have heq : n = (n - 47500) + 47500 := by omega
    rw [heq]
    exact cl_w0 ⟨n - 47500, hr⟩
  ·
    by_cases h1 : n < 47600
    ·
      have hr : n - 47550 < 50 := by omega
      have heq : n = (n - 47550) + 47550 := by omega
      rw [heq]
      exact cl_w1 ⟨n - 47550, hr⟩
    ·
      by_cases h2 : n < 47650
      ·
        have hr : n - 47600 < 50 := by omega
        have heq : n = (n - 47600) + 47600 := by omega
        rw [heq]
        exact cl_w2 ⟨n - 47600, hr⟩
      ·
        by_cases h3 : n < 47700
        ·
          have hr : n - 47650 < 50 := by omega
          have heq : n = (n - 47650) + 47650 := by omega
          rw [heq]
          exact cl_w3 ⟨n - 47650, hr⟩
        ·
          by_cases h4 : n < 47750
          ·
            have hr : n - 47700 < 50 := by omega
            have heq : n = (n - 47700) + 47700 := by omega
            rw [heq]
            exact cl_w4 ⟨n - 47700, hr⟩
          ·
            by_cases h5 : n < 47800
            ·
              have hr : n - 47750 < 50 := by omega
              have heq : n = (n - 47750) + 47750 := by omega
              rw [heq]
              exact cl_w5 ⟨n - 47750, hr⟩
            ·
              by_cases h6 : n < 47850
              ·
                have hr : n - 47800 < 50 := by omega
                have heq : n = (n - 47800) + 47800 := by omega
                rw [heq]
                exact cl_w6 ⟨n - 47800, hr⟩
              ·
                by_cases h7 : n < 47900
                ·
                  have hr : n - 47850 < 50 := by omega
                  have heq : n = (n - 47850) + 47850 := by omega
                  rw [heq]
                  exact cl_w7 ⟨n - 47850, hr⟩
                ·
                  by_cases h8 : n < 47950
                  ·
                    have hr : n - 47900 < 50 := by omega
                    have heq : n = (n - 47900) + 47900 := by omega
                    rw [heq]
                    exact cl_w8 ⟨n - 47900, hr⟩
                  ·
                    by_cases h9 : n < 48000
                    ·
                      have hr : n - 47950 < 50 := by omega
                      have heq : n = (n - 47950) + 47950 := by omega
                      rw [heq]
                      exact cl_w9 ⟨n - 47950, hr⟩
                    ·
                      by_cases h10 : n < 48050
                      ·
                        have hr : n - 48000 < 50 := by omega
                        have heq : n = (n - 48000) + 48000 := by omega
                        rw [heq]
                        exact cl_w10 ⟨n - 48000, hr⟩
                      ·
                        by_cases h11 : n < 48100
                        ·
                          have hr : n - 48050 < 50 := by omega
                          have heq : n = (n - 48050) + 48050 := by omega
                          rw [heq]
                          exact cl_w11 ⟨n - 48050, hr⟩
                        ·
                          by_cases h12 : n < 48150
                          ·
                            have hr : n - 48100 < 50 := by omega
                            have heq : n = (n - 48100) + 48100 := by omega
                            rw [heq]
                            exact cl_w12 ⟨n - 48100, hr⟩
                          ·
                            by_cases h13 : n < 48200
                            ·
                              have hr : n - 48150 < 50 := by omega
                              have heq : n = (n - 48150) + 48150 := by omega
                              rw [heq]
                              exact cl_w13 ⟨n - 48150, hr⟩
                            ·
                              by_cases h14 : n < 48250
                              ·
                                have hr : n - 48200 < 50 := by omega
                                have heq : n = (n - 48200) + 48200 := by omega
                                rw [heq]
                                exact cl_w14 ⟨n - 48200, hr⟩
                              ·
                                by_cases h15 : n < 48300
                                ·
                                  have hr : n - 48250 < 50 := by omega
                                  have heq : n = (n - 48250) + 48250 := by omega
                                  rw [heq]
                                  exact cl_w15 ⟨n - 48250, hr⟩
                                ·
                                  by_cases h16 : n < 48350
                                  ·
                                    have hr : n - 48300 < 50 := by omega
                                    have heq : n = (n - 48300) + 48300 := by omega
                                    rw [heq]
                                    exact cl_w16 ⟨n - 48300, hr⟩
                                  ·
                                    by_cases h17 : n < 48400
                                    ·
                                      have hr : n - 48350 < 50 := by omega
                                      have heq : n = (n - 48350) + 48350 := by omega
                                      rw [heq]
                                      exact cl_w17 ⟨n - 48350, hr⟩
                                    ·
                                      by_cases h18 : n < 48450
                                      ·
                                        have hr : n - 48400 < 50 := by omega
                                        have heq : n = (n - 48400) + 48400 := by omega
                                        rw [heq]
                                        exact cl_w18 ⟨n - 48400, hr⟩
                                      ·
                                        by_cases h19 : n < 48500
                                        ·
                                          have hr : n - 48450 < 50 := by omega
                                          have heq : n = (n - 48450) + 48450 := by omega
                                          rw [heq]
                                          exact cl_w19 ⟨n - 48450, hr⟩
                                        ·
                                          by_cases h20 : n < 48550
                                          ·
                                            have hr : n - 48500 < 50 := by omega
                                            have heq : n = (n - 48500) + 48500 := by omega
                                            rw [heq]
                                            exact cl_w20 ⟨n - 48500, hr⟩
                                          ·
                                            by_cases h21 : n < 48600
                                            ·
                                              have hr : n - 48550 < 50 := by omega
                                              have heq : n = (n - 48550) + 48550 := by omega
                                              rw [heq]
                                              exact cl_w21 ⟨n - 48550, hr⟩
                                            ·
                                              by_cases h22 : n < 48650
                                              ·
                                                have hr : n - 48600 < 50 := by omega
                                                have heq : n = (n - 48600) + 48600 := by omega
                                                rw [heq]
                                                exact cl_w22 ⟨n - 48600, hr⟩
                                              ·
                                                by_cases h23 : n < 48700
                                                ·
                                                  have hr : n - 48650 < 50 := by omega
                                                  have heq : n = (n - 48650) + 48650 := by omega
                                                  rw [heq]
                                                  exact cl_w23 ⟨n - 48650, hr⟩
                                                ·
                                                  by_cases h24 : n < 48750
                                                  ·
                                                    have hr : n - 48700 < 50 := by omega
                                                    have heq : n = (n - 48700) + 48700 := by omega
                                                    rw [heq]
                                                    exact cl_w24 ⟨n - 48700, hr⟩
                                                  ·
                                                    by_cases h25 : n < 48800
                                                    ·
                                                      have hr : n - 48750 < 50 := by omega
                                                      have heq : n = (n - 48750) + 48750 := by omega
                                                      rw [heq]
                                                      exact cl_w25 ⟨n - 48750, hr⟩
                                                    ·
                                                      by_cases h26 : n < 48850
                                                      ·
                                                        have hr : n - 48800 < 50 := by omega
                                                        have heq : n = (n - 48800) + 48800 := by omega
                                                        rw [heq]
                                                        exact cl_w26 ⟨n - 48800, hr⟩
                                                      ·
                                                        by_cases h27 : n < 48900
                                                        ·
                                                          have hr : n - 48850 < 50 := by omega
                                                          have heq : n = (n - 48850) + 48850 := by omega
                                                          rw [heq]
                                                          exact cl_w27 ⟨n - 48850, hr⟩
                                                        ·
                                                          by_cases h28 : n < 48950
                                                          ·
                                                            have hr : n - 48900 < 50 := by omega
                                                            have heq : n = (n - 48900) + 48900 := by omega
                                                            rw [heq]
                                                            exact cl_w28 ⟨n - 48900, hr⟩
                                                          ·
                                                            by_cases h29 : n < 49000
                                                            ·
                                                              have hr : n - 48950 < 50 := by omega
                                                              have heq : n = (n - 48950) + 48950 := by omega
                                                              rw [heq]
                                                              exact cl_w29 ⟨n - 48950, hr⟩
                                                            ·
                                                              by_cases h30 : n < 49050
                                                              ·
                                                                have hr : n - 49000 < 50 := by omega
                                                                have heq : n = (n - 49000) + 49000 := by omega
                                                                rw [heq]
                                                                exact cl_w30 ⟨n - 49000, hr⟩
                                                              ·
                                                                by_cases h31 : n < 49100
                                                                ·
                                                                  have hr : n - 49050 < 50 := by omega
                                                                  have heq : n = (n - 49050) + 49050 := by omega
                                                                  rw [heq]
                                                                  exact cl_w31 ⟨n - 49050, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 49150
                                                                  ·
                                                                    have hr : n - 49100 < 50 := by omega
                                                                    have heq : n = (n - 49100) + 49100 := by omega
                                                                    rw [heq]
                                                                    exact cl_w32 ⟨n - 49100, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 49200
                                                                    ·
                                                                      have hr : n - 49150 < 50 := by omega
                                                                      have heq : n = (n - 49150) + 49150 := by omega
                                                                      rw [heq]
                                                                      exact cl_w33 ⟨n - 49150, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 49250
                                                                      ·
                                                                        have hr : n - 49200 < 50 := by omega
                                                                        have heq : n = (n - 49200) + 49200 := by omega
                                                                        rw [heq]
                                                                        exact cl_w34 ⟨n - 49200, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 49300
                                                                        ·
                                                                          have hr : n - 49250 < 50 := by omega
                                                                          have heq : n = (n - 49250) + 49250 := by omega
                                                                          rw [heq]
                                                                          exact cl_w35 ⟨n - 49250, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 49350
                                                                          ·
                                                                            have hr : n - 49300 < 50 := by omega
                                                                            have heq : n = (n - 49300) + 49300 := by omega
                                                                            rw [heq]
                                                                            exact cl_w36 ⟨n - 49300, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 49400
                                                                            ·
                                                                              have hr : n - 49350 < 50 := by omega
                                                                              have heq : n = (n - 49350) + 49350 := by omega
                                                                              rw [heq]
                                                                              exact cl_w37 ⟨n - 49350, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 49450
                                                                              ·
                                                                                have hr : n - 49400 < 50 := by omega
                                                                                have heq : n = (n - 49400) + 49400 := by omega
                                                                                rw [heq]
                                                                                exact cl_w38 ⟨n - 49400, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 49500
                                                                                ·
                                                                                  have hr : n - 49450 < 50 := by omega
                                                                                  have heq : n = (n - 49450) + 49450 := by omega
                                                                                  rw [heq]
                                                                                  exact cl_w39 ⟨n - 49450, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 49550
                                                                                  ·
                                                                                    have hr : n - 49500 < 50 := by omega
                                                                                    have heq : n = (n - 49500) + 49500 := by omega
                                                                                    rw [heq]
                                                                                    exact cl_w40 ⟨n - 49500, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 49600
                                                                                    ·
                                                                                      have hr : n - 49550 < 50 := by omega
                                                                                      have heq : n = (n - 49550) + 49550 := by omega
                                                                                      rw [heq]
                                                                                      exact cl_w41 ⟨n - 49550, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 49650
                                                                                      ·
                                                                                        have hr : n - 49600 < 50 := by omega
                                                                                        have heq : n = (n - 49600) + 49600 := by omega
                                                                                        rw [heq]
                                                                                        exact cl_w42 ⟨n - 49600, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 49700
                                                                                        ·
                                                                                          have hr : n - 49650 < 50 := by omega
                                                                                          have heq : n = (n - 49650) + 49650 := by omega
                                                                                          rw [heq]
                                                                                          exact cl_w43 ⟨n - 49650, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 49750
                                                                                          ·
                                                                                            have hr : n - 49700 < 50 := by omega
                                                                                            have heq : n = (n - 49700) + 49700 := by omega
                                                                                            rw [heq]
                                                                                            exact cl_w44 ⟨n - 49700, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 49800
                                                                                            ·
                                                                                              have hr : n - 49750 < 50 := by omega
                                                                                              have heq : n = (n - 49750) + 49750 := by omega
                                                                                              rw [heq]
                                                                                              exact cl_w45 ⟨n - 49750, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 49850
                                                                                              ·
                                                                                                have hr : n - 49800 < 50 := by omega
                                                                                                have heq : n = (n - 49800) + 49800 := by omega
                                                                                                rw [heq]
                                                                                                exact cl_w46 ⟨n - 49800, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 49900
                                                                                                ·
                                                                                                  have hr : n - 49850 < 50 := by omega
                                                                                                  have heq : n = (n - 49850) + 49850 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cl_w47 ⟨n - 49850, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 49950
                                                                                                  ·
                                                                                                    have hr : n - 49900 < 50 := by omega
                                                                                                    have heq : n = (n - 49900) + 49900 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w48 ⟨n - 49900, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 49950 < 50 := by omega
                                                                                                    have heq : n = (n - 49950) + 49950 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w49 ⟨n - 49950, hr⟩


theorem densSupG_lt_range : ∀ n, 47500 ≤ n → n < 50000 → densSupG n < 2 ^ 1771 := by
  intro n hlo hhi
  by_cases h0 : n < 47550
  · have hr : n - 47500 < 50 := by omega
    have heq : n = (n - 47500) + 47500 := by omega
    rw [heq]
    exact bd_w0 ⟨n - 47500, hr⟩
  ·
    by_cases h1 : n < 47600
    ·
      have hr : n - 47550 < 50 := by omega
      have heq : n = (n - 47550) + 47550 := by omega
      rw [heq]
      exact bd_w1 ⟨n - 47550, hr⟩
    ·
      by_cases h2 : n < 47650
      ·
        have hr : n - 47600 < 50 := by omega
        have heq : n = (n - 47600) + 47600 := by omega
        rw [heq]
        exact bd_w2 ⟨n - 47600, hr⟩
      ·
        by_cases h3 : n < 47700
        ·
          have hr : n - 47650 < 50 := by omega
          have heq : n = (n - 47650) + 47650 := by omega
          rw [heq]
          exact bd_w3 ⟨n - 47650, hr⟩
        ·
          by_cases h4 : n < 47750
          ·
            have hr : n - 47700 < 50 := by omega
            have heq : n = (n - 47700) + 47700 := by omega
            rw [heq]
            exact bd_w4 ⟨n - 47700, hr⟩
          ·
            by_cases h5 : n < 47800
            ·
              have hr : n - 47750 < 50 := by omega
              have heq : n = (n - 47750) + 47750 := by omega
              rw [heq]
              exact bd_w5 ⟨n - 47750, hr⟩
            ·
              by_cases h6 : n < 47850
              ·
                have hr : n - 47800 < 50 := by omega
                have heq : n = (n - 47800) + 47800 := by omega
                rw [heq]
                exact bd_w6 ⟨n - 47800, hr⟩
              ·
                by_cases h7 : n < 47900
                ·
                  have hr : n - 47850 < 50 := by omega
                  have heq : n = (n - 47850) + 47850 := by omega
                  rw [heq]
                  exact bd_w7 ⟨n - 47850, hr⟩
                ·
                  by_cases h8 : n < 47950
                  ·
                    have hr : n - 47900 < 50 := by omega
                    have heq : n = (n - 47900) + 47900 := by omega
                    rw [heq]
                    exact bd_w8 ⟨n - 47900, hr⟩
                  ·
                    by_cases h9 : n < 48000
                    ·
                      have hr : n - 47950 < 50 := by omega
                      have heq : n = (n - 47950) + 47950 := by omega
                      rw [heq]
                      exact bd_w9 ⟨n - 47950, hr⟩
                    ·
                      by_cases h10 : n < 48050
                      ·
                        have hr : n - 48000 < 50 := by omega
                        have heq : n = (n - 48000) + 48000 := by omega
                        rw [heq]
                        exact bd_w10 ⟨n - 48000, hr⟩
                      ·
                        by_cases h11 : n < 48100
                        ·
                          have hr : n - 48050 < 50 := by omega
                          have heq : n = (n - 48050) + 48050 := by omega
                          rw [heq]
                          exact bd_w11 ⟨n - 48050, hr⟩
                        ·
                          by_cases h12 : n < 48150
                          ·
                            have hr : n - 48100 < 50 := by omega
                            have heq : n = (n - 48100) + 48100 := by omega
                            rw [heq]
                            exact bd_w12 ⟨n - 48100, hr⟩
                          ·
                            by_cases h13 : n < 48200
                            ·
                              have hr : n - 48150 < 50 := by omega
                              have heq : n = (n - 48150) + 48150 := by omega
                              rw [heq]
                              exact bd_w13 ⟨n - 48150, hr⟩
                            ·
                              by_cases h14 : n < 48250
                              ·
                                have hr : n - 48200 < 50 := by omega
                                have heq : n = (n - 48200) + 48200 := by omega
                                rw [heq]
                                exact bd_w14 ⟨n - 48200, hr⟩
                              ·
                                by_cases h15 : n < 48300
                                ·
                                  have hr : n - 48250 < 50 := by omega
                                  have heq : n = (n - 48250) + 48250 := by omega
                                  rw [heq]
                                  exact bd_w15 ⟨n - 48250, hr⟩
                                ·
                                  by_cases h16 : n < 48350
                                  ·
                                    have hr : n - 48300 < 50 := by omega
                                    have heq : n = (n - 48300) + 48300 := by omega
                                    rw [heq]
                                    exact bd_w16 ⟨n - 48300, hr⟩
                                  ·
                                    by_cases h17 : n < 48400
                                    ·
                                      have hr : n - 48350 < 50 := by omega
                                      have heq : n = (n - 48350) + 48350 := by omega
                                      rw [heq]
                                      exact bd_w17 ⟨n - 48350, hr⟩
                                    ·
                                      by_cases h18 : n < 48450
                                      ·
                                        have hr : n - 48400 < 50 := by omega
                                        have heq : n = (n - 48400) + 48400 := by omega
                                        rw [heq]
                                        exact bd_w18 ⟨n - 48400, hr⟩
                                      ·
                                        by_cases h19 : n < 48500
                                        ·
                                          have hr : n - 48450 < 50 := by omega
                                          have heq : n = (n - 48450) + 48450 := by omega
                                          rw [heq]
                                          exact bd_w19 ⟨n - 48450, hr⟩
                                        ·
                                          by_cases h20 : n < 48550
                                          ·
                                            have hr : n - 48500 < 50 := by omega
                                            have heq : n = (n - 48500) + 48500 := by omega
                                            rw [heq]
                                            exact bd_w20 ⟨n - 48500, hr⟩
                                          ·
                                            by_cases h21 : n < 48600
                                            ·
                                              have hr : n - 48550 < 50 := by omega
                                              have heq : n = (n - 48550) + 48550 := by omega
                                              rw [heq]
                                              exact bd_w21 ⟨n - 48550, hr⟩
                                            ·
                                              by_cases h22 : n < 48650
                                              ·
                                                have hr : n - 48600 < 50 := by omega
                                                have heq : n = (n - 48600) + 48600 := by omega
                                                rw [heq]
                                                exact bd_w22 ⟨n - 48600, hr⟩
                                              ·
                                                by_cases h23 : n < 48700
                                                ·
                                                  have hr : n - 48650 < 50 := by omega
                                                  have heq : n = (n - 48650) + 48650 := by omega
                                                  rw [heq]
                                                  exact bd_w23 ⟨n - 48650, hr⟩
                                                ·
                                                  by_cases h24 : n < 48750
                                                  ·
                                                    have hr : n - 48700 < 50 := by omega
                                                    have heq : n = (n - 48700) + 48700 := by omega
                                                    rw [heq]
                                                    exact bd_w24 ⟨n - 48700, hr⟩
                                                  ·
                                                    by_cases h25 : n < 48800
                                                    ·
                                                      have hr : n - 48750 < 50 := by omega
                                                      have heq : n = (n - 48750) + 48750 := by omega
                                                      rw [heq]
                                                      exact bd_w25 ⟨n - 48750, hr⟩
                                                    ·
                                                      by_cases h26 : n < 48850
                                                      ·
                                                        have hr : n - 48800 < 50 := by omega
                                                        have heq : n = (n - 48800) + 48800 := by omega
                                                        rw [heq]
                                                        exact bd_w26 ⟨n - 48800, hr⟩
                                                      ·
                                                        by_cases h27 : n < 48900
                                                        ·
                                                          have hr : n - 48850 < 50 := by omega
                                                          have heq : n = (n - 48850) + 48850 := by omega
                                                          rw [heq]
                                                          exact bd_w27 ⟨n - 48850, hr⟩
                                                        ·
                                                          by_cases h28 : n < 48950
                                                          ·
                                                            have hr : n - 48900 < 50 := by omega
                                                            have heq : n = (n - 48900) + 48900 := by omega
                                                            rw [heq]
                                                            exact bd_w28 ⟨n - 48900, hr⟩
                                                          ·
                                                            by_cases h29 : n < 49000
                                                            ·
                                                              have hr : n - 48950 < 50 := by omega
                                                              have heq : n = (n - 48950) + 48950 := by omega
                                                              rw [heq]
                                                              exact bd_w29 ⟨n - 48950, hr⟩
                                                            ·
                                                              by_cases h30 : n < 49050
                                                              ·
                                                                have hr : n - 49000 < 50 := by omega
                                                                have heq : n = (n - 49000) + 49000 := by omega
                                                                rw [heq]
                                                                exact bd_w30 ⟨n - 49000, hr⟩
                                                              ·
                                                                by_cases h31 : n < 49100
                                                                ·
                                                                  have hr : n - 49050 < 50 := by omega
                                                                  have heq : n = (n - 49050) + 49050 := by omega
                                                                  rw [heq]
                                                                  exact bd_w31 ⟨n - 49050, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 49150
                                                                  ·
                                                                    have hr : n - 49100 < 50 := by omega
                                                                    have heq : n = (n - 49100) + 49100 := by omega
                                                                    rw [heq]
                                                                    exact bd_w32 ⟨n - 49100, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 49200
                                                                    ·
                                                                      have hr : n - 49150 < 50 := by omega
                                                                      have heq : n = (n - 49150) + 49150 := by omega
                                                                      rw [heq]
                                                                      exact bd_w33 ⟨n - 49150, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 49250
                                                                      ·
                                                                        have hr : n - 49200 < 50 := by omega
                                                                        have heq : n = (n - 49200) + 49200 := by omega
                                                                        rw [heq]
                                                                        exact bd_w34 ⟨n - 49200, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 49300
                                                                        ·
                                                                          have hr : n - 49250 < 50 := by omega
                                                                          have heq : n = (n - 49250) + 49250 := by omega
                                                                          rw [heq]
                                                                          exact bd_w35 ⟨n - 49250, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 49350
                                                                          ·
                                                                            have hr : n - 49300 < 50 := by omega
                                                                            have heq : n = (n - 49300) + 49300 := by omega
                                                                            rw [heq]
                                                                            exact bd_w36 ⟨n - 49300, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 49400
                                                                            ·
                                                                              have hr : n - 49350 < 50 := by omega
                                                                              have heq : n = (n - 49350) + 49350 := by omega
                                                                              rw [heq]
                                                                              exact bd_w37 ⟨n - 49350, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 49450
                                                                              ·
                                                                                have hr : n - 49400 < 50 := by omega
                                                                                have heq : n = (n - 49400) + 49400 := by omega
                                                                                rw [heq]
                                                                                exact bd_w38 ⟨n - 49400, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 49500
                                                                                ·
                                                                                  have hr : n - 49450 < 50 := by omega
                                                                                  have heq : n = (n - 49450) + 49450 := by omega
                                                                                  rw [heq]
                                                                                  exact bd_w39 ⟨n - 49450, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 49550
                                                                                  ·
                                                                                    have hr : n - 49500 < 50 := by omega
                                                                                    have heq : n = (n - 49500) + 49500 := by omega
                                                                                    rw [heq]
                                                                                    exact bd_w40 ⟨n - 49500, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 49600
                                                                                    ·
                                                                                      have hr : n - 49550 < 50 := by omega
                                                                                      have heq : n = (n - 49550) + 49550 := by omega
                                                                                      rw [heq]
                                                                                      exact bd_w41 ⟨n - 49550, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 49650
                                                                                      ·
                                                                                        have hr : n - 49600 < 50 := by omega
                                                                                        have heq : n = (n - 49600) + 49600 := by omega
                                                                                        rw [heq]
                                                                                        exact bd_w42 ⟨n - 49600, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 49700
                                                                                        ·
                                                                                          have hr : n - 49650 < 50 := by omega
                                                                                          have heq : n = (n - 49650) + 49650 := by omega
                                                                                          rw [heq]
                                                                                          exact bd_w43 ⟨n - 49650, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 49750
                                                                                          ·
                                                                                            have hr : n - 49700 < 50 := by omega
                                                                                            have heq : n = (n - 49700) + 49700 := by omega
                                                                                            rw [heq]
                                                                                            exact bd_w44 ⟨n - 49700, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 49800
                                                                                            ·
                                                                                              have hr : n - 49750 < 50 := by omega
                                                                                              have heq : n = (n - 49750) + 49750 := by omega
                                                                                              rw [heq]
                                                                                              exact bd_w45 ⟨n - 49750, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 49850
                                                                                              ·
                                                                                                have hr : n - 49800 < 50 := by omega
                                                                                                have heq : n = (n - 49800) + 49800 := by omega
                                                                                                rw [heq]
                                                                                                exact bd_w46 ⟨n - 49800, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 49900
                                                                                                ·
                                                                                                  have hr : n - 49850 < 50 := by omega
                                                                                                  have heq : n = (n - 49850) + 49850 := by omega
                                                                                                  rw [heq]
                                                                                                  exact bd_w47 ⟨n - 49850, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 49950
                                                                                                  ·
                                                                                                    have hr : n - 49900 < 50 := by omega
                                                                                                    have heq : n = (n - 49900) + 49900 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w48 ⟨n - 49900, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 49950 < 50 := by omega
                                                                                                    have heq : n = (n - 49950) + 49950 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w49 ⟨n - 49950, hr⟩


end IntMul.Kappa.R8.Bit.Oppbank.CentBound9b


