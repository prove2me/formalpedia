-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound6b
-- name    : IntMul_Kappa_R8_Data_BitOppbankCentBound6b
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:01:26.631539+00:00
-- url     : https://prove2.me/theorems/3a5bff85-ff86-414c-8835-d77664e31943
-- title:
--   HasCentre certificates dens nodes [32500,35000)
-- statement:
--   # Densified centre certificates, pack 6b
--
--   For every densified node index $n$ with $32500\le n<35000$,
--   $$
--   \mathrm{centredStar}(\mathrm{densSupG}\,n,\mathrm{centF}\,n)=\mathsf{true},\quad
--   \mathrm{centF}\,n<23,\quad
--   \mathrm{densSupG}\,n < 2^{1771}.
--   $$
--   Proved by decide on Fin 50 windows (no native_decide). Half-pack for 300s server budget.
-- source:
--   R8 BitOppbank AllDensCentred; jfstack_23 densified supports

-- CentBound pack 6b: densified HasCentre certificates on n ∈ [32500, 35000)
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

namespace IntMul.Kappa.R8.Bit.Oppbank.CentBound6b


private theorem cs_w0 : ∀ n : Fin 50, centredStar (densSupG (n.val + 32500)) (centF (n.val + 32500)) = true := by decide
private theorem cl_w0 : ∀ n : Fin 50, centF (n.val + 32500) < 23 := by decide
private theorem bd_w0 : ∀ n : Fin 50, densSupG (n.val + 32500) < 2 ^ 1771 := by decide
private theorem cs_w1 : ∀ n : Fin 50, centredStar (densSupG (n.val + 32550)) (centF (n.val + 32550)) = true := by decide
private theorem cl_w1 : ∀ n : Fin 50, centF (n.val + 32550) < 23 := by decide
private theorem bd_w1 : ∀ n : Fin 50, densSupG (n.val + 32550) < 2 ^ 1771 := by decide
private theorem cs_w2 : ∀ n : Fin 50, centredStar (densSupG (n.val + 32600)) (centF (n.val + 32600)) = true := by decide
private theorem cl_w2 : ∀ n : Fin 50, centF (n.val + 32600) < 23 := by decide
private theorem bd_w2 : ∀ n : Fin 50, densSupG (n.val + 32600) < 2 ^ 1771 := by decide
private theorem cs_w3 : ∀ n : Fin 50, centredStar (densSupG (n.val + 32650)) (centF (n.val + 32650)) = true := by decide
private theorem cl_w3 : ∀ n : Fin 50, centF (n.val + 32650) < 23 := by decide
private theorem bd_w3 : ∀ n : Fin 50, densSupG (n.val + 32650) < 2 ^ 1771 := by decide
private theorem cs_w4 : ∀ n : Fin 50, centredStar (densSupG (n.val + 32700)) (centF (n.val + 32700)) = true := by decide
private theorem cl_w4 : ∀ n : Fin 50, centF (n.val + 32700) < 23 := by decide
private theorem bd_w4 : ∀ n : Fin 50, densSupG (n.val + 32700) < 2 ^ 1771 := by decide
private theorem cs_w5 : ∀ n : Fin 50, centredStar (densSupG (n.val + 32750)) (centF (n.val + 32750)) = true := by decide
private theorem cl_w5 : ∀ n : Fin 50, centF (n.val + 32750) < 23 := by decide
private theorem bd_w5 : ∀ n : Fin 50, densSupG (n.val + 32750) < 2 ^ 1771 := by decide
private theorem cs_w6 : ∀ n : Fin 50, centredStar (densSupG (n.val + 32800)) (centF (n.val + 32800)) = true := by decide
private theorem cl_w6 : ∀ n : Fin 50, centF (n.val + 32800) < 23 := by decide
private theorem bd_w6 : ∀ n : Fin 50, densSupG (n.val + 32800) < 2 ^ 1771 := by decide
private theorem cs_w7 : ∀ n : Fin 50, centredStar (densSupG (n.val + 32850)) (centF (n.val + 32850)) = true := by decide
private theorem cl_w7 : ∀ n : Fin 50, centF (n.val + 32850) < 23 := by decide
private theorem bd_w7 : ∀ n : Fin 50, densSupG (n.val + 32850) < 2 ^ 1771 := by decide
private theorem cs_w8 : ∀ n : Fin 50, centredStar (densSupG (n.val + 32900)) (centF (n.val + 32900)) = true := by decide
private theorem cl_w8 : ∀ n : Fin 50, centF (n.val + 32900) < 23 := by decide
private theorem bd_w8 : ∀ n : Fin 50, densSupG (n.val + 32900) < 2 ^ 1771 := by decide
private theorem cs_w9 : ∀ n : Fin 50, centredStar (densSupG (n.val + 32950)) (centF (n.val + 32950)) = true := by decide
private theorem cl_w9 : ∀ n : Fin 50, centF (n.val + 32950) < 23 := by decide
private theorem bd_w9 : ∀ n : Fin 50, densSupG (n.val + 32950) < 2 ^ 1771 := by decide
private theorem cs_w10 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33000)) (centF (n.val + 33000)) = true := by decide
private theorem cl_w10 : ∀ n : Fin 50, centF (n.val + 33000) < 23 := by decide
private theorem bd_w10 : ∀ n : Fin 50, densSupG (n.val + 33000) < 2 ^ 1771 := by decide
private theorem cs_w11 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33050)) (centF (n.val + 33050)) = true := by decide
private theorem cl_w11 : ∀ n : Fin 50, centF (n.val + 33050) < 23 := by decide
private theorem bd_w11 : ∀ n : Fin 50, densSupG (n.val + 33050) < 2 ^ 1771 := by decide
private theorem cs_w12 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33100)) (centF (n.val + 33100)) = true := by decide
private theorem cl_w12 : ∀ n : Fin 50, centF (n.val + 33100) < 23 := by decide
private theorem bd_w12 : ∀ n : Fin 50, densSupG (n.val + 33100) < 2 ^ 1771 := by decide
private theorem cs_w13 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33150)) (centF (n.val + 33150)) = true := by decide
private theorem cl_w13 : ∀ n : Fin 50, centF (n.val + 33150) < 23 := by decide
private theorem bd_w13 : ∀ n : Fin 50, densSupG (n.val + 33150) < 2 ^ 1771 := by decide
private theorem cs_w14 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33200)) (centF (n.val + 33200)) = true := by decide
private theorem cl_w14 : ∀ n : Fin 50, centF (n.val + 33200) < 23 := by decide
private theorem bd_w14 : ∀ n : Fin 50, densSupG (n.val + 33200) < 2 ^ 1771 := by decide
private theorem cs_w15 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33250)) (centF (n.val + 33250)) = true := by decide
private theorem cl_w15 : ∀ n : Fin 50, centF (n.val + 33250) < 23 := by decide
private theorem bd_w15 : ∀ n : Fin 50, densSupG (n.val + 33250) < 2 ^ 1771 := by decide
private theorem cs_w16 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33300)) (centF (n.val + 33300)) = true := by decide
private theorem cl_w16 : ∀ n : Fin 50, centF (n.val + 33300) < 23 := by decide
private theorem bd_w16 : ∀ n : Fin 50, densSupG (n.val + 33300) < 2 ^ 1771 := by decide
private theorem cs_w17 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33350)) (centF (n.val + 33350)) = true := by decide
private theorem cl_w17 : ∀ n : Fin 50, centF (n.val + 33350) < 23 := by decide
private theorem bd_w17 : ∀ n : Fin 50, densSupG (n.val + 33350) < 2 ^ 1771 := by decide
private theorem cs_w18 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33400)) (centF (n.val + 33400)) = true := by decide
private theorem cl_w18 : ∀ n : Fin 50, centF (n.val + 33400) < 23 := by decide
private theorem bd_w18 : ∀ n : Fin 50, densSupG (n.val + 33400) < 2 ^ 1771 := by decide
private theorem cs_w19 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33450)) (centF (n.val + 33450)) = true := by decide
private theorem cl_w19 : ∀ n : Fin 50, centF (n.val + 33450) < 23 := by decide
private theorem bd_w19 : ∀ n : Fin 50, densSupG (n.val + 33450) < 2 ^ 1771 := by decide
private theorem cs_w20 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33500)) (centF (n.val + 33500)) = true := by decide
private theorem cl_w20 : ∀ n : Fin 50, centF (n.val + 33500) < 23 := by decide
private theorem bd_w20 : ∀ n : Fin 50, densSupG (n.val + 33500) < 2 ^ 1771 := by decide
private theorem cs_w21 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33550)) (centF (n.val + 33550)) = true := by decide
private theorem cl_w21 : ∀ n : Fin 50, centF (n.val + 33550) < 23 := by decide
private theorem bd_w21 : ∀ n : Fin 50, densSupG (n.val + 33550) < 2 ^ 1771 := by decide
private theorem cs_w22 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33600)) (centF (n.val + 33600)) = true := by decide
private theorem cl_w22 : ∀ n : Fin 50, centF (n.val + 33600) < 23 := by decide
private theorem bd_w22 : ∀ n : Fin 50, densSupG (n.val + 33600) < 2 ^ 1771 := by decide
private theorem cs_w23 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33650)) (centF (n.val + 33650)) = true := by decide
private theorem cl_w23 : ∀ n : Fin 50, centF (n.val + 33650) < 23 := by decide
private theorem bd_w23 : ∀ n : Fin 50, densSupG (n.val + 33650) < 2 ^ 1771 := by decide
private theorem cs_w24 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33700)) (centF (n.val + 33700)) = true := by decide
private theorem cl_w24 : ∀ n : Fin 50, centF (n.val + 33700) < 23 := by decide
private theorem bd_w24 : ∀ n : Fin 50, densSupG (n.val + 33700) < 2 ^ 1771 := by decide
private theorem cs_w25 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33750)) (centF (n.val + 33750)) = true := by decide
private theorem cl_w25 : ∀ n : Fin 50, centF (n.val + 33750) < 23 := by decide
private theorem bd_w25 : ∀ n : Fin 50, densSupG (n.val + 33750) < 2 ^ 1771 := by decide
private theorem cs_w26 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33800)) (centF (n.val + 33800)) = true := by decide
private theorem cl_w26 : ∀ n : Fin 50, centF (n.val + 33800) < 23 := by decide
private theorem bd_w26 : ∀ n : Fin 50, densSupG (n.val + 33800) < 2 ^ 1771 := by decide
private theorem cs_w27 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33850)) (centF (n.val + 33850)) = true := by decide
private theorem cl_w27 : ∀ n : Fin 50, centF (n.val + 33850) < 23 := by decide
private theorem bd_w27 : ∀ n : Fin 50, densSupG (n.val + 33850) < 2 ^ 1771 := by decide
private theorem cs_w28 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33900)) (centF (n.val + 33900)) = true := by decide
private theorem cl_w28 : ∀ n : Fin 50, centF (n.val + 33900) < 23 := by decide
private theorem bd_w28 : ∀ n : Fin 50, densSupG (n.val + 33900) < 2 ^ 1771 := by decide
private theorem cs_w29 : ∀ n : Fin 50, centredStar (densSupG (n.val + 33950)) (centF (n.val + 33950)) = true := by decide
private theorem cl_w29 : ∀ n : Fin 50, centF (n.val + 33950) < 23 := by decide
private theorem bd_w29 : ∀ n : Fin 50, densSupG (n.val + 33950) < 2 ^ 1771 := by decide
private theorem cs_w30 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34000)) (centF (n.val + 34000)) = true := by decide
private theorem cl_w30 : ∀ n : Fin 50, centF (n.val + 34000) < 23 := by decide
private theorem bd_w30 : ∀ n : Fin 50, densSupG (n.val + 34000) < 2 ^ 1771 := by decide
private theorem cs_w31 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34050)) (centF (n.val + 34050)) = true := by decide
private theorem cl_w31 : ∀ n : Fin 50, centF (n.val + 34050) < 23 := by decide
private theorem bd_w31 : ∀ n : Fin 50, densSupG (n.val + 34050) < 2 ^ 1771 := by decide
private theorem cs_w32 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34100)) (centF (n.val + 34100)) = true := by decide
private theorem cl_w32 : ∀ n : Fin 50, centF (n.val + 34100) < 23 := by decide
private theorem bd_w32 : ∀ n : Fin 50, densSupG (n.val + 34100) < 2 ^ 1771 := by decide
private theorem cs_w33 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34150)) (centF (n.val + 34150)) = true := by decide
private theorem cl_w33 : ∀ n : Fin 50, centF (n.val + 34150) < 23 := by decide
private theorem bd_w33 : ∀ n : Fin 50, densSupG (n.val + 34150) < 2 ^ 1771 := by decide
private theorem cs_w34 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34200)) (centF (n.val + 34200)) = true := by decide
private theorem cl_w34 : ∀ n : Fin 50, centF (n.val + 34200) < 23 := by decide
private theorem bd_w34 : ∀ n : Fin 50, densSupG (n.val + 34200) < 2 ^ 1771 := by decide
private theorem cs_w35 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34250)) (centF (n.val + 34250)) = true := by decide
private theorem cl_w35 : ∀ n : Fin 50, centF (n.val + 34250) < 23 := by decide
private theorem bd_w35 : ∀ n : Fin 50, densSupG (n.val + 34250) < 2 ^ 1771 := by decide
private theorem cs_w36 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34300)) (centF (n.val + 34300)) = true := by decide
private theorem cl_w36 : ∀ n : Fin 50, centF (n.val + 34300) < 23 := by decide
private theorem bd_w36 : ∀ n : Fin 50, densSupG (n.val + 34300) < 2 ^ 1771 := by decide
private theorem cs_w37 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34350)) (centF (n.val + 34350)) = true := by decide
private theorem cl_w37 : ∀ n : Fin 50, centF (n.val + 34350) < 23 := by decide
private theorem bd_w37 : ∀ n : Fin 50, densSupG (n.val + 34350) < 2 ^ 1771 := by decide
private theorem cs_w38 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34400)) (centF (n.val + 34400)) = true := by decide
private theorem cl_w38 : ∀ n : Fin 50, centF (n.val + 34400) < 23 := by decide
private theorem bd_w38 : ∀ n : Fin 50, densSupG (n.val + 34400) < 2 ^ 1771 := by decide
private theorem cs_w39 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34450)) (centF (n.val + 34450)) = true := by decide
private theorem cl_w39 : ∀ n : Fin 50, centF (n.val + 34450) < 23 := by decide
private theorem bd_w39 : ∀ n : Fin 50, densSupG (n.val + 34450) < 2 ^ 1771 := by decide
private theorem cs_w40 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34500)) (centF (n.val + 34500)) = true := by decide
private theorem cl_w40 : ∀ n : Fin 50, centF (n.val + 34500) < 23 := by decide
private theorem bd_w40 : ∀ n : Fin 50, densSupG (n.val + 34500) < 2 ^ 1771 := by decide
private theorem cs_w41 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34550)) (centF (n.val + 34550)) = true := by decide
private theorem cl_w41 : ∀ n : Fin 50, centF (n.val + 34550) < 23 := by decide
private theorem bd_w41 : ∀ n : Fin 50, densSupG (n.val + 34550) < 2 ^ 1771 := by decide
private theorem cs_w42 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34600)) (centF (n.val + 34600)) = true := by decide
private theorem cl_w42 : ∀ n : Fin 50, centF (n.val + 34600) < 23 := by decide
private theorem bd_w42 : ∀ n : Fin 50, densSupG (n.val + 34600) < 2 ^ 1771 := by decide
private theorem cs_w43 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34650)) (centF (n.val + 34650)) = true := by decide
private theorem cl_w43 : ∀ n : Fin 50, centF (n.val + 34650) < 23 := by decide
private theorem bd_w43 : ∀ n : Fin 50, densSupG (n.val + 34650) < 2 ^ 1771 := by decide
private theorem cs_w44 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34700)) (centF (n.val + 34700)) = true := by decide
private theorem cl_w44 : ∀ n : Fin 50, centF (n.val + 34700) < 23 := by decide
private theorem bd_w44 : ∀ n : Fin 50, densSupG (n.val + 34700) < 2 ^ 1771 := by decide
private theorem cs_w45 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34750)) (centF (n.val + 34750)) = true := by decide
private theorem cl_w45 : ∀ n : Fin 50, centF (n.val + 34750) < 23 := by decide
private theorem bd_w45 : ∀ n : Fin 50, densSupG (n.val + 34750) < 2 ^ 1771 := by decide
private theorem cs_w46 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34800)) (centF (n.val + 34800)) = true := by decide
private theorem cl_w46 : ∀ n : Fin 50, centF (n.val + 34800) < 23 := by decide
private theorem bd_w46 : ∀ n : Fin 50, densSupG (n.val + 34800) < 2 ^ 1771 := by decide
private theorem cs_w47 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34850)) (centF (n.val + 34850)) = true := by decide
private theorem cl_w47 : ∀ n : Fin 50, centF (n.val + 34850) < 23 := by decide
private theorem bd_w47 : ∀ n : Fin 50, densSupG (n.val + 34850) < 2 ^ 1771 := by decide
private theorem cs_w48 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34900)) (centF (n.val + 34900)) = true := by decide
private theorem cl_w48 : ∀ n : Fin 50, centF (n.val + 34900) < 23 := by decide
private theorem bd_w48 : ∀ n : Fin 50, densSupG (n.val + 34900) < 2 ^ 1771 := by decide
private theorem cs_w49 : ∀ n : Fin 50, centredStar (densSupG (n.val + 34950)) (centF (n.val + 34950)) = true := by decide
private theorem cl_w49 : ∀ n : Fin 50, centF (n.val + 34950) < 23 := by decide
private theorem bd_w49 : ∀ n : Fin 50, densSupG (n.val + 34950) < 2 ^ 1771 := by decide
theorem centredStar_range : ∀ n, 32500 ≤ n → n < 35000 → centredStar (densSupG n) (centF n) = true := by
  intro n hlo hhi
  by_cases h0 : n < 32550
  · have hr : n - 32500 < 50 := by omega
    have heq : n = (n - 32500) + 32500 := by omega
    rw [heq]
    exact cs_w0 ⟨n - 32500, hr⟩
  ·
    by_cases h1 : n < 32600
    ·
      have hr : n - 32550 < 50 := by omega
      have heq : n = (n - 32550) + 32550 := by omega
      rw [heq]
      exact cs_w1 ⟨n - 32550, hr⟩
    ·
      by_cases h2 : n < 32650
      ·
        have hr : n - 32600 < 50 := by omega
        have heq : n = (n - 32600) + 32600 := by omega
        rw [heq]
        exact cs_w2 ⟨n - 32600, hr⟩
      ·
        by_cases h3 : n < 32700
        ·
          have hr : n - 32650 < 50 := by omega
          have heq : n = (n - 32650) + 32650 := by omega
          rw [heq]
          exact cs_w3 ⟨n - 32650, hr⟩
        ·
          by_cases h4 : n < 32750
          ·
            have hr : n - 32700 < 50 := by omega
            have heq : n = (n - 32700) + 32700 := by omega
            rw [heq]
            exact cs_w4 ⟨n - 32700, hr⟩
          ·
            by_cases h5 : n < 32800
            ·
              have hr : n - 32750 < 50 := by omega
              have heq : n = (n - 32750) + 32750 := by omega
              rw [heq]
              exact cs_w5 ⟨n - 32750, hr⟩
            ·
              by_cases h6 : n < 32850
              ·
                have hr : n - 32800 < 50 := by omega
                have heq : n = (n - 32800) + 32800 := by omega
                rw [heq]
                exact cs_w6 ⟨n - 32800, hr⟩
              ·
                by_cases h7 : n < 32900
                ·
                  have hr : n - 32850 < 50 := by omega
                  have heq : n = (n - 32850) + 32850 := by omega
                  rw [heq]
                  exact cs_w7 ⟨n - 32850, hr⟩
                ·
                  by_cases h8 : n < 32950
                  ·
                    have hr : n - 32900 < 50 := by omega
                    have heq : n = (n - 32900) + 32900 := by omega
                    rw [heq]
                    exact cs_w8 ⟨n - 32900, hr⟩
                  ·
                    by_cases h9 : n < 33000
                    ·
                      have hr : n - 32950 < 50 := by omega
                      have heq : n = (n - 32950) + 32950 := by omega
                      rw [heq]
                      exact cs_w9 ⟨n - 32950, hr⟩
                    ·
                      by_cases h10 : n < 33050
                      ·
                        have hr : n - 33000 < 50 := by omega
                        have heq : n = (n - 33000) + 33000 := by omega
                        rw [heq]
                        exact cs_w10 ⟨n - 33000, hr⟩
                      ·
                        by_cases h11 : n < 33100
                        ·
                          have hr : n - 33050 < 50 := by omega
                          have heq : n = (n - 33050) + 33050 := by omega
                          rw [heq]
                          exact cs_w11 ⟨n - 33050, hr⟩
                        ·
                          by_cases h12 : n < 33150
                          ·
                            have hr : n - 33100 < 50 := by omega
                            have heq : n = (n - 33100) + 33100 := by omega
                            rw [heq]
                            exact cs_w12 ⟨n - 33100, hr⟩
                          ·
                            by_cases h13 : n < 33200
                            ·
                              have hr : n - 33150 < 50 := by omega
                              have heq : n = (n - 33150) + 33150 := by omega
                              rw [heq]
                              exact cs_w13 ⟨n - 33150, hr⟩
                            ·
                              by_cases h14 : n < 33250
                              ·
                                have hr : n - 33200 < 50 := by omega
                                have heq : n = (n - 33200) + 33200 := by omega
                                rw [heq]
                                exact cs_w14 ⟨n - 33200, hr⟩
                              ·
                                by_cases h15 : n < 33300
                                ·
                                  have hr : n - 33250 < 50 := by omega
                                  have heq : n = (n - 33250) + 33250 := by omega
                                  rw [heq]
                                  exact cs_w15 ⟨n - 33250, hr⟩
                                ·
                                  by_cases h16 : n < 33350
                                  ·
                                    have hr : n - 33300 < 50 := by omega
                                    have heq : n = (n - 33300) + 33300 := by omega
                                    rw [heq]
                                    exact cs_w16 ⟨n - 33300, hr⟩
                                  ·
                                    by_cases h17 : n < 33400
                                    ·
                                      have hr : n - 33350 < 50 := by omega
                                      have heq : n = (n - 33350) + 33350 := by omega
                                      rw [heq]
                                      exact cs_w17 ⟨n - 33350, hr⟩
                                    ·
                                      by_cases h18 : n < 33450
                                      ·
                                        have hr : n - 33400 < 50 := by omega
                                        have heq : n = (n - 33400) + 33400 := by omega
                                        rw [heq]
                                        exact cs_w18 ⟨n - 33400, hr⟩
                                      ·
                                        by_cases h19 : n < 33500
                                        ·
                                          have hr : n - 33450 < 50 := by omega
                                          have heq : n = (n - 33450) + 33450 := by omega
                                          rw [heq]
                                          exact cs_w19 ⟨n - 33450, hr⟩
                                        ·
                                          by_cases h20 : n < 33550
                                          ·
                                            have hr : n - 33500 < 50 := by omega
                                            have heq : n = (n - 33500) + 33500 := by omega
                                            rw [heq]
                                            exact cs_w20 ⟨n - 33500, hr⟩
                                          ·
                                            by_cases h21 : n < 33600
                                            ·
                                              have hr : n - 33550 < 50 := by omega
                                              have heq : n = (n - 33550) + 33550 := by omega
                                              rw [heq]
                                              exact cs_w21 ⟨n - 33550, hr⟩
                                            ·
                                              by_cases h22 : n < 33650
                                              ·
                                                have hr : n - 33600 < 50 := by omega
                                                have heq : n = (n - 33600) + 33600 := by omega
                                                rw [heq]
                                                exact cs_w22 ⟨n - 33600, hr⟩
                                              ·
                                                by_cases h23 : n < 33700
                                                ·
                                                  have hr : n - 33650 < 50 := by omega
                                                  have heq : n = (n - 33650) + 33650 := by omega
                                                  rw [heq]
                                                  exact cs_w23 ⟨n - 33650, hr⟩
                                                ·
                                                  by_cases h24 : n < 33750
                                                  ·
                                                    have hr : n - 33700 < 50 := by omega
                                                    have heq : n = (n - 33700) + 33700 := by omega
                                                    rw [heq]
                                                    exact cs_w24 ⟨n - 33700, hr⟩
                                                  ·
                                                    by_cases h25 : n < 33800
                                                    ·
                                                      have hr : n - 33750 < 50 := by omega
                                                      have heq : n = (n - 33750) + 33750 := by omega
                                                      rw [heq]
                                                      exact cs_w25 ⟨n - 33750, hr⟩
                                                    ·
                                                      by_cases h26 : n < 33850
                                                      ·
                                                        have hr : n - 33800 < 50 := by omega
                                                        have heq : n = (n - 33800) + 33800 := by omega
                                                        rw [heq]
                                                        exact cs_w26 ⟨n - 33800, hr⟩
                                                      ·
                                                        by_cases h27 : n < 33900
                                                        ·
                                                          have hr : n - 33850 < 50 := by omega
                                                          have heq : n = (n - 33850) + 33850 := by omega
                                                          rw [heq]
                                                          exact cs_w27 ⟨n - 33850, hr⟩
                                                        ·
                                                          by_cases h28 : n < 33950
                                                          ·
                                                            have hr : n - 33900 < 50 := by omega
                                                            have heq : n = (n - 33900) + 33900 := by omega
                                                            rw [heq]
                                                            exact cs_w28 ⟨n - 33900, hr⟩
                                                          ·
                                                            by_cases h29 : n < 34000
                                                            ·
                                                              have hr : n - 33950 < 50 := by omega
                                                              have heq : n = (n - 33950) + 33950 := by omega
                                                              rw [heq]
                                                              exact cs_w29 ⟨n - 33950, hr⟩
                                                            ·
                                                              by_cases h30 : n < 34050
                                                              ·
                                                                have hr : n - 34000 < 50 := by omega
                                                                have heq : n = (n - 34000) + 34000 := by omega
                                                                rw [heq]
                                                                exact cs_w30 ⟨n - 34000, hr⟩
                                                              ·
                                                                by_cases h31 : n < 34100
                                                                ·
                                                                  have hr : n - 34050 < 50 := by omega
                                                                  have heq : n = (n - 34050) + 34050 := by omega
                                                                  rw [heq]
                                                                  exact cs_w31 ⟨n - 34050, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 34150
                                                                  ·
                                                                    have hr : n - 34100 < 50 := by omega
                                                                    have heq : n = (n - 34100) + 34100 := by omega
                                                                    rw [heq]
                                                                    exact cs_w32 ⟨n - 34100, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 34200
                                                                    ·
                                                                      have hr : n - 34150 < 50 := by omega
                                                                      have heq : n = (n - 34150) + 34150 := by omega
                                                                      rw [heq]
                                                                      exact cs_w33 ⟨n - 34150, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 34250
                                                                      ·
                                                                        have hr : n - 34200 < 50 := by omega
                                                                        have heq : n = (n - 34200) + 34200 := by omega
                                                                        rw [heq]
                                                                        exact cs_w34 ⟨n - 34200, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 34300
                                                                        ·
                                                                          have hr : n - 34250 < 50 := by omega
                                                                          have heq : n = (n - 34250) + 34250 := by omega
                                                                          rw [heq]
                                                                          exact cs_w35 ⟨n - 34250, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 34350
                                                                          ·
                                                                            have hr : n - 34300 < 50 := by omega
                                                                            have heq : n = (n - 34300) + 34300 := by omega
                                                                            rw [heq]
                                                                            exact cs_w36 ⟨n - 34300, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 34400
                                                                            ·
                                                                              have hr : n - 34350 < 50 := by omega
                                                                              have heq : n = (n - 34350) + 34350 := by omega
                                                                              rw [heq]
                                                                              exact cs_w37 ⟨n - 34350, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 34450
                                                                              ·
                                                                                have hr : n - 34400 < 50 := by omega
                                                                                have heq : n = (n - 34400) + 34400 := by omega
                                                                                rw [heq]
                                                                                exact cs_w38 ⟨n - 34400, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 34500
                                                                                ·
                                                                                  have hr : n - 34450 < 50 := by omega
                                                                                  have heq : n = (n - 34450) + 34450 := by omega
                                                                                  rw [heq]
                                                                                  exact cs_w39 ⟨n - 34450, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 34550
                                                                                  ·
                                                                                    have hr : n - 34500 < 50 := by omega
                                                                                    have heq : n = (n - 34500) + 34500 := by omega
                                                                                    rw [heq]
                                                                                    exact cs_w40 ⟨n - 34500, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 34600
                                                                                    ·
                                                                                      have hr : n - 34550 < 50 := by omega
                                                                                      have heq : n = (n - 34550) + 34550 := by omega
                                                                                      rw [heq]
                                                                                      exact cs_w41 ⟨n - 34550, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 34650
                                                                                      ·
                                                                                        have hr : n - 34600 < 50 := by omega
                                                                                        have heq : n = (n - 34600) + 34600 := by omega
                                                                                        rw [heq]
                                                                                        exact cs_w42 ⟨n - 34600, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 34700
                                                                                        ·
                                                                                          have hr : n - 34650 < 50 := by omega
                                                                                          have heq : n = (n - 34650) + 34650 := by omega
                                                                                          rw [heq]
                                                                                          exact cs_w43 ⟨n - 34650, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 34750
                                                                                          ·
                                                                                            have hr : n - 34700 < 50 := by omega
                                                                                            have heq : n = (n - 34700) + 34700 := by omega
                                                                                            rw [heq]
                                                                                            exact cs_w44 ⟨n - 34700, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 34800
                                                                                            ·
                                                                                              have hr : n - 34750 < 50 := by omega
                                                                                              have heq : n = (n - 34750) + 34750 := by omega
                                                                                              rw [heq]
                                                                                              exact cs_w45 ⟨n - 34750, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 34850
                                                                                              ·
                                                                                                have hr : n - 34800 < 50 := by omega
                                                                                                have heq : n = (n - 34800) + 34800 := by omega
                                                                                                rw [heq]
                                                                                                exact cs_w46 ⟨n - 34800, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 34900
                                                                                                ·
                                                                                                  have hr : n - 34850 < 50 := by omega
                                                                                                  have heq : n = (n - 34850) + 34850 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cs_w47 ⟨n - 34850, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 34950
                                                                                                  ·
                                                                                                    have hr : n - 34900 < 50 := by omega
                                                                                                    have heq : n = (n - 34900) + 34900 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w48 ⟨n - 34900, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 34950 < 50 := by omega
                                                                                                    have heq : n = (n - 34950) + 34950 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w49 ⟨n - 34950, hr⟩


theorem centF_lt_range : ∀ n, 32500 ≤ n → n < 35000 → centF n < 23 := by
  intro n hlo hhi
  by_cases h0 : n < 32550
  · have hr : n - 32500 < 50 := by omega
    have heq : n = (n - 32500) + 32500 := by omega
    rw [heq]
    exact cl_w0 ⟨n - 32500, hr⟩
  ·
    by_cases h1 : n < 32600
    ·
      have hr : n - 32550 < 50 := by omega
      have heq : n = (n - 32550) + 32550 := by omega
      rw [heq]
      exact cl_w1 ⟨n - 32550, hr⟩
    ·
      by_cases h2 : n < 32650
      ·
        have hr : n - 32600 < 50 := by omega
        have heq : n = (n - 32600) + 32600 := by omega
        rw [heq]
        exact cl_w2 ⟨n - 32600, hr⟩
      ·
        by_cases h3 : n < 32700
        ·
          have hr : n - 32650 < 50 := by omega
          have heq : n = (n - 32650) + 32650 := by omega
          rw [heq]
          exact cl_w3 ⟨n - 32650, hr⟩
        ·
          by_cases h4 : n < 32750
          ·
            have hr : n - 32700 < 50 := by omega
            have heq : n = (n - 32700) + 32700 := by omega
            rw [heq]
            exact cl_w4 ⟨n - 32700, hr⟩
          ·
            by_cases h5 : n < 32800
            ·
              have hr : n - 32750 < 50 := by omega
              have heq : n = (n - 32750) + 32750 := by omega
              rw [heq]
              exact cl_w5 ⟨n - 32750, hr⟩
            ·
              by_cases h6 : n < 32850
              ·
                have hr : n - 32800 < 50 := by omega
                have heq : n = (n - 32800) + 32800 := by omega
                rw [heq]
                exact cl_w6 ⟨n - 32800, hr⟩
              ·
                by_cases h7 : n < 32900
                ·
                  have hr : n - 32850 < 50 := by omega
                  have heq : n = (n - 32850) + 32850 := by omega
                  rw [heq]
                  exact cl_w7 ⟨n - 32850, hr⟩
                ·
                  by_cases h8 : n < 32950
                  ·
                    have hr : n - 32900 < 50 := by omega
                    have heq : n = (n - 32900) + 32900 := by omega
                    rw [heq]
                    exact cl_w8 ⟨n - 32900, hr⟩
                  ·
                    by_cases h9 : n < 33000
                    ·
                      have hr : n - 32950 < 50 := by omega
                      have heq : n = (n - 32950) + 32950 := by omega
                      rw [heq]
                      exact cl_w9 ⟨n - 32950, hr⟩
                    ·
                      by_cases h10 : n < 33050
                      ·
                        have hr : n - 33000 < 50 := by omega
                        have heq : n = (n - 33000) + 33000 := by omega
                        rw [heq]
                        exact cl_w10 ⟨n - 33000, hr⟩
                      ·
                        by_cases h11 : n < 33100
                        ·
                          have hr : n - 33050 < 50 := by omega
                          have heq : n = (n - 33050) + 33050 := by omega
                          rw [heq]
                          exact cl_w11 ⟨n - 33050, hr⟩
                        ·
                          by_cases h12 : n < 33150
                          ·
                            have hr : n - 33100 < 50 := by omega
                            have heq : n = (n - 33100) + 33100 := by omega
                            rw [heq]
                            exact cl_w12 ⟨n - 33100, hr⟩
                          ·
                            by_cases h13 : n < 33200
                            ·
                              have hr : n - 33150 < 50 := by omega
                              have heq : n = (n - 33150) + 33150 := by omega
                              rw [heq]
                              exact cl_w13 ⟨n - 33150, hr⟩
                            ·
                              by_cases h14 : n < 33250
                              ·
                                have hr : n - 33200 < 50 := by omega
                                have heq : n = (n - 33200) + 33200 := by omega
                                rw [heq]
                                exact cl_w14 ⟨n - 33200, hr⟩
                              ·
                                by_cases h15 : n < 33300
                                ·
                                  have hr : n - 33250 < 50 := by omega
                                  have heq : n = (n - 33250) + 33250 := by omega
                                  rw [heq]
                                  exact cl_w15 ⟨n - 33250, hr⟩
                                ·
                                  by_cases h16 : n < 33350
                                  ·
                                    have hr : n - 33300 < 50 := by omega
                                    have heq : n = (n - 33300) + 33300 := by omega
                                    rw [heq]
                                    exact cl_w16 ⟨n - 33300, hr⟩
                                  ·
                                    by_cases h17 : n < 33400
                                    ·
                                      have hr : n - 33350 < 50 := by omega
                                      have heq : n = (n - 33350) + 33350 := by omega
                                      rw [heq]
                                      exact cl_w17 ⟨n - 33350, hr⟩
                                    ·
                                      by_cases h18 : n < 33450
                                      ·
                                        have hr : n - 33400 < 50 := by omega
                                        have heq : n = (n - 33400) + 33400 := by omega
                                        rw [heq]
                                        exact cl_w18 ⟨n - 33400, hr⟩
                                      ·
                                        by_cases h19 : n < 33500
                                        ·
                                          have hr : n - 33450 < 50 := by omega
                                          have heq : n = (n - 33450) + 33450 := by omega
                                          rw [heq]
                                          exact cl_w19 ⟨n - 33450, hr⟩
                                        ·
                                          by_cases h20 : n < 33550
                                          ·
                                            have hr : n - 33500 < 50 := by omega
                                            have heq : n = (n - 33500) + 33500 := by omega
                                            rw [heq]
                                            exact cl_w20 ⟨n - 33500, hr⟩
                                          ·
                                            by_cases h21 : n < 33600
                                            ·
                                              have hr : n - 33550 < 50 := by omega
                                              have heq : n = (n - 33550) + 33550 := by omega
                                              rw [heq]
                                              exact cl_w21 ⟨n - 33550, hr⟩
                                            ·
                                              by_cases h22 : n < 33650
                                              ·
                                                have hr : n - 33600 < 50 := by omega
                                                have heq : n = (n - 33600) + 33600 := by omega
                                                rw [heq]
                                                exact cl_w22 ⟨n - 33600, hr⟩
                                              ·
                                                by_cases h23 : n < 33700
                                                ·
                                                  have hr : n - 33650 < 50 := by omega
                                                  have heq : n = (n - 33650) + 33650 := by omega
                                                  rw [heq]
                                                  exact cl_w23 ⟨n - 33650, hr⟩
                                                ·
                                                  by_cases h24 : n < 33750
                                                  ·
                                                    have hr : n - 33700 < 50 := by omega
                                                    have heq : n = (n - 33700) + 33700 := by omega
                                                    rw [heq]
                                                    exact cl_w24 ⟨n - 33700, hr⟩
                                                  ·
                                                    by_cases h25 : n < 33800
                                                    ·
                                                      have hr : n - 33750 < 50 := by omega
                                                      have heq : n = (n - 33750) + 33750 := by omega
                                                      rw [heq]
                                                      exact cl_w25 ⟨n - 33750, hr⟩
                                                    ·
                                                      by_cases h26 : n < 33850
                                                      ·
                                                        have hr : n - 33800 < 50 := by omega
                                                        have heq : n = (n - 33800) + 33800 := by omega
                                                        rw [heq]
                                                        exact cl_w26 ⟨n - 33800, hr⟩
                                                      ·
                                                        by_cases h27 : n < 33900
                                                        ·
                                                          have hr : n - 33850 < 50 := by omega
                                                          have heq : n = (n - 33850) + 33850 := by omega
                                                          rw [heq]
                                                          exact cl_w27 ⟨n - 33850, hr⟩
                                                        ·
                                                          by_cases h28 : n < 33950
                                                          ·
                                                            have hr : n - 33900 < 50 := by omega
                                                            have heq : n = (n - 33900) + 33900 := by omega
                                                            rw [heq]
                                                            exact cl_w28 ⟨n - 33900, hr⟩
                                                          ·
                                                            by_cases h29 : n < 34000
                                                            ·
                                                              have hr : n - 33950 < 50 := by omega
                                                              have heq : n = (n - 33950) + 33950 := by omega
                                                              rw [heq]
                                                              exact cl_w29 ⟨n - 33950, hr⟩
                                                            ·
                                                              by_cases h30 : n < 34050
                                                              ·
                                                                have hr : n - 34000 < 50 := by omega
                                                                have heq : n = (n - 34000) + 34000 := by omega
                                                                rw [heq]
                                                                exact cl_w30 ⟨n - 34000, hr⟩
                                                              ·
                                                                by_cases h31 : n < 34100
                                                                ·
                                                                  have hr : n - 34050 < 50 := by omega
                                                                  have heq : n = (n - 34050) + 34050 := by omega
                                                                  rw [heq]
                                                                  exact cl_w31 ⟨n - 34050, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 34150
                                                                  ·
                                                                    have hr : n - 34100 < 50 := by omega
                                                                    have heq : n = (n - 34100) + 34100 := by omega
                                                                    rw [heq]
                                                                    exact cl_w32 ⟨n - 34100, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 34200
                                                                    ·
                                                                      have hr : n - 34150 < 50 := by omega
                                                                      have heq : n = (n - 34150) + 34150 := by omega
                                                                      rw [heq]
                                                                      exact cl_w33 ⟨n - 34150, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 34250
                                                                      ·
                                                                        have hr : n - 34200 < 50 := by omega
                                                                        have heq : n = (n - 34200) + 34200 := by omega
                                                                        rw [heq]
                                                                        exact cl_w34 ⟨n - 34200, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 34300
                                                                        ·
                                                                          have hr : n - 34250 < 50 := by omega
                                                                          have heq : n = (n - 34250) + 34250 := by omega
                                                                          rw [heq]
                                                                          exact cl_w35 ⟨n - 34250, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 34350
                                                                          ·
                                                                            have hr : n - 34300 < 50 := by omega
                                                                            have heq : n = (n - 34300) + 34300 := by omega
                                                                            rw [heq]
                                                                            exact cl_w36 ⟨n - 34300, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 34400
                                                                            ·
                                                                              have hr : n - 34350 < 50 := by omega
                                                                              have heq : n = (n - 34350) + 34350 := by omega
                                                                              rw [heq]
                                                                              exact cl_w37 ⟨n - 34350, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 34450
                                                                              ·
                                                                                have hr : n - 34400 < 50 := by omega
                                                                                have heq : n = (n - 34400) + 34400 := by omega
                                                                                rw [heq]
                                                                                exact cl_w38 ⟨n - 34400, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 34500
                                                                                ·
                                                                                  have hr : n - 34450 < 50 := by omega
                                                                                  have heq : n = (n - 34450) + 34450 := by omega
                                                                                  rw [heq]
                                                                                  exact cl_w39 ⟨n - 34450, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 34550
                                                                                  ·
                                                                                    have hr : n - 34500 < 50 := by omega
                                                                                    have heq : n = (n - 34500) + 34500 := by omega
                                                                                    rw [heq]
                                                                                    exact cl_w40 ⟨n - 34500, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 34600
                                                                                    ·
                                                                                      have hr : n - 34550 < 50 := by omega
                                                                                      have heq : n = (n - 34550) + 34550 := by omega
                                                                                      rw [heq]
                                                                                      exact cl_w41 ⟨n - 34550, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 34650
                                                                                      ·
                                                                                        have hr : n - 34600 < 50 := by omega
                                                                                        have heq : n = (n - 34600) + 34600 := by omega
                                                                                        rw [heq]
                                                                                        exact cl_w42 ⟨n - 34600, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 34700
                                                                                        ·
                                                                                          have hr : n - 34650 < 50 := by omega
                                                                                          have heq : n = (n - 34650) + 34650 := by omega
                                                                                          rw [heq]
                                                                                          exact cl_w43 ⟨n - 34650, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 34750
                                                                                          ·
                                                                                            have hr : n - 34700 < 50 := by omega
                                                                                            have heq : n = (n - 34700) + 34700 := by omega
                                                                                            rw [heq]
                                                                                            exact cl_w44 ⟨n - 34700, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 34800
                                                                                            ·
                                                                                              have hr : n - 34750 < 50 := by omega
                                                                                              have heq : n = (n - 34750) + 34750 := by omega
                                                                                              rw [heq]
                                                                                              exact cl_w45 ⟨n - 34750, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 34850
                                                                                              ·
                                                                                                have hr : n - 34800 < 50 := by omega
                                                                                                have heq : n = (n - 34800) + 34800 := by omega
                                                                                                rw [heq]
                                                                                                exact cl_w46 ⟨n - 34800, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 34900
                                                                                                ·
                                                                                                  have hr : n - 34850 < 50 := by omega
                                                                                                  have heq : n = (n - 34850) + 34850 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cl_w47 ⟨n - 34850, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 34950
                                                                                                  ·
                                                                                                    have hr : n - 34900 < 50 := by omega
                                                                                                    have heq : n = (n - 34900) + 34900 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w48 ⟨n - 34900, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 34950 < 50 := by omega
                                                                                                    have heq : n = (n - 34950) + 34950 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w49 ⟨n - 34950, hr⟩


theorem densSupG_lt_range : ∀ n, 32500 ≤ n → n < 35000 → densSupG n < 2 ^ 1771 := by
  intro n hlo hhi
  by_cases h0 : n < 32550
  · have hr : n - 32500 < 50 := by omega
    have heq : n = (n - 32500) + 32500 := by omega
    rw [heq]
    exact bd_w0 ⟨n - 32500, hr⟩
  ·
    by_cases h1 : n < 32600
    ·
      have hr : n - 32550 < 50 := by omega
      have heq : n = (n - 32550) + 32550 := by omega
      rw [heq]
      exact bd_w1 ⟨n - 32550, hr⟩
    ·
      by_cases h2 : n < 32650
      ·
        have hr : n - 32600 < 50 := by omega
        have heq : n = (n - 32600) + 32600 := by omega
        rw [heq]
        exact bd_w2 ⟨n - 32600, hr⟩
      ·
        by_cases h3 : n < 32700
        ·
          have hr : n - 32650 < 50 := by omega
          have heq : n = (n - 32650) + 32650 := by omega
          rw [heq]
          exact bd_w3 ⟨n - 32650, hr⟩
        ·
          by_cases h4 : n < 32750
          ·
            have hr : n - 32700 < 50 := by omega
            have heq : n = (n - 32700) + 32700 := by omega
            rw [heq]
            exact bd_w4 ⟨n - 32700, hr⟩
          ·
            by_cases h5 : n < 32800
            ·
              have hr : n - 32750 < 50 := by omega
              have heq : n = (n - 32750) + 32750 := by omega
              rw [heq]
              exact bd_w5 ⟨n - 32750, hr⟩
            ·
              by_cases h6 : n < 32850
              ·
                have hr : n - 32800 < 50 := by omega
                have heq : n = (n - 32800) + 32800 := by omega
                rw [heq]
                exact bd_w6 ⟨n - 32800, hr⟩
              ·
                by_cases h7 : n < 32900
                ·
                  have hr : n - 32850 < 50 := by omega
                  have heq : n = (n - 32850) + 32850 := by omega
                  rw [heq]
                  exact bd_w7 ⟨n - 32850, hr⟩
                ·
                  by_cases h8 : n < 32950
                  ·
                    have hr : n - 32900 < 50 := by omega
                    have heq : n = (n - 32900) + 32900 := by omega
                    rw [heq]
                    exact bd_w8 ⟨n - 32900, hr⟩
                  ·
                    by_cases h9 : n < 33000
                    ·
                      have hr : n - 32950 < 50 := by omega
                      have heq : n = (n - 32950) + 32950 := by omega
                      rw [heq]
                      exact bd_w9 ⟨n - 32950, hr⟩
                    ·
                      by_cases h10 : n < 33050
                      ·
                        have hr : n - 33000 < 50 := by omega
                        have heq : n = (n - 33000) + 33000 := by omega
                        rw [heq]
                        exact bd_w10 ⟨n - 33000, hr⟩
                      ·
                        by_cases h11 : n < 33100
                        ·
                          have hr : n - 33050 < 50 := by omega
                          have heq : n = (n - 33050) + 33050 := by omega
                          rw [heq]
                          exact bd_w11 ⟨n - 33050, hr⟩
                        ·
                          by_cases h12 : n < 33150
                          ·
                            have hr : n - 33100 < 50 := by omega
                            have heq : n = (n - 33100) + 33100 := by omega
                            rw [heq]
                            exact bd_w12 ⟨n - 33100, hr⟩
                          ·
                            by_cases h13 : n < 33200
                            ·
                              have hr : n - 33150 < 50 := by omega
                              have heq : n = (n - 33150) + 33150 := by omega
                              rw [heq]
                              exact bd_w13 ⟨n - 33150, hr⟩
                            ·
                              by_cases h14 : n < 33250
                              ·
                                have hr : n - 33200 < 50 := by omega
                                have heq : n = (n - 33200) + 33200 := by omega
                                rw [heq]
                                exact bd_w14 ⟨n - 33200, hr⟩
                              ·
                                by_cases h15 : n < 33300
                                ·
                                  have hr : n - 33250 < 50 := by omega
                                  have heq : n = (n - 33250) + 33250 := by omega
                                  rw [heq]
                                  exact bd_w15 ⟨n - 33250, hr⟩
                                ·
                                  by_cases h16 : n < 33350
                                  ·
                                    have hr : n - 33300 < 50 := by omega
                                    have heq : n = (n - 33300) + 33300 := by omega
                                    rw [heq]
                                    exact bd_w16 ⟨n - 33300, hr⟩
                                  ·
                                    by_cases h17 : n < 33400
                                    ·
                                      have hr : n - 33350 < 50 := by omega
                                      have heq : n = (n - 33350) + 33350 := by omega
                                      rw [heq]
                                      exact bd_w17 ⟨n - 33350, hr⟩
                                    ·
                                      by_cases h18 : n < 33450
                                      ·
                                        have hr : n - 33400 < 50 := by omega
                                        have heq : n = (n - 33400) + 33400 := by omega
                                        rw [heq]
                                        exact bd_w18 ⟨n - 33400, hr⟩
                                      ·
                                        by_cases h19 : n < 33500
                                        ·
                                          have hr : n - 33450 < 50 := by omega
                                          have heq : n = (n - 33450) + 33450 := by omega
                                          rw [heq]
                                          exact bd_w19 ⟨n - 33450, hr⟩
                                        ·
                                          by_cases h20 : n < 33550
                                          ·
                                            have hr : n - 33500 < 50 := by omega
                                            have heq : n = (n - 33500) + 33500 := by omega
                                            rw [heq]
                                            exact bd_w20 ⟨n - 33500, hr⟩
                                          ·
                                            by_cases h21 : n < 33600
                                            ·
                                              have hr : n - 33550 < 50 := by omega
                                              have heq : n = (n - 33550) + 33550 := by omega
                                              rw [heq]
                                              exact bd_w21 ⟨n - 33550, hr⟩
                                            ·
                                              by_cases h22 : n < 33650
                                              ·
                                                have hr : n - 33600 < 50 := by omega
                                                have heq : n = (n - 33600) + 33600 := by omega
                                                rw [heq]
                                                exact bd_w22 ⟨n - 33600, hr⟩
                                              ·
                                                by_cases h23 : n < 33700
                                                ·
                                                  have hr : n - 33650 < 50 := by omega
                                                  have heq : n = (n - 33650) + 33650 := by omega
                                                  rw [heq]
                                                  exact bd_w23 ⟨n - 33650, hr⟩
                                                ·
                                                  by_cases h24 : n < 33750
                                                  ·
                                                    have hr : n - 33700 < 50 := by omega
                                                    have heq : n = (n - 33700) + 33700 := by omega
                                                    rw [heq]
                                                    exact bd_w24 ⟨n - 33700, hr⟩
                                                  ·
                                                    by_cases h25 : n < 33800
                                                    ·
                                                      have hr : n - 33750 < 50 := by omega
                                                      have heq : n = (n - 33750) + 33750 := by omega
                                                      rw [heq]
                                                      exact bd_w25 ⟨n - 33750, hr⟩
                                                    ·
                                                      by_cases h26 : n < 33850
                                                      ·
                                                        have hr : n - 33800 < 50 := by omega
                                                        have heq : n = (n - 33800) + 33800 := by omega
                                                        rw [heq]
                                                        exact bd_w26 ⟨n - 33800, hr⟩
                                                      ·
                                                        by_cases h27 : n < 33900
                                                        ·
                                                          have hr : n - 33850 < 50 := by omega
                                                          have heq : n = (n - 33850) + 33850 := by omega
                                                          rw [heq]
                                                          exact bd_w27 ⟨n - 33850, hr⟩
                                                        ·
                                                          by_cases h28 : n < 33950
                                                          ·
                                                            have hr : n - 33900 < 50 := by omega
                                                            have heq : n = (n - 33900) + 33900 := by omega
                                                            rw [heq]
                                                            exact bd_w28 ⟨n - 33900, hr⟩
                                                          ·
                                                            by_cases h29 : n < 34000
                                                            ·
                                                              have hr : n - 33950 < 50 := by omega
                                                              have heq : n = (n - 33950) + 33950 := by omega
                                                              rw [heq]
                                                              exact bd_w29 ⟨n - 33950, hr⟩
                                                            ·
                                                              by_cases h30 : n < 34050
                                                              ·
                                                                have hr : n - 34000 < 50 := by omega
                                                                have heq : n = (n - 34000) + 34000 := by omega
                                                                rw [heq]
                                                                exact bd_w30 ⟨n - 34000, hr⟩
                                                              ·
                                                                by_cases h31 : n < 34100
                                                                ·
                                                                  have hr : n - 34050 < 50 := by omega
                                                                  have heq : n = (n - 34050) + 34050 := by omega
                                                                  rw [heq]
                                                                  exact bd_w31 ⟨n - 34050, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 34150
                                                                  ·
                                                                    have hr : n - 34100 < 50 := by omega
                                                                    have heq : n = (n - 34100) + 34100 := by omega
                                                                    rw [heq]
                                                                    exact bd_w32 ⟨n - 34100, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 34200
                                                                    ·
                                                                      have hr : n - 34150 < 50 := by omega
                                                                      have heq : n = (n - 34150) + 34150 := by omega
                                                                      rw [heq]
                                                                      exact bd_w33 ⟨n - 34150, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 34250
                                                                      ·
                                                                        have hr : n - 34200 < 50 := by omega
                                                                        have heq : n = (n - 34200) + 34200 := by omega
                                                                        rw [heq]
                                                                        exact bd_w34 ⟨n - 34200, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 34300
                                                                        ·
                                                                          have hr : n - 34250 < 50 := by omega
                                                                          have heq : n = (n - 34250) + 34250 := by omega
                                                                          rw [heq]
                                                                          exact bd_w35 ⟨n - 34250, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 34350
                                                                          ·
                                                                            have hr : n - 34300 < 50 := by omega
                                                                            have heq : n = (n - 34300) + 34300 := by omega
                                                                            rw [heq]
                                                                            exact bd_w36 ⟨n - 34300, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 34400
                                                                            ·
                                                                              have hr : n - 34350 < 50 := by omega
                                                                              have heq : n = (n - 34350) + 34350 := by omega
                                                                              rw [heq]
                                                                              exact bd_w37 ⟨n - 34350, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 34450
                                                                              ·
                                                                                have hr : n - 34400 < 50 := by omega
                                                                                have heq : n = (n - 34400) + 34400 := by omega
                                                                                rw [heq]
                                                                                exact bd_w38 ⟨n - 34400, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 34500
                                                                                ·
                                                                                  have hr : n - 34450 < 50 := by omega
                                                                                  have heq : n = (n - 34450) + 34450 := by omega
                                                                                  rw [heq]
                                                                                  exact bd_w39 ⟨n - 34450, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 34550
                                                                                  ·
                                                                                    have hr : n - 34500 < 50 := by omega
                                                                                    have heq : n = (n - 34500) + 34500 := by omega
                                                                                    rw [heq]
                                                                                    exact bd_w40 ⟨n - 34500, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 34600
                                                                                    ·
                                                                                      have hr : n - 34550 < 50 := by omega
                                                                                      have heq : n = (n - 34550) + 34550 := by omega
                                                                                      rw [heq]
                                                                                      exact bd_w41 ⟨n - 34550, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 34650
                                                                                      ·
                                                                                        have hr : n - 34600 < 50 := by omega
                                                                                        have heq : n = (n - 34600) + 34600 := by omega
                                                                                        rw [heq]
                                                                                        exact bd_w42 ⟨n - 34600, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 34700
                                                                                        ·
                                                                                          have hr : n - 34650 < 50 := by omega
                                                                                          have heq : n = (n - 34650) + 34650 := by omega
                                                                                          rw [heq]
                                                                                          exact bd_w43 ⟨n - 34650, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 34750
                                                                                          ·
                                                                                            have hr : n - 34700 < 50 := by omega
                                                                                            have heq : n = (n - 34700) + 34700 := by omega
                                                                                            rw [heq]
                                                                                            exact bd_w44 ⟨n - 34700, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 34800
                                                                                            ·
                                                                                              have hr : n - 34750 < 50 := by omega
                                                                                              have heq : n = (n - 34750) + 34750 := by omega
                                                                                              rw [heq]
                                                                                              exact bd_w45 ⟨n - 34750, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 34850
                                                                                              ·
                                                                                                have hr : n - 34800 < 50 := by omega
                                                                                                have heq : n = (n - 34800) + 34800 := by omega
                                                                                                rw [heq]
                                                                                                exact bd_w46 ⟨n - 34800, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 34900
                                                                                                ·
                                                                                                  have hr : n - 34850 < 50 := by omega
                                                                                                  have heq : n = (n - 34850) + 34850 := by omega
                                                                                                  rw [heq]
                                                                                                  exact bd_w47 ⟨n - 34850, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 34950
                                                                                                  ·
                                                                                                    have hr : n - 34900 < 50 := by omega
                                                                                                    have heq : n = (n - 34900) + 34900 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w48 ⟨n - 34900, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 34950 < 50 := by omega
                                                                                                    have heq : n = (n - 34950) + 34950 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w49 ⟨n - 34950, hr⟩


end IntMul.Kappa.R8.Bit.Oppbank.CentBound6b


