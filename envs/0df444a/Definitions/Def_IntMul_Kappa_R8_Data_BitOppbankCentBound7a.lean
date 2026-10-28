-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound7a
-- name    : IntMul_Kappa_R8_Data_BitOppbankCentBound7a
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:04:08.752037+00:00
-- url     : https://prove2.me/theorems/0037b94b-be08-4789-8c99-ef27100b2d07
-- title:
--   HasCentre certificates dens nodes [35000,37500)
-- statement:
--   # Densified centre certificates, pack 7a
--
--   For every densified node index $n$ with $35000\le n<37500$,
--   $$
--   \mathrm{centredStar}(\mathrm{densSupG}\,n,\mathrm{centF}\,n)=\mathsf{true},\quad
--   \mathrm{centF}\,n<23,\quad
--   \mathrm{densSupG}\,n < 2^{1771}.
--   $$
--   Proved by decide on Fin 50 windows (no native_decide). Half-pack for 300s server budget.
-- source:
--   R8 BitOppbank AllDensCentred; jfstack_23 densified supports

-- CentBound pack 7a: densified HasCentre certificates on n ∈ [35000, 37500)
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

namespace IntMul.Kappa.R8.Bit.Oppbank.CentBound7a


private theorem cs_w0 : ∀ n : Fin 50, centredStar (densSupG (n.val + 35000)) (centF (n.val + 35000)) = true := by decide
private theorem cl_w0 : ∀ n : Fin 50, centF (n.val + 35000) < 23 := by decide
private theorem bd_w0 : ∀ n : Fin 50, densSupG (n.val + 35000) < 2 ^ 1771 := by decide
private theorem cs_w1 : ∀ n : Fin 50, centredStar (densSupG (n.val + 35050)) (centF (n.val + 35050)) = true := by decide
private theorem cl_w1 : ∀ n : Fin 50, centF (n.val + 35050) < 23 := by decide
private theorem bd_w1 : ∀ n : Fin 50, densSupG (n.val + 35050) < 2 ^ 1771 := by decide
private theorem cs_w2 : ∀ n : Fin 50, centredStar (densSupG (n.val + 35100)) (centF (n.val + 35100)) = true := by decide
private theorem cl_w2 : ∀ n : Fin 50, centF (n.val + 35100) < 23 := by decide
private theorem bd_w2 : ∀ n : Fin 50, densSupG (n.val + 35100) < 2 ^ 1771 := by decide
private theorem cs_w3 : ∀ n : Fin 50, centredStar (densSupG (n.val + 35150)) (centF (n.val + 35150)) = true := by decide
private theorem cl_w3 : ∀ n : Fin 50, centF (n.val + 35150) < 23 := by decide
private theorem bd_w3 : ∀ n : Fin 50, densSupG (n.val + 35150) < 2 ^ 1771 := by decide
private theorem cs_w4 : ∀ n : Fin 50, centredStar (densSupG (n.val + 35200)) (centF (n.val + 35200)) = true := by decide
private theorem cl_w4 : ∀ n : Fin 50, centF (n.val + 35200) < 23 := by decide
private theorem bd_w4 : ∀ n : Fin 50, densSupG (n.val + 35200) < 2 ^ 1771 := by decide
private theorem cs_w5 : ∀ n : Fin 50, centredStar (densSupG (n.val + 35250)) (centF (n.val + 35250)) = true := by decide
private theorem cl_w5 : ∀ n : Fin 50, centF (n.val + 35250) < 23 := by decide
private theorem bd_w5 : ∀ n : Fin 50, densSupG (n.val + 35250) < 2 ^ 1771 := by decide
private theorem cs_w6 : ∀ n : Fin 50, centredStar (densSupG (n.val + 35300)) (centF (n.val + 35300)) = true := by decide
private theorem cl_w6 : ∀ n : Fin 50, centF (n.val + 35300) < 23 := by decide
private theorem bd_w6 : ∀ n : Fin 50, densSupG (n.val + 35300) < 2 ^ 1771 := by decide
private theorem cs_w7 : ∀ n : Fin 50, centredStar (densSupG (n.val + 35350)) (centF (n.val + 35350)) = true := by decide
private theorem cl_w7 : ∀ n : Fin 50, centF (n.val + 35350) < 23 := by decide
private theorem bd_w7 : ∀ n : Fin 50, densSupG (n.val + 35350) < 2 ^ 1771 := by decide
private theorem cs_w8 : ∀ n : Fin 50, centredStar (densSupG (n.val + 35400)) (centF (n.val + 35400)) = true := by decide
private theorem cl_w8 : ∀ n : Fin 50, centF (n.val + 35400) < 23 := by decide
private theorem bd_w8 : ∀ n : Fin 50, densSupG (n.val + 35400) < 2 ^ 1771 := by decide
private theorem cs_w9 : ∀ n : Fin 50, centredStar (densSupG (n.val + 35450)) (centF (n.val + 35450)) = true := by decide
private theorem cl_w9 : ∀ n : Fin 50, centF (n.val + 35450) < 23 := by decide
private theorem bd_w9 : ∀ n : Fin 50, densSupG (n.val + 35450) < 2 ^ 1771 := by decide
private theorem cs_w10 : ∀ n : Fin 50, centredStar (densSupG (n.val + 35500)) (centF (n.val + 35500)) = true := by decide
private theorem cl_w10 : ∀ n : Fin 50, centF (n.val + 35500) < 23 := by decide
private theorem bd_w10 : ∀ n : Fin 50, densSupG (n.val + 35500) < 2 ^ 1771 := by decide
private theorem cs_w11 : ∀ n : Fin 50, centredStar (densSupG (n.val + 35550)) (centF (n.val + 35550)) = true := by decide
private theorem cl_w11 : ∀ n : Fin 50, centF (n.val + 35550) < 23 := by decide
private theorem bd_w11 : ∀ n : Fin 50, densSupG (n.val + 35550) < 2 ^ 1771 := by decide
private theorem cs_w12 : ∀ n : Fin 50, centredStar (densSupG (n.val + 35600)) (centF (n.val + 35600)) = true := by decide
private theorem cl_w12 : ∀ n : Fin 50, centF (n.val + 35600) < 23 := by decide
private theorem bd_w12 : ∀ n : Fin 50, densSupG (n.val + 35600) < 2 ^ 1771 := by decide
private theorem cs_w13 : ∀ n : Fin 50, centredStar (densSupG (n.val + 35650)) (centF (n.val + 35650)) = true := by decide
private theorem cl_w13 : ∀ n : Fin 50, centF (n.val + 35650) < 23 := by decide
private theorem bd_w13 : ∀ n : Fin 50, densSupG (n.val + 35650) < 2 ^ 1771 := by decide
private theorem cs_w14 : ∀ n : Fin 50, centredStar (densSupG (n.val + 35700)) (centF (n.val + 35700)) = true := by decide
private theorem cl_w14 : ∀ n : Fin 50, centF (n.val + 35700) < 23 := by decide
private theorem bd_w14 : ∀ n : Fin 50, densSupG (n.val + 35700) < 2 ^ 1771 := by decide
private theorem cs_w15 : ∀ n : Fin 50, centredStar (densSupG (n.val + 35750)) (centF (n.val + 35750)) = true := by decide
private theorem cl_w15 : ∀ n : Fin 50, centF (n.val + 35750) < 23 := by decide
private theorem bd_w15 : ∀ n : Fin 50, densSupG (n.val + 35750) < 2 ^ 1771 := by decide
private theorem cs_w16 : ∀ n : Fin 50, centredStar (densSupG (n.val + 35800)) (centF (n.val + 35800)) = true := by decide
private theorem cl_w16 : ∀ n : Fin 50, centF (n.val + 35800) < 23 := by decide
private theorem bd_w16 : ∀ n : Fin 50, densSupG (n.val + 35800) < 2 ^ 1771 := by decide
private theorem cs_w17 : ∀ n : Fin 50, centredStar (densSupG (n.val + 35850)) (centF (n.val + 35850)) = true := by decide
private theorem cl_w17 : ∀ n : Fin 50, centF (n.val + 35850) < 23 := by decide
private theorem bd_w17 : ∀ n : Fin 50, densSupG (n.val + 35850) < 2 ^ 1771 := by decide
private theorem cs_w18 : ∀ n : Fin 50, centredStar (densSupG (n.val + 35900)) (centF (n.val + 35900)) = true := by decide
private theorem cl_w18 : ∀ n : Fin 50, centF (n.val + 35900) < 23 := by decide
private theorem bd_w18 : ∀ n : Fin 50, densSupG (n.val + 35900) < 2 ^ 1771 := by decide
private theorem cs_w19 : ∀ n : Fin 50, centredStar (densSupG (n.val + 35950)) (centF (n.val + 35950)) = true := by decide
private theorem cl_w19 : ∀ n : Fin 50, centF (n.val + 35950) < 23 := by decide
private theorem bd_w19 : ∀ n : Fin 50, densSupG (n.val + 35950) < 2 ^ 1771 := by decide
private theorem cs_w20 : ∀ n : Fin 50, centredStar (densSupG (n.val + 36000)) (centF (n.val + 36000)) = true := by decide
private theorem cl_w20 : ∀ n : Fin 50, centF (n.val + 36000) < 23 := by decide
private theorem bd_w20 : ∀ n : Fin 50, densSupG (n.val + 36000) < 2 ^ 1771 := by decide
private theorem cs_w21 : ∀ n : Fin 50, centredStar (densSupG (n.val + 36050)) (centF (n.val + 36050)) = true := by decide
private theorem cl_w21 : ∀ n : Fin 50, centF (n.val + 36050) < 23 := by decide
private theorem bd_w21 : ∀ n : Fin 50, densSupG (n.val + 36050) < 2 ^ 1771 := by decide
private theorem cs_w22 : ∀ n : Fin 50, centredStar (densSupG (n.val + 36100)) (centF (n.val + 36100)) = true := by decide
private theorem cl_w22 : ∀ n : Fin 50, centF (n.val + 36100) < 23 := by decide
private theorem bd_w22 : ∀ n : Fin 50, densSupG (n.val + 36100) < 2 ^ 1771 := by decide
private theorem cs_w23 : ∀ n : Fin 50, centredStar (densSupG (n.val + 36150)) (centF (n.val + 36150)) = true := by decide
private theorem cl_w23 : ∀ n : Fin 50, centF (n.val + 36150) < 23 := by decide
private theorem bd_w23 : ∀ n : Fin 50, densSupG (n.val + 36150) < 2 ^ 1771 := by decide
private theorem cs_w24 : ∀ n : Fin 50, centredStar (densSupG (n.val + 36200)) (centF (n.val + 36200)) = true := by decide
private theorem cl_w24 : ∀ n : Fin 50, centF (n.val + 36200) < 23 := by decide
private theorem bd_w24 : ∀ n : Fin 50, densSupG (n.val + 36200) < 2 ^ 1771 := by decide
private theorem cs_w25 : ∀ n : Fin 50, centredStar (densSupG (n.val + 36250)) (centF (n.val + 36250)) = true := by decide
private theorem cl_w25 : ∀ n : Fin 50, centF (n.val + 36250) < 23 := by decide
private theorem bd_w25 : ∀ n : Fin 50, densSupG (n.val + 36250) < 2 ^ 1771 := by decide
private theorem cs_w26 : ∀ n : Fin 50, centredStar (densSupG (n.val + 36300)) (centF (n.val + 36300)) = true := by decide
private theorem cl_w26 : ∀ n : Fin 50, centF (n.val + 36300) < 23 := by decide
private theorem bd_w26 : ∀ n : Fin 50, densSupG (n.val + 36300) < 2 ^ 1771 := by decide
private theorem cs_w27 : ∀ n : Fin 50, centredStar (densSupG (n.val + 36350)) (centF (n.val + 36350)) = true := by decide
private theorem cl_w27 : ∀ n : Fin 50, centF (n.val + 36350) < 23 := by decide
private theorem bd_w27 : ∀ n : Fin 50, densSupG (n.val + 36350) < 2 ^ 1771 := by decide
private theorem cs_w28 : ∀ n : Fin 50, centredStar (densSupG (n.val + 36400)) (centF (n.val + 36400)) = true := by decide
private theorem cl_w28 : ∀ n : Fin 50, centF (n.val + 36400) < 23 := by decide
private theorem bd_w28 : ∀ n : Fin 50, densSupG (n.val + 36400) < 2 ^ 1771 := by decide
private theorem cs_w29 : ∀ n : Fin 50, centredStar (densSupG (n.val + 36450)) (centF (n.val + 36450)) = true := by decide
private theorem cl_w29 : ∀ n : Fin 50, centF (n.val + 36450) < 23 := by decide
private theorem bd_w29 : ∀ n : Fin 50, densSupG (n.val + 36450) < 2 ^ 1771 := by decide
private theorem cs_w30 : ∀ n : Fin 50, centredStar (densSupG (n.val + 36500)) (centF (n.val + 36500)) = true := by decide
private theorem cl_w30 : ∀ n : Fin 50, centF (n.val + 36500) < 23 := by decide
private theorem bd_w30 : ∀ n : Fin 50, densSupG (n.val + 36500) < 2 ^ 1771 := by decide
private theorem cs_w31 : ∀ n : Fin 50, centredStar (densSupG (n.val + 36550)) (centF (n.val + 36550)) = true := by decide
private theorem cl_w31 : ∀ n : Fin 50, centF (n.val + 36550) < 23 := by decide
private theorem bd_w31 : ∀ n : Fin 50, densSupG (n.val + 36550) < 2 ^ 1771 := by decide
private theorem cs_w32 : ∀ n : Fin 50, centredStar (densSupG (n.val + 36600)) (centF (n.val + 36600)) = true := by decide
private theorem cl_w32 : ∀ n : Fin 50, centF (n.val + 36600) < 23 := by decide
private theorem bd_w32 : ∀ n : Fin 50, densSupG (n.val + 36600) < 2 ^ 1771 := by decide
private theorem cs_w33 : ∀ n : Fin 50, centredStar (densSupG (n.val + 36650)) (centF (n.val + 36650)) = true := by decide
private theorem cl_w33 : ∀ n : Fin 50, centF (n.val + 36650) < 23 := by decide
private theorem bd_w33 : ∀ n : Fin 50, densSupG (n.val + 36650) < 2 ^ 1771 := by decide
private theorem cs_w34 : ∀ n : Fin 50, centredStar (densSupG (n.val + 36700)) (centF (n.val + 36700)) = true := by decide
private theorem cl_w34 : ∀ n : Fin 50, centF (n.val + 36700) < 23 := by decide
private theorem bd_w34 : ∀ n : Fin 50, densSupG (n.val + 36700) < 2 ^ 1771 := by decide
private theorem cs_w35 : ∀ n : Fin 50, centredStar (densSupG (n.val + 36750)) (centF (n.val + 36750)) = true := by decide
private theorem cl_w35 : ∀ n : Fin 50, centF (n.val + 36750) < 23 := by decide
private theorem bd_w35 : ∀ n : Fin 50, densSupG (n.val + 36750) < 2 ^ 1771 := by decide
private theorem cs_w36 : ∀ n : Fin 50, centredStar (densSupG (n.val + 36800)) (centF (n.val + 36800)) = true := by decide
private theorem cl_w36 : ∀ n : Fin 50, centF (n.val + 36800) < 23 := by decide
private theorem bd_w36 : ∀ n : Fin 50, densSupG (n.val + 36800) < 2 ^ 1771 := by decide
private theorem cs_w37 : ∀ n : Fin 50, centredStar (densSupG (n.val + 36850)) (centF (n.val + 36850)) = true := by decide
private theorem cl_w37 : ∀ n : Fin 50, centF (n.val + 36850) < 23 := by decide
private theorem bd_w37 : ∀ n : Fin 50, densSupG (n.val + 36850) < 2 ^ 1771 := by decide
private theorem cs_w38 : ∀ n : Fin 50, centredStar (densSupG (n.val + 36900)) (centF (n.val + 36900)) = true := by decide
private theorem cl_w38 : ∀ n : Fin 50, centF (n.val + 36900) < 23 := by decide
private theorem bd_w38 : ∀ n : Fin 50, densSupG (n.val + 36900) < 2 ^ 1771 := by decide
private theorem cs_w39 : ∀ n : Fin 50, centredStar (densSupG (n.val + 36950)) (centF (n.val + 36950)) = true := by decide
private theorem cl_w39 : ∀ n : Fin 50, centF (n.val + 36950) < 23 := by decide
private theorem bd_w39 : ∀ n : Fin 50, densSupG (n.val + 36950) < 2 ^ 1771 := by decide
private theorem cs_w40 : ∀ n : Fin 50, centredStar (densSupG (n.val + 37000)) (centF (n.val + 37000)) = true := by decide
private theorem cl_w40 : ∀ n : Fin 50, centF (n.val + 37000) < 23 := by decide
private theorem bd_w40 : ∀ n : Fin 50, densSupG (n.val + 37000) < 2 ^ 1771 := by decide
private theorem cs_w41 : ∀ n : Fin 50, centredStar (densSupG (n.val + 37050)) (centF (n.val + 37050)) = true := by decide
private theorem cl_w41 : ∀ n : Fin 50, centF (n.val + 37050) < 23 := by decide
private theorem bd_w41 : ∀ n : Fin 50, densSupG (n.val + 37050) < 2 ^ 1771 := by decide
private theorem cs_w42 : ∀ n : Fin 50, centredStar (densSupG (n.val + 37100)) (centF (n.val + 37100)) = true := by decide
private theorem cl_w42 : ∀ n : Fin 50, centF (n.val + 37100) < 23 := by decide
private theorem bd_w42 : ∀ n : Fin 50, densSupG (n.val + 37100) < 2 ^ 1771 := by decide
private theorem cs_w43 : ∀ n : Fin 50, centredStar (densSupG (n.val + 37150)) (centF (n.val + 37150)) = true := by decide
private theorem cl_w43 : ∀ n : Fin 50, centF (n.val + 37150) < 23 := by decide
private theorem bd_w43 : ∀ n : Fin 50, densSupG (n.val + 37150) < 2 ^ 1771 := by decide
private theorem cs_w44 : ∀ n : Fin 50, centredStar (densSupG (n.val + 37200)) (centF (n.val + 37200)) = true := by decide
private theorem cl_w44 : ∀ n : Fin 50, centF (n.val + 37200) < 23 := by decide
private theorem bd_w44 : ∀ n : Fin 50, densSupG (n.val + 37200) < 2 ^ 1771 := by decide
private theorem cs_w45 : ∀ n : Fin 50, centredStar (densSupG (n.val + 37250)) (centF (n.val + 37250)) = true := by decide
private theorem cl_w45 : ∀ n : Fin 50, centF (n.val + 37250) < 23 := by decide
private theorem bd_w45 : ∀ n : Fin 50, densSupG (n.val + 37250) < 2 ^ 1771 := by decide
private theorem cs_w46 : ∀ n : Fin 50, centredStar (densSupG (n.val + 37300)) (centF (n.val + 37300)) = true := by decide
private theorem cl_w46 : ∀ n : Fin 50, centF (n.val + 37300) < 23 := by decide
private theorem bd_w46 : ∀ n : Fin 50, densSupG (n.val + 37300) < 2 ^ 1771 := by decide
private theorem cs_w47 : ∀ n : Fin 50, centredStar (densSupG (n.val + 37350)) (centF (n.val + 37350)) = true := by decide
private theorem cl_w47 : ∀ n : Fin 50, centF (n.val + 37350) < 23 := by decide
private theorem bd_w47 : ∀ n : Fin 50, densSupG (n.val + 37350) < 2 ^ 1771 := by decide
private theorem cs_w48 : ∀ n : Fin 50, centredStar (densSupG (n.val + 37400)) (centF (n.val + 37400)) = true := by decide
private theorem cl_w48 : ∀ n : Fin 50, centF (n.val + 37400) < 23 := by decide
private theorem bd_w48 : ∀ n : Fin 50, densSupG (n.val + 37400) < 2 ^ 1771 := by decide
private theorem cs_w49 : ∀ n : Fin 50, centredStar (densSupG (n.val + 37450)) (centF (n.val + 37450)) = true := by decide
private theorem cl_w49 : ∀ n : Fin 50, centF (n.val + 37450) < 23 := by decide
private theorem bd_w49 : ∀ n : Fin 50, densSupG (n.val + 37450) < 2 ^ 1771 := by decide
theorem centredStar_range : ∀ n, 35000 ≤ n → n < 37500 → centredStar (densSupG n) (centF n) = true := by
  intro n hlo hhi
  by_cases h0 : n < 35050
  · have hr : n - 35000 < 50 := by omega
    have heq : n = (n - 35000) + 35000 := by omega
    rw [heq]
    exact cs_w0 ⟨n - 35000, hr⟩
  ·
    by_cases h1 : n < 35100
    ·
      have hr : n - 35050 < 50 := by omega
      have heq : n = (n - 35050) + 35050 := by omega
      rw [heq]
      exact cs_w1 ⟨n - 35050, hr⟩
    ·
      by_cases h2 : n < 35150
      ·
        have hr : n - 35100 < 50 := by omega
        have heq : n = (n - 35100) + 35100 := by omega
        rw [heq]
        exact cs_w2 ⟨n - 35100, hr⟩
      ·
        by_cases h3 : n < 35200
        ·
          have hr : n - 35150 < 50 := by omega
          have heq : n = (n - 35150) + 35150 := by omega
          rw [heq]
          exact cs_w3 ⟨n - 35150, hr⟩
        ·
          by_cases h4 : n < 35250
          ·
            have hr : n - 35200 < 50 := by omega
            have heq : n = (n - 35200) + 35200 := by omega
            rw [heq]
            exact cs_w4 ⟨n - 35200, hr⟩
          ·
            by_cases h5 : n < 35300
            ·
              have hr : n - 35250 < 50 := by omega
              have heq : n = (n - 35250) + 35250 := by omega
              rw [heq]
              exact cs_w5 ⟨n - 35250, hr⟩
            ·
              by_cases h6 : n < 35350
              ·
                have hr : n - 35300 < 50 := by omega
                have heq : n = (n - 35300) + 35300 := by omega
                rw [heq]
                exact cs_w6 ⟨n - 35300, hr⟩
              ·
                by_cases h7 : n < 35400
                ·
                  have hr : n - 35350 < 50 := by omega
                  have heq : n = (n - 35350) + 35350 := by omega
                  rw [heq]
                  exact cs_w7 ⟨n - 35350, hr⟩
                ·
                  by_cases h8 : n < 35450
                  ·
                    have hr : n - 35400 < 50 := by omega
                    have heq : n = (n - 35400) + 35400 := by omega
                    rw [heq]
                    exact cs_w8 ⟨n - 35400, hr⟩
                  ·
                    by_cases h9 : n < 35500
                    ·
                      have hr : n - 35450 < 50 := by omega
                      have heq : n = (n - 35450) + 35450 := by omega
                      rw [heq]
                      exact cs_w9 ⟨n - 35450, hr⟩
                    ·
                      by_cases h10 : n < 35550
                      ·
                        have hr : n - 35500 < 50 := by omega
                        have heq : n = (n - 35500) + 35500 := by omega
                        rw [heq]
                        exact cs_w10 ⟨n - 35500, hr⟩
                      ·
                        by_cases h11 : n < 35600
                        ·
                          have hr : n - 35550 < 50 := by omega
                          have heq : n = (n - 35550) + 35550 := by omega
                          rw [heq]
                          exact cs_w11 ⟨n - 35550, hr⟩
                        ·
                          by_cases h12 : n < 35650
                          ·
                            have hr : n - 35600 < 50 := by omega
                            have heq : n = (n - 35600) + 35600 := by omega
                            rw [heq]
                            exact cs_w12 ⟨n - 35600, hr⟩
                          ·
                            by_cases h13 : n < 35700
                            ·
                              have hr : n - 35650 < 50 := by omega
                              have heq : n = (n - 35650) + 35650 := by omega
                              rw [heq]
                              exact cs_w13 ⟨n - 35650, hr⟩
                            ·
                              by_cases h14 : n < 35750
                              ·
                                have hr : n - 35700 < 50 := by omega
                                have heq : n = (n - 35700) + 35700 := by omega
                                rw [heq]
                                exact cs_w14 ⟨n - 35700, hr⟩
                              ·
                                by_cases h15 : n < 35800
                                ·
                                  have hr : n - 35750 < 50 := by omega
                                  have heq : n = (n - 35750) + 35750 := by omega
                                  rw [heq]
                                  exact cs_w15 ⟨n - 35750, hr⟩
                                ·
                                  by_cases h16 : n < 35850
                                  ·
                                    have hr : n - 35800 < 50 := by omega
                                    have heq : n = (n - 35800) + 35800 := by omega
                                    rw [heq]
                                    exact cs_w16 ⟨n - 35800, hr⟩
                                  ·
                                    by_cases h17 : n < 35900
                                    ·
                                      have hr : n - 35850 < 50 := by omega
                                      have heq : n = (n - 35850) + 35850 := by omega
                                      rw [heq]
                                      exact cs_w17 ⟨n - 35850, hr⟩
                                    ·
                                      by_cases h18 : n < 35950
                                      ·
                                        have hr : n - 35900 < 50 := by omega
                                        have heq : n = (n - 35900) + 35900 := by omega
                                        rw [heq]
                                        exact cs_w18 ⟨n - 35900, hr⟩
                                      ·
                                        by_cases h19 : n < 36000
                                        ·
                                          have hr : n - 35950 < 50 := by omega
                                          have heq : n = (n - 35950) + 35950 := by omega
                                          rw [heq]
                                          exact cs_w19 ⟨n - 35950, hr⟩
                                        ·
                                          by_cases h20 : n < 36050
                                          ·
                                            have hr : n - 36000 < 50 := by omega
                                            have heq : n = (n - 36000) + 36000 := by omega
                                            rw [heq]
                                            exact cs_w20 ⟨n - 36000, hr⟩
                                          ·
                                            by_cases h21 : n < 36100
                                            ·
                                              have hr : n - 36050 < 50 := by omega
                                              have heq : n = (n - 36050) + 36050 := by omega
                                              rw [heq]
                                              exact cs_w21 ⟨n - 36050, hr⟩
                                            ·
                                              by_cases h22 : n < 36150
                                              ·
                                                have hr : n - 36100 < 50 := by omega
                                                have heq : n = (n - 36100) + 36100 := by omega
                                                rw [heq]
                                                exact cs_w22 ⟨n - 36100, hr⟩
                                              ·
                                                by_cases h23 : n < 36200
                                                ·
                                                  have hr : n - 36150 < 50 := by omega
                                                  have heq : n = (n - 36150) + 36150 := by omega
                                                  rw [heq]
                                                  exact cs_w23 ⟨n - 36150, hr⟩
                                                ·
                                                  by_cases h24 : n < 36250
                                                  ·
                                                    have hr : n - 36200 < 50 := by omega
                                                    have heq : n = (n - 36200) + 36200 := by omega
                                                    rw [heq]
                                                    exact cs_w24 ⟨n - 36200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 36300
                                                    ·
                                                      have hr : n - 36250 < 50 := by omega
                                                      have heq : n = (n - 36250) + 36250 := by omega
                                                      rw [heq]
                                                      exact cs_w25 ⟨n - 36250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 36350
                                                      ·
                                                        have hr : n - 36300 < 50 := by omega
                                                        have heq : n = (n - 36300) + 36300 := by omega
                                                        rw [heq]
                                                        exact cs_w26 ⟨n - 36300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 36400
                                                        ·
                                                          have hr : n - 36350 < 50 := by omega
                                                          have heq : n = (n - 36350) + 36350 := by omega
                                                          rw [heq]
                                                          exact cs_w27 ⟨n - 36350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 36450
                                                          ·
                                                            have hr : n - 36400 < 50 := by omega
                                                            have heq : n = (n - 36400) + 36400 := by omega
                                                            rw [heq]
                                                            exact cs_w28 ⟨n - 36400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 36500
                                                            ·
                                                              have hr : n - 36450 < 50 := by omega
                                                              have heq : n = (n - 36450) + 36450 := by omega
                                                              rw [heq]
                                                              exact cs_w29 ⟨n - 36450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 36550
                                                              ·
                                                                have hr : n - 36500 < 50 := by omega
                                                                have heq : n = (n - 36500) + 36500 := by omega
                                                                rw [heq]
                                                                exact cs_w30 ⟨n - 36500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 36600
                                                                ·
                                                                  have hr : n - 36550 < 50 := by omega
                                                                  have heq : n = (n - 36550) + 36550 := by omega
                                                                  rw [heq]
                                                                  exact cs_w31 ⟨n - 36550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 36650
                                                                  ·
                                                                    have hr : n - 36600 < 50 := by omega
                                                                    have heq : n = (n - 36600) + 36600 := by omega
                                                                    rw [heq]
                                                                    exact cs_w32 ⟨n - 36600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 36700
                                                                    ·
                                                                      have hr : n - 36650 < 50 := by omega
                                                                      have heq : n = (n - 36650) + 36650 := by omega
                                                                      rw [heq]
                                                                      exact cs_w33 ⟨n - 36650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 36750
                                                                      ·
                                                                        have hr : n - 36700 < 50 := by omega
                                                                        have heq : n = (n - 36700) + 36700 := by omega
                                                                        rw [heq]
                                                                        exact cs_w34 ⟨n - 36700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 36800
                                                                        ·
                                                                          have hr : n - 36750 < 50 := by omega
                                                                          have heq : n = (n - 36750) + 36750 := by omega
                                                                          rw [heq]
                                                                          exact cs_w35 ⟨n - 36750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 36850
                                                                          ·
                                                                            have hr : n - 36800 < 50 := by omega
                                                                            have heq : n = (n - 36800) + 36800 := by omega
                                                                            rw [heq]
                                                                            exact cs_w36 ⟨n - 36800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 36900
                                                                            ·
                                                                              have hr : n - 36850 < 50 := by omega
                                                                              have heq : n = (n - 36850) + 36850 := by omega
                                                                              rw [heq]
                                                                              exact cs_w37 ⟨n - 36850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 36950
                                                                              ·
                                                                                have hr : n - 36900 < 50 := by omega
                                                                                have heq : n = (n - 36900) + 36900 := by omega
                                                                                rw [heq]
                                                                                exact cs_w38 ⟨n - 36900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 37000
                                                                                ·
                                                                                  have hr : n - 36950 < 50 := by omega
                                                                                  have heq : n = (n - 36950) + 36950 := by omega
                                                                                  rw [heq]
                                                                                  exact cs_w39 ⟨n - 36950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 37050
                                                                                  ·
                                                                                    have hr : n - 37000 < 50 := by omega
                                                                                    have heq : n = (n - 37000) + 37000 := by omega
                                                                                    rw [heq]
                                                                                    exact cs_w40 ⟨n - 37000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 37100
                                                                                    ·
                                                                                      have hr : n - 37050 < 50 := by omega
                                                                                      have heq : n = (n - 37050) + 37050 := by omega
                                                                                      rw [heq]
                                                                                      exact cs_w41 ⟨n - 37050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 37150
                                                                                      ·
                                                                                        have hr : n - 37100 < 50 := by omega
                                                                                        have heq : n = (n - 37100) + 37100 := by omega
                                                                                        rw [heq]
                                                                                        exact cs_w42 ⟨n - 37100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 37200
                                                                                        ·
                                                                                          have hr : n - 37150 < 50 := by omega
                                                                                          have heq : n = (n - 37150) + 37150 := by omega
                                                                                          rw [heq]
                                                                                          exact cs_w43 ⟨n - 37150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 37250
                                                                                          ·
                                                                                            have hr : n - 37200 < 50 := by omega
                                                                                            have heq : n = (n - 37200) + 37200 := by omega
                                                                                            rw [heq]
                                                                                            exact cs_w44 ⟨n - 37200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 37300
                                                                                            ·
                                                                                              have hr : n - 37250 < 50 := by omega
                                                                                              have heq : n = (n - 37250) + 37250 := by omega
                                                                                              rw [heq]
                                                                                              exact cs_w45 ⟨n - 37250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 37350
                                                                                              ·
                                                                                                have hr : n - 37300 < 50 := by omega
                                                                                                have heq : n = (n - 37300) + 37300 := by omega
                                                                                                rw [heq]
                                                                                                exact cs_w46 ⟨n - 37300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 37400
                                                                                                ·
                                                                                                  have hr : n - 37350 < 50 := by omega
                                                                                                  have heq : n = (n - 37350) + 37350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cs_w47 ⟨n - 37350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 37450
                                                                                                  ·
                                                                                                    have hr : n - 37400 < 50 := by omega
                                                                                                    have heq : n = (n - 37400) + 37400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w48 ⟨n - 37400, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 37450 < 50 := by omega
                                                                                                    have heq : n = (n - 37450) + 37450 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w49 ⟨n - 37450, hr⟩


theorem centF_lt_range : ∀ n, 35000 ≤ n → n < 37500 → centF n < 23 := by
  intro n hlo hhi
  by_cases h0 : n < 35050
  · have hr : n - 35000 < 50 := by omega
    have heq : n = (n - 35000) + 35000 := by omega
    rw [heq]
    exact cl_w0 ⟨n - 35000, hr⟩
  ·
    by_cases h1 : n < 35100
    ·
      have hr : n - 35050 < 50 := by omega
      have heq : n = (n - 35050) + 35050 := by omega
      rw [heq]
      exact cl_w1 ⟨n - 35050, hr⟩
    ·
      by_cases h2 : n < 35150
      ·
        have hr : n - 35100 < 50 := by omega
        have heq : n = (n - 35100) + 35100 := by omega
        rw [heq]
        exact cl_w2 ⟨n - 35100, hr⟩
      ·
        by_cases h3 : n < 35200
        ·
          have hr : n - 35150 < 50 := by omega
          have heq : n = (n - 35150) + 35150 := by omega
          rw [heq]
          exact cl_w3 ⟨n - 35150, hr⟩
        ·
          by_cases h4 : n < 35250
          ·
            have hr : n - 35200 < 50 := by omega
            have heq : n = (n - 35200) + 35200 := by omega
            rw [heq]
            exact cl_w4 ⟨n - 35200, hr⟩
          ·
            by_cases h5 : n < 35300
            ·
              have hr : n - 35250 < 50 := by omega
              have heq : n = (n - 35250) + 35250 := by omega
              rw [heq]
              exact cl_w5 ⟨n - 35250, hr⟩
            ·
              by_cases h6 : n < 35350
              ·
                have hr : n - 35300 < 50 := by omega
                have heq : n = (n - 35300) + 35300 := by omega
                rw [heq]
                exact cl_w6 ⟨n - 35300, hr⟩
              ·
                by_cases h7 : n < 35400
                ·
                  have hr : n - 35350 < 50 := by omega
                  have heq : n = (n - 35350) + 35350 := by omega
                  rw [heq]
                  exact cl_w7 ⟨n - 35350, hr⟩
                ·
                  by_cases h8 : n < 35450
                  ·
                    have hr : n - 35400 < 50 := by omega
                    have heq : n = (n - 35400) + 35400 := by omega
                    rw [heq]
                    exact cl_w8 ⟨n - 35400, hr⟩
                  ·
                    by_cases h9 : n < 35500
                    ·
                      have hr : n - 35450 < 50 := by omega
                      have heq : n = (n - 35450) + 35450 := by omega
                      rw [heq]
                      exact cl_w9 ⟨n - 35450, hr⟩
                    ·
                      by_cases h10 : n < 35550
                      ·
                        have hr : n - 35500 < 50 := by omega
                        have heq : n = (n - 35500) + 35500 := by omega
                        rw [heq]
                        exact cl_w10 ⟨n - 35500, hr⟩
                      ·
                        by_cases h11 : n < 35600
                        ·
                          have hr : n - 35550 < 50 := by omega
                          have heq : n = (n - 35550) + 35550 := by omega
                          rw [heq]
                          exact cl_w11 ⟨n - 35550, hr⟩
                        ·
                          by_cases h12 : n < 35650
                          ·
                            have hr : n - 35600 < 50 := by omega
                            have heq : n = (n - 35600) + 35600 := by omega
                            rw [heq]
                            exact cl_w12 ⟨n - 35600, hr⟩
                          ·
                            by_cases h13 : n < 35700
                            ·
                              have hr : n - 35650 < 50 := by omega
                              have heq : n = (n - 35650) + 35650 := by omega
                              rw [heq]
                              exact cl_w13 ⟨n - 35650, hr⟩
                            ·
                              by_cases h14 : n < 35750
                              ·
                                have hr : n - 35700 < 50 := by omega
                                have heq : n = (n - 35700) + 35700 := by omega
                                rw [heq]
                                exact cl_w14 ⟨n - 35700, hr⟩
                              ·
                                by_cases h15 : n < 35800
                                ·
                                  have hr : n - 35750 < 50 := by omega
                                  have heq : n = (n - 35750) + 35750 := by omega
                                  rw [heq]
                                  exact cl_w15 ⟨n - 35750, hr⟩
                                ·
                                  by_cases h16 : n < 35850
                                  ·
                                    have hr : n - 35800 < 50 := by omega
                                    have heq : n = (n - 35800) + 35800 := by omega
                                    rw [heq]
                                    exact cl_w16 ⟨n - 35800, hr⟩
                                  ·
                                    by_cases h17 : n < 35900
                                    ·
                                      have hr : n - 35850 < 50 := by omega
                                      have heq : n = (n - 35850) + 35850 := by omega
                                      rw [heq]
                                      exact cl_w17 ⟨n - 35850, hr⟩
                                    ·
                                      by_cases h18 : n < 35950
                                      ·
                                        have hr : n - 35900 < 50 := by omega
                                        have heq : n = (n - 35900) + 35900 := by omega
                                        rw [heq]
                                        exact cl_w18 ⟨n - 35900, hr⟩
                                      ·
                                        by_cases h19 : n < 36000
                                        ·
                                          have hr : n - 35950 < 50 := by omega
                                          have heq : n = (n - 35950) + 35950 := by omega
                                          rw [heq]
                                          exact cl_w19 ⟨n - 35950, hr⟩
                                        ·
                                          by_cases h20 : n < 36050
                                          ·
                                            have hr : n - 36000 < 50 := by omega
                                            have heq : n = (n - 36000) + 36000 := by omega
                                            rw [heq]
                                            exact cl_w20 ⟨n - 36000, hr⟩
                                          ·
                                            by_cases h21 : n < 36100
                                            ·
                                              have hr : n - 36050 < 50 := by omega
                                              have heq : n = (n - 36050) + 36050 := by omega
                                              rw [heq]
                                              exact cl_w21 ⟨n - 36050, hr⟩
                                            ·
                                              by_cases h22 : n < 36150
                                              ·
                                                have hr : n - 36100 < 50 := by omega
                                                have heq : n = (n - 36100) + 36100 := by omega
                                                rw [heq]
                                                exact cl_w22 ⟨n - 36100, hr⟩
                                              ·
                                                by_cases h23 : n < 36200
                                                ·
                                                  have hr : n - 36150 < 50 := by omega
                                                  have heq : n = (n - 36150) + 36150 := by omega
                                                  rw [heq]
                                                  exact cl_w23 ⟨n - 36150, hr⟩
                                                ·
                                                  by_cases h24 : n < 36250
                                                  ·
                                                    have hr : n - 36200 < 50 := by omega
                                                    have heq : n = (n - 36200) + 36200 := by omega
                                                    rw [heq]
                                                    exact cl_w24 ⟨n - 36200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 36300
                                                    ·
                                                      have hr : n - 36250 < 50 := by omega
                                                      have heq : n = (n - 36250) + 36250 := by omega
                                                      rw [heq]
                                                      exact cl_w25 ⟨n - 36250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 36350
                                                      ·
                                                        have hr : n - 36300 < 50 := by omega
                                                        have heq : n = (n - 36300) + 36300 := by omega
                                                        rw [heq]
                                                        exact cl_w26 ⟨n - 36300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 36400
                                                        ·
                                                          have hr : n - 36350 < 50 := by omega
                                                          have heq : n = (n - 36350) + 36350 := by omega
                                                          rw [heq]
                                                          exact cl_w27 ⟨n - 36350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 36450
                                                          ·
                                                            have hr : n - 36400 < 50 := by omega
                                                            have heq : n = (n - 36400) + 36400 := by omega
                                                            rw [heq]
                                                            exact cl_w28 ⟨n - 36400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 36500
                                                            ·
                                                              have hr : n - 36450 < 50 := by omega
                                                              have heq : n = (n - 36450) + 36450 := by omega
                                                              rw [heq]
                                                              exact cl_w29 ⟨n - 36450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 36550
                                                              ·
                                                                have hr : n - 36500 < 50 := by omega
                                                                have heq : n = (n - 36500) + 36500 := by omega
                                                                rw [heq]
                                                                exact cl_w30 ⟨n - 36500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 36600
                                                                ·
                                                                  have hr : n - 36550 < 50 := by omega
                                                                  have heq : n = (n - 36550) + 36550 := by omega
                                                                  rw [heq]
                                                                  exact cl_w31 ⟨n - 36550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 36650
                                                                  ·
                                                                    have hr : n - 36600 < 50 := by omega
                                                                    have heq : n = (n - 36600) + 36600 := by omega
                                                                    rw [heq]
                                                                    exact cl_w32 ⟨n - 36600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 36700
                                                                    ·
                                                                      have hr : n - 36650 < 50 := by omega
                                                                      have heq : n = (n - 36650) + 36650 := by omega
                                                                      rw [heq]
                                                                      exact cl_w33 ⟨n - 36650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 36750
                                                                      ·
                                                                        have hr : n - 36700 < 50 := by omega
                                                                        have heq : n = (n - 36700) + 36700 := by omega
                                                                        rw [heq]
                                                                        exact cl_w34 ⟨n - 36700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 36800
                                                                        ·
                                                                          have hr : n - 36750 < 50 := by omega
                                                                          have heq : n = (n - 36750) + 36750 := by omega
                                                                          rw [heq]
                                                                          exact cl_w35 ⟨n - 36750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 36850
                                                                          ·
                                                                            have hr : n - 36800 < 50 := by omega
                                                                            have heq : n = (n - 36800) + 36800 := by omega
                                                                            rw [heq]
                                                                            exact cl_w36 ⟨n - 36800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 36900
                                                                            ·
                                                                              have hr : n - 36850 < 50 := by omega
                                                                              have heq : n = (n - 36850) + 36850 := by omega
                                                                              rw [heq]
                                                                              exact cl_w37 ⟨n - 36850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 36950
                                                                              ·
                                                                                have hr : n - 36900 < 50 := by omega
                                                                                have heq : n = (n - 36900) + 36900 := by omega
                                                                                rw [heq]
                                                                                exact cl_w38 ⟨n - 36900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 37000
                                                                                ·
                                                                                  have hr : n - 36950 < 50 := by omega
                                                                                  have heq : n = (n - 36950) + 36950 := by omega
                                                                                  rw [heq]
                                                                                  exact cl_w39 ⟨n - 36950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 37050
                                                                                  ·
                                                                                    have hr : n - 37000 < 50 := by omega
                                                                                    have heq : n = (n - 37000) + 37000 := by omega
                                                                                    rw [heq]
                                                                                    exact cl_w40 ⟨n - 37000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 37100
                                                                                    ·
                                                                                      have hr : n - 37050 < 50 := by omega
                                                                                      have heq : n = (n - 37050) + 37050 := by omega
                                                                                      rw [heq]
                                                                                      exact cl_w41 ⟨n - 37050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 37150
                                                                                      ·
                                                                                        have hr : n - 37100 < 50 := by omega
                                                                                        have heq : n = (n - 37100) + 37100 := by omega
                                                                                        rw [heq]
                                                                                        exact cl_w42 ⟨n - 37100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 37200
                                                                                        ·
                                                                                          have hr : n - 37150 < 50 := by omega
                                                                                          have heq : n = (n - 37150) + 37150 := by omega
                                                                                          rw [heq]
                                                                                          exact cl_w43 ⟨n - 37150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 37250
                                                                                          ·
                                                                                            have hr : n - 37200 < 50 := by omega
                                                                                            have heq : n = (n - 37200) + 37200 := by omega
                                                                                            rw [heq]
                                                                                            exact cl_w44 ⟨n - 37200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 37300
                                                                                            ·
                                                                                              have hr : n - 37250 < 50 := by omega
                                                                                              have heq : n = (n - 37250) + 37250 := by omega
                                                                                              rw [heq]
                                                                                              exact cl_w45 ⟨n - 37250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 37350
                                                                                              ·
                                                                                                have hr : n - 37300 < 50 := by omega
                                                                                                have heq : n = (n - 37300) + 37300 := by omega
                                                                                                rw [heq]
                                                                                                exact cl_w46 ⟨n - 37300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 37400
                                                                                                ·
                                                                                                  have hr : n - 37350 < 50 := by omega
                                                                                                  have heq : n = (n - 37350) + 37350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cl_w47 ⟨n - 37350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 37450
                                                                                                  ·
                                                                                                    have hr : n - 37400 < 50 := by omega
                                                                                                    have heq : n = (n - 37400) + 37400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w48 ⟨n - 37400, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 37450 < 50 := by omega
                                                                                                    have heq : n = (n - 37450) + 37450 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w49 ⟨n - 37450, hr⟩


theorem densSupG_lt_range : ∀ n, 35000 ≤ n → n < 37500 → densSupG n < 2 ^ 1771 := by
  intro n hlo hhi
  by_cases h0 : n < 35050
  · have hr : n - 35000 < 50 := by omega
    have heq : n = (n - 35000) + 35000 := by omega
    rw [heq]
    exact bd_w0 ⟨n - 35000, hr⟩
  ·
    by_cases h1 : n < 35100
    ·
      have hr : n - 35050 < 50 := by omega
      have heq : n = (n - 35050) + 35050 := by omega
      rw [heq]
      exact bd_w1 ⟨n - 35050, hr⟩
    ·
      by_cases h2 : n < 35150
      ·
        have hr : n - 35100 < 50 := by omega
        have heq : n = (n - 35100) + 35100 := by omega
        rw [heq]
        exact bd_w2 ⟨n - 35100, hr⟩
      ·
        by_cases h3 : n < 35200
        ·
          have hr : n - 35150 < 50 := by omega
          have heq : n = (n - 35150) + 35150 := by omega
          rw [heq]
          exact bd_w3 ⟨n - 35150, hr⟩
        ·
          by_cases h4 : n < 35250
          ·
            have hr : n - 35200 < 50 := by omega
            have heq : n = (n - 35200) + 35200 := by omega
            rw [heq]
            exact bd_w4 ⟨n - 35200, hr⟩
          ·
            by_cases h5 : n < 35300
            ·
              have hr : n - 35250 < 50 := by omega
              have heq : n = (n - 35250) + 35250 := by omega
              rw [heq]
              exact bd_w5 ⟨n - 35250, hr⟩
            ·
              by_cases h6 : n < 35350
              ·
                have hr : n - 35300 < 50 := by omega
                have heq : n = (n - 35300) + 35300 := by omega
                rw [heq]
                exact bd_w6 ⟨n - 35300, hr⟩
              ·
                by_cases h7 : n < 35400
                ·
                  have hr : n - 35350 < 50 := by omega
                  have heq : n = (n - 35350) + 35350 := by omega
                  rw [heq]
                  exact bd_w7 ⟨n - 35350, hr⟩
                ·
                  by_cases h8 : n < 35450
                  ·
                    have hr : n - 35400 < 50 := by omega
                    have heq : n = (n - 35400) + 35400 := by omega
                    rw [heq]
                    exact bd_w8 ⟨n - 35400, hr⟩
                  ·
                    by_cases h9 : n < 35500
                    ·
                      have hr : n - 35450 < 50 := by omega
                      have heq : n = (n - 35450) + 35450 := by omega
                      rw [heq]
                      exact bd_w9 ⟨n - 35450, hr⟩
                    ·
                      by_cases h10 : n < 35550
                      ·
                        have hr : n - 35500 < 50 := by omega
                        have heq : n = (n - 35500) + 35500 := by omega
                        rw [heq]
                        exact bd_w10 ⟨n - 35500, hr⟩
                      ·
                        by_cases h11 : n < 35600
                        ·
                          have hr : n - 35550 < 50 := by omega
                          have heq : n = (n - 35550) + 35550 := by omega
                          rw [heq]
                          exact bd_w11 ⟨n - 35550, hr⟩
                        ·
                          by_cases h12 : n < 35650
                          ·
                            have hr : n - 35600 < 50 := by omega
                            have heq : n = (n - 35600) + 35600 := by omega
                            rw [heq]
                            exact bd_w12 ⟨n - 35600, hr⟩
                          ·
                            by_cases h13 : n < 35700
                            ·
                              have hr : n - 35650 < 50 := by omega
                              have heq : n = (n - 35650) + 35650 := by omega
                              rw [heq]
                              exact bd_w13 ⟨n - 35650, hr⟩
                            ·
                              by_cases h14 : n < 35750
                              ·
                                have hr : n - 35700 < 50 := by omega
                                have heq : n = (n - 35700) + 35700 := by omega
                                rw [heq]
                                exact bd_w14 ⟨n - 35700, hr⟩
                              ·
                                by_cases h15 : n < 35800
                                ·
                                  have hr : n - 35750 < 50 := by omega
                                  have heq : n = (n - 35750) + 35750 := by omega
                                  rw [heq]
                                  exact bd_w15 ⟨n - 35750, hr⟩
                                ·
                                  by_cases h16 : n < 35850
                                  ·
                                    have hr : n - 35800 < 50 := by omega
                                    have heq : n = (n - 35800) + 35800 := by omega
                                    rw [heq]
                                    exact bd_w16 ⟨n - 35800, hr⟩
                                  ·
                                    by_cases h17 : n < 35900
                                    ·
                                      have hr : n - 35850 < 50 := by omega
                                      have heq : n = (n - 35850) + 35850 := by omega
                                      rw [heq]
                                      exact bd_w17 ⟨n - 35850, hr⟩
                                    ·
                                      by_cases h18 : n < 35950
                                      ·
                                        have hr : n - 35900 < 50 := by omega
                                        have heq : n = (n - 35900) + 35900 := by omega
                                        rw [heq]
                                        exact bd_w18 ⟨n - 35900, hr⟩
                                      ·
                                        by_cases h19 : n < 36000
                                        ·
                                          have hr : n - 35950 < 50 := by omega
                                          have heq : n = (n - 35950) + 35950 := by omega
                                          rw [heq]
                                          exact bd_w19 ⟨n - 35950, hr⟩
                                        ·
                                          by_cases h20 : n < 36050
                                          ·
                                            have hr : n - 36000 < 50 := by omega
                                            have heq : n = (n - 36000) + 36000 := by omega
                                            rw [heq]
                                            exact bd_w20 ⟨n - 36000, hr⟩
                                          ·
                                            by_cases h21 : n < 36100
                                            ·
                                              have hr : n - 36050 < 50 := by omega
                                              have heq : n = (n - 36050) + 36050 := by omega
                                              rw [heq]
                                              exact bd_w21 ⟨n - 36050, hr⟩
                                            ·
                                              by_cases h22 : n < 36150
                                              ·
                                                have hr : n - 36100 < 50 := by omega
                                                have heq : n = (n - 36100) + 36100 := by omega
                                                rw [heq]
                                                exact bd_w22 ⟨n - 36100, hr⟩
                                              ·
                                                by_cases h23 : n < 36200
                                                ·
                                                  have hr : n - 36150 < 50 := by omega
                                                  have heq : n = (n - 36150) + 36150 := by omega
                                                  rw [heq]
                                                  exact bd_w23 ⟨n - 36150, hr⟩
                                                ·
                                                  by_cases h24 : n < 36250
                                                  ·
                                                    have hr : n - 36200 < 50 := by omega
                                                    have heq : n = (n - 36200) + 36200 := by omega
                                                    rw [heq]
                                                    exact bd_w24 ⟨n - 36200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 36300
                                                    ·
                                                      have hr : n - 36250 < 50 := by omega
                                                      have heq : n = (n - 36250) + 36250 := by omega
                                                      rw [heq]
                                                      exact bd_w25 ⟨n - 36250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 36350
                                                      ·
                                                        have hr : n - 36300 < 50 := by omega
                                                        have heq : n = (n - 36300) + 36300 := by omega
                                                        rw [heq]
                                                        exact bd_w26 ⟨n - 36300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 36400
                                                        ·
                                                          have hr : n - 36350 < 50 := by omega
                                                          have heq : n = (n - 36350) + 36350 := by omega
                                                          rw [heq]
                                                          exact bd_w27 ⟨n - 36350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 36450
                                                          ·
                                                            have hr : n - 36400 < 50 := by omega
                                                            have heq : n = (n - 36400) + 36400 := by omega
                                                            rw [heq]
                                                            exact bd_w28 ⟨n - 36400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 36500
                                                            ·
                                                              have hr : n - 36450 < 50 := by omega
                                                              have heq : n = (n - 36450) + 36450 := by omega
                                                              rw [heq]
                                                              exact bd_w29 ⟨n - 36450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 36550
                                                              ·
                                                                have hr : n - 36500 < 50 := by omega
                                                                have heq : n = (n - 36500) + 36500 := by omega
                                                                rw [heq]
                                                                exact bd_w30 ⟨n - 36500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 36600
                                                                ·
                                                                  have hr : n - 36550 < 50 := by omega
                                                                  have heq : n = (n - 36550) + 36550 := by omega
                                                                  rw [heq]
                                                                  exact bd_w31 ⟨n - 36550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 36650
                                                                  ·
                                                                    have hr : n - 36600 < 50 := by omega
                                                                    have heq : n = (n - 36600) + 36600 := by omega
                                                                    rw [heq]
                                                                    exact bd_w32 ⟨n - 36600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 36700
                                                                    ·
                                                                      have hr : n - 36650 < 50 := by omega
                                                                      have heq : n = (n - 36650) + 36650 := by omega
                                                                      rw [heq]
                                                                      exact bd_w33 ⟨n - 36650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 36750
                                                                      ·
                                                                        have hr : n - 36700 < 50 := by omega
                                                                        have heq : n = (n - 36700) + 36700 := by omega
                                                                        rw [heq]
                                                                        exact bd_w34 ⟨n - 36700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 36800
                                                                        ·
                                                                          have hr : n - 36750 < 50 := by omega
                                                                          have heq : n = (n - 36750) + 36750 := by omega
                                                                          rw [heq]
                                                                          exact bd_w35 ⟨n - 36750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 36850
                                                                          ·
                                                                            have hr : n - 36800 < 50 := by omega
                                                                            have heq : n = (n - 36800) + 36800 := by omega
                                                                            rw [heq]
                                                                            exact bd_w36 ⟨n - 36800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 36900
                                                                            ·
                                                                              have hr : n - 36850 < 50 := by omega
                                                                              have heq : n = (n - 36850) + 36850 := by omega
                                                                              rw [heq]
                                                                              exact bd_w37 ⟨n - 36850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 36950
                                                                              ·
                                                                                have hr : n - 36900 < 50 := by omega
                                                                                have heq : n = (n - 36900) + 36900 := by omega
                                                                                rw [heq]
                                                                                exact bd_w38 ⟨n - 36900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 37000
                                                                                ·
                                                                                  have hr : n - 36950 < 50 := by omega
                                                                                  have heq : n = (n - 36950) + 36950 := by omega
                                                                                  rw [heq]
                                                                                  exact bd_w39 ⟨n - 36950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 37050
                                                                                  ·
                                                                                    have hr : n - 37000 < 50 := by omega
                                                                                    have heq : n = (n - 37000) + 37000 := by omega
                                                                                    rw [heq]
                                                                                    exact bd_w40 ⟨n - 37000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 37100
                                                                                    ·
                                                                                      have hr : n - 37050 < 50 := by omega
                                                                                      have heq : n = (n - 37050) + 37050 := by omega
                                                                                      rw [heq]
                                                                                      exact bd_w41 ⟨n - 37050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 37150
                                                                                      ·
                                                                                        have hr : n - 37100 < 50 := by omega
                                                                                        have heq : n = (n - 37100) + 37100 := by omega
                                                                                        rw [heq]
                                                                                        exact bd_w42 ⟨n - 37100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 37200
                                                                                        ·
                                                                                          have hr : n - 37150 < 50 := by omega
                                                                                          have heq : n = (n - 37150) + 37150 := by omega
                                                                                          rw [heq]
                                                                                          exact bd_w43 ⟨n - 37150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 37250
                                                                                          ·
                                                                                            have hr : n - 37200 < 50 := by omega
                                                                                            have heq : n = (n - 37200) + 37200 := by omega
                                                                                            rw [heq]
                                                                                            exact bd_w44 ⟨n - 37200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 37300
                                                                                            ·
                                                                                              have hr : n - 37250 < 50 := by omega
                                                                                              have heq : n = (n - 37250) + 37250 := by omega
                                                                                              rw [heq]
                                                                                              exact bd_w45 ⟨n - 37250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 37350
                                                                                              ·
                                                                                                have hr : n - 37300 < 50 := by omega
                                                                                                have heq : n = (n - 37300) + 37300 := by omega
                                                                                                rw [heq]
                                                                                                exact bd_w46 ⟨n - 37300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 37400
                                                                                                ·
                                                                                                  have hr : n - 37350 < 50 := by omega
                                                                                                  have heq : n = (n - 37350) + 37350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact bd_w47 ⟨n - 37350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 37450
                                                                                                  ·
                                                                                                    have hr : n - 37400 < 50 := by omega
                                                                                                    have heq : n = (n - 37400) + 37400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w48 ⟨n - 37400, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 37450 < 50 := by omega
                                                                                                    have heq : n = (n - 37450) + 37450 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w49 ⟨n - 37450, hr⟩


end IntMul.Kappa.R8.Bit.Oppbank.CentBound7a


