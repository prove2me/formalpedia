-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound9a
-- name    : IntMul_Kappa_R8_Data_BitOppbankCentBound9a
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:08:53.889398+00:00
-- url     : https://prove2.me/theorems/c41d9d45-33fe-46eb-811a-2c6dc9ebcf49
-- title:
--   HasCentre certificates dens nodes [45000,47500)
-- statement:
--   # Densified centre certificates, pack 9a
--
--   For every densified node index $n$ with $45000\le n<47500$,
--   $$
--   \mathrm{centredStar}(\mathrm{densSupG}\,n,\mathrm{centF}\,n)=\mathsf{true},\quad
--   \mathrm{centF}\,n<23,\quad
--   \mathrm{densSupG}\,n < 2^{1771}.
--   $$
--   Proved by decide on Fin 50 windows (no native_decide). Half-pack for 300s server budget.
-- source:
--   R8 BitOppbank AllDensCentred; jfstack_23 densified supports

-- CentBound pack 9a: densified HasCentre certificates on n ∈ [45000, 47500)
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

namespace IntMul.Kappa.R8.Bit.Oppbank.CentBound9a


private theorem cs_w0 : ∀ n : Fin 50, centredStar (densSupG (n.val + 45000)) (centF (n.val + 45000)) = true := by decide
private theorem cl_w0 : ∀ n : Fin 50, centF (n.val + 45000) < 23 := by decide
private theorem bd_w0 : ∀ n : Fin 50, densSupG (n.val + 45000) < 2 ^ 1771 := by decide
private theorem cs_w1 : ∀ n : Fin 50, centredStar (densSupG (n.val + 45050)) (centF (n.val + 45050)) = true := by decide
private theorem cl_w1 : ∀ n : Fin 50, centF (n.val + 45050) < 23 := by decide
private theorem bd_w1 : ∀ n : Fin 50, densSupG (n.val + 45050) < 2 ^ 1771 := by decide
private theorem cs_w2 : ∀ n : Fin 50, centredStar (densSupG (n.val + 45100)) (centF (n.val + 45100)) = true := by decide
private theorem cl_w2 : ∀ n : Fin 50, centF (n.val + 45100) < 23 := by decide
private theorem bd_w2 : ∀ n : Fin 50, densSupG (n.val + 45100) < 2 ^ 1771 := by decide
private theorem cs_w3 : ∀ n : Fin 50, centredStar (densSupG (n.val + 45150)) (centF (n.val + 45150)) = true := by decide
private theorem cl_w3 : ∀ n : Fin 50, centF (n.val + 45150) < 23 := by decide
private theorem bd_w3 : ∀ n : Fin 50, densSupG (n.val + 45150) < 2 ^ 1771 := by decide
private theorem cs_w4 : ∀ n : Fin 50, centredStar (densSupG (n.val + 45200)) (centF (n.val + 45200)) = true := by decide
private theorem cl_w4 : ∀ n : Fin 50, centF (n.val + 45200) < 23 := by decide
private theorem bd_w4 : ∀ n : Fin 50, densSupG (n.val + 45200) < 2 ^ 1771 := by decide
private theorem cs_w5 : ∀ n : Fin 50, centredStar (densSupG (n.val + 45250)) (centF (n.val + 45250)) = true := by decide
private theorem cl_w5 : ∀ n : Fin 50, centF (n.val + 45250) < 23 := by decide
private theorem bd_w5 : ∀ n : Fin 50, densSupG (n.val + 45250) < 2 ^ 1771 := by decide
private theorem cs_w6 : ∀ n : Fin 50, centredStar (densSupG (n.val + 45300)) (centF (n.val + 45300)) = true := by decide
private theorem cl_w6 : ∀ n : Fin 50, centF (n.val + 45300) < 23 := by decide
private theorem bd_w6 : ∀ n : Fin 50, densSupG (n.val + 45300) < 2 ^ 1771 := by decide
private theorem cs_w7 : ∀ n : Fin 50, centredStar (densSupG (n.val + 45350)) (centF (n.val + 45350)) = true := by decide
private theorem cl_w7 : ∀ n : Fin 50, centF (n.val + 45350) < 23 := by decide
private theorem bd_w7 : ∀ n : Fin 50, densSupG (n.val + 45350) < 2 ^ 1771 := by decide
private theorem cs_w8 : ∀ n : Fin 50, centredStar (densSupG (n.val + 45400)) (centF (n.val + 45400)) = true := by decide
private theorem cl_w8 : ∀ n : Fin 50, centF (n.val + 45400) < 23 := by decide
private theorem bd_w8 : ∀ n : Fin 50, densSupG (n.val + 45400) < 2 ^ 1771 := by decide
private theorem cs_w9 : ∀ n : Fin 50, centredStar (densSupG (n.val + 45450)) (centF (n.val + 45450)) = true := by decide
private theorem cl_w9 : ∀ n : Fin 50, centF (n.val + 45450) < 23 := by decide
private theorem bd_w9 : ∀ n : Fin 50, densSupG (n.val + 45450) < 2 ^ 1771 := by decide
private theorem cs_w10 : ∀ n : Fin 50, centredStar (densSupG (n.val + 45500)) (centF (n.val + 45500)) = true := by decide
private theorem cl_w10 : ∀ n : Fin 50, centF (n.val + 45500) < 23 := by decide
private theorem bd_w10 : ∀ n : Fin 50, densSupG (n.val + 45500) < 2 ^ 1771 := by decide
private theorem cs_w11 : ∀ n : Fin 50, centredStar (densSupG (n.val + 45550)) (centF (n.val + 45550)) = true := by decide
private theorem cl_w11 : ∀ n : Fin 50, centF (n.val + 45550) < 23 := by decide
private theorem bd_w11 : ∀ n : Fin 50, densSupG (n.val + 45550) < 2 ^ 1771 := by decide
private theorem cs_w12 : ∀ n : Fin 50, centredStar (densSupG (n.val + 45600)) (centF (n.val + 45600)) = true := by decide
private theorem cl_w12 : ∀ n : Fin 50, centF (n.val + 45600) < 23 := by decide
private theorem bd_w12 : ∀ n : Fin 50, densSupG (n.val + 45600) < 2 ^ 1771 := by decide
private theorem cs_w13 : ∀ n : Fin 50, centredStar (densSupG (n.val + 45650)) (centF (n.val + 45650)) = true := by decide
private theorem cl_w13 : ∀ n : Fin 50, centF (n.val + 45650) < 23 := by decide
private theorem bd_w13 : ∀ n : Fin 50, densSupG (n.val + 45650) < 2 ^ 1771 := by decide
private theorem cs_w14 : ∀ n : Fin 50, centredStar (densSupG (n.val + 45700)) (centF (n.val + 45700)) = true := by decide
private theorem cl_w14 : ∀ n : Fin 50, centF (n.val + 45700) < 23 := by decide
private theorem bd_w14 : ∀ n : Fin 50, densSupG (n.val + 45700) < 2 ^ 1771 := by decide
private theorem cs_w15 : ∀ n : Fin 50, centredStar (densSupG (n.val + 45750)) (centF (n.val + 45750)) = true := by decide
private theorem cl_w15 : ∀ n : Fin 50, centF (n.val + 45750) < 23 := by decide
private theorem bd_w15 : ∀ n : Fin 50, densSupG (n.val + 45750) < 2 ^ 1771 := by decide
private theorem cs_w16 : ∀ n : Fin 50, centredStar (densSupG (n.val + 45800)) (centF (n.val + 45800)) = true := by decide
private theorem cl_w16 : ∀ n : Fin 50, centF (n.val + 45800) < 23 := by decide
private theorem bd_w16 : ∀ n : Fin 50, densSupG (n.val + 45800) < 2 ^ 1771 := by decide
private theorem cs_w17 : ∀ n : Fin 50, centredStar (densSupG (n.val + 45850)) (centF (n.val + 45850)) = true := by decide
private theorem cl_w17 : ∀ n : Fin 50, centF (n.val + 45850) < 23 := by decide
private theorem bd_w17 : ∀ n : Fin 50, densSupG (n.val + 45850) < 2 ^ 1771 := by decide
private theorem cs_w18 : ∀ n : Fin 50, centredStar (densSupG (n.val + 45900)) (centF (n.val + 45900)) = true := by decide
private theorem cl_w18 : ∀ n : Fin 50, centF (n.val + 45900) < 23 := by decide
private theorem bd_w18 : ∀ n : Fin 50, densSupG (n.val + 45900) < 2 ^ 1771 := by decide
private theorem cs_w19 : ∀ n : Fin 50, centredStar (densSupG (n.val + 45950)) (centF (n.val + 45950)) = true := by decide
private theorem cl_w19 : ∀ n : Fin 50, centF (n.val + 45950) < 23 := by decide
private theorem bd_w19 : ∀ n : Fin 50, densSupG (n.val + 45950) < 2 ^ 1771 := by decide
private theorem cs_w20 : ∀ n : Fin 50, centredStar (densSupG (n.val + 46000)) (centF (n.val + 46000)) = true := by decide
private theorem cl_w20 : ∀ n : Fin 50, centF (n.val + 46000) < 23 := by decide
private theorem bd_w20 : ∀ n : Fin 50, densSupG (n.val + 46000) < 2 ^ 1771 := by decide
private theorem cs_w21 : ∀ n : Fin 50, centredStar (densSupG (n.val + 46050)) (centF (n.val + 46050)) = true := by decide
private theorem cl_w21 : ∀ n : Fin 50, centF (n.val + 46050) < 23 := by decide
private theorem bd_w21 : ∀ n : Fin 50, densSupG (n.val + 46050) < 2 ^ 1771 := by decide
private theorem cs_w22 : ∀ n : Fin 50, centredStar (densSupG (n.val + 46100)) (centF (n.val + 46100)) = true := by decide
private theorem cl_w22 : ∀ n : Fin 50, centF (n.val + 46100) < 23 := by decide
private theorem bd_w22 : ∀ n : Fin 50, densSupG (n.val + 46100) < 2 ^ 1771 := by decide
private theorem cs_w23 : ∀ n : Fin 50, centredStar (densSupG (n.val + 46150)) (centF (n.val + 46150)) = true := by decide
private theorem cl_w23 : ∀ n : Fin 50, centF (n.val + 46150) < 23 := by decide
private theorem bd_w23 : ∀ n : Fin 50, densSupG (n.val + 46150) < 2 ^ 1771 := by decide
private theorem cs_w24 : ∀ n : Fin 50, centredStar (densSupG (n.val + 46200)) (centF (n.val + 46200)) = true := by decide
private theorem cl_w24 : ∀ n : Fin 50, centF (n.val + 46200) < 23 := by decide
private theorem bd_w24 : ∀ n : Fin 50, densSupG (n.val + 46200) < 2 ^ 1771 := by decide
private theorem cs_w25 : ∀ n : Fin 50, centredStar (densSupG (n.val + 46250)) (centF (n.val + 46250)) = true := by decide
private theorem cl_w25 : ∀ n : Fin 50, centF (n.val + 46250) < 23 := by decide
private theorem bd_w25 : ∀ n : Fin 50, densSupG (n.val + 46250) < 2 ^ 1771 := by decide
private theorem cs_w26 : ∀ n : Fin 50, centredStar (densSupG (n.val + 46300)) (centF (n.val + 46300)) = true := by decide
private theorem cl_w26 : ∀ n : Fin 50, centF (n.val + 46300) < 23 := by decide
private theorem bd_w26 : ∀ n : Fin 50, densSupG (n.val + 46300) < 2 ^ 1771 := by decide
private theorem cs_w27 : ∀ n : Fin 50, centredStar (densSupG (n.val + 46350)) (centF (n.val + 46350)) = true := by decide
private theorem cl_w27 : ∀ n : Fin 50, centF (n.val + 46350) < 23 := by decide
private theorem bd_w27 : ∀ n : Fin 50, densSupG (n.val + 46350) < 2 ^ 1771 := by decide
private theorem cs_w28 : ∀ n : Fin 50, centredStar (densSupG (n.val + 46400)) (centF (n.val + 46400)) = true := by decide
private theorem cl_w28 : ∀ n : Fin 50, centF (n.val + 46400) < 23 := by decide
private theorem bd_w28 : ∀ n : Fin 50, densSupG (n.val + 46400) < 2 ^ 1771 := by decide
private theorem cs_w29 : ∀ n : Fin 50, centredStar (densSupG (n.val + 46450)) (centF (n.val + 46450)) = true := by decide
private theorem cl_w29 : ∀ n : Fin 50, centF (n.val + 46450) < 23 := by decide
private theorem bd_w29 : ∀ n : Fin 50, densSupG (n.val + 46450) < 2 ^ 1771 := by decide
private theorem cs_w30 : ∀ n : Fin 50, centredStar (densSupG (n.val + 46500)) (centF (n.val + 46500)) = true := by decide
private theorem cl_w30 : ∀ n : Fin 50, centF (n.val + 46500) < 23 := by decide
private theorem bd_w30 : ∀ n : Fin 50, densSupG (n.val + 46500) < 2 ^ 1771 := by decide
private theorem cs_w31 : ∀ n : Fin 50, centredStar (densSupG (n.val + 46550)) (centF (n.val + 46550)) = true := by decide
private theorem cl_w31 : ∀ n : Fin 50, centF (n.val + 46550) < 23 := by decide
private theorem bd_w31 : ∀ n : Fin 50, densSupG (n.val + 46550) < 2 ^ 1771 := by decide
private theorem cs_w32 : ∀ n : Fin 50, centredStar (densSupG (n.val + 46600)) (centF (n.val + 46600)) = true := by decide
private theorem cl_w32 : ∀ n : Fin 50, centF (n.val + 46600) < 23 := by decide
private theorem bd_w32 : ∀ n : Fin 50, densSupG (n.val + 46600) < 2 ^ 1771 := by decide
private theorem cs_w33 : ∀ n : Fin 50, centredStar (densSupG (n.val + 46650)) (centF (n.val + 46650)) = true := by decide
private theorem cl_w33 : ∀ n : Fin 50, centF (n.val + 46650) < 23 := by decide
private theorem bd_w33 : ∀ n : Fin 50, densSupG (n.val + 46650) < 2 ^ 1771 := by decide
private theorem cs_w34 : ∀ n : Fin 50, centredStar (densSupG (n.val + 46700)) (centF (n.val + 46700)) = true := by decide
private theorem cl_w34 : ∀ n : Fin 50, centF (n.val + 46700) < 23 := by decide
private theorem bd_w34 : ∀ n : Fin 50, densSupG (n.val + 46700) < 2 ^ 1771 := by decide
private theorem cs_w35 : ∀ n : Fin 50, centredStar (densSupG (n.val + 46750)) (centF (n.val + 46750)) = true := by decide
private theorem cl_w35 : ∀ n : Fin 50, centF (n.val + 46750) < 23 := by decide
private theorem bd_w35 : ∀ n : Fin 50, densSupG (n.val + 46750) < 2 ^ 1771 := by decide
private theorem cs_w36 : ∀ n : Fin 50, centredStar (densSupG (n.val + 46800)) (centF (n.val + 46800)) = true := by decide
private theorem cl_w36 : ∀ n : Fin 50, centF (n.val + 46800) < 23 := by decide
private theorem bd_w36 : ∀ n : Fin 50, densSupG (n.val + 46800) < 2 ^ 1771 := by decide
private theorem cs_w37 : ∀ n : Fin 50, centredStar (densSupG (n.val + 46850)) (centF (n.val + 46850)) = true := by decide
private theorem cl_w37 : ∀ n : Fin 50, centF (n.val + 46850) < 23 := by decide
private theorem bd_w37 : ∀ n : Fin 50, densSupG (n.val + 46850) < 2 ^ 1771 := by decide
private theorem cs_w38 : ∀ n : Fin 50, centredStar (densSupG (n.val + 46900)) (centF (n.val + 46900)) = true := by decide
private theorem cl_w38 : ∀ n : Fin 50, centF (n.val + 46900) < 23 := by decide
private theorem bd_w38 : ∀ n : Fin 50, densSupG (n.val + 46900) < 2 ^ 1771 := by decide
private theorem cs_w39 : ∀ n : Fin 50, centredStar (densSupG (n.val + 46950)) (centF (n.val + 46950)) = true := by decide
private theorem cl_w39 : ∀ n : Fin 50, centF (n.val + 46950) < 23 := by decide
private theorem bd_w39 : ∀ n : Fin 50, densSupG (n.val + 46950) < 2 ^ 1771 := by decide
private theorem cs_w40 : ∀ n : Fin 50, centredStar (densSupG (n.val + 47000)) (centF (n.val + 47000)) = true := by decide
private theorem cl_w40 : ∀ n : Fin 50, centF (n.val + 47000) < 23 := by decide
private theorem bd_w40 : ∀ n : Fin 50, densSupG (n.val + 47000) < 2 ^ 1771 := by decide
private theorem cs_w41 : ∀ n : Fin 50, centredStar (densSupG (n.val + 47050)) (centF (n.val + 47050)) = true := by decide
private theorem cl_w41 : ∀ n : Fin 50, centF (n.val + 47050) < 23 := by decide
private theorem bd_w41 : ∀ n : Fin 50, densSupG (n.val + 47050) < 2 ^ 1771 := by decide
private theorem cs_w42 : ∀ n : Fin 50, centredStar (densSupG (n.val + 47100)) (centF (n.val + 47100)) = true := by decide
private theorem cl_w42 : ∀ n : Fin 50, centF (n.val + 47100) < 23 := by decide
private theorem bd_w42 : ∀ n : Fin 50, densSupG (n.val + 47100) < 2 ^ 1771 := by decide
private theorem cs_w43 : ∀ n : Fin 50, centredStar (densSupG (n.val + 47150)) (centF (n.val + 47150)) = true := by decide
private theorem cl_w43 : ∀ n : Fin 50, centF (n.val + 47150) < 23 := by decide
private theorem bd_w43 : ∀ n : Fin 50, densSupG (n.val + 47150) < 2 ^ 1771 := by decide
private theorem cs_w44 : ∀ n : Fin 50, centredStar (densSupG (n.val + 47200)) (centF (n.val + 47200)) = true := by decide
private theorem cl_w44 : ∀ n : Fin 50, centF (n.val + 47200) < 23 := by decide
private theorem bd_w44 : ∀ n : Fin 50, densSupG (n.val + 47200) < 2 ^ 1771 := by decide
private theorem cs_w45 : ∀ n : Fin 50, centredStar (densSupG (n.val + 47250)) (centF (n.val + 47250)) = true := by decide
private theorem cl_w45 : ∀ n : Fin 50, centF (n.val + 47250) < 23 := by decide
private theorem bd_w45 : ∀ n : Fin 50, densSupG (n.val + 47250) < 2 ^ 1771 := by decide
private theorem cs_w46 : ∀ n : Fin 50, centredStar (densSupG (n.val + 47300)) (centF (n.val + 47300)) = true := by decide
private theorem cl_w46 : ∀ n : Fin 50, centF (n.val + 47300) < 23 := by decide
private theorem bd_w46 : ∀ n : Fin 50, densSupG (n.val + 47300) < 2 ^ 1771 := by decide
private theorem cs_w47 : ∀ n : Fin 50, centredStar (densSupG (n.val + 47350)) (centF (n.val + 47350)) = true := by decide
private theorem cl_w47 : ∀ n : Fin 50, centF (n.val + 47350) < 23 := by decide
private theorem bd_w47 : ∀ n : Fin 50, densSupG (n.val + 47350) < 2 ^ 1771 := by decide
private theorem cs_w48 : ∀ n : Fin 50, centredStar (densSupG (n.val + 47400)) (centF (n.val + 47400)) = true := by decide
private theorem cl_w48 : ∀ n : Fin 50, centF (n.val + 47400) < 23 := by decide
private theorem bd_w48 : ∀ n : Fin 50, densSupG (n.val + 47400) < 2 ^ 1771 := by decide
private theorem cs_w49 : ∀ n : Fin 50, centredStar (densSupG (n.val + 47450)) (centF (n.val + 47450)) = true := by decide
private theorem cl_w49 : ∀ n : Fin 50, centF (n.val + 47450) < 23 := by decide
private theorem bd_w49 : ∀ n : Fin 50, densSupG (n.val + 47450) < 2 ^ 1771 := by decide
theorem centredStar_range : ∀ n, 45000 ≤ n → n < 47500 → centredStar (densSupG n) (centF n) = true := by
  intro n hlo hhi
  by_cases h0 : n < 45050
  · have hr : n - 45000 < 50 := by omega
    have heq : n = (n - 45000) + 45000 := by omega
    rw [heq]
    exact cs_w0 ⟨n - 45000, hr⟩
  ·
    by_cases h1 : n < 45100
    ·
      have hr : n - 45050 < 50 := by omega
      have heq : n = (n - 45050) + 45050 := by omega
      rw [heq]
      exact cs_w1 ⟨n - 45050, hr⟩
    ·
      by_cases h2 : n < 45150
      ·
        have hr : n - 45100 < 50 := by omega
        have heq : n = (n - 45100) + 45100 := by omega
        rw [heq]
        exact cs_w2 ⟨n - 45100, hr⟩
      ·
        by_cases h3 : n < 45200
        ·
          have hr : n - 45150 < 50 := by omega
          have heq : n = (n - 45150) + 45150 := by omega
          rw [heq]
          exact cs_w3 ⟨n - 45150, hr⟩
        ·
          by_cases h4 : n < 45250
          ·
            have hr : n - 45200 < 50 := by omega
            have heq : n = (n - 45200) + 45200 := by omega
            rw [heq]
            exact cs_w4 ⟨n - 45200, hr⟩
          ·
            by_cases h5 : n < 45300
            ·
              have hr : n - 45250 < 50 := by omega
              have heq : n = (n - 45250) + 45250 := by omega
              rw [heq]
              exact cs_w5 ⟨n - 45250, hr⟩
            ·
              by_cases h6 : n < 45350
              ·
                have hr : n - 45300 < 50 := by omega
                have heq : n = (n - 45300) + 45300 := by omega
                rw [heq]
                exact cs_w6 ⟨n - 45300, hr⟩
              ·
                by_cases h7 : n < 45400
                ·
                  have hr : n - 45350 < 50 := by omega
                  have heq : n = (n - 45350) + 45350 := by omega
                  rw [heq]
                  exact cs_w7 ⟨n - 45350, hr⟩
                ·
                  by_cases h8 : n < 45450
                  ·
                    have hr : n - 45400 < 50 := by omega
                    have heq : n = (n - 45400) + 45400 := by omega
                    rw [heq]
                    exact cs_w8 ⟨n - 45400, hr⟩
                  ·
                    by_cases h9 : n < 45500
                    ·
                      have hr : n - 45450 < 50 := by omega
                      have heq : n = (n - 45450) + 45450 := by omega
                      rw [heq]
                      exact cs_w9 ⟨n - 45450, hr⟩
                    ·
                      by_cases h10 : n < 45550
                      ·
                        have hr : n - 45500 < 50 := by omega
                        have heq : n = (n - 45500) + 45500 := by omega
                        rw [heq]
                        exact cs_w10 ⟨n - 45500, hr⟩
                      ·
                        by_cases h11 : n < 45600
                        ·
                          have hr : n - 45550 < 50 := by omega
                          have heq : n = (n - 45550) + 45550 := by omega
                          rw [heq]
                          exact cs_w11 ⟨n - 45550, hr⟩
                        ·
                          by_cases h12 : n < 45650
                          ·
                            have hr : n - 45600 < 50 := by omega
                            have heq : n = (n - 45600) + 45600 := by omega
                            rw [heq]
                            exact cs_w12 ⟨n - 45600, hr⟩
                          ·
                            by_cases h13 : n < 45700
                            ·
                              have hr : n - 45650 < 50 := by omega
                              have heq : n = (n - 45650) + 45650 := by omega
                              rw [heq]
                              exact cs_w13 ⟨n - 45650, hr⟩
                            ·
                              by_cases h14 : n < 45750
                              ·
                                have hr : n - 45700 < 50 := by omega
                                have heq : n = (n - 45700) + 45700 := by omega
                                rw [heq]
                                exact cs_w14 ⟨n - 45700, hr⟩
                              ·
                                by_cases h15 : n < 45800
                                ·
                                  have hr : n - 45750 < 50 := by omega
                                  have heq : n = (n - 45750) + 45750 := by omega
                                  rw [heq]
                                  exact cs_w15 ⟨n - 45750, hr⟩
                                ·
                                  by_cases h16 : n < 45850
                                  ·
                                    have hr : n - 45800 < 50 := by omega
                                    have heq : n = (n - 45800) + 45800 := by omega
                                    rw [heq]
                                    exact cs_w16 ⟨n - 45800, hr⟩
                                  ·
                                    by_cases h17 : n < 45900
                                    ·
                                      have hr : n - 45850 < 50 := by omega
                                      have heq : n = (n - 45850) + 45850 := by omega
                                      rw [heq]
                                      exact cs_w17 ⟨n - 45850, hr⟩
                                    ·
                                      by_cases h18 : n < 45950
                                      ·
                                        have hr : n - 45900 < 50 := by omega
                                        have heq : n = (n - 45900) + 45900 := by omega
                                        rw [heq]
                                        exact cs_w18 ⟨n - 45900, hr⟩
                                      ·
                                        by_cases h19 : n < 46000
                                        ·
                                          have hr : n - 45950 < 50 := by omega
                                          have heq : n = (n - 45950) + 45950 := by omega
                                          rw [heq]
                                          exact cs_w19 ⟨n - 45950, hr⟩
                                        ·
                                          by_cases h20 : n < 46050
                                          ·
                                            have hr : n - 46000 < 50 := by omega
                                            have heq : n = (n - 46000) + 46000 := by omega
                                            rw [heq]
                                            exact cs_w20 ⟨n - 46000, hr⟩
                                          ·
                                            by_cases h21 : n < 46100
                                            ·
                                              have hr : n - 46050 < 50 := by omega
                                              have heq : n = (n - 46050) + 46050 := by omega
                                              rw [heq]
                                              exact cs_w21 ⟨n - 46050, hr⟩
                                            ·
                                              by_cases h22 : n < 46150
                                              ·
                                                have hr : n - 46100 < 50 := by omega
                                                have heq : n = (n - 46100) + 46100 := by omega
                                                rw [heq]
                                                exact cs_w22 ⟨n - 46100, hr⟩
                                              ·
                                                by_cases h23 : n < 46200
                                                ·
                                                  have hr : n - 46150 < 50 := by omega
                                                  have heq : n = (n - 46150) + 46150 := by omega
                                                  rw [heq]
                                                  exact cs_w23 ⟨n - 46150, hr⟩
                                                ·
                                                  by_cases h24 : n < 46250
                                                  ·
                                                    have hr : n - 46200 < 50 := by omega
                                                    have heq : n = (n - 46200) + 46200 := by omega
                                                    rw [heq]
                                                    exact cs_w24 ⟨n - 46200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 46300
                                                    ·
                                                      have hr : n - 46250 < 50 := by omega
                                                      have heq : n = (n - 46250) + 46250 := by omega
                                                      rw [heq]
                                                      exact cs_w25 ⟨n - 46250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 46350
                                                      ·
                                                        have hr : n - 46300 < 50 := by omega
                                                        have heq : n = (n - 46300) + 46300 := by omega
                                                        rw [heq]
                                                        exact cs_w26 ⟨n - 46300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 46400
                                                        ·
                                                          have hr : n - 46350 < 50 := by omega
                                                          have heq : n = (n - 46350) + 46350 := by omega
                                                          rw [heq]
                                                          exact cs_w27 ⟨n - 46350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 46450
                                                          ·
                                                            have hr : n - 46400 < 50 := by omega
                                                            have heq : n = (n - 46400) + 46400 := by omega
                                                            rw [heq]
                                                            exact cs_w28 ⟨n - 46400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 46500
                                                            ·
                                                              have hr : n - 46450 < 50 := by omega
                                                              have heq : n = (n - 46450) + 46450 := by omega
                                                              rw [heq]
                                                              exact cs_w29 ⟨n - 46450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 46550
                                                              ·
                                                                have hr : n - 46500 < 50 := by omega
                                                                have heq : n = (n - 46500) + 46500 := by omega
                                                                rw [heq]
                                                                exact cs_w30 ⟨n - 46500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 46600
                                                                ·
                                                                  have hr : n - 46550 < 50 := by omega
                                                                  have heq : n = (n - 46550) + 46550 := by omega
                                                                  rw [heq]
                                                                  exact cs_w31 ⟨n - 46550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 46650
                                                                  ·
                                                                    have hr : n - 46600 < 50 := by omega
                                                                    have heq : n = (n - 46600) + 46600 := by omega
                                                                    rw [heq]
                                                                    exact cs_w32 ⟨n - 46600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 46700
                                                                    ·
                                                                      have hr : n - 46650 < 50 := by omega
                                                                      have heq : n = (n - 46650) + 46650 := by omega
                                                                      rw [heq]
                                                                      exact cs_w33 ⟨n - 46650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 46750
                                                                      ·
                                                                        have hr : n - 46700 < 50 := by omega
                                                                        have heq : n = (n - 46700) + 46700 := by omega
                                                                        rw [heq]
                                                                        exact cs_w34 ⟨n - 46700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 46800
                                                                        ·
                                                                          have hr : n - 46750 < 50 := by omega
                                                                          have heq : n = (n - 46750) + 46750 := by omega
                                                                          rw [heq]
                                                                          exact cs_w35 ⟨n - 46750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 46850
                                                                          ·
                                                                            have hr : n - 46800 < 50 := by omega
                                                                            have heq : n = (n - 46800) + 46800 := by omega
                                                                            rw [heq]
                                                                            exact cs_w36 ⟨n - 46800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 46900
                                                                            ·
                                                                              have hr : n - 46850 < 50 := by omega
                                                                              have heq : n = (n - 46850) + 46850 := by omega
                                                                              rw [heq]
                                                                              exact cs_w37 ⟨n - 46850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 46950
                                                                              ·
                                                                                have hr : n - 46900 < 50 := by omega
                                                                                have heq : n = (n - 46900) + 46900 := by omega
                                                                                rw [heq]
                                                                                exact cs_w38 ⟨n - 46900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 47000
                                                                                ·
                                                                                  have hr : n - 46950 < 50 := by omega
                                                                                  have heq : n = (n - 46950) + 46950 := by omega
                                                                                  rw [heq]
                                                                                  exact cs_w39 ⟨n - 46950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 47050
                                                                                  ·
                                                                                    have hr : n - 47000 < 50 := by omega
                                                                                    have heq : n = (n - 47000) + 47000 := by omega
                                                                                    rw [heq]
                                                                                    exact cs_w40 ⟨n - 47000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 47100
                                                                                    ·
                                                                                      have hr : n - 47050 < 50 := by omega
                                                                                      have heq : n = (n - 47050) + 47050 := by omega
                                                                                      rw [heq]
                                                                                      exact cs_w41 ⟨n - 47050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 47150
                                                                                      ·
                                                                                        have hr : n - 47100 < 50 := by omega
                                                                                        have heq : n = (n - 47100) + 47100 := by omega
                                                                                        rw [heq]
                                                                                        exact cs_w42 ⟨n - 47100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 47200
                                                                                        ·
                                                                                          have hr : n - 47150 < 50 := by omega
                                                                                          have heq : n = (n - 47150) + 47150 := by omega
                                                                                          rw [heq]
                                                                                          exact cs_w43 ⟨n - 47150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 47250
                                                                                          ·
                                                                                            have hr : n - 47200 < 50 := by omega
                                                                                            have heq : n = (n - 47200) + 47200 := by omega
                                                                                            rw [heq]
                                                                                            exact cs_w44 ⟨n - 47200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 47300
                                                                                            ·
                                                                                              have hr : n - 47250 < 50 := by omega
                                                                                              have heq : n = (n - 47250) + 47250 := by omega
                                                                                              rw [heq]
                                                                                              exact cs_w45 ⟨n - 47250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 47350
                                                                                              ·
                                                                                                have hr : n - 47300 < 50 := by omega
                                                                                                have heq : n = (n - 47300) + 47300 := by omega
                                                                                                rw [heq]
                                                                                                exact cs_w46 ⟨n - 47300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 47400
                                                                                                ·
                                                                                                  have hr : n - 47350 < 50 := by omega
                                                                                                  have heq : n = (n - 47350) + 47350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cs_w47 ⟨n - 47350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 47450
                                                                                                  ·
                                                                                                    have hr : n - 47400 < 50 := by omega
                                                                                                    have heq : n = (n - 47400) + 47400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w48 ⟨n - 47400, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 47450 < 50 := by omega
                                                                                                    have heq : n = (n - 47450) + 47450 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w49 ⟨n - 47450, hr⟩


theorem centF_lt_range : ∀ n, 45000 ≤ n → n < 47500 → centF n < 23 := by
  intro n hlo hhi
  by_cases h0 : n < 45050
  · have hr : n - 45000 < 50 := by omega
    have heq : n = (n - 45000) + 45000 := by omega
    rw [heq]
    exact cl_w0 ⟨n - 45000, hr⟩
  ·
    by_cases h1 : n < 45100
    ·
      have hr : n - 45050 < 50 := by omega
      have heq : n = (n - 45050) + 45050 := by omega
      rw [heq]
      exact cl_w1 ⟨n - 45050, hr⟩
    ·
      by_cases h2 : n < 45150
      ·
        have hr : n - 45100 < 50 := by omega
        have heq : n = (n - 45100) + 45100 := by omega
        rw [heq]
        exact cl_w2 ⟨n - 45100, hr⟩
      ·
        by_cases h3 : n < 45200
        ·
          have hr : n - 45150 < 50 := by omega
          have heq : n = (n - 45150) + 45150 := by omega
          rw [heq]
          exact cl_w3 ⟨n - 45150, hr⟩
        ·
          by_cases h4 : n < 45250
          ·
            have hr : n - 45200 < 50 := by omega
            have heq : n = (n - 45200) + 45200 := by omega
            rw [heq]
            exact cl_w4 ⟨n - 45200, hr⟩
          ·
            by_cases h5 : n < 45300
            ·
              have hr : n - 45250 < 50 := by omega
              have heq : n = (n - 45250) + 45250 := by omega
              rw [heq]
              exact cl_w5 ⟨n - 45250, hr⟩
            ·
              by_cases h6 : n < 45350
              ·
                have hr : n - 45300 < 50 := by omega
                have heq : n = (n - 45300) + 45300 := by omega
                rw [heq]
                exact cl_w6 ⟨n - 45300, hr⟩
              ·
                by_cases h7 : n < 45400
                ·
                  have hr : n - 45350 < 50 := by omega
                  have heq : n = (n - 45350) + 45350 := by omega
                  rw [heq]
                  exact cl_w7 ⟨n - 45350, hr⟩
                ·
                  by_cases h8 : n < 45450
                  ·
                    have hr : n - 45400 < 50 := by omega
                    have heq : n = (n - 45400) + 45400 := by omega
                    rw [heq]
                    exact cl_w8 ⟨n - 45400, hr⟩
                  ·
                    by_cases h9 : n < 45500
                    ·
                      have hr : n - 45450 < 50 := by omega
                      have heq : n = (n - 45450) + 45450 := by omega
                      rw [heq]
                      exact cl_w9 ⟨n - 45450, hr⟩
                    ·
                      by_cases h10 : n < 45550
                      ·
                        have hr : n - 45500 < 50 := by omega
                        have heq : n = (n - 45500) + 45500 := by omega
                        rw [heq]
                        exact cl_w10 ⟨n - 45500, hr⟩
                      ·
                        by_cases h11 : n < 45600
                        ·
                          have hr : n - 45550 < 50 := by omega
                          have heq : n = (n - 45550) + 45550 := by omega
                          rw [heq]
                          exact cl_w11 ⟨n - 45550, hr⟩
                        ·
                          by_cases h12 : n < 45650
                          ·
                            have hr : n - 45600 < 50 := by omega
                            have heq : n = (n - 45600) + 45600 := by omega
                            rw [heq]
                            exact cl_w12 ⟨n - 45600, hr⟩
                          ·
                            by_cases h13 : n < 45700
                            ·
                              have hr : n - 45650 < 50 := by omega
                              have heq : n = (n - 45650) + 45650 := by omega
                              rw [heq]
                              exact cl_w13 ⟨n - 45650, hr⟩
                            ·
                              by_cases h14 : n < 45750
                              ·
                                have hr : n - 45700 < 50 := by omega
                                have heq : n = (n - 45700) + 45700 := by omega
                                rw [heq]
                                exact cl_w14 ⟨n - 45700, hr⟩
                              ·
                                by_cases h15 : n < 45800
                                ·
                                  have hr : n - 45750 < 50 := by omega
                                  have heq : n = (n - 45750) + 45750 := by omega
                                  rw [heq]
                                  exact cl_w15 ⟨n - 45750, hr⟩
                                ·
                                  by_cases h16 : n < 45850
                                  ·
                                    have hr : n - 45800 < 50 := by omega
                                    have heq : n = (n - 45800) + 45800 := by omega
                                    rw [heq]
                                    exact cl_w16 ⟨n - 45800, hr⟩
                                  ·
                                    by_cases h17 : n < 45900
                                    ·
                                      have hr : n - 45850 < 50 := by omega
                                      have heq : n = (n - 45850) + 45850 := by omega
                                      rw [heq]
                                      exact cl_w17 ⟨n - 45850, hr⟩
                                    ·
                                      by_cases h18 : n < 45950
                                      ·
                                        have hr : n - 45900 < 50 := by omega
                                        have heq : n = (n - 45900) + 45900 := by omega
                                        rw [heq]
                                        exact cl_w18 ⟨n - 45900, hr⟩
                                      ·
                                        by_cases h19 : n < 46000
                                        ·
                                          have hr : n - 45950 < 50 := by omega
                                          have heq : n = (n - 45950) + 45950 := by omega
                                          rw [heq]
                                          exact cl_w19 ⟨n - 45950, hr⟩
                                        ·
                                          by_cases h20 : n < 46050
                                          ·
                                            have hr : n - 46000 < 50 := by omega
                                            have heq : n = (n - 46000) + 46000 := by omega
                                            rw [heq]
                                            exact cl_w20 ⟨n - 46000, hr⟩
                                          ·
                                            by_cases h21 : n < 46100
                                            ·
                                              have hr : n - 46050 < 50 := by omega
                                              have heq : n = (n - 46050) + 46050 := by omega
                                              rw [heq]
                                              exact cl_w21 ⟨n - 46050, hr⟩
                                            ·
                                              by_cases h22 : n < 46150
                                              ·
                                                have hr : n - 46100 < 50 := by omega
                                                have heq : n = (n - 46100) + 46100 := by omega
                                                rw [heq]
                                                exact cl_w22 ⟨n - 46100, hr⟩
                                              ·
                                                by_cases h23 : n < 46200
                                                ·
                                                  have hr : n - 46150 < 50 := by omega
                                                  have heq : n = (n - 46150) + 46150 := by omega
                                                  rw [heq]
                                                  exact cl_w23 ⟨n - 46150, hr⟩
                                                ·
                                                  by_cases h24 : n < 46250
                                                  ·
                                                    have hr : n - 46200 < 50 := by omega
                                                    have heq : n = (n - 46200) + 46200 := by omega
                                                    rw [heq]
                                                    exact cl_w24 ⟨n - 46200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 46300
                                                    ·
                                                      have hr : n - 46250 < 50 := by omega
                                                      have heq : n = (n - 46250) + 46250 := by omega
                                                      rw [heq]
                                                      exact cl_w25 ⟨n - 46250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 46350
                                                      ·
                                                        have hr : n - 46300 < 50 := by omega
                                                        have heq : n = (n - 46300) + 46300 := by omega
                                                        rw [heq]
                                                        exact cl_w26 ⟨n - 46300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 46400
                                                        ·
                                                          have hr : n - 46350 < 50 := by omega
                                                          have heq : n = (n - 46350) + 46350 := by omega
                                                          rw [heq]
                                                          exact cl_w27 ⟨n - 46350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 46450
                                                          ·
                                                            have hr : n - 46400 < 50 := by omega
                                                            have heq : n = (n - 46400) + 46400 := by omega
                                                            rw [heq]
                                                            exact cl_w28 ⟨n - 46400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 46500
                                                            ·
                                                              have hr : n - 46450 < 50 := by omega
                                                              have heq : n = (n - 46450) + 46450 := by omega
                                                              rw [heq]
                                                              exact cl_w29 ⟨n - 46450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 46550
                                                              ·
                                                                have hr : n - 46500 < 50 := by omega
                                                                have heq : n = (n - 46500) + 46500 := by omega
                                                                rw [heq]
                                                                exact cl_w30 ⟨n - 46500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 46600
                                                                ·
                                                                  have hr : n - 46550 < 50 := by omega
                                                                  have heq : n = (n - 46550) + 46550 := by omega
                                                                  rw [heq]
                                                                  exact cl_w31 ⟨n - 46550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 46650
                                                                  ·
                                                                    have hr : n - 46600 < 50 := by omega
                                                                    have heq : n = (n - 46600) + 46600 := by omega
                                                                    rw [heq]
                                                                    exact cl_w32 ⟨n - 46600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 46700
                                                                    ·
                                                                      have hr : n - 46650 < 50 := by omega
                                                                      have heq : n = (n - 46650) + 46650 := by omega
                                                                      rw [heq]
                                                                      exact cl_w33 ⟨n - 46650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 46750
                                                                      ·
                                                                        have hr : n - 46700 < 50 := by omega
                                                                        have heq : n = (n - 46700) + 46700 := by omega
                                                                        rw [heq]
                                                                        exact cl_w34 ⟨n - 46700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 46800
                                                                        ·
                                                                          have hr : n - 46750 < 50 := by omega
                                                                          have heq : n = (n - 46750) + 46750 := by omega
                                                                          rw [heq]
                                                                          exact cl_w35 ⟨n - 46750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 46850
                                                                          ·
                                                                            have hr : n - 46800 < 50 := by omega
                                                                            have heq : n = (n - 46800) + 46800 := by omega
                                                                            rw [heq]
                                                                            exact cl_w36 ⟨n - 46800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 46900
                                                                            ·
                                                                              have hr : n - 46850 < 50 := by omega
                                                                              have heq : n = (n - 46850) + 46850 := by omega
                                                                              rw [heq]
                                                                              exact cl_w37 ⟨n - 46850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 46950
                                                                              ·
                                                                                have hr : n - 46900 < 50 := by omega
                                                                                have heq : n = (n - 46900) + 46900 := by omega
                                                                                rw [heq]
                                                                                exact cl_w38 ⟨n - 46900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 47000
                                                                                ·
                                                                                  have hr : n - 46950 < 50 := by omega
                                                                                  have heq : n = (n - 46950) + 46950 := by omega
                                                                                  rw [heq]
                                                                                  exact cl_w39 ⟨n - 46950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 47050
                                                                                  ·
                                                                                    have hr : n - 47000 < 50 := by omega
                                                                                    have heq : n = (n - 47000) + 47000 := by omega
                                                                                    rw [heq]
                                                                                    exact cl_w40 ⟨n - 47000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 47100
                                                                                    ·
                                                                                      have hr : n - 47050 < 50 := by omega
                                                                                      have heq : n = (n - 47050) + 47050 := by omega
                                                                                      rw [heq]
                                                                                      exact cl_w41 ⟨n - 47050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 47150
                                                                                      ·
                                                                                        have hr : n - 47100 < 50 := by omega
                                                                                        have heq : n = (n - 47100) + 47100 := by omega
                                                                                        rw [heq]
                                                                                        exact cl_w42 ⟨n - 47100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 47200
                                                                                        ·
                                                                                          have hr : n - 47150 < 50 := by omega
                                                                                          have heq : n = (n - 47150) + 47150 := by omega
                                                                                          rw [heq]
                                                                                          exact cl_w43 ⟨n - 47150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 47250
                                                                                          ·
                                                                                            have hr : n - 47200 < 50 := by omega
                                                                                            have heq : n = (n - 47200) + 47200 := by omega
                                                                                            rw [heq]
                                                                                            exact cl_w44 ⟨n - 47200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 47300
                                                                                            ·
                                                                                              have hr : n - 47250 < 50 := by omega
                                                                                              have heq : n = (n - 47250) + 47250 := by omega
                                                                                              rw [heq]
                                                                                              exact cl_w45 ⟨n - 47250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 47350
                                                                                              ·
                                                                                                have hr : n - 47300 < 50 := by omega
                                                                                                have heq : n = (n - 47300) + 47300 := by omega
                                                                                                rw [heq]
                                                                                                exact cl_w46 ⟨n - 47300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 47400
                                                                                                ·
                                                                                                  have hr : n - 47350 < 50 := by omega
                                                                                                  have heq : n = (n - 47350) + 47350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cl_w47 ⟨n - 47350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 47450
                                                                                                  ·
                                                                                                    have hr : n - 47400 < 50 := by omega
                                                                                                    have heq : n = (n - 47400) + 47400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w48 ⟨n - 47400, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 47450 < 50 := by omega
                                                                                                    have heq : n = (n - 47450) + 47450 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w49 ⟨n - 47450, hr⟩


theorem densSupG_lt_range : ∀ n, 45000 ≤ n → n < 47500 → densSupG n < 2 ^ 1771 := by
  intro n hlo hhi
  by_cases h0 : n < 45050
  · have hr : n - 45000 < 50 := by omega
    have heq : n = (n - 45000) + 45000 := by omega
    rw [heq]
    exact bd_w0 ⟨n - 45000, hr⟩
  ·
    by_cases h1 : n < 45100
    ·
      have hr : n - 45050 < 50 := by omega
      have heq : n = (n - 45050) + 45050 := by omega
      rw [heq]
      exact bd_w1 ⟨n - 45050, hr⟩
    ·
      by_cases h2 : n < 45150
      ·
        have hr : n - 45100 < 50 := by omega
        have heq : n = (n - 45100) + 45100 := by omega
        rw [heq]
        exact bd_w2 ⟨n - 45100, hr⟩
      ·
        by_cases h3 : n < 45200
        ·
          have hr : n - 45150 < 50 := by omega
          have heq : n = (n - 45150) + 45150 := by omega
          rw [heq]
          exact bd_w3 ⟨n - 45150, hr⟩
        ·
          by_cases h4 : n < 45250
          ·
            have hr : n - 45200 < 50 := by omega
            have heq : n = (n - 45200) + 45200 := by omega
            rw [heq]
            exact bd_w4 ⟨n - 45200, hr⟩
          ·
            by_cases h5 : n < 45300
            ·
              have hr : n - 45250 < 50 := by omega
              have heq : n = (n - 45250) + 45250 := by omega
              rw [heq]
              exact bd_w5 ⟨n - 45250, hr⟩
            ·
              by_cases h6 : n < 45350
              ·
                have hr : n - 45300 < 50 := by omega
                have heq : n = (n - 45300) + 45300 := by omega
                rw [heq]
                exact bd_w6 ⟨n - 45300, hr⟩
              ·
                by_cases h7 : n < 45400
                ·
                  have hr : n - 45350 < 50 := by omega
                  have heq : n = (n - 45350) + 45350 := by omega
                  rw [heq]
                  exact bd_w7 ⟨n - 45350, hr⟩
                ·
                  by_cases h8 : n < 45450
                  ·
                    have hr : n - 45400 < 50 := by omega
                    have heq : n = (n - 45400) + 45400 := by omega
                    rw [heq]
                    exact bd_w8 ⟨n - 45400, hr⟩
                  ·
                    by_cases h9 : n < 45500
                    ·
                      have hr : n - 45450 < 50 := by omega
                      have heq : n = (n - 45450) + 45450 := by omega
                      rw [heq]
                      exact bd_w9 ⟨n - 45450, hr⟩
                    ·
                      by_cases h10 : n < 45550
                      ·
                        have hr : n - 45500 < 50 := by omega
                        have heq : n = (n - 45500) + 45500 := by omega
                        rw [heq]
                        exact bd_w10 ⟨n - 45500, hr⟩
                      ·
                        by_cases h11 : n < 45600
                        ·
                          have hr : n - 45550 < 50 := by omega
                          have heq : n = (n - 45550) + 45550 := by omega
                          rw [heq]
                          exact bd_w11 ⟨n - 45550, hr⟩
                        ·
                          by_cases h12 : n < 45650
                          ·
                            have hr : n - 45600 < 50 := by omega
                            have heq : n = (n - 45600) + 45600 := by omega
                            rw [heq]
                            exact bd_w12 ⟨n - 45600, hr⟩
                          ·
                            by_cases h13 : n < 45700
                            ·
                              have hr : n - 45650 < 50 := by omega
                              have heq : n = (n - 45650) + 45650 := by omega
                              rw [heq]
                              exact bd_w13 ⟨n - 45650, hr⟩
                            ·
                              by_cases h14 : n < 45750
                              ·
                                have hr : n - 45700 < 50 := by omega
                                have heq : n = (n - 45700) + 45700 := by omega
                                rw [heq]
                                exact bd_w14 ⟨n - 45700, hr⟩
                              ·
                                by_cases h15 : n < 45800
                                ·
                                  have hr : n - 45750 < 50 := by omega
                                  have heq : n = (n - 45750) + 45750 := by omega
                                  rw [heq]
                                  exact bd_w15 ⟨n - 45750, hr⟩
                                ·
                                  by_cases h16 : n < 45850
                                  ·
                                    have hr : n - 45800 < 50 := by omega
                                    have heq : n = (n - 45800) + 45800 := by omega
                                    rw [heq]
                                    exact bd_w16 ⟨n - 45800, hr⟩
                                  ·
                                    by_cases h17 : n < 45900
                                    ·
                                      have hr : n - 45850 < 50 := by omega
                                      have heq : n = (n - 45850) + 45850 := by omega
                                      rw [heq]
                                      exact bd_w17 ⟨n - 45850, hr⟩
                                    ·
                                      by_cases h18 : n < 45950
                                      ·
                                        have hr : n - 45900 < 50 := by omega
                                        have heq : n = (n - 45900) + 45900 := by omega
                                        rw [heq]
                                        exact bd_w18 ⟨n - 45900, hr⟩
                                      ·
                                        by_cases h19 : n < 46000
                                        ·
                                          have hr : n - 45950 < 50 := by omega
                                          have heq : n = (n - 45950) + 45950 := by omega
                                          rw [heq]
                                          exact bd_w19 ⟨n - 45950, hr⟩
                                        ·
                                          by_cases h20 : n < 46050
                                          ·
                                            have hr : n - 46000 < 50 := by omega
                                            have heq : n = (n - 46000) + 46000 := by omega
                                            rw [heq]
                                            exact bd_w20 ⟨n - 46000, hr⟩
                                          ·
                                            by_cases h21 : n < 46100
                                            ·
                                              have hr : n - 46050 < 50 := by omega
                                              have heq : n = (n - 46050) + 46050 := by omega
                                              rw [heq]
                                              exact bd_w21 ⟨n - 46050, hr⟩
                                            ·
                                              by_cases h22 : n < 46150
                                              ·
                                                have hr : n - 46100 < 50 := by omega
                                                have heq : n = (n - 46100) + 46100 := by omega
                                                rw [heq]
                                                exact bd_w22 ⟨n - 46100, hr⟩
                                              ·
                                                by_cases h23 : n < 46200
                                                ·
                                                  have hr : n - 46150 < 50 := by omega
                                                  have heq : n = (n - 46150) + 46150 := by omega
                                                  rw [heq]
                                                  exact bd_w23 ⟨n - 46150, hr⟩
                                                ·
                                                  by_cases h24 : n < 46250
                                                  ·
                                                    have hr : n - 46200 < 50 := by omega
                                                    have heq : n = (n - 46200) + 46200 := by omega
                                                    rw [heq]
                                                    exact bd_w24 ⟨n - 46200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 46300
                                                    ·
                                                      have hr : n - 46250 < 50 := by omega
                                                      have heq : n = (n - 46250) + 46250 := by omega
                                                      rw [heq]
                                                      exact bd_w25 ⟨n - 46250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 46350
                                                      ·
                                                        have hr : n - 46300 < 50 := by omega
                                                        have heq : n = (n - 46300) + 46300 := by omega
                                                        rw [heq]
                                                        exact bd_w26 ⟨n - 46300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 46400
                                                        ·
                                                          have hr : n - 46350 < 50 := by omega
                                                          have heq : n = (n - 46350) + 46350 := by omega
                                                          rw [heq]
                                                          exact bd_w27 ⟨n - 46350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 46450
                                                          ·
                                                            have hr : n - 46400 < 50 := by omega
                                                            have heq : n = (n - 46400) + 46400 := by omega
                                                            rw [heq]
                                                            exact bd_w28 ⟨n - 46400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 46500
                                                            ·
                                                              have hr : n - 46450 < 50 := by omega
                                                              have heq : n = (n - 46450) + 46450 := by omega
                                                              rw [heq]
                                                              exact bd_w29 ⟨n - 46450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 46550
                                                              ·
                                                                have hr : n - 46500 < 50 := by omega
                                                                have heq : n = (n - 46500) + 46500 := by omega
                                                                rw [heq]
                                                                exact bd_w30 ⟨n - 46500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 46600
                                                                ·
                                                                  have hr : n - 46550 < 50 := by omega
                                                                  have heq : n = (n - 46550) + 46550 := by omega
                                                                  rw [heq]
                                                                  exact bd_w31 ⟨n - 46550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 46650
                                                                  ·
                                                                    have hr : n - 46600 < 50 := by omega
                                                                    have heq : n = (n - 46600) + 46600 := by omega
                                                                    rw [heq]
                                                                    exact bd_w32 ⟨n - 46600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 46700
                                                                    ·
                                                                      have hr : n - 46650 < 50 := by omega
                                                                      have heq : n = (n - 46650) + 46650 := by omega
                                                                      rw [heq]
                                                                      exact bd_w33 ⟨n - 46650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 46750
                                                                      ·
                                                                        have hr : n - 46700 < 50 := by omega
                                                                        have heq : n = (n - 46700) + 46700 := by omega
                                                                        rw [heq]
                                                                        exact bd_w34 ⟨n - 46700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 46800
                                                                        ·
                                                                          have hr : n - 46750 < 50 := by omega
                                                                          have heq : n = (n - 46750) + 46750 := by omega
                                                                          rw [heq]
                                                                          exact bd_w35 ⟨n - 46750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 46850
                                                                          ·
                                                                            have hr : n - 46800 < 50 := by omega
                                                                            have heq : n = (n - 46800) + 46800 := by omega
                                                                            rw [heq]
                                                                            exact bd_w36 ⟨n - 46800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 46900
                                                                            ·
                                                                              have hr : n - 46850 < 50 := by omega
                                                                              have heq : n = (n - 46850) + 46850 := by omega
                                                                              rw [heq]
                                                                              exact bd_w37 ⟨n - 46850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 46950
                                                                              ·
                                                                                have hr : n - 46900 < 50 := by omega
                                                                                have heq : n = (n - 46900) + 46900 := by omega
                                                                                rw [heq]
                                                                                exact bd_w38 ⟨n - 46900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 47000
                                                                                ·
                                                                                  have hr : n - 46950 < 50 := by omega
                                                                                  have heq : n = (n - 46950) + 46950 := by omega
                                                                                  rw [heq]
                                                                                  exact bd_w39 ⟨n - 46950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 47050
                                                                                  ·
                                                                                    have hr : n - 47000 < 50 := by omega
                                                                                    have heq : n = (n - 47000) + 47000 := by omega
                                                                                    rw [heq]
                                                                                    exact bd_w40 ⟨n - 47000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 47100
                                                                                    ·
                                                                                      have hr : n - 47050 < 50 := by omega
                                                                                      have heq : n = (n - 47050) + 47050 := by omega
                                                                                      rw [heq]
                                                                                      exact bd_w41 ⟨n - 47050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 47150
                                                                                      ·
                                                                                        have hr : n - 47100 < 50 := by omega
                                                                                        have heq : n = (n - 47100) + 47100 := by omega
                                                                                        rw [heq]
                                                                                        exact bd_w42 ⟨n - 47100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 47200
                                                                                        ·
                                                                                          have hr : n - 47150 < 50 := by omega
                                                                                          have heq : n = (n - 47150) + 47150 := by omega
                                                                                          rw [heq]
                                                                                          exact bd_w43 ⟨n - 47150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 47250
                                                                                          ·
                                                                                            have hr : n - 47200 < 50 := by omega
                                                                                            have heq : n = (n - 47200) + 47200 := by omega
                                                                                            rw [heq]
                                                                                            exact bd_w44 ⟨n - 47200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 47300
                                                                                            ·
                                                                                              have hr : n - 47250 < 50 := by omega
                                                                                              have heq : n = (n - 47250) + 47250 := by omega
                                                                                              rw [heq]
                                                                                              exact bd_w45 ⟨n - 47250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 47350
                                                                                              ·
                                                                                                have hr : n - 47300 < 50 := by omega
                                                                                                have heq : n = (n - 47300) + 47300 := by omega
                                                                                                rw [heq]
                                                                                                exact bd_w46 ⟨n - 47300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 47400
                                                                                                ·
                                                                                                  have hr : n - 47350 < 50 := by omega
                                                                                                  have heq : n = (n - 47350) + 47350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact bd_w47 ⟨n - 47350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 47450
                                                                                                  ·
                                                                                                    have hr : n - 47400 < 50 := by omega
                                                                                                    have heq : n = (n - 47400) + 47400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w48 ⟨n - 47400, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 47450 < 50 := by omega
                                                                                                    have heq : n = (n - 47450) + 47450 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w49 ⟨n - 47450, hr⟩


end IntMul.Kappa.R8.Bit.Oppbank.CentBound9a


