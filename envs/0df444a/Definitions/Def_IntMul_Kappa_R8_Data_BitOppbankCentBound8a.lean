-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound8a
-- name    : IntMul_Kappa_R8_Data_BitOppbankCentBound8a
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:06:36.872135+00:00
-- url     : https://prove2.me/theorems/8b609549-b367-4fcb-8635-a41859fde765
-- title:
--   HasCentre certificates dens nodes [40000,42500)
-- statement:
--   # Densified centre certificates, pack 8a
--
--   For every densified node index $n$ with $40000\le n<42500$,
--   $$
--   \mathrm{centredStar}(\mathrm{densSupG}\,n,\mathrm{centF}\,n)=\mathsf{true},\quad
--   \mathrm{centF}\,n<23,\quad
--   \mathrm{densSupG}\,n < 2^{1771}.
--   $$
--   Proved by decide on Fin 50 windows (no native_decide). Half-pack for 300s server budget.
-- source:
--   R8 BitOppbank AllDensCentred; jfstack_23 densified supports

-- CentBound pack 8a: densified HasCentre certificates on n ∈ [40000, 42500)
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

namespace IntMul.Kappa.R8.Bit.Oppbank.CentBound8a


private theorem cs_w0 : ∀ n : Fin 50, centredStar (densSupG (n.val + 40000)) (centF (n.val + 40000)) = true := by decide
private theorem cl_w0 : ∀ n : Fin 50, centF (n.val + 40000) < 23 := by decide
private theorem bd_w0 : ∀ n : Fin 50, densSupG (n.val + 40000) < 2 ^ 1771 := by decide
private theorem cs_w1 : ∀ n : Fin 50, centredStar (densSupG (n.val + 40050)) (centF (n.val + 40050)) = true := by decide
private theorem cl_w1 : ∀ n : Fin 50, centF (n.val + 40050) < 23 := by decide
private theorem bd_w1 : ∀ n : Fin 50, densSupG (n.val + 40050) < 2 ^ 1771 := by decide
private theorem cs_w2 : ∀ n : Fin 50, centredStar (densSupG (n.val + 40100)) (centF (n.val + 40100)) = true := by decide
private theorem cl_w2 : ∀ n : Fin 50, centF (n.val + 40100) < 23 := by decide
private theorem bd_w2 : ∀ n : Fin 50, densSupG (n.val + 40100) < 2 ^ 1771 := by decide
private theorem cs_w3 : ∀ n : Fin 50, centredStar (densSupG (n.val + 40150)) (centF (n.val + 40150)) = true := by decide
private theorem cl_w3 : ∀ n : Fin 50, centF (n.val + 40150) < 23 := by decide
private theorem bd_w3 : ∀ n : Fin 50, densSupG (n.val + 40150) < 2 ^ 1771 := by decide
private theorem cs_w4 : ∀ n : Fin 50, centredStar (densSupG (n.val + 40200)) (centF (n.val + 40200)) = true := by decide
private theorem cl_w4 : ∀ n : Fin 50, centF (n.val + 40200) < 23 := by decide
private theorem bd_w4 : ∀ n : Fin 50, densSupG (n.val + 40200) < 2 ^ 1771 := by decide
private theorem cs_w5 : ∀ n : Fin 50, centredStar (densSupG (n.val + 40250)) (centF (n.val + 40250)) = true := by decide
private theorem cl_w5 : ∀ n : Fin 50, centF (n.val + 40250) < 23 := by decide
private theorem bd_w5 : ∀ n : Fin 50, densSupG (n.val + 40250) < 2 ^ 1771 := by decide
private theorem cs_w6 : ∀ n : Fin 50, centredStar (densSupG (n.val + 40300)) (centF (n.val + 40300)) = true := by decide
private theorem cl_w6 : ∀ n : Fin 50, centF (n.val + 40300) < 23 := by decide
private theorem bd_w6 : ∀ n : Fin 50, densSupG (n.val + 40300) < 2 ^ 1771 := by decide
private theorem cs_w7 : ∀ n : Fin 50, centredStar (densSupG (n.val + 40350)) (centF (n.val + 40350)) = true := by decide
private theorem cl_w7 : ∀ n : Fin 50, centF (n.val + 40350) < 23 := by decide
private theorem bd_w7 : ∀ n : Fin 50, densSupG (n.val + 40350) < 2 ^ 1771 := by decide
private theorem cs_w8 : ∀ n : Fin 50, centredStar (densSupG (n.val + 40400)) (centF (n.val + 40400)) = true := by decide
private theorem cl_w8 : ∀ n : Fin 50, centF (n.val + 40400) < 23 := by decide
private theorem bd_w8 : ∀ n : Fin 50, densSupG (n.val + 40400) < 2 ^ 1771 := by decide
private theorem cs_w9 : ∀ n : Fin 50, centredStar (densSupG (n.val + 40450)) (centF (n.val + 40450)) = true := by decide
private theorem cl_w9 : ∀ n : Fin 50, centF (n.val + 40450) < 23 := by decide
private theorem bd_w9 : ∀ n : Fin 50, densSupG (n.val + 40450) < 2 ^ 1771 := by decide
private theorem cs_w10 : ∀ n : Fin 50, centredStar (densSupG (n.val + 40500)) (centF (n.val + 40500)) = true := by decide
private theorem cl_w10 : ∀ n : Fin 50, centF (n.val + 40500) < 23 := by decide
private theorem bd_w10 : ∀ n : Fin 50, densSupG (n.val + 40500) < 2 ^ 1771 := by decide
private theorem cs_w11 : ∀ n : Fin 50, centredStar (densSupG (n.val + 40550)) (centF (n.val + 40550)) = true := by decide
private theorem cl_w11 : ∀ n : Fin 50, centF (n.val + 40550) < 23 := by decide
private theorem bd_w11 : ∀ n : Fin 50, densSupG (n.val + 40550) < 2 ^ 1771 := by decide
private theorem cs_w12 : ∀ n : Fin 50, centredStar (densSupG (n.val + 40600)) (centF (n.val + 40600)) = true := by decide
private theorem cl_w12 : ∀ n : Fin 50, centF (n.val + 40600) < 23 := by decide
private theorem bd_w12 : ∀ n : Fin 50, densSupG (n.val + 40600) < 2 ^ 1771 := by decide
private theorem cs_w13 : ∀ n : Fin 50, centredStar (densSupG (n.val + 40650)) (centF (n.val + 40650)) = true := by decide
private theorem cl_w13 : ∀ n : Fin 50, centF (n.val + 40650) < 23 := by decide
private theorem bd_w13 : ∀ n : Fin 50, densSupG (n.val + 40650) < 2 ^ 1771 := by decide
private theorem cs_w14 : ∀ n : Fin 50, centredStar (densSupG (n.val + 40700)) (centF (n.val + 40700)) = true := by decide
private theorem cl_w14 : ∀ n : Fin 50, centF (n.val + 40700) < 23 := by decide
private theorem bd_w14 : ∀ n : Fin 50, densSupG (n.val + 40700) < 2 ^ 1771 := by decide
private theorem cs_w15 : ∀ n : Fin 50, centredStar (densSupG (n.val + 40750)) (centF (n.val + 40750)) = true := by decide
private theorem cl_w15 : ∀ n : Fin 50, centF (n.val + 40750) < 23 := by decide
private theorem bd_w15 : ∀ n : Fin 50, densSupG (n.val + 40750) < 2 ^ 1771 := by decide
private theorem cs_w16 : ∀ n : Fin 50, centredStar (densSupG (n.val + 40800)) (centF (n.val + 40800)) = true := by decide
private theorem cl_w16 : ∀ n : Fin 50, centF (n.val + 40800) < 23 := by decide
private theorem bd_w16 : ∀ n : Fin 50, densSupG (n.val + 40800) < 2 ^ 1771 := by decide
private theorem cs_w17 : ∀ n : Fin 50, centredStar (densSupG (n.val + 40850)) (centF (n.val + 40850)) = true := by decide
private theorem cl_w17 : ∀ n : Fin 50, centF (n.val + 40850) < 23 := by decide
private theorem bd_w17 : ∀ n : Fin 50, densSupG (n.val + 40850) < 2 ^ 1771 := by decide
private theorem cs_w18 : ∀ n : Fin 50, centredStar (densSupG (n.val + 40900)) (centF (n.val + 40900)) = true := by decide
private theorem cl_w18 : ∀ n : Fin 50, centF (n.val + 40900) < 23 := by decide
private theorem bd_w18 : ∀ n : Fin 50, densSupG (n.val + 40900) < 2 ^ 1771 := by decide
private theorem cs_w19 : ∀ n : Fin 50, centredStar (densSupG (n.val + 40950)) (centF (n.val + 40950)) = true := by decide
private theorem cl_w19 : ∀ n : Fin 50, centF (n.val + 40950) < 23 := by decide
private theorem bd_w19 : ∀ n : Fin 50, densSupG (n.val + 40950) < 2 ^ 1771 := by decide
private theorem cs_w20 : ∀ n : Fin 50, centredStar (densSupG (n.val + 41000)) (centF (n.val + 41000)) = true := by decide
private theorem cl_w20 : ∀ n : Fin 50, centF (n.val + 41000) < 23 := by decide
private theorem bd_w20 : ∀ n : Fin 50, densSupG (n.val + 41000) < 2 ^ 1771 := by decide
private theorem cs_w21 : ∀ n : Fin 50, centredStar (densSupG (n.val + 41050)) (centF (n.val + 41050)) = true := by decide
private theorem cl_w21 : ∀ n : Fin 50, centF (n.val + 41050) < 23 := by decide
private theorem bd_w21 : ∀ n : Fin 50, densSupG (n.val + 41050) < 2 ^ 1771 := by decide
private theorem cs_w22 : ∀ n : Fin 50, centredStar (densSupG (n.val + 41100)) (centF (n.val + 41100)) = true := by decide
private theorem cl_w22 : ∀ n : Fin 50, centF (n.val + 41100) < 23 := by decide
private theorem bd_w22 : ∀ n : Fin 50, densSupG (n.val + 41100) < 2 ^ 1771 := by decide
private theorem cs_w23 : ∀ n : Fin 50, centredStar (densSupG (n.val + 41150)) (centF (n.val + 41150)) = true := by decide
private theorem cl_w23 : ∀ n : Fin 50, centF (n.val + 41150) < 23 := by decide
private theorem bd_w23 : ∀ n : Fin 50, densSupG (n.val + 41150) < 2 ^ 1771 := by decide
private theorem cs_w24 : ∀ n : Fin 50, centredStar (densSupG (n.val + 41200)) (centF (n.val + 41200)) = true := by decide
private theorem cl_w24 : ∀ n : Fin 50, centF (n.val + 41200) < 23 := by decide
private theorem bd_w24 : ∀ n : Fin 50, densSupG (n.val + 41200) < 2 ^ 1771 := by decide
private theorem cs_w25 : ∀ n : Fin 50, centredStar (densSupG (n.val + 41250)) (centF (n.val + 41250)) = true := by decide
private theorem cl_w25 : ∀ n : Fin 50, centF (n.val + 41250) < 23 := by decide
private theorem bd_w25 : ∀ n : Fin 50, densSupG (n.val + 41250) < 2 ^ 1771 := by decide
private theorem cs_w26 : ∀ n : Fin 50, centredStar (densSupG (n.val + 41300)) (centF (n.val + 41300)) = true := by decide
private theorem cl_w26 : ∀ n : Fin 50, centF (n.val + 41300) < 23 := by decide
private theorem bd_w26 : ∀ n : Fin 50, densSupG (n.val + 41300) < 2 ^ 1771 := by decide
private theorem cs_w27 : ∀ n : Fin 50, centredStar (densSupG (n.val + 41350)) (centF (n.val + 41350)) = true := by decide
private theorem cl_w27 : ∀ n : Fin 50, centF (n.val + 41350) < 23 := by decide
private theorem bd_w27 : ∀ n : Fin 50, densSupG (n.val + 41350) < 2 ^ 1771 := by decide
private theorem cs_w28 : ∀ n : Fin 50, centredStar (densSupG (n.val + 41400)) (centF (n.val + 41400)) = true := by decide
private theorem cl_w28 : ∀ n : Fin 50, centF (n.val + 41400) < 23 := by decide
private theorem bd_w28 : ∀ n : Fin 50, densSupG (n.val + 41400) < 2 ^ 1771 := by decide
private theorem cs_w29 : ∀ n : Fin 50, centredStar (densSupG (n.val + 41450)) (centF (n.val + 41450)) = true := by decide
private theorem cl_w29 : ∀ n : Fin 50, centF (n.val + 41450) < 23 := by decide
private theorem bd_w29 : ∀ n : Fin 50, densSupG (n.val + 41450) < 2 ^ 1771 := by decide
private theorem cs_w30 : ∀ n : Fin 50, centredStar (densSupG (n.val + 41500)) (centF (n.val + 41500)) = true := by decide
private theorem cl_w30 : ∀ n : Fin 50, centF (n.val + 41500) < 23 := by decide
private theorem bd_w30 : ∀ n : Fin 50, densSupG (n.val + 41500) < 2 ^ 1771 := by decide
private theorem cs_w31 : ∀ n : Fin 50, centredStar (densSupG (n.val + 41550)) (centF (n.val + 41550)) = true := by decide
private theorem cl_w31 : ∀ n : Fin 50, centF (n.val + 41550) < 23 := by decide
private theorem bd_w31 : ∀ n : Fin 50, densSupG (n.val + 41550) < 2 ^ 1771 := by decide
private theorem cs_w32 : ∀ n : Fin 50, centredStar (densSupG (n.val + 41600)) (centF (n.val + 41600)) = true := by decide
private theorem cl_w32 : ∀ n : Fin 50, centF (n.val + 41600) < 23 := by decide
private theorem bd_w32 : ∀ n : Fin 50, densSupG (n.val + 41600) < 2 ^ 1771 := by decide
private theorem cs_w33 : ∀ n : Fin 50, centredStar (densSupG (n.val + 41650)) (centF (n.val + 41650)) = true := by decide
private theorem cl_w33 : ∀ n : Fin 50, centF (n.val + 41650) < 23 := by decide
private theorem bd_w33 : ∀ n : Fin 50, densSupG (n.val + 41650) < 2 ^ 1771 := by decide
private theorem cs_w34 : ∀ n : Fin 50, centredStar (densSupG (n.val + 41700)) (centF (n.val + 41700)) = true := by decide
private theorem cl_w34 : ∀ n : Fin 50, centF (n.val + 41700) < 23 := by decide
private theorem bd_w34 : ∀ n : Fin 50, densSupG (n.val + 41700) < 2 ^ 1771 := by decide
private theorem cs_w35 : ∀ n : Fin 50, centredStar (densSupG (n.val + 41750)) (centF (n.val + 41750)) = true := by decide
private theorem cl_w35 : ∀ n : Fin 50, centF (n.val + 41750) < 23 := by decide
private theorem bd_w35 : ∀ n : Fin 50, densSupG (n.val + 41750) < 2 ^ 1771 := by decide
private theorem cs_w36 : ∀ n : Fin 50, centredStar (densSupG (n.val + 41800)) (centF (n.val + 41800)) = true := by decide
private theorem cl_w36 : ∀ n : Fin 50, centF (n.val + 41800) < 23 := by decide
private theorem bd_w36 : ∀ n : Fin 50, densSupG (n.val + 41800) < 2 ^ 1771 := by decide
private theorem cs_w37 : ∀ n : Fin 50, centredStar (densSupG (n.val + 41850)) (centF (n.val + 41850)) = true := by decide
private theorem cl_w37 : ∀ n : Fin 50, centF (n.val + 41850) < 23 := by decide
private theorem bd_w37 : ∀ n : Fin 50, densSupG (n.val + 41850) < 2 ^ 1771 := by decide
private theorem cs_w38 : ∀ n : Fin 50, centredStar (densSupG (n.val + 41900)) (centF (n.val + 41900)) = true := by decide
private theorem cl_w38 : ∀ n : Fin 50, centF (n.val + 41900) < 23 := by decide
private theorem bd_w38 : ∀ n : Fin 50, densSupG (n.val + 41900) < 2 ^ 1771 := by decide
private theorem cs_w39 : ∀ n : Fin 50, centredStar (densSupG (n.val + 41950)) (centF (n.val + 41950)) = true := by decide
private theorem cl_w39 : ∀ n : Fin 50, centF (n.val + 41950) < 23 := by decide
private theorem bd_w39 : ∀ n : Fin 50, densSupG (n.val + 41950) < 2 ^ 1771 := by decide
private theorem cs_w40 : ∀ n : Fin 50, centredStar (densSupG (n.val + 42000)) (centF (n.val + 42000)) = true := by decide
private theorem cl_w40 : ∀ n : Fin 50, centF (n.val + 42000) < 23 := by decide
private theorem bd_w40 : ∀ n : Fin 50, densSupG (n.val + 42000) < 2 ^ 1771 := by decide
private theorem cs_w41 : ∀ n : Fin 50, centredStar (densSupG (n.val + 42050)) (centF (n.val + 42050)) = true := by decide
private theorem cl_w41 : ∀ n : Fin 50, centF (n.val + 42050) < 23 := by decide
private theorem bd_w41 : ∀ n : Fin 50, densSupG (n.val + 42050) < 2 ^ 1771 := by decide
private theorem cs_w42 : ∀ n : Fin 50, centredStar (densSupG (n.val + 42100)) (centF (n.val + 42100)) = true := by decide
private theorem cl_w42 : ∀ n : Fin 50, centF (n.val + 42100) < 23 := by decide
private theorem bd_w42 : ∀ n : Fin 50, densSupG (n.val + 42100) < 2 ^ 1771 := by decide
private theorem cs_w43 : ∀ n : Fin 50, centredStar (densSupG (n.val + 42150)) (centF (n.val + 42150)) = true := by decide
private theorem cl_w43 : ∀ n : Fin 50, centF (n.val + 42150) < 23 := by decide
private theorem bd_w43 : ∀ n : Fin 50, densSupG (n.val + 42150) < 2 ^ 1771 := by decide
private theorem cs_w44 : ∀ n : Fin 50, centredStar (densSupG (n.val + 42200)) (centF (n.val + 42200)) = true := by decide
private theorem cl_w44 : ∀ n : Fin 50, centF (n.val + 42200) < 23 := by decide
private theorem bd_w44 : ∀ n : Fin 50, densSupG (n.val + 42200) < 2 ^ 1771 := by decide
private theorem cs_w45 : ∀ n : Fin 50, centredStar (densSupG (n.val + 42250)) (centF (n.val + 42250)) = true := by decide
private theorem cl_w45 : ∀ n : Fin 50, centF (n.val + 42250) < 23 := by decide
private theorem bd_w45 : ∀ n : Fin 50, densSupG (n.val + 42250) < 2 ^ 1771 := by decide
private theorem cs_w46 : ∀ n : Fin 50, centredStar (densSupG (n.val + 42300)) (centF (n.val + 42300)) = true := by decide
private theorem cl_w46 : ∀ n : Fin 50, centF (n.val + 42300) < 23 := by decide
private theorem bd_w46 : ∀ n : Fin 50, densSupG (n.val + 42300) < 2 ^ 1771 := by decide
private theorem cs_w47 : ∀ n : Fin 50, centredStar (densSupG (n.val + 42350)) (centF (n.val + 42350)) = true := by decide
private theorem cl_w47 : ∀ n : Fin 50, centF (n.val + 42350) < 23 := by decide
private theorem bd_w47 : ∀ n : Fin 50, densSupG (n.val + 42350) < 2 ^ 1771 := by decide
private theorem cs_w48 : ∀ n : Fin 50, centredStar (densSupG (n.val + 42400)) (centF (n.val + 42400)) = true := by decide
private theorem cl_w48 : ∀ n : Fin 50, centF (n.val + 42400) < 23 := by decide
private theorem bd_w48 : ∀ n : Fin 50, densSupG (n.val + 42400) < 2 ^ 1771 := by decide
private theorem cs_w49 : ∀ n : Fin 50, centredStar (densSupG (n.val + 42450)) (centF (n.val + 42450)) = true := by decide
private theorem cl_w49 : ∀ n : Fin 50, centF (n.val + 42450) < 23 := by decide
private theorem bd_w49 : ∀ n : Fin 50, densSupG (n.val + 42450) < 2 ^ 1771 := by decide
theorem centredStar_range : ∀ n, 40000 ≤ n → n < 42500 → centredStar (densSupG n) (centF n) = true := by
  intro n hlo hhi
  by_cases h0 : n < 40050
  · have hr : n - 40000 < 50 := by omega
    have heq : n = (n - 40000) + 40000 := by omega
    rw [heq]
    exact cs_w0 ⟨n - 40000, hr⟩
  ·
    by_cases h1 : n < 40100
    ·
      have hr : n - 40050 < 50 := by omega
      have heq : n = (n - 40050) + 40050 := by omega
      rw [heq]
      exact cs_w1 ⟨n - 40050, hr⟩
    ·
      by_cases h2 : n < 40150
      ·
        have hr : n - 40100 < 50 := by omega
        have heq : n = (n - 40100) + 40100 := by omega
        rw [heq]
        exact cs_w2 ⟨n - 40100, hr⟩
      ·
        by_cases h3 : n < 40200
        ·
          have hr : n - 40150 < 50 := by omega
          have heq : n = (n - 40150) + 40150 := by omega
          rw [heq]
          exact cs_w3 ⟨n - 40150, hr⟩
        ·
          by_cases h4 : n < 40250
          ·
            have hr : n - 40200 < 50 := by omega
            have heq : n = (n - 40200) + 40200 := by omega
            rw [heq]
            exact cs_w4 ⟨n - 40200, hr⟩
          ·
            by_cases h5 : n < 40300
            ·
              have hr : n - 40250 < 50 := by omega
              have heq : n = (n - 40250) + 40250 := by omega
              rw [heq]
              exact cs_w5 ⟨n - 40250, hr⟩
            ·
              by_cases h6 : n < 40350
              ·
                have hr : n - 40300 < 50 := by omega
                have heq : n = (n - 40300) + 40300 := by omega
                rw [heq]
                exact cs_w6 ⟨n - 40300, hr⟩
              ·
                by_cases h7 : n < 40400
                ·
                  have hr : n - 40350 < 50 := by omega
                  have heq : n = (n - 40350) + 40350 := by omega
                  rw [heq]
                  exact cs_w7 ⟨n - 40350, hr⟩
                ·
                  by_cases h8 : n < 40450
                  ·
                    have hr : n - 40400 < 50 := by omega
                    have heq : n = (n - 40400) + 40400 := by omega
                    rw [heq]
                    exact cs_w8 ⟨n - 40400, hr⟩
                  ·
                    by_cases h9 : n < 40500
                    ·
                      have hr : n - 40450 < 50 := by omega
                      have heq : n = (n - 40450) + 40450 := by omega
                      rw [heq]
                      exact cs_w9 ⟨n - 40450, hr⟩
                    ·
                      by_cases h10 : n < 40550
                      ·
                        have hr : n - 40500 < 50 := by omega
                        have heq : n = (n - 40500) + 40500 := by omega
                        rw [heq]
                        exact cs_w10 ⟨n - 40500, hr⟩
                      ·
                        by_cases h11 : n < 40600
                        ·
                          have hr : n - 40550 < 50 := by omega
                          have heq : n = (n - 40550) + 40550 := by omega
                          rw [heq]
                          exact cs_w11 ⟨n - 40550, hr⟩
                        ·
                          by_cases h12 : n < 40650
                          ·
                            have hr : n - 40600 < 50 := by omega
                            have heq : n = (n - 40600) + 40600 := by omega
                            rw [heq]
                            exact cs_w12 ⟨n - 40600, hr⟩
                          ·
                            by_cases h13 : n < 40700
                            ·
                              have hr : n - 40650 < 50 := by omega
                              have heq : n = (n - 40650) + 40650 := by omega
                              rw [heq]
                              exact cs_w13 ⟨n - 40650, hr⟩
                            ·
                              by_cases h14 : n < 40750
                              ·
                                have hr : n - 40700 < 50 := by omega
                                have heq : n = (n - 40700) + 40700 := by omega
                                rw [heq]
                                exact cs_w14 ⟨n - 40700, hr⟩
                              ·
                                by_cases h15 : n < 40800
                                ·
                                  have hr : n - 40750 < 50 := by omega
                                  have heq : n = (n - 40750) + 40750 := by omega
                                  rw [heq]
                                  exact cs_w15 ⟨n - 40750, hr⟩
                                ·
                                  by_cases h16 : n < 40850
                                  ·
                                    have hr : n - 40800 < 50 := by omega
                                    have heq : n = (n - 40800) + 40800 := by omega
                                    rw [heq]
                                    exact cs_w16 ⟨n - 40800, hr⟩
                                  ·
                                    by_cases h17 : n < 40900
                                    ·
                                      have hr : n - 40850 < 50 := by omega
                                      have heq : n = (n - 40850) + 40850 := by omega
                                      rw [heq]
                                      exact cs_w17 ⟨n - 40850, hr⟩
                                    ·
                                      by_cases h18 : n < 40950
                                      ·
                                        have hr : n - 40900 < 50 := by omega
                                        have heq : n = (n - 40900) + 40900 := by omega
                                        rw [heq]
                                        exact cs_w18 ⟨n - 40900, hr⟩
                                      ·
                                        by_cases h19 : n < 41000
                                        ·
                                          have hr : n - 40950 < 50 := by omega
                                          have heq : n = (n - 40950) + 40950 := by omega
                                          rw [heq]
                                          exact cs_w19 ⟨n - 40950, hr⟩
                                        ·
                                          by_cases h20 : n < 41050
                                          ·
                                            have hr : n - 41000 < 50 := by omega
                                            have heq : n = (n - 41000) + 41000 := by omega
                                            rw [heq]
                                            exact cs_w20 ⟨n - 41000, hr⟩
                                          ·
                                            by_cases h21 : n < 41100
                                            ·
                                              have hr : n - 41050 < 50 := by omega
                                              have heq : n = (n - 41050) + 41050 := by omega
                                              rw [heq]
                                              exact cs_w21 ⟨n - 41050, hr⟩
                                            ·
                                              by_cases h22 : n < 41150
                                              ·
                                                have hr : n - 41100 < 50 := by omega
                                                have heq : n = (n - 41100) + 41100 := by omega
                                                rw [heq]
                                                exact cs_w22 ⟨n - 41100, hr⟩
                                              ·
                                                by_cases h23 : n < 41200
                                                ·
                                                  have hr : n - 41150 < 50 := by omega
                                                  have heq : n = (n - 41150) + 41150 := by omega
                                                  rw [heq]
                                                  exact cs_w23 ⟨n - 41150, hr⟩
                                                ·
                                                  by_cases h24 : n < 41250
                                                  ·
                                                    have hr : n - 41200 < 50 := by omega
                                                    have heq : n = (n - 41200) + 41200 := by omega
                                                    rw [heq]
                                                    exact cs_w24 ⟨n - 41200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 41300
                                                    ·
                                                      have hr : n - 41250 < 50 := by omega
                                                      have heq : n = (n - 41250) + 41250 := by omega
                                                      rw [heq]
                                                      exact cs_w25 ⟨n - 41250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 41350
                                                      ·
                                                        have hr : n - 41300 < 50 := by omega
                                                        have heq : n = (n - 41300) + 41300 := by omega
                                                        rw [heq]
                                                        exact cs_w26 ⟨n - 41300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 41400
                                                        ·
                                                          have hr : n - 41350 < 50 := by omega
                                                          have heq : n = (n - 41350) + 41350 := by omega
                                                          rw [heq]
                                                          exact cs_w27 ⟨n - 41350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 41450
                                                          ·
                                                            have hr : n - 41400 < 50 := by omega
                                                            have heq : n = (n - 41400) + 41400 := by omega
                                                            rw [heq]
                                                            exact cs_w28 ⟨n - 41400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 41500
                                                            ·
                                                              have hr : n - 41450 < 50 := by omega
                                                              have heq : n = (n - 41450) + 41450 := by omega
                                                              rw [heq]
                                                              exact cs_w29 ⟨n - 41450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 41550
                                                              ·
                                                                have hr : n - 41500 < 50 := by omega
                                                                have heq : n = (n - 41500) + 41500 := by omega
                                                                rw [heq]
                                                                exact cs_w30 ⟨n - 41500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 41600
                                                                ·
                                                                  have hr : n - 41550 < 50 := by omega
                                                                  have heq : n = (n - 41550) + 41550 := by omega
                                                                  rw [heq]
                                                                  exact cs_w31 ⟨n - 41550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 41650
                                                                  ·
                                                                    have hr : n - 41600 < 50 := by omega
                                                                    have heq : n = (n - 41600) + 41600 := by omega
                                                                    rw [heq]
                                                                    exact cs_w32 ⟨n - 41600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 41700
                                                                    ·
                                                                      have hr : n - 41650 < 50 := by omega
                                                                      have heq : n = (n - 41650) + 41650 := by omega
                                                                      rw [heq]
                                                                      exact cs_w33 ⟨n - 41650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 41750
                                                                      ·
                                                                        have hr : n - 41700 < 50 := by omega
                                                                        have heq : n = (n - 41700) + 41700 := by omega
                                                                        rw [heq]
                                                                        exact cs_w34 ⟨n - 41700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 41800
                                                                        ·
                                                                          have hr : n - 41750 < 50 := by omega
                                                                          have heq : n = (n - 41750) + 41750 := by omega
                                                                          rw [heq]
                                                                          exact cs_w35 ⟨n - 41750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 41850
                                                                          ·
                                                                            have hr : n - 41800 < 50 := by omega
                                                                            have heq : n = (n - 41800) + 41800 := by omega
                                                                            rw [heq]
                                                                            exact cs_w36 ⟨n - 41800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 41900
                                                                            ·
                                                                              have hr : n - 41850 < 50 := by omega
                                                                              have heq : n = (n - 41850) + 41850 := by omega
                                                                              rw [heq]
                                                                              exact cs_w37 ⟨n - 41850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 41950
                                                                              ·
                                                                                have hr : n - 41900 < 50 := by omega
                                                                                have heq : n = (n - 41900) + 41900 := by omega
                                                                                rw [heq]
                                                                                exact cs_w38 ⟨n - 41900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 42000
                                                                                ·
                                                                                  have hr : n - 41950 < 50 := by omega
                                                                                  have heq : n = (n - 41950) + 41950 := by omega
                                                                                  rw [heq]
                                                                                  exact cs_w39 ⟨n - 41950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 42050
                                                                                  ·
                                                                                    have hr : n - 42000 < 50 := by omega
                                                                                    have heq : n = (n - 42000) + 42000 := by omega
                                                                                    rw [heq]
                                                                                    exact cs_w40 ⟨n - 42000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 42100
                                                                                    ·
                                                                                      have hr : n - 42050 < 50 := by omega
                                                                                      have heq : n = (n - 42050) + 42050 := by omega
                                                                                      rw [heq]
                                                                                      exact cs_w41 ⟨n - 42050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 42150
                                                                                      ·
                                                                                        have hr : n - 42100 < 50 := by omega
                                                                                        have heq : n = (n - 42100) + 42100 := by omega
                                                                                        rw [heq]
                                                                                        exact cs_w42 ⟨n - 42100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 42200
                                                                                        ·
                                                                                          have hr : n - 42150 < 50 := by omega
                                                                                          have heq : n = (n - 42150) + 42150 := by omega
                                                                                          rw [heq]
                                                                                          exact cs_w43 ⟨n - 42150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 42250
                                                                                          ·
                                                                                            have hr : n - 42200 < 50 := by omega
                                                                                            have heq : n = (n - 42200) + 42200 := by omega
                                                                                            rw [heq]
                                                                                            exact cs_w44 ⟨n - 42200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 42300
                                                                                            ·
                                                                                              have hr : n - 42250 < 50 := by omega
                                                                                              have heq : n = (n - 42250) + 42250 := by omega
                                                                                              rw [heq]
                                                                                              exact cs_w45 ⟨n - 42250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 42350
                                                                                              ·
                                                                                                have hr : n - 42300 < 50 := by omega
                                                                                                have heq : n = (n - 42300) + 42300 := by omega
                                                                                                rw [heq]
                                                                                                exact cs_w46 ⟨n - 42300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 42400
                                                                                                ·
                                                                                                  have hr : n - 42350 < 50 := by omega
                                                                                                  have heq : n = (n - 42350) + 42350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cs_w47 ⟨n - 42350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 42450
                                                                                                  ·
                                                                                                    have hr : n - 42400 < 50 := by omega
                                                                                                    have heq : n = (n - 42400) + 42400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w48 ⟨n - 42400, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 42450 < 50 := by omega
                                                                                                    have heq : n = (n - 42450) + 42450 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cs_w49 ⟨n - 42450, hr⟩


theorem centF_lt_range : ∀ n, 40000 ≤ n → n < 42500 → centF n < 23 := by
  intro n hlo hhi
  by_cases h0 : n < 40050
  · have hr : n - 40000 < 50 := by omega
    have heq : n = (n - 40000) + 40000 := by omega
    rw [heq]
    exact cl_w0 ⟨n - 40000, hr⟩
  ·
    by_cases h1 : n < 40100
    ·
      have hr : n - 40050 < 50 := by omega
      have heq : n = (n - 40050) + 40050 := by omega
      rw [heq]
      exact cl_w1 ⟨n - 40050, hr⟩
    ·
      by_cases h2 : n < 40150
      ·
        have hr : n - 40100 < 50 := by omega
        have heq : n = (n - 40100) + 40100 := by omega
        rw [heq]
        exact cl_w2 ⟨n - 40100, hr⟩
      ·
        by_cases h3 : n < 40200
        ·
          have hr : n - 40150 < 50 := by omega
          have heq : n = (n - 40150) + 40150 := by omega
          rw [heq]
          exact cl_w3 ⟨n - 40150, hr⟩
        ·
          by_cases h4 : n < 40250
          ·
            have hr : n - 40200 < 50 := by omega
            have heq : n = (n - 40200) + 40200 := by omega
            rw [heq]
            exact cl_w4 ⟨n - 40200, hr⟩
          ·
            by_cases h5 : n < 40300
            ·
              have hr : n - 40250 < 50 := by omega
              have heq : n = (n - 40250) + 40250 := by omega
              rw [heq]
              exact cl_w5 ⟨n - 40250, hr⟩
            ·
              by_cases h6 : n < 40350
              ·
                have hr : n - 40300 < 50 := by omega
                have heq : n = (n - 40300) + 40300 := by omega
                rw [heq]
                exact cl_w6 ⟨n - 40300, hr⟩
              ·
                by_cases h7 : n < 40400
                ·
                  have hr : n - 40350 < 50 := by omega
                  have heq : n = (n - 40350) + 40350 := by omega
                  rw [heq]
                  exact cl_w7 ⟨n - 40350, hr⟩
                ·
                  by_cases h8 : n < 40450
                  ·
                    have hr : n - 40400 < 50 := by omega
                    have heq : n = (n - 40400) + 40400 := by omega
                    rw [heq]
                    exact cl_w8 ⟨n - 40400, hr⟩
                  ·
                    by_cases h9 : n < 40500
                    ·
                      have hr : n - 40450 < 50 := by omega
                      have heq : n = (n - 40450) + 40450 := by omega
                      rw [heq]
                      exact cl_w9 ⟨n - 40450, hr⟩
                    ·
                      by_cases h10 : n < 40550
                      ·
                        have hr : n - 40500 < 50 := by omega
                        have heq : n = (n - 40500) + 40500 := by omega
                        rw [heq]
                        exact cl_w10 ⟨n - 40500, hr⟩
                      ·
                        by_cases h11 : n < 40600
                        ·
                          have hr : n - 40550 < 50 := by omega
                          have heq : n = (n - 40550) + 40550 := by omega
                          rw [heq]
                          exact cl_w11 ⟨n - 40550, hr⟩
                        ·
                          by_cases h12 : n < 40650
                          ·
                            have hr : n - 40600 < 50 := by omega
                            have heq : n = (n - 40600) + 40600 := by omega
                            rw [heq]
                            exact cl_w12 ⟨n - 40600, hr⟩
                          ·
                            by_cases h13 : n < 40700
                            ·
                              have hr : n - 40650 < 50 := by omega
                              have heq : n = (n - 40650) + 40650 := by omega
                              rw [heq]
                              exact cl_w13 ⟨n - 40650, hr⟩
                            ·
                              by_cases h14 : n < 40750
                              ·
                                have hr : n - 40700 < 50 := by omega
                                have heq : n = (n - 40700) + 40700 := by omega
                                rw [heq]
                                exact cl_w14 ⟨n - 40700, hr⟩
                              ·
                                by_cases h15 : n < 40800
                                ·
                                  have hr : n - 40750 < 50 := by omega
                                  have heq : n = (n - 40750) + 40750 := by omega
                                  rw [heq]
                                  exact cl_w15 ⟨n - 40750, hr⟩
                                ·
                                  by_cases h16 : n < 40850
                                  ·
                                    have hr : n - 40800 < 50 := by omega
                                    have heq : n = (n - 40800) + 40800 := by omega
                                    rw [heq]
                                    exact cl_w16 ⟨n - 40800, hr⟩
                                  ·
                                    by_cases h17 : n < 40900
                                    ·
                                      have hr : n - 40850 < 50 := by omega
                                      have heq : n = (n - 40850) + 40850 := by omega
                                      rw [heq]
                                      exact cl_w17 ⟨n - 40850, hr⟩
                                    ·
                                      by_cases h18 : n < 40950
                                      ·
                                        have hr : n - 40900 < 50 := by omega
                                        have heq : n = (n - 40900) + 40900 := by omega
                                        rw [heq]
                                        exact cl_w18 ⟨n - 40900, hr⟩
                                      ·
                                        by_cases h19 : n < 41000
                                        ·
                                          have hr : n - 40950 < 50 := by omega
                                          have heq : n = (n - 40950) + 40950 := by omega
                                          rw [heq]
                                          exact cl_w19 ⟨n - 40950, hr⟩
                                        ·
                                          by_cases h20 : n < 41050
                                          ·
                                            have hr : n - 41000 < 50 := by omega
                                            have heq : n = (n - 41000) + 41000 := by omega
                                            rw [heq]
                                            exact cl_w20 ⟨n - 41000, hr⟩
                                          ·
                                            by_cases h21 : n < 41100
                                            ·
                                              have hr : n - 41050 < 50 := by omega
                                              have heq : n = (n - 41050) + 41050 := by omega
                                              rw [heq]
                                              exact cl_w21 ⟨n - 41050, hr⟩
                                            ·
                                              by_cases h22 : n < 41150
                                              ·
                                                have hr : n - 41100 < 50 := by omega
                                                have heq : n = (n - 41100) + 41100 := by omega
                                                rw [heq]
                                                exact cl_w22 ⟨n - 41100, hr⟩
                                              ·
                                                by_cases h23 : n < 41200
                                                ·
                                                  have hr : n - 41150 < 50 := by omega
                                                  have heq : n = (n - 41150) + 41150 := by omega
                                                  rw [heq]
                                                  exact cl_w23 ⟨n - 41150, hr⟩
                                                ·
                                                  by_cases h24 : n < 41250
                                                  ·
                                                    have hr : n - 41200 < 50 := by omega
                                                    have heq : n = (n - 41200) + 41200 := by omega
                                                    rw [heq]
                                                    exact cl_w24 ⟨n - 41200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 41300
                                                    ·
                                                      have hr : n - 41250 < 50 := by omega
                                                      have heq : n = (n - 41250) + 41250 := by omega
                                                      rw [heq]
                                                      exact cl_w25 ⟨n - 41250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 41350
                                                      ·
                                                        have hr : n - 41300 < 50 := by omega
                                                        have heq : n = (n - 41300) + 41300 := by omega
                                                        rw [heq]
                                                        exact cl_w26 ⟨n - 41300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 41400
                                                        ·
                                                          have hr : n - 41350 < 50 := by omega
                                                          have heq : n = (n - 41350) + 41350 := by omega
                                                          rw [heq]
                                                          exact cl_w27 ⟨n - 41350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 41450
                                                          ·
                                                            have hr : n - 41400 < 50 := by omega
                                                            have heq : n = (n - 41400) + 41400 := by omega
                                                            rw [heq]
                                                            exact cl_w28 ⟨n - 41400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 41500
                                                            ·
                                                              have hr : n - 41450 < 50 := by omega
                                                              have heq : n = (n - 41450) + 41450 := by omega
                                                              rw [heq]
                                                              exact cl_w29 ⟨n - 41450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 41550
                                                              ·
                                                                have hr : n - 41500 < 50 := by omega
                                                                have heq : n = (n - 41500) + 41500 := by omega
                                                                rw [heq]
                                                                exact cl_w30 ⟨n - 41500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 41600
                                                                ·
                                                                  have hr : n - 41550 < 50 := by omega
                                                                  have heq : n = (n - 41550) + 41550 := by omega
                                                                  rw [heq]
                                                                  exact cl_w31 ⟨n - 41550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 41650
                                                                  ·
                                                                    have hr : n - 41600 < 50 := by omega
                                                                    have heq : n = (n - 41600) + 41600 := by omega
                                                                    rw [heq]
                                                                    exact cl_w32 ⟨n - 41600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 41700
                                                                    ·
                                                                      have hr : n - 41650 < 50 := by omega
                                                                      have heq : n = (n - 41650) + 41650 := by omega
                                                                      rw [heq]
                                                                      exact cl_w33 ⟨n - 41650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 41750
                                                                      ·
                                                                        have hr : n - 41700 < 50 := by omega
                                                                        have heq : n = (n - 41700) + 41700 := by omega
                                                                        rw [heq]
                                                                        exact cl_w34 ⟨n - 41700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 41800
                                                                        ·
                                                                          have hr : n - 41750 < 50 := by omega
                                                                          have heq : n = (n - 41750) + 41750 := by omega
                                                                          rw [heq]
                                                                          exact cl_w35 ⟨n - 41750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 41850
                                                                          ·
                                                                            have hr : n - 41800 < 50 := by omega
                                                                            have heq : n = (n - 41800) + 41800 := by omega
                                                                            rw [heq]
                                                                            exact cl_w36 ⟨n - 41800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 41900
                                                                            ·
                                                                              have hr : n - 41850 < 50 := by omega
                                                                              have heq : n = (n - 41850) + 41850 := by omega
                                                                              rw [heq]
                                                                              exact cl_w37 ⟨n - 41850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 41950
                                                                              ·
                                                                                have hr : n - 41900 < 50 := by omega
                                                                                have heq : n = (n - 41900) + 41900 := by omega
                                                                                rw [heq]
                                                                                exact cl_w38 ⟨n - 41900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 42000
                                                                                ·
                                                                                  have hr : n - 41950 < 50 := by omega
                                                                                  have heq : n = (n - 41950) + 41950 := by omega
                                                                                  rw [heq]
                                                                                  exact cl_w39 ⟨n - 41950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 42050
                                                                                  ·
                                                                                    have hr : n - 42000 < 50 := by omega
                                                                                    have heq : n = (n - 42000) + 42000 := by omega
                                                                                    rw [heq]
                                                                                    exact cl_w40 ⟨n - 42000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 42100
                                                                                    ·
                                                                                      have hr : n - 42050 < 50 := by omega
                                                                                      have heq : n = (n - 42050) + 42050 := by omega
                                                                                      rw [heq]
                                                                                      exact cl_w41 ⟨n - 42050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 42150
                                                                                      ·
                                                                                        have hr : n - 42100 < 50 := by omega
                                                                                        have heq : n = (n - 42100) + 42100 := by omega
                                                                                        rw [heq]
                                                                                        exact cl_w42 ⟨n - 42100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 42200
                                                                                        ·
                                                                                          have hr : n - 42150 < 50 := by omega
                                                                                          have heq : n = (n - 42150) + 42150 := by omega
                                                                                          rw [heq]
                                                                                          exact cl_w43 ⟨n - 42150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 42250
                                                                                          ·
                                                                                            have hr : n - 42200 < 50 := by omega
                                                                                            have heq : n = (n - 42200) + 42200 := by omega
                                                                                            rw [heq]
                                                                                            exact cl_w44 ⟨n - 42200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 42300
                                                                                            ·
                                                                                              have hr : n - 42250 < 50 := by omega
                                                                                              have heq : n = (n - 42250) + 42250 := by omega
                                                                                              rw [heq]
                                                                                              exact cl_w45 ⟨n - 42250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 42350
                                                                                              ·
                                                                                                have hr : n - 42300 < 50 := by omega
                                                                                                have heq : n = (n - 42300) + 42300 := by omega
                                                                                                rw [heq]
                                                                                                exact cl_w46 ⟨n - 42300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 42400
                                                                                                ·
                                                                                                  have hr : n - 42350 < 50 := by omega
                                                                                                  have heq : n = (n - 42350) + 42350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact cl_w47 ⟨n - 42350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 42450
                                                                                                  ·
                                                                                                    have hr : n - 42400 < 50 := by omega
                                                                                                    have heq : n = (n - 42400) + 42400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w48 ⟨n - 42400, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 42450 < 50 := by omega
                                                                                                    have heq : n = (n - 42450) + 42450 := by omega
                                                                                                    rw [heq]
                                                                                                    exact cl_w49 ⟨n - 42450, hr⟩


theorem densSupG_lt_range : ∀ n, 40000 ≤ n → n < 42500 → densSupG n < 2 ^ 1771 := by
  intro n hlo hhi
  by_cases h0 : n < 40050
  · have hr : n - 40000 < 50 := by omega
    have heq : n = (n - 40000) + 40000 := by omega
    rw [heq]
    exact bd_w0 ⟨n - 40000, hr⟩
  ·
    by_cases h1 : n < 40100
    ·
      have hr : n - 40050 < 50 := by omega
      have heq : n = (n - 40050) + 40050 := by omega
      rw [heq]
      exact bd_w1 ⟨n - 40050, hr⟩
    ·
      by_cases h2 : n < 40150
      ·
        have hr : n - 40100 < 50 := by omega
        have heq : n = (n - 40100) + 40100 := by omega
        rw [heq]
        exact bd_w2 ⟨n - 40100, hr⟩
      ·
        by_cases h3 : n < 40200
        ·
          have hr : n - 40150 < 50 := by omega
          have heq : n = (n - 40150) + 40150 := by omega
          rw [heq]
          exact bd_w3 ⟨n - 40150, hr⟩
        ·
          by_cases h4 : n < 40250
          ·
            have hr : n - 40200 < 50 := by omega
            have heq : n = (n - 40200) + 40200 := by omega
            rw [heq]
            exact bd_w4 ⟨n - 40200, hr⟩
          ·
            by_cases h5 : n < 40300
            ·
              have hr : n - 40250 < 50 := by omega
              have heq : n = (n - 40250) + 40250 := by omega
              rw [heq]
              exact bd_w5 ⟨n - 40250, hr⟩
            ·
              by_cases h6 : n < 40350
              ·
                have hr : n - 40300 < 50 := by omega
                have heq : n = (n - 40300) + 40300 := by omega
                rw [heq]
                exact bd_w6 ⟨n - 40300, hr⟩
              ·
                by_cases h7 : n < 40400
                ·
                  have hr : n - 40350 < 50 := by omega
                  have heq : n = (n - 40350) + 40350 := by omega
                  rw [heq]
                  exact bd_w7 ⟨n - 40350, hr⟩
                ·
                  by_cases h8 : n < 40450
                  ·
                    have hr : n - 40400 < 50 := by omega
                    have heq : n = (n - 40400) + 40400 := by omega
                    rw [heq]
                    exact bd_w8 ⟨n - 40400, hr⟩
                  ·
                    by_cases h9 : n < 40500
                    ·
                      have hr : n - 40450 < 50 := by omega
                      have heq : n = (n - 40450) + 40450 := by omega
                      rw [heq]
                      exact bd_w9 ⟨n - 40450, hr⟩
                    ·
                      by_cases h10 : n < 40550
                      ·
                        have hr : n - 40500 < 50 := by omega
                        have heq : n = (n - 40500) + 40500 := by omega
                        rw [heq]
                        exact bd_w10 ⟨n - 40500, hr⟩
                      ·
                        by_cases h11 : n < 40600
                        ·
                          have hr : n - 40550 < 50 := by omega
                          have heq : n = (n - 40550) + 40550 := by omega
                          rw [heq]
                          exact bd_w11 ⟨n - 40550, hr⟩
                        ·
                          by_cases h12 : n < 40650
                          ·
                            have hr : n - 40600 < 50 := by omega
                            have heq : n = (n - 40600) + 40600 := by omega
                            rw [heq]
                            exact bd_w12 ⟨n - 40600, hr⟩
                          ·
                            by_cases h13 : n < 40700
                            ·
                              have hr : n - 40650 < 50 := by omega
                              have heq : n = (n - 40650) + 40650 := by omega
                              rw [heq]
                              exact bd_w13 ⟨n - 40650, hr⟩
                            ·
                              by_cases h14 : n < 40750
                              ·
                                have hr : n - 40700 < 50 := by omega
                                have heq : n = (n - 40700) + 40700 := by omega
                                rw [heq]
                                exact bd_w14 ⟨n - 40700, hr⟩
                              ·
                                by_cases h15 : n < 40800
                                ·
                                  have hr : n - 40750 < 50 := by omega
                                  have heq : n = (n - 40750) + 40750 := by omega
                                  rw [heq]
                                  exact bd_w15 ⟨n - 40750, hr⟩
                                ·
                                  by_cases h16 : n < 40850
                                  ·
                                    have hr : n - 40800 < 50 := by omega
                                    have heq : n = (n - 40800) + 40800 := by omega
                                    rw [heq]
                                    exact bd_w16 ⟨n - 40800, hr⟩
                                  ·
                                    by_cases h17 : n < 40900
                                    ·
                                      have hr : n - 40850 < 50 := by omega
                                      have heq : n = (n - 40850) + 40850 := by omega
                                      rw [heq]
                                      exact bd_w17 ⟨n - 40850, hr⟩
                                    ·
                                      by_cases h18 : n < 40950
                                      ·
                                        have hr : n - 40900 < 50 := by omega
                                        have heq : n = (n - 40900) + 40900 := by omega
                                        rw [heq]
                                        exact bd_w18 ⟨n - 40900, hr⟩
                                      ·
                                        by_cases h19 : n < 41000
                                        ·
                                          have hr : n - 40950 < 50 := by omega
                                          have heq : n = (n - 40950) + 40950 := by omega
                                          rw [heq]
                                          exact bd_w19 ⟨n - 40950, hr⟩
                                        ·
                                          by_cases h20 : n < 41050
                                          ·
                                            have hr : n - 41000 < 50 := by omega
                                            have heq : n = (n - 41000) + 41000 := by omega
                                            rw [heq]
                                            exact bd_w20 ⟨n - 41000, hr⟩
                                          ·
                                            by_cases h21 : n < 41100
                                            ·
                                              have hr : n - 41050 < 50 := by omega
                                              have heq : n = (n - 41050) + 41050 := by omega
                                              rw [heq]
                                              exact bd_w21 ⟨n - 41050, hr⟩
                                            ·
                                              by_cases h22 : n < 41150
                                              ·
                                                have hr : n - 41100 < 50 := by omega
                                                have heq : n = (n - 41100) + 41100 := by omega
                                                rw [heq]
                                                exact bd_w22 ⟨n - 41100, hr⟩
                                              ·
                                                by_cases h23 : n < 41200
                                                ·
                                                  have hr : n - 41150 < 50 := by omega
                                                  have heq : n = (n - 41150) + 41150 := by omega
                                                  rw [heq]
                                                  exact bd_w23 ⟨n - 41150, hr⟩
                                                ·
                                                  by_cases h24 : n < 41250
                                                  ·
                                                    have hr : n - 41200 < 50 := by omega
                                                    have heq : n = (n - 41200) + 41200 := by omega
                                                    rw [heq]
                                                    exact bd_w24 ⟨n - 41200, hr⟩
                                                  ·
                                                    by_cases h25 : n < 41300
                                                    ·
                                                      have hr : n - 41250 < 50 := by omega
                                                      have heq : n = (n - 41250) + 41250 := by omega
                                                      rw [heq]
                                                      exact bd_w25 ⟨n - 41250, hr⟩
                                                    ·
                                                      by_cases h26 : n < 41350
                                                      ·
                                                        have hr : n - 41300 < 50 := by omega
                                                        have heq : n = (n - 41300) + 41300 := by omega
                                                        rw [heq]
                                                        exact bd_w26 ⟨n - 41300, hr⟩
                                                      ·
                                                        by_cases h27 : n < 41400
                                                        ·
                                                          have hr : n - 41350 < 50 := by omega
                                                          have heq : n = (n - 41350) + 41350 := by omega
                                                          rw [heq]
                                                          exact bd_w27 ⟨n - 41350, hr⟩
                                                        ·
                                                          by_cases h28 : n < 41450
                                                          ·
                                                            have hr : n - 41400 < 50 := by omega
                                                            have heq : n = (n - 41400) + 41400 := by omega
                                                            rw [heq]
                                                            exact bd_w28 ⟨n - 41400, hr⟩
                                                          ·
                                                            by_cases h29 : n < 41500
                                                            ·
                                                              have hr : n - 41450 < 50 := by omega
                                                              have heq : n = (n - 41450) + 41450 := by omega
                                                              rw [heq]
                                                              exact bd_w29 ⟨n - 41450, hr⟩
                                                            ·
                                                              by_cases h30 : n < 41550
                                                              ·
                                                                have hr : n - 41500 < 50 := by omega
                                                                have heq : n = (n - 41500) + 41500 := by omega
                                                                rw [heq]
                                                                exact bd_w30 ⟨n - 41500, hr⟩
                                                              ·
                                                                by_cases h31 : n < 41600
                                                                ·
                                                                  have hr : n - 41550 < 50 := by omega
                                                                  have heq : n = (n - 41550) + 41550 := by omega
                                                                  rw [heq]
                                                                  exact bd_w31 ⟨n - 41550, hr⟩
                                                                ·
                                                                  by_cases h32 : n < 41650
                                                                  ·
                                                                    have hr : n - 41600 < 50 := by omega
                                                                    have heq : n = (n - 41600) + 41600 := by omega
                                                                    rw [heq]
                                                                    exact bd_w32 ⟨n - 41600, hr⟩
                                                                  ·
                                                                    by_cases h33 : n < 41700
                                                                    ·
                                                                      have hr : n - 41650 < 50 := by omega
                                                                      have heq : n = (n - 41650) + 41650 := by omega
                                                                      rw [heq]
                                                                      exact bd_w33 ⟨n - 41650, hr⟩
                                                                    ·
                                                                      by_cases h34 : n < 41750
                                                                      ·
                                                                        have hr : n - 41700 < 50 := by omega
                                                                        have heq : n = (n - 41700) + 41700 := by omega
                                                                        rw [heq]
                                                                        exact bd_w34 ⟨n - 41700, hr⟩
                                                                      ·
                                                                        by_cases h35 : n < 41800
                                                                        ·
                                                                          have hr : n - 41750 < 50 := by omega
                                                                          have heq : n = (n - 41750) + 41750 := by omega
                                                                          rw [heq]
                                                                          exact bd_w35 ⟨n - 41750, hr⟩
                                                                        ·
                                                                          by_cases h36 : n < 41850
                                                                          ·
                                                                            have hr : n - 41800 < 50 := by omega
                                                                            have heq : n = (n - 41800) + 41800 := by omega
                                                                            rw [heq]
                                                                            exact bd_w36 ⟨n - 41800, hr⟩
                                                                          ·
                                                                            by_cases h37 : n < 41900
                                                                            ·
                                                                              have hr : n - 41850 < 50 := by omega
                                                                              have heq : n = (n - 41850) + 41850 := by omega
                                                                              rw [heq]
                                                                              exact bd_w37 ⟨n - 41850, hr⟩
                                                                            ·
                                                                              by_cases h38 : n < 41950
                                                                              ·
                                                                                have hr : n - 41900 < 50 := by omega
                                                                                have heq : n = (n - 41900) + 41900 := by omega
                                                                                rw [heq]
                                                                                exact bd_w38 ⟨n - 41900, hr⟩
                                                                              ·
                                                                                by_cases h39 : n < 42000
                                                                                ·
                                                                                  have hr : n - 41950 < 50 := by omega
                                                                                  have heq : n = (n - 41950) + 41950 := by omega
                                                                                  rw [heq]
                                                                                  exact bd_w39 ⟨n - 41950, hr⟩
                                                                                ·
                                                                                  by_cases h40 : n < 42050
                                                                                  ·
                                                                                    have hr : n - 42000 < 50 := by omega
                                                                                    have heq : n = (n - 42000) + 42000 := by omega
                                                                                    rw [heq]
                                                                                    exact bd_w40 ⟨n - 42000, hr⟩
                                                                                  ·
                                                                                    by_cases h41 : n < 42100
                                                                                    ·
                                                                                      have hr : n - 42050 < 50 := by omega
                                                                                      have heq : n = (n - 42050) + 42050 := by omega
                                                                                      rw [heq]
                                                                                      exact bd_w41 ⟨n - 42050, hr⟩
                                                                                    ·
                                                                                      by_cases h42 : n < 42150
                                                                                      ·
                                                                                        have hr : n - 42100 < 50 := by omega
                                                                                        have heq : n = (n - 42100) + 42100 := by omega
                                                                                        rw [heq]
                                                                                        exact bd_w42 ⟨n - 42100, hr⟩
                                                                                      ·
                                                                                        by_cases h43 : n < 42200
                                                                                        ·
                                                                                          have hr : n - 42150 < 50 := by omega
                                                                                          have heq : n = (n - 42150) + 42150 := by omega
                                                                                          rw [heq]
                                                                                          exact bd_w43 ⟨n - 42150, hr⟩
                                                                                        ·
                                                                                          by_cases h44 : n < 42250
                                                                                          ·
                                                                                            have hr : n - 42200 < 50 := by omega
                                                                                            have heq : n = (n - 42200) + 42200 := by omega
                                                                                            rw [heq]
                                                                                            exact bd_w44 ⟨n - 42200, hr⟩
                                                                                          ·
                                                                                            by_cases h45 : n < 42300
                                                                                            ·
                                                                                              have hr : n - 42250 < 50 := by omega
                                                                                              have heq : n = (n - 42250) + 42250 := by omega
                                                                                              rw [heq]
                                                                                              exact bd_w45 ⟨n - 42250, hr⟩
                                                                                            ·
                                                                                              by_cases h46 : n < 42350
                                                                                              ·
                                                                                                have hr : n - 42300 < 50 := by omega
                                                                                                have heq : n = (n - 42300) + 42300 := by omega
                                                                                                rw [heq]
                                                                                                exact bd_w46 ⟨n - 42300, hr⟩
                                                                                              ·
                                                                                                by_cases h47 : n < 42400
                                                                                                ·
                                                                                                  have hr : n - 42350 < 50 := by omega
                                                                                                  have heq : n = (n - 42350) + 42350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact bd_w47 ⟨n - 42350, hr⟩
                                                                                                ·
                                                                                                  by_cases h48 : n < 42450
                                                                                                  ·
                                                                                                    have hr : n - 42400 < 50 := by omega
                                                                                                    have heq : n = (n - 42400) + 42400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w48 ⟨n - 42400, hr⟩
                                                                                                  ·
                                                                                                    have hr : n - 42450 < 50 := by omega
                                                                                                    have heq : n = (n - 42450) + 42450 := by omega
                                                                                                    rw [heq]
                                                                                                    exact bd_w49 ⟨n - 42450, hr⟩


end IntMul.Kappa.R8.Bit.Oppbank.CentBound8a


