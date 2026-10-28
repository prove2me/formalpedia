-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound1
-- name    : IntMul_Kappa_R8_Data_BitOppbankDimBound1
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:02:32.342982+00:00
-- url     : https://prove2.me/theorems/094a91e8-4556-4ba5-9589-681bc30c4a33
-- title:
--   Densified dimF $\le 22$ pack 1 ($[5000,10000)$)
-- statement:
--   Pack 1 of the densified dimension-field bound.
--
--   For every densified node index $n$ with $5000\le n<10000$, the 5-bit field $\mathrm{dimF}(n)$ extracted from $\mathrm{DIMT}$ satisfies
--   $$1\le \mathrm{dimF}(n)\le 22.$$
--   Proved by `decide` on successive `Fin 50` windows (no `native_decide`).
-- source:
--   R8 BitNB densified DIMT field bound; Fin-window decide packs

-- DimBound pack 1: dimF bounds on n ∈ [5000, 10000)

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.ChkBitArg
open IntMul.Kappa.R8.Bit.Oppbank.SupG

namespace IntMul.Kappa.R8.Bit.Oppbank.DimBound1

private theorem le_w100 : ∀ n : Fin 50, dimF (n.val + 5000) ≤ 22 := by decide
private theorem pos_w100 : ∀ n : Fin 50, 0 < dimF (n.val + 5000) := by decide
private theorem le_w101 : ∀ n : Fin 50, dimF (n.val + 5050) ≤ 22 := by decide
private theorem pos_w101 : ∀ n : Fin 50, 0 < dimF (n.val + 5050) := by decide
private theorem le_w102 : ∀ n : Fin 50, dimF (n.val + 5100) ≤ 22 := by decide
private theorem pos_w102 : ∀ n : Fin 50, 0 < dimF (n.val + 5100) := by decide
private theorem le_w103 : ∀ n : Fin 50, dimF (n.val + 5150) ≤ 22 := by decide
private theorem pos_w103 : ∀ n : Fin 50, 0 < dimF (n.val + 5150) := by decide
private theorem le_w104 : ∀ n : Fin 50, dimF (n.val + 5200) ≤ 22 := by decide
private theorem pos_w104 : ∀ n : Fin 50, 0 < dimF (n.val + 5200) := by decide
private theorem le_w105 : ∀ n : Fin 50, dimF (n.val + 5250) ≤ 22 := by decide
private theorem pos_w105 : ∀ n : Fin 50, 0 < dimF (n.val + 5250) := by decide
private theorem le_w106 : ∀ n : Fin 50, dimF (n.val + 5300) ≤ 22 := by decide
private theorem pos_w106 : ∀ n : Fin 50, 0 < dimF (n.val + 5300) := by decide
private theorem le_w107 : ∀ n : Fin 50, dimF (n.val + 5350) ≤ 22 := by decide
private theorem pos_w107 : ∀ n : Fin 50, 0 < dimF (n.val + 5350) := by decide
private theorem le_w108 : ∀ n : Fin 50, dimF (n.val + 5400) ≤ 22 := by decide
private theorem pos_w108 : ∀ n : Fin 50, 0 < dimF (n.val + 5400) := by decide
private theorem le_w109 : ∀ n : Fin 50, dimF (n.val + 5450) ≤ 22 := by decide
private theorem pos_w109 : ∀ n : Fin 50, 0 < dimF (n.val + 5450) := by decide
private theorem le_w110 : ∀ n : Fin 50, dimF (n.val + 5500) ≤ 22 := by decide
private theorem pos_w110 : ∀ n : Fin 50, 0 < dimF (n.val + 5500) := by decide
private theorem le_w111 : ∀ n : Fin 50, dimF (n.val + 5550) ≤ 22 := by decide
private theorem pos_w111 : ∀ n : Fin 50, 0 < dimF (n.val + 5550) := by decide
private theorem le_w112 : ∀ n : Fin 50, dimF (n.val + 5600) ≤ 22 := by decide
private theorem pos_w112 : ∀ n : Fin 50, 0 < dimF (n.val + 5600) := by decide
private theorem le_w113 : ∀ n : Fin 50, dimF (n.val + 5650) ≤ 22 := by decide
private theorem pos_w113 : ∀ n : Fin 50, 0 < dimF (n.val + 5650) := by decide
private theorem le_w114 : ∀ n : Fin 50, dimF (n.val + 5700) ≤ 22 := by decide
private theorem pos_w114 : ∀ n : Fin 50, 0 < dimF (n.val + 5700) := by decide
private theorem le_w115 : ∀ n : Fin 50, dimF (n.val + 5750) ≤ 22 := by decide
private theorem pos_w115 : ∀ n : Fin 50, 0 < dimF (n.val + 5750) := by decide
private theorem le_w116 : ∀ n : Fin 50, dimF (n.val + 5800) ≤ 22 := by decide
private theorem pos_w116 : ∀ n : Fin 50, 0 < dimF (n.val + 5800) := by decide
private theorem le_w117 : ∀ n : Fin 50, dimF (n.val + 5850) ≤ 22 := by decide
private theorem pos_w117 : ∀ n : Fin 50, 0 < dimF (n.val + 5850) := by decide
private theorem le_w118 : ∀ n : Fin 50, dimF (n.val + 5900) ≤ 22 := by decide
private theorem pos_w118 : ∀ n : Fin 50, 0 < dimF (n.val + 5900) := by decide
private theorem le_w119 : ∀ n : Fin 50, dimF (n.val + 5950) ≤ 22 := by decide
private theorem pos_w119 : ∀ n : Fin 50, 0 < dimF (n.val + 5950) := by decide
private theorem le_w120 : ∀ n : Fin 50, dimF (n.val + 6000) ≤ 22 := by decide
private theorem pos_w120 : ∀ n : Fin 50, 0 < dimF (n.val + 6000) := by decide
private theorem le_w121 : ∀ n : Fin 50, dimF (n.val + 6050) ≤ 22 := by decide
private theorem pos_w121 : ∀ n : Fin 50, 0 < dimF (n.val + 6050) := by decide
private theorem le_w122 : ∀ n : Fin 50, dimF (n.val + 6100) ≤ 22 := by decide
private theorem pos_w122 : ∀ n : Fin 50, 0 < dimF (n.val + 6100) := by decide
private theorem le_w123 : ∀ n : Fin 50, dimF (n.val + 6150) ≤ 22 := by decide
private theorem pos_w123 : ∀ n : Fin 50, 0 < dimF (n.val + 6150) := by decide
private theorem le_w124 : ∀ n : Fin 50, dimF (n.val + 6200) ≤ 22 := by decide
private theorem pos_w124 : ∀ n : Fin 50, 0 < dimF (n.val + 6200) := by decide
private theorem le_w125 : ∀ n : Fin 50, dimF (n.val + 6250) ≤ 22 := by decide
private theorem pos_w125 : ∀ n : Fin 50, 0 < dimF (n.val + 6250) := by decide
private theorem le_w126 : ∀ n : Fin 50, dimF (n.val + 6300) ≤ 22 := by decide
private theorem pos_w126 : ∀ n : Fin 50, 0 < dimF (n.val + 6300) := by decide
private theorem le_w127 : ∀ n : Fin 50, dimF (n.val + 6350) ≤ 22 := by decide
private theorem pos_w127 : ∀ n : Fin 50, 0 < dimF (n.val + 6350) := by decide
private theorem le_w128 : ∀ n : Fin 50, dimF (n.val + 6400) ≤ 22 := by decide
private theorem pos_w128 : ∀ n : Fin 50, 0 < dimF (n.val + 6400) := by decide
private theorem le_w129 : ∀ n : Fin 50, dimF (n.val + 6450) ≤ 22 := by decide
private theorem pos_w129 : ∀ n : Fin 50, 0 < dimF (n.val + 6450) := by decide
private theorem le_w130 : ∀ n : Fin 50, dimF (n.val + 6500) ≤ 22 := by decide
private theorem pos_w130 : ∀ n : Fin 50, 0 < dimF (n.val + 6500) := by decide
private theorem le_w131 : ∀ n : Fin 50, dimF (n.val + 6550) ≤ 22 := by decide
private theorem pos_w131 : ∀ n : Fin 50, 0 < dimF (n.val + 6550) := by decide
private theorem le_w132 : ∀ n : Fin 50, dimF (n.val + 6600) ≤ 22 := by decide
private theorem pos_w132 : ∀ n : Fin 50, 0 < dimF (n.val + 6600) := by decide
private theorem le_w133 : ∀ n : Fin 50, dimF (n.val + 6650) ≤ 22 := by decide
private theorem pos_w133 : ∀ n : Fin 50, 0 < dimF (n.val + 6650) := by decide
private theorem le_w134 : ∀ n : Fin 50, dimF (n.val + 6700) ≤ 22 := by decide
private theorem pos_w134 : ∀ n : Fin 50, 0 < dimF (n.val + 6700) := by decide
private theorem le_w135 : ∀ n : Fin 50, dimF (n.val + 6750) ≤ 22 := by decide
private theorem pos_w135 : ∀ n : Fin 50, 0 < dimF (n.val + 6750) := by decide
private theorem le_w136 : ∀ n : Fin 50, dimF (n.val + 6800) ≤ 22 := by decide
private theorem pos_w136 : ∀ n : Fin 50, 0 < dimF (n.val + 6800) := by decide
private theorem le_w137 : ∀ n : Fin 50, dimF (n.val + 6850) ≤ 22 := by decide
private theorem pos_w137 : ∀ n : Fin 50, 0 < dimF (n.val + 6850) := by decide
private theorem le_w138 : ∀ n : Fin 50, dimF (n.val + 6900) ≤ 22 := by decide
private theorem pos_w138 : ∀ n : Fin 50, 0 < dimF (n.val + 6900) := by decide
private theorem le_w139 : ∀ n : Fin 50, dimF (n.val + 6950) ≤ 22 := by decide
private theorem pos_w139 : ∀ n : Fin 50, 0 < dimF (n.val + 6950) := by decide
private theorem le_w140 : ∀ n : Fin 50, dimF (n.val + 7000) ≤ 22 := by decide
private theorem pos_w140 : ∀ n : Fin 50, 0 < dimF (n.val + 7000) := by decide
private theorem le_w141 : ∀ n : Fin 50, dimF (n.val + 7050) ≤ 22 := by decide
private theorem pos_w141 : ∀ n : Fin 50, 0 < dimF (n.val + 7050) := by decide
private theorem le_w142 : ∀ n : Fin 50, dimF (n.val + 7100) ≤ 22 := by decide
private theorem pos_w142 : ∀ n : Fin 50, 0 < dimF (n.val + 7100) := by decide
private theorem le_w143 : ∀ n : Fin 50, dimF (n.val + 7150) ≤ 22 := by decide
private theorem pos_w143 : ∀ n : Fin 50, 0 < dimF (n.val + 7150) := by decide
private theorem le_w144 : ∀ n : Fin 50, dimF (n.val + 7200) ≤ 22 := by decide
private theorem pos_w144 : ∀ n : Fin 50, 0 < dimF (n.val + 7200) := by decide
private theorem le_w145 : ∀ n : Fin 50, dimF (n.val + 7250) ≤ 22 := by decide
private theorem pos_w145 : ∀ n : Fin 50, 0 < dimF (n.val + 7250) := by decide
private theorem le_w146 : ∀ n : Fin 50, dimF (n.val + 7300) ≤ 22 := by decide
private theorem pos_w146 : ∀ n : Fin 50, 0 < dimF (n.val + 7300) := by decide
private theorem le_w147 : ∀ n : Fin 50, dimF (n.val + 7350) ≤ 22 := by decide
private theorem pos_w147 : ∀ n : Fin 50, 0 < dimF (n.val + 7350) := by decide
private theorem le_w148 : ∀ n : Fin 50, dimF (n.val + 7400) ≤ 22 := by decide
private theorem pos_w148 : ∀ n : Fin 50, 0 < dimF (n.val + 7400) := by decide
private theorem le_w149 : ∀ n : Fin 50, dimF (n.val + 7450) ≤ 22 := by decide
private theorem pos_w149 : ∀ n : Fin 50, 0 < dimF (n.val + 7450) := by decide
private theorem le_w150 : ∀ n : Fin 50, dimF (n.val + 7500) ≤ 22 := by decide
private theorem pos_w150 : ∀ n : Fin 50, 0 < dimF (n.val + 7500) := by decide
private theorem le_w151 : ∀ n : Fin 50, dimF (n.val + 7550) ≤ 22 := by decide
private theorem pos_w151 : ∀ n : Fin 50, 0 < dimF (n.val + 7550) := by decide
private theorem le_w152 : ∀ n : Fin 50, dimF (n.val + 7600) ≤ 22 := by decide
private theorem pos_w152 : ∀ n : Fin 50, 0 < dimF (n.val + 7600) := by decide
private theorem le_w153 : ∀ n : Fin 50, dimF (n.val + 7650) ≤ 22 := by decide
private theorem pos_w153 : ∀ n : Fin 50, 0 < dimF (n.val + 7650) := by decide
private theorem le_w154 : ∀ n : Fin 50, dimF (n.val + 7700) ≤ 22 := by decide
private theorem pos_w154 : ∀ n : Fin 50, 0 < dimF (n.val + 7700) := by decide
private theorem le_w155 : ∀ n : Fin 50, dimF (n.val + 7750) ≤ 22 := by decide
private theorem pos_w155 : ∀ n : Fin 50, 0 < dimF (n.val + 7750) := by decide
private theorem le_w156 : ∀ n : Fin 50, dimF (n.val + 7800) ≤ 22 := by decide
private theorem pos_w156 : ∀ n : Fin 50, 0 < dimF (n.val + 7800) := by decide
private theorem le_w157 : ∀ n : Fin 50, dimF (n.val + 7850) ≤ 22 := by decide
private theorem pos_w157 : ∀ n : Fin 50, 0 < dimF (n.val + 7850) := by decide
private theorem le_w158 : ∀ n : Fin 50, dimF (n.val + 7900) ≤ 22 := by decide
private theorem pos_w158 : ∀ n : Fin 50, 0 < dimF (n.val + 7900) := by decide
private theorem le_w159 : ∀ n : Fin 50, dimF (n.val + 7950) ≤ 22 := by decide
private theorem pos_w159 : ∀ n : Fin 50, 0 < dimF (n.val + 7950) := by decide
private theorem le_w160 : ∀ n : Fin 50, dimF (n.val + 8000) ≤ 22 := by decide
private theorem pos_w160 : ∀ n : Fin 50, 0 < dimF (n.val + 8000) := by decide
private theorem le_w161 : ∀ n : Fin 50, dimF (n.val + 8050) ≤ 22 := by decide
private theorem pos_w161 : ∀ n : Fin 50, 0 < dimF (n.val + 8050) := by decide
private theorem le_w162 : ∀ n : Fin 50, dimF (n.val + 8100) ≤ 22 := by decide
private theorem pos_w162 : ∀ n : Fin 50, 0 < dimF (n.val + 8100) := by decide
private theorem le_w163 : ∀ n : Fin 50, dimF (n.val + 8150) ≤ 22 := by decide
private theorem pos_w163 : ∀ n : Fin 50, 0 < dimF (n.val + 8150) := by decide
private theorem le_w164 : ∀ n : Fin 50, dimF (n.val + 8200) ≤ 22 := by decide
private theorem pos_w164 : ∀ n : Fin 50, 0 < dimF (n.val + 8200) := by decide
private theorem le_w165 : ∀ n : Fin 50, dimF (n.val + 8250) ≤ 22 := by decide
private theorem pos_w165 : ∀ n : Fin 50, 0 < dimF (n.val + 8250) := by decide
private theorem le_w166 : ∀ n : Fin 50, dimF (n.val + 8300) ≤ 22 := by decide
private theorem pos_w166 : ∀ n : Fin 50, 0 < dimF (n.val + 8300) := by decide
private theorem le_w167 : ∀ n : Fin 50, dimF (n.val + 8350) ≤ 22 := by decide
private theorem pos_w167 : ∀ n : Fin 50, 0 < dimF (n.val + 8350) := by decide
private theorem le_w168 : ∀ n : Fin 50, dimF (n.val + 8400) ≤ 22 := by decide
private theorem pos_w168 : ∀ n : Fin 50, 0 < dimF (n.val + 8400) := by decide
private theorem le_w169 : ∀ n : Fin 50, dimF (n.val + 8450) ≤ 22 := by decide
private theorem pos_w169 : ∀ n : Fin 50, 0 < dimF (n.val + 8450) := by decide
private theorem le_w170 : ∀ n : Fin 50, dimF (n.val + 8500) ≤ 22 := by decide
private theorem pos_w170 : ∀ n : Fin 50, 0 < dimF (n.val + 8500) := by decide
private theorem le_w171 : ∀ n : Fin 50, dimF (n.val + 8550) ≤ 22 := by decide
private theorem pos_w171 : ∀ n : Fin 50, 0 < dimF (n.val + 8550) := by decide
private theorem le_w172 : ∀ n : Fin 50, dimF (n.val + 8600) ≤ 22 := by decide
private theorem pos_w172 : ∀ n : Fin 50, 0 < dimF (n.val + 8600) := by decide
private theorem le_w173 : ∀ n : Fin 50, dimF (n.val + 8650) ≤ 22 := by decide
private theorem pos_w173 : ∀ n : Fin 50, 0 < dimF (n.val + 8650) := by decide
private theorem le_w174 : ∀ n : Fin 50, dimF (n.val + 8700) ≤ 22 := by decide
private theorem pos_w174 : ∀ n : Fin 50, 0 < dimF (n.val + 8700) := by decide
private theorem le_w175 : ∀ n : Fin 50, dimF (n.val + 8750) ≤ 22 := by decide
private theorem pos_w175 : ∀ n : Fin 50, 0 < dimF (n.val + 8750) := by decide
private theorem le_w176 : ∀ n : Fin 50, dimF (n.val + 8800) ≤ 22 := by decide
private theorem pos_w176 : ∀ n : Fin 50, 0 < dimF (n.val + 8800) := by decide
private theorem le_w177 : ∀ n : Fin 50, dimF (n.val + 8850) ≤ 22 := by decide
private theorem pos_w177 : ∀ n : Fin 50, 0 < dimF (n.val + 8850) := by decide
private theorem le_w178 : ∀ n : Fin 50, dimF (n.val + 8900) ≤ 22 := by decide
private theorem pos_w178 : ∀ n : Fin 50, 0 < dimF (n.val + 8900) := by decide
private theorem le_w179 : ∀ n : Fin 50, dimF (n.val + 8950) ≤ 22 := by decide
private theorem pos_w179 : ∀ n : Fin 50, 0 < dimF (n.val + 8950) := by decide
private theorem le_w180 : ∀ n : Fin 50, dimF (n.val + 9000) ≤ 22 := by decide
private theorem pos_w180 : ∀ n : Fin 50, 0 < dimF (n.val + 9000) := by decide
private theorem le_w181 : ∀ n : Fin 50, dimF (n.val + 9050) ≤ 22 := by decide
private theorem pos_w181 : ∀ n : Fin 50, 0 < dimF (n.val + 9050) := by decide
private theorem le_w182 : ∀ n : Fin 50, dimF (n.val + 9100) ≤ 22 := by decide
private theorem pos_w182 : ∀ n : Fin 50, 0 < dimF (n.val + 9100) := by decide
private theorem le_w183 : ∀ n : Fin 50, dimF (n.val + 9150) ≤ 22 := by decide
private theorem pos_w183 : ∀ n : Fin 50, 0 < dimF (n.val + 9150) := by decide
private theorem le_w184 : ∀ n : Fin 50, dimF (n.val + 9200) ≤ 22 := by decide
private theorem pos_w184 : ∀ n : Fin 50, 0 < dimF (n.val + 9200) := by decide
private theorem le_w185 : ∀ n : Fin 50, dimF (n.val + 9250) ≤ 22 := by decide
private theorem pos_w185 : ∀ n : Fin 50, 0 < dimF (n.val + 9250) := by decide
private theorem le_w186 : ∀ n : Fin 50, dimF (n.val + 9300) ≤ 22 := by decide
private theorem pos_w186 : ∀ n : Fin 50, 0 < dimF (n.val + 9300) := by decide
private theorem le_w187 : ∀ n : Fin 50, dimF (n.val + 9350) ≤ 22 := by decide
private theorem pos_w187 : ∀ n : Fin 50, 0 < dimF (n.val + 9350) := by decide
private theorem le_w188 : ∀ n : Fin 50, dimF (n.val + 9400) ≤ 22 := by decide
private theorem pos_w188 : ∀ n : Fin 50, 0 < dimF (n.val + 9400) := by decide
private theorem le_w189 : ∀ n : Fin 50, dimF (n.val + 9450) ≤ 22 := by decide
private theorem pos_w189 : ∀ n : Fin 50, 0 < dimF (n.val + 9450) := by decide
private theorem le_w190 : ∀ n : Fin 50, dimF (n.val + 9500) ≤ 22 := by decide
private theorem pos_w190 : ∀ n : Fin 50, 0 < dimF (n.val + 9500) := by decide
private theorem le_w191 : ∀ n : Fin 50, dimF (n.val + 9550) ≤ 22 := by decide
private theorem pos_w191 : ∀ n : Fin 50, 0 < dimF (n.val + 9550) := by decide
private theorem le_w192 : ∀ n : Fin 50, dimF (n.val + 9600) ≤ 22 := by decide
private theorem pos_w192 : ∀ n : Fin 50, 0 < dimF (n.val + 9600) := by decide
private theorem le_w193 : ∀ n : Fin 50, dimF (n.val + 9650) ≤ 22 := by decide
private theorem pos_w193 : ∀ n : Fin 50, 0 < dimF (n.val + 9650) := by decide
private theorem le_w194 : ∀ n : Fin 50, dimF (n.val + 9700) ≤ 22 := by decide
private theorem pos_w194 : ∀ n : Fin 50, 0 < dimF (n.val + 9700) := by decide
private theorem le_w195 : ∀ n : Fin 50, dimF (n.val + 9750) ≤ 22 := by decide
private theorem pos_w195 : ∀ n : Fin 50, 0 < dimF (n.val + 9750) := by decide
private theorem le_w196 : ∀ n : Fin 50, dimF (n.val + 9800) ≤ 22 := by decide
private theorem pos_w196 : ∀ n : Fin 50, 0 < dimF (n.val + 9800) := by decide
private theorem le_w197 : ∀ n : Fin 50, dimF (n.val + 9850) ≤ 22 := by decide
private theorem pos_w197 : ∀ n : Fin 50, 0 < dimF (n.val + 9850) := by decide
private theorem le_w198 : ∀ n : Fin 50, dimF (n.val + 9900) ≤ 22 := by decide
private theorem pos_w198 : ∀ n : Fin 50, 0 < dimF (n.val + 9900) := by decide
private theorem le_w199 : ∀ n : Fin 50, dimF (n.val + 9950) ≤ 22 := by decide
private theorem pos_w199 : ∀ n : Fin 50, 0 < dimF (n.val + 9950) := by decide

theorem dimF_le_22_range : ∀ n, 5000 ≤ n → n < 10000 → dimF n ≤ 22 := by
  intro n hlo hhi
  by_cases h0 : n < 5050
  · have hr : n - 5000 < 50 := by omega
    have heq : n = (n - 5000) + 5000 := by omega
    rw [heq]
    exact le_w100 ⟨n - 5000, hr⟩
  · by_cases h1 : n < 5100
    · have hr : n - 5050 < 50 := by omega
      have heq : n = (n - 5050) + 5050 := by omega
      rw [heq]
      exact le_w101 ⟨n - 5050, hr⟩
    · by_cases h2 : n < 5150
      · have hr : n - 5100 < 50 := by omega
        have heq : n = (n - 5100) + 5100 := by omega
        rw [heq]
        exact le_w102 ⟨n - 5100, hr⟩
      · by_cases h3 : n < 5200
        · have hr : n - 5150 < 50 := by omega
          have heq : n = (n - 5150) + 5150 := by omega
          rw [heq]
          exact le_w103 ⟨n - 5150, hr⟩
        · by_cases h4 : n < 5250
          · have hr : n - 5200 < 50 := by omega
            have heq : n = (n - 5200) + 5200 := by omega
            rw [heq]
            exact le_w104 ⟨n - 5200, hr⟩
          · by_cases h5 : n < 5300
            · have hr : n - 5250 < 50 := by omega
              have heq : n = (n - 5250) + 5250 := by omega
              rw [heq]
              exact le_w105 ⟨n - 5250, hr⟩
            · by_cases h6 : n < 5350
              · have hr : n - 5300 < 50 := by omega
                have heq : n = (n - 5300) + 5300 := by omega
                rw [heq]
                exact le_w106 ⟨n - 5300, hr⟩
              · by_cases h7 : n < 5400
                · have hr : n - 5350 < 50 := by omega
                  have heq : n = (n - 5350) + 5350 := by omega
                  rw [heq]
                  exact le_w107 ⟨n - 5350, hr⟩
                · by_cases h8 : n < 5450
                  · have hr : n - 5400 < 50 := by omega
                    have heq : n = (n - 5400) + 5400 := by omega
                    rw [heq]
                    exact le_w108 ⟨n - 5400, hr⟩
                  · by_cases h9 : n < 5500
                    · have hr : n - 5450 < 50 := by omega
                      have heq : n = (n - 5450) + 5450 := by omega
                      rw [heq]
                      exact le_w109 ⟨n - 5450, hr⟩
                    · by_cases h10 : n < 5550
                      · have hr : n - 5500 < 50 := by omega
                        have heq : n = (n - 5500) + 5500 := by omega
                        rw [heq]
                        exact le_w110 ⟨n - 5500, hr⟩
                      · by_cases h11 : n < 5600
                        · have hr : n - 5550 < 50 := by omega
                          have heq : n = (n - 5550) + 5550 := by omega
                          rw [heq]
                          exact le_w111 ⟨n - 5550, hr⟩
                        · by_cases h12 : n < 5650
                          · have hr : n - 5600 < 50 := by omega
                            have heq : n = (n - 5600) + 5600 := by omega
                            rw [heq]
                            exact le_w112 ⟨n - 5600, hr⟩
                          · by_cases h13 : n < 5700
                            · have hr : n - 5650 < 50 := by omega
                              have heq : n = (n - 5650) + 5650 := by omega
                              rw [heq]
                              exact le_w113 ⟨n - 5650, hr⟩
                            · by_cases h14 : n < 5750
                              · have hr : n - 5700 < 50 := by omega
                                have heq : n = (n - 5700) + 5700 := by omega
                                rw [heq]
                                exact le_w114 ⟨n - 5700, hr⟩
                              · by_cases h15 : n < 5800
                                · have hr : n - 5750 < 50 := by omega
                                  have heq : n = (n - 5750) + 5750 := by omega
                                  rw [heq]
                                  exact le_w115 ⟨n - 5750, hr⟩
                                · by_cases h16 : n < 5850
                                  · have hr : n - 5800 < 50 := by omega
                                    have heq : n = (n - 5800) + 5800 := by omega
                                    rw [heq]
                                    exact le_w116 ⟨n - 5800, hr⟩
                                  · by_cases h17 : n < 5900
                                    · have hr : n - 5850 < 50 := by omega
                                      have heq : n = (n - 5850) + 5850 := by omega
                                      rw [heq]
                                      exact le_w117 ⟨n - 5850, hr⟩
                                    · by_cases h18 : n < 5950
                                      · have hr : n - 5900 < 50 := by omega
                                        have heq : n = (n - 5900) + 5900 := by omega
                                        rw [heq]
                                        exact le_w118 ⟨n - 5900, hr⟩
                                      · by_cases h19 : n < 6000
                                        · have hr : n - 5950 < 50 := by omega
                                          have heq : n = (n - 5950) + 5950 := by omega
                                          rw [heq]
                                          exact le_w119 ⟨n - 5950, hr⟩
                                        · by_cases h20 : n < 6050
                                          · have hr : n - 6000 < 50 := by omega
                                            have heq : n = (n - 6000) + 6000 := by omega
                                            rw [heq]
                                            exact le_w120 ⟨n - 6000, hr⟩
                                          · by_cases h21 : n < 6100
                                            · have hr : n - 6050 < 50 := by omega
                                              have heq : n = (n - 6050) + 6050 := by omega
                                              rw [heq]
                                              exact le_w121 ⟨n - 6050, hr⟩
                                            · by_cases h22 : n < 6150
                                              · have hr : n - 6100 < 50 := by omega
                                                have heq : n = (n - 6100) + 6100 := by omega
                                                rw [heq]
                                                exact le_w122 ⟨n - 6100, hr⟩
                                              · by_cases h23 : n < 6200
                                                · have hr : n - 6150 < 50 := by omega
                                                  have heq : n = (n - 6150) + 6150 := by omega
                                                  rw [heq]
                                                  exact le_w123 ⟨n - 6150, hr⟩
                                                · by_cases h24 : n < 6250
                                                  · have hr : n - 6200 < 50 := by omega
                                                    have heq : n = (n - 6200) + 6200 := by omega
                                                    rw [heq]
                                                    exact le_w124 ⟨n - 6200, hr⟩
                                                  · by_cases h25 : n < 6300
                                                    · have hr : n - 6250 < 50 := by omega
                                                      have heq : n = (n - 6250) + 6250 := by omega
                                                      rw [heq]
                                                      exact le_w125 ⟨n - 6250, hr⟩
                                                    · by_cases h26 : n < 6350
                                                      · have hr : n - 6300 < 50 := by omega
                                                        have heq : n = (n - 6300) + 6300 := by omega
                                                        rw [heq]
                                                        exact le_w126 ⟨n - 6300, hr⟩
                                                      · by_cases h27 : n < 6400
                                                        · have hr : n - 6350 < 50 := by omega
                                                          have heq : n = (n - 6350) + 6350 := by omega
                                                          rw [heq]
                                                          exact le_w127 ⟨n - 6350, hr⟩
                                                        · by_cases h28 : n < 6450
                                                          · have hr : n - 6400 < 50 := by omega
                                                            have heq : n = (n - 6400) + 6400 := by omega
                                                            rw [heq]
                                                            exact le_w128 ⟨n - 6400, hr⟩
                                                          · by_cases h29 : n < 6500
                                                            · have hr : n - 6450 < 50 := by omega
                                                              have heq : n = (n - 6450) + 6450 := by omega
                                                              rw [heq]
                                                              exact le_w129 ⟨n - 6450, hr⟩
                                                            · by_cases h30 : n < 6550
                                                              · have hr : n - 6500 < 50 := by omega
                                                                have heq : n = (n - 6500) + 6500 := by omega
                                                                rw [heq]
                                                                exact le_w130 ⟨n - 6500, hr⟩
                                                              · by_cases h31 : n < 6600
                                                                · have hr : n - 6550 < 50 := by omega
                                                                  have heq : n = (n - 6550) + 6550 := by omega
                                                                  rw [heq]
                                                                  exact le_w131 ⟨n - 6550, hr⟩
                                                                · by_cases h32 : n < 6650
                                                                  · have hr : n - 6600 < 50 := by omega
                                                                    have heq : n = (n - 6600) + 6600 := by omega
                                                                    rw [heq]
                                                                    exact le_w132 ⟨n - 6600, hr⟩
                                                                  · by_cases h33 : n < 6700
                                                                    · have hr : n - 6650 < 50 := by omega
                                                                      have heq : n = (n - 6650) + 6650 := by omega
                                                                      rw [heq]
                                                                      exact le_w133 ⟨n - 6650, hr⟩
                                                                    · by_cases h34 : n < 6750
                                                                      · have hr : n - 6700 < 50 := by omega
                                                                        have heq : n = (n - 6700) + 6700 := by omega
                                                                        rw [heq]
                                                                        exact le_w134 ⟨n - 6700, hr⟩
                                                                      · by_cases h35 : n < 6800
                                                                        · have hr : n - 6750 < 50 := by omega
                                                                          have heq : n = (n - 6750) + 6750 := by omega
                                                                          rw [heq]
                                                                          exact le_w135 ⟨n - 6750, hr⟩
                                                                        · by_cases h36 : n < 6850
                                                                          · have hr : n - 6800 < 50 := by omega
                                                                            have heq : n = (n - 6800) + 6800 := by omega
                                                                            rw [heq]
                                                                            exact le_w136 ⟨n - 6800, hr⟩
                                                                          · by_cases h37 : n < 6900
                                                                            · have hr : n - 6850 < 50 := by omega
                                                                              have heq : n = (n - 6850) + 6850 := by omega
                                                                              rw [heq]
                                                                              exact le_w137 ⟨n - 6850, hr⟩
                                                                            · by_cases h38 : n < 6950
                                                                              · have hr : n - 6900 < 50 := by omega
                                                                                have heq : n = (n - 6900) + 6900 := by omega
                                                                                rw [heq]
                                                                                exact le_w138 ⟨n - 6900, hr⟩
                                                                              · by_cases h39 : n < 7000
                                                                                · have hr : n - 6950 < 50 := by omega
                                                                                  have heq : n = (n - 6950) + 6950 := by omega
                                                                                  rw [heq]
                                                                                  exact le_w139 ⟨n - 6950, hr⟩
                                                                                · by_cases h40 : n < 7050
                                                                                  · have hr : n - 7000 < 50 := by omega
                                                                                    have heq : n = (n - 7000) + 7000 := by omega
                                                                                    rw [heq]
                                                                                    exact le_w140 ⟨n - 7000, hr⟩
                                                                                  · by_cases h41 : n < 7100
                                                                                    · have hr : n - 7050 < 50 := by omega
                                                                                      have heq : n = (n - 7050) + 7050 := by omega
                                                                                      rw [heq]
                                                                                      exact le_w141 ⟨n - 7050, hr⟩
                                                                                    · by_cases h42 : n < 7150
                                                                                      · have hr : n - 7100 < 50 := by omega
                                                                                        have heq : n = (n - 7100) + 7100 := by omega
                                                                                        rw [heq]
                                                                                        exact le_w142 ⟨n - 7100, hr⟩
                                                                                      · by_cases h43 : n < 7200
                                                                                        · have hr : n - 7150 < 50 := by omega
                                                                                          have heq : n = (n - 7150) + 7150 := by omega
                                                                                          rw [heq]
                                                                                          exact le_w143 ⟨n - 7150, hr⟩
                                                                                        · by_cases h44 : n < 7250
                                                                                          · have hr : n - 7200 < 50 := by omega
                                                                                            have heq : n = (n - 7200) + 7200 := by omega
                                                                                            rw [heq]
                                                                                            exact le_w144 ⟨n - 7200, hr⟩
                                                                                          · by_cases h45 : n < 7300
                                                                                            · have hr : n - 7250 < 50 := by omega
                                                                                              have heq : n = (n - 7250) + 7250 := by omega
                                                                                              rw [heq]
                                                                                              exact le_w145 ⟨n - 7250, hr⟩
                                                                                            · by_cases h46 : n < 7350
                                                                                              · have hr : n - 7300 < 50 := by omega
                                                                                                have heq : n = (n - 7300) + 7300 := by omega
                                                                                                rw [heq]
                                                                                                exact le_w146 ⟨n - 7300, hr⟩
                                                                                              · by_cases h47 : n < 7400
                                                                                                · have hr : n - 7350 < 50 := by omega
                                                                                                  have heq : n = (n - 7350) + 7350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact le_w147 ⟨n - 7350, hr⟩
                                                                                                · by_cases h48 : n < 7450
                                                                                                  · have hr : n - 7400 < 50 := by omega
                                                                                                    have heq : n = (n - 7400) + 7400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact le_w148 ⟨n - 7400, hr⟩
                                                                                                  · by_cases h49 : n < 7500
                                                                                                    · have hr : n - 7450 < 50 := by omega
                                                                                                      have heq : n = (n - 7450) + 7450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact le_w149 ⟨n - 7450, hr⟩
                                                                                                    · by_cases h50 : n < 7550
                                                                                                      · have hr : n - 7500 < 50 := by omega
                                                                                                        have heq : n = (n - 7500) + 7500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact le_w150 ⟨n - 7500, hr⟩
                                                                                                      · by_cases h51 : n < 7600
                                                                                                        · have hr : n - 7550 < 50 := by omega
                                                                                                          have heq : n = (n - 7550) + 7550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact le_w151 ⟨n - 7550, hr⟩
                                                                                                        · by_cases h52 : n < 7650
                                                                                                          · have hr : n - 7600 < 50 := by omega
                                                                                                            have heq : n = (n - 7600) + 7600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact le_w152 ⟨n - 7600, hr⟩
                                                                                                          · by_cases h53 : n < 7700
                                                                                                            · have hr : n - 7650 < 50 := by omega
                                                                                                              have heq : n = (n - 7650) + 7650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact le_w153 ⟨n - 7650, hr⟩
                                                                                                            · by_cases h54 : n < 7750
                                                                                                              · have hr : n - 7700 < 50 := by omega
                                                                                                                have heq : n = (n - 7700) + 7700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact le_w154 ⟨n - 7700, hr⟩
                                                                                                              · by_cases h55 : n < 7800
                                                                                                                · have hr : n - 7750 < 50 := by omega
                                                                                                                  have heq : n = (n - 7750) + 7750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact le_w155 ⟨n - 7750, hr⟩
                                                                                                                · by_cases h56 : n < 7850
                                                                                                                  · have hr : n - 7800 < 50 := by omega
                                                                                                                    have heq : n = (n - 7800) + 7800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact le_w156 ⟨n - 7800, hr⟩
                                                                                                                  · by_cases h57 : n < 7900
                                                                                                                    · have hr : n - 7850 < 50 := by omega
                                                                                                                      have heq : n = (n - 7850) + 7850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact le_w157 ⟨n - 7850, hr⟩
                                                                                                                    · by_cases h58 : n < 7950
                                                                                                                      · have hr : n - 7900 < 50 := by omega
                                                                                                                        have heq : n = (n - 7900) + 7900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact le_w158 ⟨n - 7900, hr⟩
                                                                                                                      · by_cases h59 : n < 8000
                                                                                                                        · have hr : n - 7950 < 50 := by omega
                                                                                                                          have heq : n = (n - 7950) + 7950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact le_w159 ⟨n - 7950, hr⟩
                                                                                                                        · by_cases h60 : n < 8050
                                                                                                                          · have hr : n - 8000 < 50 := by omega
                                                                                                                            have heq : n = (n - 8000) + 8000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact le_w160 ⟨n - 8000, hr⟩
                                                                                                                          · by_cases h61 : n < 8100
                                                                                                                            · have hr : n - 8050 < 50 := by omega
                                                                                                                              have heq : n = (n - 8050) + 8050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact le_w161 ⟨n - 8050, hr⟩
                                                                                                                            · by_cases h62 : n < 8150
                                                                                                                              · have hr : n - 8100 < 50 := by omega
                                                                                                                                have heq : n = (n - 8100) + 8100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact le_w162 ⟨n - 8100, hr⟩
                                                                                                                              · by_cases h63 : n < 8200
                                                                                                                                · have hr : n - 8150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 8150) + 8150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact le_w163 ⟨n - 8150, hr⟩
                                                                                                                                · by_cases h64 : n < 8250
                                                                                                                                  · have hr : n - 8200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 8200) + 8200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact le_w164 ⟨n - 8200, hr⟩
                                                                                                                                  · by_cases h65 : n < 8300
                                                                                                                                    · have hr : n - 8250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 8250) + 8250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact le_w165 ⟨n - 8250, hr⟩
                                                                                                                                    · by_cases h66 : n < 8350
                                                                                                                                      · have hr : n - 8300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 8300) + 8300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact le_w166 ⟨n - 8300, hr⟩
                                                                                                                                      · by_cases h67 : n < 8400
                                                                                                                                        · have hr : n - 8350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 8350) + 8350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact le_w167 ⟨n - 8350, hr⟩
                                                                                                                                        · by_cases h68 : n < 8450
                                                                                                                                          · have hr : n - 8400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 8400) + 8400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact le_w168 ⟨n - 8400, hr⟩
                                                                                                                                          · by_cases h69 : n < 8500
                                                                                                                                            · have hr : n - 8450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 8450) + 8450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact le_w169 ⟨n - 8450, hr⟩
                                                                                                                                            · by_cases h70 : n < 8550
                                                                                                                                              · have hr : n - 8500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 8500) + 8500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact le_w170 ⟨n - 8500, hr⟩
                                                                                                                                              · by_cases h71 : n < 8600
                                                                                                                                                · have hr : n - 8550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 8550) + 8550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact le_w171 ⟨n - 8550, hr⟩
                                                                                                                                                · by_cases h72 : n < 8650
                                                                                                                                                  · have hr : n - 8600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 8600) + 8600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact le_w172 ⟨n - 8600, hr⟩
                                                                                                                                                  · by_cases h73 : n < 8700
                                                                                                                                                    · have hr : n - 8650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 8650) + 8650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact le_w173 ⟨n - 8650, hr⟩
                                                                                                                                                    · by_cases h74 : n < 8750
                                                                                                                                                      · have hr : n - 8700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 8700) + 8700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact le_w174 ⟨n - 8700, hr⟩
                                                                                                                                                      · by_cases h75 : n < 8800
                                                                                                                                                        · have hr : n - 8750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 8750) + 8750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact le_w175 ⟨n - 8750, hr⟩
                                                                                                                                                        · by_cases h76 : n < 8850
                                                                                                                                                          · have hr : n - 8800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 8800) + 8800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact le_w176 ⟨n - 8800, hr⟩
                                                                                                                                                          · by_cases h77 : n < 8900
                                                                                                                                                            · have hr : n - 8850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 8850) + 8850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact le_w177 ⟨n - 8850, hr⟩
                                                                                                                                                            · by_cases h78 : n < 8950
                                                                                                                                                              · have hr : n - 8900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 8900) + 8900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact le_w178 ⟨n - 8900, hr⟩
                                                                                                                                                              · by_cases h79 : n < 9000
                                                                                                                                                                · have hr : n - 8950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 8950) + 8950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact le_w179 ⟨n - 8950, hr⟩
                                                                                                                                                                · by_cases h80 : n < 9050
                                                                                                                                                                  · have hr : n - 9000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 9000) + 9000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact le_w180 ⟨n - 9000, hr⟩
                                                                                                                                                                  · by_cases h81 : n < 9100
                                                                                                                                                                    · have hr : n - 9050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 9050) + 9050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact le_w181 ⟨n - 9050, hr⟩
                                                                                                                                                                    · by_cases h82 : n < 9150
                                                                                                                                                                      · have hr : n - 9100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 9100) + 9100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact le_w182 ⟨n - 9100, hr⟩
                                                                                                                                                                      · by_cases h83 : n < 9200
                                                                                                                                                                        · have hr : n - 9150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 9150) + 9150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact le_w183 ⟨n - 9150, hr⟩
                                                                                                                                                                        · by_cases h84 : n < 9250
                                                                                                                                                                          · have hr : n - 9200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 9200) + 9200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact le_w184 ⟨n - 9200, hr⟩
                                                                                                                                                                          · by_cases h85 : n < 9300
                                                                                                                                                                            · have hr : n - 9250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 9250) + 9250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact le_w185 ⟨n - 9250, hr⟩
                                                                                                                                                                            · by_cases h86 : n < 9350
                                                                                                                                                                              · have hr : n - 9300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 9300) + 9300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact le_w186 ⟨n - 9300, hr⟩
                                                                                                                                                                              · by_cases h87 : n < 9400
                                                                                                                                                                                · have hr : n - 9350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 9350) + 9350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact le_w187 ⟨n - 9350, hr⟩
                                                                                                                                                                                · by_cases h88 : n < 9450
                                                                                                                                                                                  · have hr : n - 9400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 9400) + 9400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact le_w188 ⟨n - 9400, hr⟩
                                                                                                                                                                                  · by_cases h89 : n < 9500
                                                                                                                                                                                    · have hr : n - 9450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 9450) + 9450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact le_w189 ⟨n - 9450, hr⟩
                                                                                                                                                                                    · by_cases h90 : n < 9550
                                                                                                                                                                                      · have hr : n - 9500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 9500) + 9500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact le_w190 ⟨n - 9500, hr⟩
                                                                                                                                                                                      · by_cases h91 : n < 9600
                                                                                                                                                                                        · have hr : n - 9550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 9550) + 9550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact le_w191 ⟨n - 9550, hr⟩
                                                                                                                                                                                        · by_cases h92 : n < 9650
                                                                                                                                                                                          · have hr : n - 9600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 9600) + 9600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact le_w192 ⟨n - 9600, hr⟩
                                                                                                                                                                                          · by_cases h93 : n < 9700
                                                                                                                                                                                            · have hr : n - 9650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 9650) + 9650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact le_w193 ⟨n - 9650, hr⟩
                                                                                                                                                                                            · by_cases h94 : n < 9750
                                                                                                                                                                                              · have hr : n - 9700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 9700) + 9700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact le_w194 ⟨n - 9700, hr⟩
                                                                                                                                                                                              · by_cases h95 : n < 9800
                                                                                                                                                                                                · have hr : n - 9750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 9750) + 9750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact le_w195 ⟨n - 9750, hr⟩
                                                                                                                                                                                                · by_cases h96 : n < 9850
                                                                                                                                                                                                  · have hr : n - 9800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 9800) + 9800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact le_w196 ⟨n - 9800, hr⟩
                                                                                                                                                                                                  · by_cases h97 : n < 9900
                                                                                                                                                                                                    · have hr : n - 9850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 9850) + 9850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact le_w197 ⟨n - 9850, hr⟩
                                                                                                                                                                                                    · by_cases h98 : n < 9950
                                                                                                                                                                                                      · have hr : n - 9900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 9900) + 9900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact le_w198 ⟨n - 9900, hr⟩
                                                                                                                                                                                                      · by_cases h99 : n < 10000
                                                                                                                                                                                                        · have hr : n - 9950 < 50 := by omega
                                                                                                                                                                                                          have heq : n = (n - 9950) + 9950 := by omega
                                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                                          exact le_w199 ⟨n - 9950, hr⟩
                                                                                                                                                                                                        · omega

theorem dimF_pos_range : ∀ n, 5000 ≤ n → n < 10000 → 0 < dimF n := by
  intro n hlo hhi
  by_cases h0 : n < 5050
  · have hr : n - 5000 < 50 := by omega
    have heq : n = (n - 5000) + 5000 := by omega
    rw [heq]
    exact pos_w100 ⟨n - 5000, hr⟩
  · by_cases h1 : n < 5100
    · have hr : n - 5050 < 50 := by omega
      have heq : n = (n - 5050) + 5050 := by omega
      rw [heq]
      exact pos_w101 ⟨n - 5050, hr⟩
    · by_cases h2 : n < 5150
      · have hr : n - 5100 < 50 := by omega
        have heq : n = (n - 5100) + 5100 := by omega
        rw [heq]
        exact pos_w102 ⟨n - 5100, hr⟩
      · by_cases h3 : n < 5200
        · have hr : n - 5150 < 50 := by omega
          have heq : n = (n - 5150) + 5150 := by omega
          rw [heq]
          exact pos_w103 ⟨n - 5150, hr⟩
        · by_cases h4 : n < 5250
          · have hr : n - 5200 < 50 := by omega
            have heq : n = (n - 5200) + 5200 := by omega
            rw [heq]
            exact pos_w104 ⟨n - 5200, hr⟩
          · by_cases h5 : n < 5300
            · have hr : n - 5250 < 50 := by omega
              have heq : n = (n - 5250) + 5250 := by omega
              rw [heq]
              exact pos_w105 ⟨n - 5250, hr⟩
            · by_cases h6 : n < 5350
              · have hr : n - 5300 < 50 := by omega
                have heq : n = (n - 5300) + 5300 := by omega
                rw [heq]
                exact pos_w106 ⟨n - 5300, hr⟩
              · by_cases h7 : n < 5400
                · have hr : n - 5350 < 50 := by omega
                  have heq : n = (n - 5350) + 5350 := by omega
                  rw [heq]
                  exact pos_w107 ⟨n - 5350, hr⟩
                · by_cases h8 : n < 5450
                  · have hr : n - 5400 < 50 := by omega
                    have heq : n = (n - 5400) + 5400 := by omega
                    rw [heq]
                    exact pos_w108 ⟨n - 5400, hr⟩
                  · by_cases h9 : n < 5500
                    · have hr : n - 5450 < 50 := by omega
                      have heq : n = (n - 5450) + 5450 := by omega
                      rw [heq]
                      exact pos_w109 ⟨n - 5450, hr⟩
                    · by_cases h10 : n < 5550
                      · have hr : n - 5500 < 50 := by omega
                        have heq : n = (n - 5500) + 5500 := by omega
                        rw [heq]
                        exact pos_w110 ⟨n - 5500, hr⟩
                      · by_cases h11 : n < 5600
                        · have hr : n - 5550 < 50 := by omega
                          have heq : n = (n - 5550) + 5550 := by omega
                          rw [heq]
                          exact pos_w111 ⟨n - 5550, hr⟩
                        · by_cases h12 : n < 5650
                          · have hr : n - 5600 < 50 := by omega
                            have heq : n = (n - 5600) + 5600 := by omega
                            rw [heq]
                            exact pos_w112 ⟨n - 5600, hr⟩
                          · by_cases h13 : n < 5700
                            · have hr : n - 5650 < 50 := by omega
                              have heq : n = (n - 5650) + 5650 := by omega
                              rw [heq]
                              exact pos_w113 ⟨n - 5650, hr⟩
                            · by_cases h14 : n < 5750
                              · have hr : n - 5700 < 50 := by omega
                                have heq : n = (n - 5700) + 5700 := by omega
                                rw [heq]
                                exact pos_w114 ⟨n - 5700, hr⟩
                              · by_cases h15 : n < 5800
                                · have hr : n - 5750 < 50 := by omega
                                  have heq : n = (n - 5750) + 5750 := by omega
                                  rw [heq]
                                  exact pos_w115 ⟨n - 5750, hr⟩
                                · by_cases h16 : n < 5850
                                  · have hr : n - 5800 < 50 := by omega
                                    have heq : n = (n - 5800) + 5800 := by omega
                                    rw [heq]
                                    exact pos_w116 ⟨n - 5800, hr⟩
                                  · by_cases h17 : n < 5900
                                    · have hr : n - 5850 < 50 := by omega
                                      have heq : n = (n - 5850) + 5850 := by omega
                                      rw [heq]
                                      exact pos_w117 ⟨n - 5850, hr⟩
                                    · by_cases h18 : n < 5950
                                      · have hr : n - 5900 < 50 := by omega
                                        have heq : n = (n - 5900) + 5900 := by omega
                                        rw [heq]
                                        exact pos_w118 ⟨n - 5900, hr⟩
                                      · by_cases h19 : n < 6000
                                        · have hr : n - 5950 < 50 := by omega
                                          have heq : n = (n - 5950) + 5950 := by omega
                                          rw [heq]
                                          exact pos_w119 ⟨n - 5950, hr⟩
                                        · by_cases h20 : n < 6050
                                          · have hr : n - 6000 < 50 := by omega
                                            have heq : n = (n - 6000) + 6000 := by omega
                                            rw [heq]
                                            exact pos_w120 ⟨n - 6000, hr⟩
                                          · by_cases h21 : n < 6100
                                            · have hr : n - 6050 < 50 := by omega
                                              have heq : n = (n - 6050) + 6050 := by omega
                                              rw [heq]
                                              exact pos_w121 ⟨n - 6050, hr⟩
                                            · by_cases h22 : n < 6150
                                              · have hr : n - 6100 < 50 := by omega
                                                have heq : n = (n - 6100) + 6100 := by omega
                                                rw [heq]
                                                exact pos_w122 ⟨n - 6100, hr⟩
                                              · by_cases h23 : n < 6200
                                                · have hr : n - 6150 < 50 := by omega
                                                  have heq : n = (n - 6150) + 6150 := by omega
                                                  rw [heq]
                                                  exact pos_w123 ⟨n - 6150, hr⟩
                                                · by_cases h24 : n < 6250
                                                  · have hr : n - 6200 < 50 := by omega
                                                    have heq : n = (n - 6200) + 6200 := by omega
                                                    rw [heq]
                                                    exact pos_w124 ⟨n - 6200, hr⟩
                                                  · by_cases h25 : n < 6300
                                                    · have hr : n - 6250 < 50 := by omega
                                                      have heq : n = (n - 6250) + 6250 := by omega
                                                      rw [heq]
                                                      exact pos_w125 ⟨n - 6250, hr⟩
                                                    · by_cases h26 : n < 6350
                                                      · have hr : n - 6300 < 50 := by omega
                                                        have heq : n = (n - 6300) + 6300 := by omega
                                                        rw [heq]
                                                        exact pos_w126 ⟨n - 6300, hr⟩
                                                      · by_cases h27 : n < 6400
                                                        · have hr : n - 6350 < 50 := by omega
                                                          have heq : n = (n - 6350) + 6350 := by omega
                                                          rw [heq]
                                                          exact pos_w127 ⟨n - 6350, hr⟩
                                                        · by_cases h28 : n < 6450
                                                          · have hr : n - 6400 < 50 := by omega
                                                            have heq : n = (n - 6400) + 6400 := by omega
                                                            rw [heq]
                                                            exact pos_w128 ⟨n - 6400, hr⟩
                                                          · by_cases h29 : n < 6500
                                                            · have hr : n - 6450 < 50 := by omega
                                                              have heq : n = (n - 6450) + 6450 := by omega
                                                              rw [heq]
                                                              exact pos_w129 ⟨n - 6450, hr⟩
                                                            · by_cases h30 : n < 6550
                                                              · have hr : n - 6500 < 50 := by omega
                                                                have heq : n = (n - 6500) + 6500 := by omega
                                                                rw [heq]
                                                                exact pos_w130 ⟨n - 6500, hr⟩
                                                              · by_cases h31 : n < 6600
                                                                · have hr : n - 6550 < 50 := by omega
                                                                  have heq : n = (n - 6550) + 6550 := by omega
                                                                  rw [heq]
                                                                  exact pos_w131 ⟨n - 6550, hr⟩
                                                                · by_cases h32 : n < 6650
                                                                  · have hr : n - 6600 < 50 := by omega
                                                                    have heq : n = (n - 6600) + 6600 := by omega
                                                                    rw [heq]
                                                                    exact pos_w132 ⟨n - 6600, hr⟩
                                                                  · by_cases h33 : n < 6700
                                                                    · have hr : n - 6650 < 50 := by omega
                                                                      have heq : n = (n - 6650) + 6650 := by omega
                                                                      rw [heq]
                                                                      exact pos_w133 ⟨n - 6650, hr⟩
                                                                    · by_cases h34 : n < 6750
                                                                      · have hr : n - 6700 < 50 := by omega
                                                                        have heq : n = (n - 6700) + 6700 := by omega
                                                                        rw [heq]
                                                                        exact pos_w134 ⟨n - 6700, hr⟩
                                                                      · by_cases h35 : n < 6800
                                                                        · have hr : n - 6750 < 50 := by omega
                                                                          have heq : n = (n - 6750) + 6750 := by omega
                                                                          rw [heq]
                                                                          exact pos_w135 ⟨n - 6750, hr⟩
                                                                        · by_cases h36 : n < 6850
                                                                          · have hr : n - 6800 < 50 := by omega
                                                                            have heq : n = (n - 6800) + 6800 := by omega
                                                                            rw [heq]
                                                                            exact pos_w136 ⟨n - 6800, hr⟩
                                                                          · by_cases h37 : n < 6900
                                                                            · have hr : n - 6850 < 50 := by omega
                                                                              have heq : n = (n - 6850) + 6850 := by omega
                                                                              rw [heq]
                                                                              exact pos_w137 ⟨n - 6850, hr⟩
                                                                            · by_cases h38 : n < 6950
                                                                              · have hr : n - 6900 < 50 := by omega
                                                                                have heq : n = (n - 6900) + 6900 := by omega
                                                                                rw [heq]
                                                                                exact pos_w138 ⟨n - 6900, hr⟩
                                                                              · by_cases h39 : n < 7000
                                                                                · have hr : n - 6950 < 50 := by omega
                                                                                  have heq : n = (n - 6950) + 6950 := by omega
                                                                                  rw [heq]
                                                                                  exact pos_w139 ⟨n - 6950, hr⟩
                                                                                · by_cases h40 : n < 7050
                                                                                  · have hr : n - 7000 < 50 := by omega
                                                                                    have heq : n = (n - 7000) + 7000 := by omega
                                                                                    rw [heq]
                                                                                    exact pos_w140 ⟨n - 7000, hr⟩
                                                                                  · by_cases h41 : n < 7100
                                                                                    · have hr : n - 7050 < 50 := by omega
                                                                                      have heq : n = (n - 7050) + 7050 := by omega
                                                                                      rw [heq]
                                                                                      exact pos_w141 ⟨n - 7050, hr⟩
                                                                                    · by_cases h42 : n < 7150
                                                                                      · have hr : n - 7100 < 50 := by omega
                                                                                        have heq : n = (n - 7100) + 7100 := by omega
                                                                                        rw [heq]
                                                                                        exact pos_w142 ⟨n - 7100, hr⟩
                                                                                      · by_cases h43 : n < 7200
                                                                                        · have hr : n - 7150 < 50 := by omega
                                                                                          have heq : n = (n - 7150) + 7150 := by omega
                                                                                          rw [heq]
                                                                                          exact pos_w143 ⟨n - 7150, hr⟩
                                                                                        · by_cases h44 : n < 7250
                                                                                          · have hr : n - 7200 < 50 := by omega
                                                                                            have heq : n = (n - 7200) + 7200 := by omega
                                                                                            rw [heq]
                                                                                            exact pos_w144 ⟨n - 7200, hr⟩
                                                                                          · by_cases h45 : n < 7300
                                                                                            · have hr : n - 7250 < 50 := by omega
                                                                                              have heq : n = (n - 7250) + 7250 := by omega
                                                                                              rw [heq]
                                                                                              exact pos_w145 ⟨n - 7250, hr⟩
                                                                                            · by_cases h46 : n < 7350
                                                                                              · have hr : n - 7300 < 50 := by omega
                                                                                                have heq : n = (n - 7300) + 7300 := by omega
                                                                                                rw [heq]
                                                                                                exact pos_w146 ⟨n - 7300, hr⟩
                                                                                              · by_cases h47 : n < 7400
                                                                                                · have hr : n - 7350 < 50 := by omega
                                                                                                  have heq : n = (n - 7350) + 7350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact pos_w147 ⟨n - 7350, hr⟩
                                                                                                · by_cases h48 : n < 7450
                                                                                                  · have hr : n - 7400 < 50 := by omega
                                                                                                    have heq : n = (n - 7400) + 7400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact pos_w148 ⟨n - 7400, hr⟩
                                                                                                  · by_cases h49 : n < 7500
                                                                                                    · have hr : n - 7450 < 50 := by omega
                                                                                                      have heq : n = (n - 7450) + 7450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact pos_w149 ⟨n - 7450, hr⟩
                                                                                                    · by_cases h50 : n < 7550
                                                                                                      · have hr : n - 7500 < 50 := by omega
                                                                                                        have heq : n = (n - 7500) + 7500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact pos_w150 ⟨n - 7500, hr⟩
                                                                                                      · by_cases h51 : n < 7600
                                                                                                        · have hr : n - 7550 < 50 := by omega
                                                                                                          have heq : n = (n - 7550) + 7550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact pos_w151 ⟨n - 7550, hr⟩
                                                                                                        · by_cases h52 : n < 7650
                                                                                                          · have hr : n - 7600 < 50 := by omega
                                                                                                            have heq : n = (n - 7600) + 7600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact pos_w152 ⟨n - 7600, hr⟩
                                                                                                          · by_cases h53 : n < 7700
                                                                                                            · have hr : n - 7650 < 50 := by omega
                                                                                                              have heq : n = (n - 7650) + 7650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact pos_w153 ⟨n - 7650, hr⟩
                                                                                                            · by_cases h54 : n < 7750
                                                                                                              · have hr : n - 7700 < 50 := by omega
                                                                                                                have heq : n = (n - 7700) + 7700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact pos_w154 ⟨n - 7700, hr⟩
                                                                                                              · by_cases h55 : n < 7800
                                                                                                                · have hr : n - 7750 < 50 := by omega
                                                                                                                  have heq : n = (n - 7750) + 7750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact pos_w155 ⟨n - 7750, hr⟩
                                                                                                                · by_cases h56 : n < 7850
                                                                                                                  · have hr : n - 7800 < 50 := by omega
                                                                                                                    have heq : n = (n - 7800) + 7800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact pos_w156 ⟨n - 7800, hr⟩
                                                                                                                  · by_cases h57 : n < 7900
                                                                                                                    · have hr : n - 7850 < 50 := by omega
                                                                                                                      have heq : n = (n - 7850) + 7850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact pos_w157 ⟨n - 7850, hr⟩
                                                                                                                    · by_cases h58 : n < 7950
                                                                                                                      · have hr : n - 7900 < 50 := by omega
                                                                                                                        have heq : n = (n - 7900) + 7900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact pos_w158 ⟨n - 7900, hr⟩
                                                                                                                      · by_cases h59 : n < 8000
                                                                                                                        · have hr : n - 7950 < 50 := by omega
                                                                                                                          have heq : n = (n - 7950) + 7950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact pos_w159 ⟨n - 7950, hr⟩
                                                                                                                        · by_cases h60 : n < 8050
                                                                                                                          · have hr : n - 8000 < 50 := by omega
                                                                                                                            have heq : n = (n - 8000) + 8000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact pos_w160 ⟨n - 8000, hr⟩
                                                                                                                          · by_cases h61 : n < 8100
                                                                                                                            · have hr : n - 8050 < 50 := by omega
                                                                                                                              have heq : n = (n - 8050) + 8050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact pos_w161 ⟨n - 8050, hr⟩
                                                                                                                            · by_cases h62 : n < 8150
                                                                                                                              · have hr : n - 8100 < 50 := by omega
                                                                                                                                have heq : n = (n - 8100) + 8100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact pos_w162 ⟨n - 8100, hr⟩
                                                                                                                              · by_cases h63 : n < 8200
                                                                                                                                · have hr : n - 8150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 8150) + 8150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact pos_w163 ⟨n - 8150, hr⟩
                                                                                                                                · by_cases h64 : n < 8250
                                                                                                                                  · have hr : n - 8200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 8200) + 8200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact pos_w164 ⟨n - 8200, hr⟩
                                                                                                                                  · by_cases h65 : n < 8300
                                                                                                                                    · have hr : n - 8250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 8250) + 8250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact pos_w165 ⟨n - 8250, hr⟩
                                                                                                                                    · by_cases h66 : n < 8350
                                                                                                                                      · have hr : n - 8300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 8300) + 8300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact pos_w166 ⟨n - 8300, hr⟩
                                                                                                                                      · by_cases h67 : n < 8400
                                                                                                                                        · have hr : n - 8350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 8350) + 8350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact pos_w167 ⟨n - 8350, hr⟩
                                                                                                                                        · by_cases h68 : n < 8450
                                                                                                                                          · have hr : n - 8400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 8400) + 8400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact pos_w168 ⟨n - 8400, hr⟩
                                                                                                                                          · by_cases h69 : n < 8500
                                                                                                                                            · have hr : n - 8450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 8450) + 8450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact pos_w169 ⟨n - 8450, hr⟩
                                                                                                                                            · by_cases h70 : n < 8550
                                                                                                                                              · have hr : n - 8500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 8500) + 8500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact pos_w170 ⟨n - 8500, hr⟩
                                                                                                                                              · by_cases h71 : n < 8600
                                                                                                                                                · have hr : n - 8550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 8550) + 8550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact pos_w171 ⟨n - 8550, hr⟩
                                                                                                                                                · by_cases h72 : n < 8650
                                                                                                                                                  · have hr : n - 8600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 8600) + 8600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact pos_w172 ⟨n - 8600, hr⟩
                                                                                                                                                  · by_cases h73 : n < 8700
                                                                                                                                                    · have hr : n - 8650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 8650) + 8650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact pos_w173 ⟨n - 8650, hr⟩
                                                                                                                                                    · by_cases h74 : n < 8750
                                                                                                                                                      · have hr : n - 8700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 8700) + 8700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact pos_w174 ⟨n - 8700, hr⟩
                                                                                                                                                      · by_cases h75 : n < 8800
                                                                                                                                                        · have hr : n - 8750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 8750) + 8750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact pos_w175 ⟨n - 8750, hr⟩
                                                                                                                                                        · by_cases h76 : n < 8850
                                                                                                                                                          · have hr : n - 8800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 8800) + 8800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact pos_w176 ⟨n - 8800, hr⟩
                                                                                                                                                          · by_cases h77 : n < 8900
                                                                                                                                                            · have hr : n - 8850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 8850) + 8850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact pos_w177 ⟨n - 8850, hr⟩
                                                                                                                                                            · by_cases h78 : n < 8950
                                                                                                                                                              · have hr : n - 8900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 8900) + 8900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact pos_w178 ⟨n - 8900, hr⟩
                                                                                                                                                              · by_cases h79 : n < 9000
                                                                                                                                                                · have hr : n - 8950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 8950) + 8950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact pos_w179 ⟨n - 8950, hr⟩
                                                                                                                                                                · by_cases h80 : n < 9050
                                                                                                                                                                  · have hr : n - 9000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 9000) + 9000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact pos_w180 ⟨n - 9000, hr⟩
                                                                                                                                                                  · by_cases h81 : n < 9100
                                                                                                                                                                    · have hr : n - 9050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 9050) + 9050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact pos_w181 ⟨n - 9050, hr⟩
                                                                                                                                                                    · by_cases h82 : n < 9150
                                                                                                                                                                      · have hr : n - 9100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 9100) + 9100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact pos_w182 ⟨n - 9100, hr⟩
                                                                                                                                                                      · by_cases h83 : n < 9200
                                                                                                                                                                        · have hr : n - 9150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 9150) + 9150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact pos_w183 ⟨n - 9150, hr⟩
                                                                                                                                                                        · by_cases h84 : n < 9250
                                                                                                                                                                          · have hr : n - 9200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 9200) + 9200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact pos_w184 ⟨n - 9200, hr⟩
                                                                                                                                                                          · by_cases h85 : n < 9300
                                                                                                                                                                            · have hr : n - 9250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 9250) + 9250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact pos_w185 ⟨n - 9250, hr⟩
                                                                                                                                                                            · by_cases h86 : n < 9350
                                                                                                                                                                              · have hr : n - 9300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 9300) + 9300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact pos_w186 ⟨n - 9300, hr⟩
                                                                                                                                                                              · by_cases h87 : n < 9400
                                                                                                                                                                                · have hr : n - 9350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 9350) + 9350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact pos_w187 ⟨n - 9350, hr⟩
                                                                                                                                                                                · by_cases h88 : n < 9450
                                                                                                                                                                                  · have hr : n - 9400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 9400) + 9400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact pos_w188 ⟨n - 9400, hr⟩
                                                                                                                                                                                  · by_cases h89 : n < 9500
                                                                                                                                                                                    · have hr : n - 9450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 9450) + 9450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact pos_w189 ⟨n - 9450, hr⟩
                                                                                                                                                                                    · by_cases h90 : n < 9550
                                                                                                                                                                                      · have hr : n - 9500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 9500) + 9500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact pos_w190 ⟨n - 9500, hr⟩
                                                                                                                                                                                      · by_cases h91 : n < 9600
                                                                                                                                                                                        · have hr : n - 9550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 9550) + 9550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact pos_w191 ⟨n - 9550, hr⟩
                                                                                                                                                                                        · by_cases h92 : n < 9650
                                                                                                                                                                                          · have hr : n - 9600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 9600) + 9600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact pos_w192 ⟨n - 9600, hr⟩
                                                                                                                                                                                          · by_cases h93 : n < 9700
                                                                                                                                                                                            · have hr : n - 9650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 9650) + 9650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact pos_w193 ⟨n - 9650, hr⟩
                                                                                                                                                                                            · by_cases h94 : n < 9750
                                                                                                                                                                                              · have hr : n - 9700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 9700) + 9700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact pos_w194 ⟨n - 9700, hr⟩
                                                                                                                                                                                              · by_cases h95 : n < 9800
                                                                                                                                                                                                · have hr : n - 9750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 9750) + 9750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact pos_w195 ⟨n - 9750, hr⟩
                                                                                                                                                                                                · by_cases h96 : n < 9850
                                                                                                                                                                                                  · have hr : n - 9800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 9800) + 9800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact pos_w196 ⟨n - 9800, hr⟩
                                                                                                                                                                                                  · by_cases h97 : n < 9900
                                                                                                                                                                                                    · have hr : n - 9850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 9850) + 9850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact pos_w197 ⟨n - 9850, hr⟩
                                                                                                                                                                                                    · by_cases h98 : n < 9950
                                                                                                                                                                                                      · have hr : n - 9900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 9900) + 9900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact pos_w198 ⟨n - 9900, hr⟩
                                                                                                                                                                                                      · by_cases h99 : n < 10000
                                                                                                                                                                                                        · have hr : n - 9950 < 50 := by omega
                                                                                                                                                                                                          have heq : n = (n - 9950) + 9950 := by omega
                                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                                          exact pos_w199 ⟨n - 9950, hr⟩
                                                                                                                                                                                                        · omega

end IntMul.Kappa.R8.Bit.Oppbank.DimBound1


