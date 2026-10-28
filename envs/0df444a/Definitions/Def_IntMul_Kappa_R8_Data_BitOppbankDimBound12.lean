-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound12
-- name    : IntMul_Kappa_R8_Data_BitOppbankDimBound12
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:02:04.345531+00:00
-- url     : https://prove2.me/theorems/a004461d-e8d5-4328-ab32-71513ba24d30
-- title:
--   Densified dimF $\le 22$ pack 12 ($[60000,62478)$)
-- statement:
--   Pack 12 of the densified dimension-field bound.
--
--   For every densified node index $n$ with $60000\le n<62478$, the 5-bit field $\mathrm{dimF}(n)$ extracted from $\mathrm{DIMT}$ satisfies
--   $$1\le \mathrm{dimF}(n)\le 22.$$
--   Proved by `decide` on successive `Fin 50` windows (no `native_decide`).
-- source:
--   R8 BitNB densified DIMT field bound; Fin-window decide packs

-- DimBound pack 12: dimF bounds on n ∈ [60000, 62478)

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

namespace IntMul.Kappa.R8.Bit.Oppbank.DimBound12

private theorem le_w1200 : ∀ n : Fin 50, dimF (n.val + 60000) ≤ 22 := by decide
private theorem pos_w1200 : ∀ n : Fin 50, 0 < dimF (n.val + 60000) := by decide
private theorem le_w1201 : ∀ n : Fin 50, dimF (n.val + 60050) ≤ 22 := by decide
private theorem pos_w1201 : ∀ n : Fin 50, 0 < dimF (n.val + 60050) := by decide
private theorem le_w1202 : ∀ n : Fin 50, dimF (n.val + 60100) ≤ 22 := by decide
private theorem pos_w1202 : ∀ n : Fin 50, 0 < dimF (n.val + 60100) := by decide
private theorem le_w1203 : ∀ n : Fin 50, dimF (n.val + 60150) ≤ 22 := by decide
private theorem pos_w1203 : ∀ n : Fin 50, 0 < dimF (n.val + 60150) := by decide
private theorem le_w1204 : ∀ n : Fin 50, dimF (n.val + 60200) ≤ 22 := by decide
private theorem pos_w1204 : ∀ n : Fin 50, 0 < dimF (n.val + 60200) := by decide
private theorem le_w1205 : ∀ n : Fin 50, dimF (n.val + 60250) ≤ 22 := by decide
private theorem pos_w1205 : ∀ n : Fin 50, 0 < dimF (n.val + 60250) := by decide
private theorem le_w1206 : ∀ n : Fin 50, dimF (n.val + 60300) ≤ 22 := by decide
private theorem pos_w1206 : ∀ n : Fin 50, 0 < dimF (n.val + 60300) := by decide
private theorem le_w1207 : ∀ n : Fin 50, dimF (n.val + 60350) ≤ 22 := by decide
private theorem pos_w1207 : ∀ n : Fin 50, 0 < dimF (n.val + 60350) := by decide
private theorem le_w1208 : ∀ n : Fin 50, dimF (n.val + 60400) ≤ 22 := by decide
private theorem pos_w1208 : ∀ n : Fin 50, 0 < dimF (n.val + 60400) := by decide
private theorem le_w1209 : ∀ n : Fin 50, dimF (n.val + 60450) ≤ 22 := by decide
private theorem pos_w1209 : ∀ n : Fin 50, 0 < dimF (n.val + 60450) := by decide
private theorem le_w1210 : ∀ n : Fin 50, dimF (n.val + 60500) ≤ 22 := by decide
private theorem pos_w1210 : ∀ n : Fin 50, 0 < dimF (n.val + 60500) := by decide
private theorem le_w1211 : ∀ n : Fin 50, dimF (n.val + 60550) ≤ 22 := by decide
private theorem pos_w1211 : ∀ n : Fin 50, 0 < dimF (n.val + 60550) := by decide
private theorem le_w1212 : ∀ n : Fin 50, dimF (n.val + 60600) ≤ 22 := by decide
private theorem pos_w1212 : ∀ n : Fin 50, 0 < dimF (n.val + 60600) := by decide
private theorem le_w1213 : ∀ n : Fin 50, dimF (n.val + 60650) ≤ 22 := by decide
private theorem pos_w1213 : ∀ n : Fin 50, 0 < dimF (n.val + 60650) := by decide
private theorem le_w1214 : ∀ n : Fin 50, dimF (n.val + 60700) ≤ 22 := by decide
private theorem pos_w1214 : ∀ n : Fin 50, 0 < dimF (n.val + 60700) := by decide
private theorem le_w1215 : ∀ n : Fin 50, dimF (n.val + 60750) ≤ 22 := by decide
private theorem pos_w1215 : ∀ n : Fin 50, 0 < dimF (n.val + 60750) := by decide
private theorem le_w1216 : ∀ n : Fin 50, dimF (n.val + 60800) ≤ 22 := by decide
private theorem pos_w1216 : ∀ n : Fin 50, 0 < dimF (n.val + 60800) := by decide
private theorem le_w1217 : ∀ n : Fin 50, dimF (n.val + 60850) ≤ 22 := by decide
private theorem pos_w1217 : ∀ n : Fin 50, 0 < dimF (n.val + 60850) := by decide
private theorem le_w1218 : ∀ n : Fin 50, dimF (n.val + 60900) ≤ 22 := by decide
private theorem pos_w1218 : ∀ n : Fin 50, 0 < dimF (n.val + 60900) := by decide
private theorem le_w1219 : ∀ n : Fin 50, dimF (n.val + 60950) ≤ 22 := by decide
private theorem pos_w1219 : ∀ n : Fin 50, 0 < dimF (n.val + 60950) := by decide
private theorem le_w1220 : ∀ n : Fin 50, dimF (n.val + 61000) ≤ 22 := by decide
private theorem pos_w1220 : ∀ n : Fin 50, 0 < dimF (n.val + 61000) := by decide
private theorem le_w1221 : ∀ n : Fin 50, dimF (n.val + 61050) ≤ 22 := by decide
private theorem pos_w1221 : ∀ n : Fin 50, 0 < dimF (n.val + 61050) := by decide
private theorem le_w1222 : ∀ n : Fin 50, dimF (n.val + 61100) ≤ 22 := by decide
private theorem pos_w1222 : ∀ n : Fin 50, 0 < dimF (n.val + 61100) := by decide
private theorem le_w1223 : ∀ n : Fin 50, dimF (n.val + 61150) ≤ 22 := by decide
private theorem pos_w1223 : ∀ n : Fin 50, 0 < dimF (n.val + 61150) := by decide
private theorem le_w1224 : ∀ n : Fin 50, dimF (n.val + 61200) ≤ 22 := by decide
private theorem pos_w1224 : ∀ n : Fin 50, 0 < dimF (n.val + 61200) := by decide
private theorem le_w1225 : ∀ n : Fin 50, dimF (n.val + 61250) ≤ 22 := by decide
private theorem pos_w1225 : ∀ n : Fin 50, 0 < dimF (n.val + 61250) := by decide
private theorem le_w1226 : ∀ n : Fin 50, dimF (n.val + 61300) ≤ 22 := by decide
private theorem pos_w1226 : ∀ n : Fin 50, 0 < dimF (n.val + 61300) := by decide
private theorem le_w1227 : ∀ n : Fin 50, dimF (n.val + 61350) ≤ 22 := by decide
private theorem pos_w1227 : ∀ n : Fin 50, 0 < dimF (n.val + 61350) := by decide
private theorem le_w1228 : ∀ n : Fin 50, dimF (n.val + 61400) ≤ 22 := by decide
private theorem pos_w1228 : ∀ n : Fin 50, 0 < dimF (n.val + 61400) := by decide
private theorem le_w1229 : ∀ n : Fin 50, dimF (n.val + 61450) ≤ 22 := by decide
private theorem pos_w1229 : ∀ n : Fin 50, 0 < dimF (n.val + 61450) := by decide
private theorem le_w1230 : ∀ n : Fin 50, dimF (n.val + 61500) ≤ 22 := by decide
private theorem pos_w1230 : ∀ n : Fin 50, 0 < dimF (n.val + 61500) := by decide
private theorem le_w1231 : ∀ n : Fin 50, dimF (n.val + 61550) ≤ 22 := by decide
private theorem pos_w1231 : ∀ n : Fin 50, 0 < dimF (n.val + 61550) := by decide
private theorem le_w1232 : ∀ n : Fin 50, dimF (n.val + 61600) ≤ 22 := by decide
private theorem pos_w1232 : ∀ n : Fin 50, 0 < dimF (n.val + 61600) := by decide
private theorem le_w1233 : ∀ n : Fin 50, dimF (n.val + 61650) ≤ 22 := by decide
private theorem pos_w1233 : ∀ n : Fin 50, 0 < dimF (n.val + 61650) := by decide
private theorem le_w1234 : ∀ n : Fin 50, dimF (n.val + 61700) ≤ 22 := by decide
private theorem pos_w1234 : ∀ n : Fin 50, 0 < dimF (n.val + 61700) := by decide
private theorem le_w1235 : ∀ n : Fin 50, dimF (n.val + 61750) ≤ 22 := by decide
private theorem pos_w1235 : ∀ n : Fin 50, 0 < dimF (n.val + 61750) := by decide
private theorem le_w1236 : ∀ n : Fin 50, dimF (n.val + 61800) ≤ 22 := by decide
private theorem pos_w1236 : ∀ n : Fin 50, 0 < dimF (n.val + 61800) := by decide
private theorem le_w1237 : ∀ n : Fin 50, dimF (n.val + 61850) ≤ 22 := by decide
private theorem pos_w1237 : ∀ n : Fin 50, 0 < dimF (n.val + 61850) := by decide
private theorem le_w1238 : ∀ n : Fin 50, dimF (n.val + 61900) ≤ 22 := by decide
private theorem pos_w1238 : ∀ n : Fin 50, 0 < dimF (n.val + 61900) := by decide
private theorem le_w1239 : ∀ n : Fin 50, dimF (n.val + 61950) ≤ 22 := by decide
private theorem pos_w1239 : ∀ n : Fin 50, 0 < dimF (n.val + 61950) := by decide
private theorem le_w1240 : ∀ n : Fin 50, dimF (n.val + 62000) ≤ 22 := by decide
private theorem pos_w1240 : ∀ n : Fin 50, 0 < dimF (n.val + 62000) := by decide
private theorem le_w1241 : ∀ n : Fin 50, dimF (n.val + 62050) ≤ 22 := by decide
private theorem pos_w1241 : ∀ n : Fin 50, 0 < dimF (n.val + 62050) := by decide
private theorem le_w1242 : ∀ n : Fin 50, dimF (n.val + 62100) ≤ 22 := by decide
private theorem pos_w1242 : ∀ n : Fin 50, 0 < dimF (n.val + 62100) := by decide
private theorem le_w1243 : ∀ n : Fin 50, dimF (n.val + 62150) ≤ 22 := by decide
private theorem pos_w1243 : ∀ n : Fin 50, 0 < dimF (n.val + 62150) := by decide
private theorem le_w1244 : ∀ n : Fin 50, dimF (n.val + 62200) ≤ 22 := by decide
private theorem pos_w1244 : ∀ n : Fin 50, 0 < dimF (n.val + 62200) := by decide
private theorem le_w1245 : ∀ n : Fin 50, dimF (n.val + 62250) ≤ 22 := by decide
private theorem pos_w1245 : ∀ n : Fin 50, 0 < dimF (n.val + 62250) := by decide
private theorem le_w1246 : ∀ n : Fin 50, dimF (n.val + 62300) ≤ 22 := by decide
private theorem pos_w1246 : ∀ n : Fin 50, 0 < dimF (n.val + 62300) := by decide
private theorem le_w1247 : ∀ n : Fin 50, dimF (n.val + 62350) ≤ 22 := by decide
private theorem pos_w1247 : ∀ n : Fin 50, 0 < dimF (n.val + 62350) := by decide
private theorem le_w1248 : ∀ n : Fin 50, dimF (n.val + 62400) ≤ 22 := by decide
private theorem pos_w1248 : ∀ n : Fin 50, 0 < dimF (n.val + 62400) := by decide
private theorem le_wlast : ∀ n : Fin 28, dimF (n.val + 62450) ≤ 22 := by decide
private theorem pos_wlast : ∀ n : Fin 28, 0 < dimF (n.val + 62450) := by decide

theorem dimF_le_22_range : ∀ n, 60000 ≤ n → n < 62478 → dimF n ≤ 22 := by
  intro n hlo hhi
  by_cases h0 : n < 60050
  · have hr : n - 60000 < 50 := by omega
    have heq : n = (n - 60000) + 60000 := by omega
    rw [heq]
    exact le_w1200 ⟨n - 60000, hr⟩
  · by_cases h1 : n < 60100
    · have hr : n - 60050 < 50 := by omega
      have heq : n = (n - 60050) + 60050 := by omega
      rw [heq]
      exact le_w1201 ⟨n - 60050, hr⟩
    · by_cases h2 : n < 60150
      · have hr : n - 60100 < 50 := by omega
        have heq : n = (n - 60100) + 60100 := by omega
        rw [heq]
        exact le_w1202 ⟨n - 60100, hr⟩
      · by_cases h3 : n < 60200
        · have hr : n - 60150 < 50 := by omega
          have heq : n = (n - 60150) + 60150 := by omega
          rw [heq]
          exact le_w1203 ⟨n - 60150, hr⟩
        · by_cases h4 : n < 60250
          · have hr : n - 60200 < 50 := by omega
            have heq : n = (n - 60200) + 60200 := by omega
            rw [heq]
            exact le_w1204 ⟨n - 60200, hr⟩
          · by_cases h5 : n < 60300
            · have hr : n - 60250 < 50 := by omega
              have heq : n = (n - 60250) + 60250 := by omega
              rw [heq]
              exact le_w1205 ⟨n - 60250, hr⟩
            · by_cases h6 : n < 60350
              · have hr : n - 60300 < 50 := by omega
                have heq : n = (n - 60300) + 60300 := by omega
                rw [heq]
                exact le_w1206 ⟨n - 60300, hr⟩
              · by_cases h7 : n < 60400
                · have hr : n - 60350 < 50 := by omega
                  have heq : n = (n - 60350) + 60350 := by omega
                  rw [heq]
                  exact le_w1207 ⟨n - 60350, hr⟩
                · by_cases h8 : n < 60450
                  · have hr : n - 60400 < 50 := by omega
                    have heq : n = (n - 60400) + 60400 := by omega
                    rw [heq]
                    exact le_w1208 ⟨n - 60400, hr⟩
                  · by_cases h9 : n < 60500
                    · have hr : n - 60450 < 50 := by omega
                      have heq : n = (n - 60450) + 60450 := by omega
                      rw [heq]
                      exact le_w1209 ⟨n - 60450, hr⟩
                    · by_cases h10 : n < 60550
                      · have hr : n - 60500 < 50 := by omega
                        have heq : n = (n - 60500) + 60500 := by omega
                        rw [heq]
                        exact le_w1210 ⟨n - 60500, hr⟩
                      · by_cases h11 : n < 60600
                        · have hr : n - 60550 < 50 := by omega
                          have heq : n = (n - 60550) + 60550 := by omega
                          rw [heq]
                          exact le_w1211 ⟨n - 60550, hr⟩
                        · by_cases h12 : n < 60650
                          · have hr : n - 60600 < 50 := by omega
                            have heq : n = (n - 60600) + 60600 := by omega
                            rw [heq]
                            exact le_w1212 ⟨n - 60600, hr⟩
                          · by_cases h13 : n < 60700
                            · have hr : n - 60650 < 50 := by omega
                              have heq : n = (n - 60650) + 60650 := by omega
                              rw [heq]
                              exact le_w1213 ⟨n - 60650, hr⟩
                            · by_cases h14 : n < 60750
                              · have hr : n - 60700 < 50 := by omega
                                have heq : n = (n - 60700) + 60700 := by omega
                                rw [heq]
                                exact le_w1214 ⟨n - 60700, hr⟩
                              · by_cases h15 : n < 60800
                                · have hr : n - 60750 < 50 := by omega
                                  have heq : n = (n - 60750) + 60750 := by omega
                                  rw [heq]
                                  exact le_w1215 ⟨n - 60750, hr⟩
                                · by_cases h16 : n < 60850
                                  · have hr : n - 60800 < 50 := by omega
                                    have heq : n = (n - 60800) + 60800 := by omega
                                    rw [heq]
                                    exact le_w1216 ⟨n - 60800, hr⟩
                                  · by_cases h17 : n < 60900
                                    · have hr : n - 60850 < 50 := by omega
                                      have heq : n = (n - 60850) + 60850 := by omega
                                      rw [heq]
                                      exact le_w1217 ⟨n - 60850, hr⟩
                                    · by_cases h18 : n < 60950
                                      · have hr : n - 60900 < 50 := by omega
                                        have heq : n = (n - 60900) + 60900 := by omega
                                        rw [heq]
                                        exact le_w1218 ⟨n - 60900, hr⟩
                                      · by_cases h19 : n < 61000
                                        · have hr : n - 60950 < 50 := by omega
                                          have heq : n = (n - 60950) + 60950 := by omega
                                          rw [heq]
                                          exact le_w1219 ⟨n - 60950, hr⟩
                                        · by_cases h20 : n < 61050
                                          · have hr : n - 61000 < 50 := by omega
                                            have heq : n = (n - 61000) + 61000 := by omega
                                            rw [heq]
                                            exact le_w1220 ⟨n - 61000, hr⟩
                                          · by_cases h21 : n < 61100
                                            · have hr : n - 61050 < 50 := by omega
                                              have heq : n = (n - 61050) + 61050 := by omega
                                              rw [heq]
                                              exact le_w1221 ⟨n - 61050, hr⟩
                                            · by_cases h22 : n < 61150
                                              · have hr : n - 61100 < 50 := by omega
                                                have heq : n = (n - 61100) + 61100 := by omega
                                                rw [heq]
                                                exact le_w1222 ⟨n - 61100, hr⟩
                                              · by_cases h23 : n < 61200
                                                · have hr : n - 61150 < 50 := by omega
                                                  have heq : n = (n - 61150) + 61150 := by omega
                                                  rw [heq]
                                                  exact le_w1223 ⟨n - 61150, hr⟩
                                                · by_cases h24 : n < 61250
                                                  · have hr : n - 61200 < 50 := by omega
                                                    have heq : n = (n - 61200) + 61200 := by omega
                                                    rw [heq]
                                                    exact le_w1224 ⟨n - 61200, hr⟩
                                                  · by_cases h25 : n < 61300
                                                    · have hr : n - 61250 < 50 := by omega
                                                      have heq : n = (n - 61250) + 61250 := by omega
                                                      rw [heq]
                                                      exact le_w1225 ⟨n - 61250, hr⟩
                                                    · by_cases h26 : n < 61350
                                                      · have hr : n - 61300 < 50 := by omega
                                                        have heq : n = (n - 61300) + 61300 := by omega
                                                        rw [heq]
                                                        exact le_w1226 ⟨n - 61300, hr⟩
                                                      · by_cases h27 : n < 61400
                                                        · have hr : n - 61350 < 50 := by omega
                                                          have heq : n = (n - 61350) + 61350 := by omega
                                                          rw [heq]
                                                          exact le_w1227 ⟨n - 61350, hr⟩
                                                        · by_cases h28 : n < 61450
                                                          · have hr : n - 61400 < 50 := by omega
                                                            have heq : n = (n - 61400) + 61400 := by omega
                                                            rw [heq]
                                                            exact le_w1228 ⟨n - 61400, hr⟩
                                                          · by_cases h29 : n < 61500
                                                            · have hr : n - 61450 < 50 := by omega
                                                              have heq : n = (n - 61450) + 61450 := by omega
                                                              rw [heq]
                                                              exact le_w1229 ⟨n - 61450, hr⟩
                                                            · by_cases h30 : n < 61550
                                                              · have hr : n - 61500 < 50 := by omega
                                                                have heq : n = (n - 61500) + 61500 := by omega
                                                                rw [heq]
                                                                exact le_w1230 ⟨n - 61500, hr⟩
                                                              · by_cases h31 : n < 61600
                                                                · have hr : n - 61550 < 50 := by omega
                                                                  have heq : n = (n - 61550) + 61550 := by omega
                                                                  rw [heq]
                                                                  exact le_w1231 ⟨n - 61550, hr⟩
                                                                · by_cases h32 : n < 61650
                                                                  · have hr : n - 61600 < 50 := by omega
                                                                    have heq : n = (n - 61600) + 61600 := by omega
                                                                    rw [heq]
                                                                    exact le_w1232 ⟨n - 61600, hr⟩
                                                                  · by_cases h33 : n < 61700
                                                                    · have hr : n - 61650 < 50 := by omega
                                                                      have heq : n = (n - 61650) + 61650 := by omega
                                                                      rw [heq]
                                                                      exact le_w1233 ⟨n - 61650, hr⟩
                                                                    · by_cases h34 : n < 61750
                                                                      · have hr : n - 61700 < 50 := by omega
                                                                        have heq : n = (n - 61700) + 61700 := by omega
                                                                        rw [heq]
                                                                        exact le_w1234 ⟨n - 61700, hr⟩
                                                                      · by_cases h35 : n < 61800
                                                                        · have hr : n - 61750 < 50 := by omega
                                                                          have heq : n = (n - 61750) + 61750 := by omega
                                                                          rw [heq]
                                                                          exact le_w1235 ⟨n - 61750, hr⟩
                                                                        · by_cases h36 : n < 61850
                                                                          · have hr : n - 61800 < 50 := by omega
                                                                            have heq : n = (n - 61800) + 61800 := by omega
                                                                            rw [heq]
                                                                            exact le_w1236 ⟨n - 61800, hr⟩
                                                                          · by_cases h37 : n < 61900
                                                                            · have hr : n - 61850 < 50 := by omega
                                                                              have heq : n = (n - 61850) + 61850 := by omega
                                                                              rw [heq]
                                                                              exact le_w1237 ⟨n - 61850, hr⟩
                                                                            · by_cases h38 : n < 61950
                                                                              · have hr : n - 61900 < 50 := by omega
                                                                                have heq : n = (n - 61900) + 61900 := by omega
                                                                                rw [heq]
                                                                                exact le_w1238 ⟨n - 61900, hr⟩
                                                                              · by_cases h39 : n < 62000
                                                                                · have hr : n - 61950 < 50 := by omega
                                                                                  have heq : n = (n - 61950) + 61950 := by omega
                                                                                  rw [heq]
                                                                                  exact le_w1239 ⟨n - 61950, hr⟩
                                                                                · by_cases h40 : n < 62050
                                                                                  · have hr : n - 62000 < 50 := by omega
                                                                                    have heq : n = (n - 62000) + 62000 := by omega
                                                                                    rw [heq]
                                                                                    exact le_w1240 ⟨n - 62000, hr⟩
                                                                                  · by_cases h41 : n < 62100
                                                                                    · have hr : n - 62050 < 50 := by omega
                                                                                      have heq : n = (n - 62050) + 62050 := by omega
                                                                                      rw [heq]
                                                                                      exact le_w1241 ⟨n - 62050, hr⟩
                                                                                    · by_cases h42 : n < 62150
                                                                                      · have hr : n - 62100 < 50 := by omega
                                                                                        have heq : n = (n - 62100) + 62100 := by omega
                                                                                        rw [heq]
                                                                                        exact le_w1242 ⟨n - 62100, hr⟩
                                                                                      · by_cases h43 : n < 62200
                                                                                        · have hr : n - 62150 < 50 := by omega
                                                                                          have heq : n = (n - 62150) + 62150 := by omega
                                                                                          rw [heq]
                                                                                          exact le_w1243 ⟨n - 62150, hr⟩
                                                                                        · by_cases h44 : n < 62250
                                                                                          · have hr : n - 62200 < 50 := by omega
                                                                                            have heq : n = (n - 62200) + 62200 := by omega
                                                                                            rw [heq]
                                                                                            exact le_w1244 ⟨n - 62200, hr⟩
                                                                                          · by_cases h45 : n < 62300
                                                                                            · have hr : n - 62250 < 50 := by omega
                                                                                              have heq : n = (n - 62250) + 62250 := by omega
                                                                                              rw [heq]
                                                                                              exact le_w1245 ⟨n - 62250, hr⟩
                                                                                            · by_cases h46 : n < 62350
                                                                                              · have hr : n - 62300 < 50 := by omega
                                                                                                have heq : n = (n - 62300) + 62300 := by omega
                                                                                                rw [heq]
                                                                                                exact le_w1246 ⟨n - 62300, hr⟩
                                                                                              · by_cases h47 : n < 62400
                                                                                                · have hr : n - 62350 < 50 := by omega
                                                                                                  have heq : n = (n - 62350) + 62350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact le_w1247 ⟨n - 62350, hr⟩
                                                                                                · by_cases h48 : n < 62450
                                                                                                  · have hr : n - 62400 < 50 := by omega
                                                                                                    have heq : n = (n - 62400) + 62400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact le_w1248 ⟨n - 62400, hr⟩
                                                                                                  · have hr : n - 62450 < 28 := by omega
                                                                                                    have heq : n = (n - 62450) + 62450 := by omega
                                                                                                    rw [heq]
                                                                                                    exact le_wlast ⟨n - 62450, hr⟩

theorem dimF_pos_range : ∀ n, 60000 ≤ n → n < 62478 → 0 < dimF n := by
  intro n hlo hhi
  by_cases h0 : n < 60050
  · have hr : n - 60000 < 50 := by omega
    have heq : n = (n - 60000) + 60000 := by omega
    rw [heq]
    exact pos_w1200 ⟨n - 60000, hr⟩
  · by_cases h1 : n < 60100
    · have hr : n - 60050 < 50 := by omega
      have heq : n = (n - 60050) + 60050 := by omega
      rw [heq]
      exact pos_w1201 ⟨n - 60050, hr⟩
    · by_cases h2 : n < 60150
      · have hr : n - 60100 < 50 := by omega
        have heq : n = (n - 60100) + 60100 := by omega
        rw [heq]
        exact pos_w1202 ⟨n - 60100, hr⟩
      · by_cases h3 : n < 60200
        · have hr : n - 60150 < 50 := by omega
          have heq : n = (n - 60150) + 60150 := by omega
          rw [heq]
          exact pos_w1203 ⟨n - 60150, hr⟩
        · by_cases h4 : n < 60250
          · have hr : n - 60200 < 50 := by omega
            have heq : n = (n - 60200) + 60200 := by omega
            rw [heq]
            exact pos_w1204 ⟨n - 60200, hr⟩
          · by_cases h5 : n < 60300
            · have hr : n - 60250 < 50 := by omega
              have heq : n = (n - 60250) + 60250 := by omega
              rw [heq]
              exact pos_w1205 ⟨n - 60250, hr⟩
            · by_cases h6 : n < 60350
              · have hr : n - 60300 < 50 := by omega
                have heq : n = (n - 60300) + 60300 := by omega
                rw [heq]
                exact pos_w1206 ⟨n - 60300, hr⟩
              · by_cases h7 : n < 60400
                · have hr : n - 60350 < 50 := by omega
                  have heq : n = (n - 60350) + 60350 := by omega
                  rw [heq]
                  exact pos_w1207 ⟨n - 60350, hr⟩
                · by_cases h8 : n < 60450
                  · have hr : n - 60400 < 50 := by omega
                    have heq : n = (n - 60400) + 60400 := by omega
                    rw [heq]
                    exact pos_w1208 ⟨n - 60400, hr⟩
                  · by_cases h9 : n < 60500
                    · have hr : n - 60450 < 50 := by omega
                      have heq : n = (n - 60450) + 60450 := by omega
                      rw [heq]
                      exact pos_w1209 ⟨n - 60450, hr⟩
                    · by_cases h10 : n < 60550
                      · have hr : n - 60500 < 50 := by omega
                        have heq : n = (n - 60500) + 60500 := by omega
                        rw [heq]
                        exact pos_w1210 ⟨n - 60500, hr⟩
                      · by_cases h11 : n < 60600
                        · have hr : n - 60550 < 50 := by omega
                          have heq : n = (n - 60550) + 60550 := by omega
                          rw [heq]
                          exact pos_w1211 ⟨n - 60550, hr⟩
                        · by_cases h12 : n < 60650
                          · have hr : n - 60600 < 50 := by omega
                            have heq : n = (n - 60600) + 60600 := by omega
                            rw [heq]
                            exact pos_w1212 ⟨n - 60600, hr⟩
                          · by_cases h13 : n < 60700
                            · have hr : n - 60650 < 50 := by omega
                              have heq : n = (n - 60650) + 60650 := by omega
                              rw [heq]
                              exact pos_w1213 ⟨n - 60650, hr⟩
                            · by_cases h14 : n < 60750
                              · have hr : n - 60700 < 50 := by omega
                                have heq : n = (n - 60700) + 60700 := by omega
                                rw [heq]
                                exact pos_w1214 ⟨n - 60700, hr⟩
                              · by_cases h15 : n < 60800
                                · have hr : n - 60750 < 50 := by omega
                                  have heq : n = (n - 60750) + 60750 := by omega
                                  rw [heq]
                                  exact pos_w1215 ⟨n - 60750, hr⟩
                                · by_cases h16 : n < 60850
                                  · have hr : n - 60800 < 50 := by omega
                                    have heq : n = (n - 60800) + 60800 := by omega
                                    rw [heq]
                                    exact pos_w1216 ⟨n - 60800, hr⟩
                                  · by_cases h17 : n < 60900
                                    · have hr : n - 60850 < 50 := by omega
                                      have heq : n = (n - 60850) + 60850 := by omega
                                      rw [heq]
                                      exact pos_w1217 ⟨n - 60850, hr⟩
                                    · by_cases h18 : n < 60950
                                      · have hr : n - 60900 < 50 := by omega
                                        have heq : n = (n - 60900) + 60900 := by omega
                                        rw [heq]
                                        exact pos_w1218 ⟨n - 60900, hr⟩
                                      · by_cases h19 : n < 61000
                                        · have hr : n - 60950 < 50 := by omega
                                          have heq : n = (n - 60950) + 60950 := by omega
                                          rw [heq]
                                          exact pos_w1219 ⟨n - 60950, hr⟩
                                        · by_cases h20 : n < 61050
                                          · have hr : n - 61000 < 50 := by omega
                                            have heq : n = (n - 61000) + 61000 := by omega
                                            rw [heq]
                                            exact pos_w1220 ⟨n - 61000, hr⟩
                                          · by_cases h21 : n < 61100
                                            · have hr : n - 61050 < 50 := by omega
                                              have heq : n = (n - 61050) + 61050 := by omega
                                              rw [heq]
                                              exact pos_w1221 ⟨n - 61050, hr⟩
                                            · by_cases h22 : n < 61150
                                              · have hr : n - 61100 < 50 := by omega
                                                have heq : n = (n - 61100) + 61100 := by omega
                                                rw [heq]
                                                exact pos_w1222 ⟨n - 61100, hr⟩
                                              · by_cases h23 : n < 61200
                                                · have hr : n - 61150 < 50 := by omega
                                                  have heq : n = (n - 61150) + 61150 := by omega
                                                  rw [heq]
                                                  exact pos_w1223 ⟨n - 61150, hr⟩
                                                · by_cases h24 : n < 61250
                                                  · have hr : n - 61200 < 50 := by omega
                                                    have heq : n = (n - 61200) + 61200 := by omega
                                                    rw [heq]
                                                    exact pos_w1224 ⟨n - 61200, hr⟩
                                                  · by_cases h25 : n < 61300
                                                    · have hr : n - 61250 < 50 := by omega
                                                      have heq : n = (n - 61250) + 61250 := by omega
                                                      rw [heq]
                                                      exact pos_w1225 ⟨n - 61250, hr⟩
                                                    · by_cases h26 : n < 61350
                                                      · have hr : n - 61300 < 50 := by omega
                                                        have heq : n = (n - 61300) + 61300 := by omega
                                                        rw [heq]
                                                        exact pos_w1226 ⟨n - 61300, hr⟩
                                                      · by_cases h27 : n < 61400
                                                        · have hr : n - 61350 < 50 := by omega
                                                          have heq : n = (n - 61350) + 61350 := by omega
                                                          rw [heq]
                                                          exact pos_w1227 ⟨n - 61350, hr⟩
                                                        · by_cases h28 : n < 61450
                                                          · have hr : n - 61400 < 50 := by omega
                                                            have heq : n = (n - 61400) + 61400 := by omega
                                                            rw [heq]
                                                            exact pos_w1228 ⟨n - 61400, hr⟩
                                                          · by_cases h29 : n < 61500
                                                            · have hr : n - 61450 < 50 := by omega
                                                              have heq : n = (n - 61450) + 61450 := by omega
                                                              rw [heq]
                                                              exact pos_w1229 ⟨n - 61450, hr⟩
                                                            · by_cases h30 : n < 61550
                                                              · have hr : n - 61500 < 50 := by omega
                                                                have heq : n = (n - 61500) + 61500 := by omega
                                                                rw [heq]
                                                                exact pos_w1230 ⟨n - 61500, hr⟩
                                                              · by_cases h31 : n < 61600
                                                                · have hr : n - 61550 < 50 := by omega
                                                                  have heq : n = (n - 61550) + 61550 := by omega
                                                                  rw [heq]
                                                                  exact pos_w1231 ⟨n - 61550, hr⟩
                                                                · by_cases h32 : n < 61650
                                                                  · have hr : n - 61600 < 50 := by omega
                                                                    have heq : n = (n - 61600) + 61600 := by omega
                                                                    rw [heq]
                                                                    exact pos_w1232 ⟨n - 61600, hr⟩
                                                                  · by_cases h33 : n < 61700
                                                                    · have hr : n - 61650 < 50 := by omega
                                                                      have heq : n = (n - 61650) + 61650 := by omega
                                                                      rw [heq]
                                                                      exact pos_w1233 ⟨n - 61650, hr⟩
                                                                    · by_cases h34 : n < 61750
                                                                      · have hr : n - 61700 < 50 := by omega
                                                                        have heq : n = (n - 61700) + 61700 := by omega
                                                                        rw [heq]
                                                                        exact pos_w1234 ⟨n - 61700, hr⟩
                                                                      · by_cases h35 : n < 61800
                                                                        · have hr : n - 61750 < 50 := by omega
                                                                          have heq : n = (n - 61750) + 61750 := by omega
                                                                          rw [heq]
                                                                          exact pos_w1235 ⟨n - 61750, hr⟩
                                                                        · by_cases h36 : n < 61850
                                                                          · have hr : n - 61800 < 50 := by omega
                                                                            have heq : n = (n - 61800) + 61800 := by omega
                                                                            rw [heq]
                                                                            exact pos_w1236 ⟨n - 61800, hr⟩
                                                                          · by_cases h37 : n < 61900
                                                                            · have hr : n - 61850 < 50 := by omega
                                                                              have heq : n = (n - 61850) + 61850 := by omega
                                                                              rw [heq]
                                                                              exact pos_w1237 ⟨n - 61850, hr⟩
                                                                            · by_cases h38 : n < 61950
                                                                              · have hr : n - 61900 < 50 := by omega
                                                                                have heq : n = (n - 61900) + 61900 := by omega
                                                                                rw [heq]
                                                                                exact pos_w1238 ⟨n - 61900, hr⟩
                                                                              · by_cases h39 : n < 62000
                                                                                · have hr : n - 61950 < 50 := by omega
                                                                                  have heq : n = (n - 61950) + 61950 := by omega
                                                                                  rw [heq]
                                                                                  exact pos_w1239 ⟨n - 61950, hr⟩
                                                                                · by_cases h40 : n < 62050
                                                                                  · have hr : n - 62000 < 50 := by omega
                                                                                    have heq : n = (n - 62000) + 62000 := by omega
                                                                                    rw [heq]
                                                                                    exact pos_w1240 ⟨n - 62000, hr⟩
                                                                                  · by_cases h41 : n < 62100
                                                                                    · have hr : n - 62050 < 50 := by omega
                                                                                      have heq : n = (n - 62050) + 62050 := by omega
                                                                                      rw [heq]
                                                                                      exact pos_w1241 ⟨n - 62050, hr⟩
                                                                                    · by_cases h42 : n < 62150
                                                                                      · have hr : n - 62100 < 50 := by omega
                                                                                        have heq : n = (n - 62100) + 62100 := by omega
                                                                                        rw [heq]
                                                                                        exact pos_w1242 ⟨n - 62100, hr⟩
                                                                                      · by_cases h43 : n < 62200
                                                                                        · have hr : n - 62150 < 50 := by omega
                                                                                          have heq : n = (n - 62150) + 62150 := by omega
                                                                                          rw [heq]
                                                                                          exact pos_w1243 ⟨n - 62150, hr⟩
                                                                                        · by_cases h44 : n < 62250
                                                                                          · have hr : n - 62200 < 50 := by omega
                                                                                            have heq : n = (n - 62200) + 62200 := by omega
                                                                                            rw [heq]
                                                                                            exact pos_w1244 ⟨n - 62200, hr⟩
                                                                                          · by_cases h45 : n < 62300
                                                                                            · have hr : n - 62250 < 50 := by omega
                                                                                              have heq : n = (n - 62250) + 62250 := by omega
                                                                                              rw [heq]
                                                                                              exact pos_w1245 ⟨n - 62250, hr⟩
                                                                                            · by_cases h46 : n < 62350
                                                                                              · have hr : n - 62300 < 50 := by omega
                                                                                                have heq : n = (n - 62300) + 62300 := by omega
                                                                                                rw [heq]
                                                                                                exact pos_w1246 ⟨n - 62300, hr⟩
                                                                                              · by_cases h47 : n < 62400
                                                                                                · have hr : n - 62350 < 50 := by omega
                                                                                                  have heq : n = (n - 62350) + 62350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact pos_w1247 ⟨n - 62350, hr⟩
                                                                                                · by_cases h48 : n < 62450
                                                                                                  · have hr : n - 62400 < 50 := by omega
                                                                                                    have heq : n = (n - 62400) + 62400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact pos_w1248 ⟨n - 62400, hr⟩
                                                                                                  · have hr : n - 62450 < 28 := by omega
                                                                                                    have heq : n = (n - 62450) + 62450 := by omega
                                                                                                    rw [heq]
                                                                                                    exact pos_wlast ⟨n - 62450, hr⟩

end IntMul.Kappa.R8.Bit.Oppbank.DimBound12


