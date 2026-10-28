-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound4
-- name    : IntMul_Kappa_R8_Data_BitOppbankDimBound4
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:04:05.066722+00:00
-- url     : https://prove2.me/theorems/4e7b8e3d-622f-443a-923d-d029b5e58a2a
-- title:
--   Densified dimF $\le 22$ pack 4 ($[20000,25000)$)
-- statement:
--   Pack 4 of the densified dimension-field bound.
--
--   For every densified node index $n$ with $20000\le n<25000$, the 5-bit field $\mathrm{dimF}(n)$ extracted from $\mathrm{DIMT}$ satisfies
--   $$1\le \mathrm{dimF}(n)\le 22.$$
--   Proved by `decide` on successive `Fin 50` windows (no `native_decide`).
-- source:
--   R8 BitNB densified DIMT field bound; Fin-window decide packs

-- DimBound pack 4: dimF bounds on n ∈ [20000, 25000)

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

namespace IntMul.Kappa.R8.Bit.Oppbank.DimBound4

private theorem le_w400 : ∀ n : Fin 50, dimF (n.val + 20000) ≤ 22 := by decide
private theorem pos_w400 : ∀ n : Fin 50, 0 < dimF (n.val + 20000) := by decide
private theorem le_w401 : ∀ n : Fin 50, dimF (n.val + 20050) ≤ 22 := by decide
private theorem pos_w401 : ∀ n : Fin 50, 0 < dimF (n.val + 20050) := by decide
private theorem le_w402 : ∀ n : Fin 50, dimF (n.val + 20100) ≤ 22 := by decide
private theorem pos_w402 : ∀ n : Fin 50, 0 < dimF (n.val + 20100) := by decide
private theorem le_w403 : ∀ n : Fin 50, dimF (n.val + 20150) ≤ 22 := by decide
private theorem pos_w403 : ∀ n : Fin 50, 0 < dimF (n.val + 20150) := by decide
private theorem le_w404 : ∀ n : Fin 50, dimF (n.val + 20200) ≤ 22 := by decide
private theorem pos_w404 : ∀ n : Fin 50, 0 < dimF (n.val + 20200) := by decide
private theorem le_w405 : ∀ n : Fin 50, dimF (n.val + 20250) ≤ 22 := by decide
private theorem pos_w405 : ∀ n : Fin 50, 0 < dimF (n.val + 20250) := by decide
private theorem le_w406 : ∀ n : Fin 50, dimF (n.val + 20300) ≤ 22 := by decide
private theorem pos_w406 : ∀ n : Fin 50, 0 < dimF (n.val + 20300) := by decide
private theorem le_w407 : ∀ n : Fin 50, dimF (n.val + 20350) ≤ 22 := by decide
private theorem pos_w407 : ∀ n : Fin 50, 0 < dimF (n.val + 20350) := by decide
private theorem le_w408 : ∀ n : Fin 50, dimF (n.val + 20400) ≤ 22 := by decide
private theorem pos_w408 : ∀ n : Fin 50, 0 < dimF (n.val + 20400) := by decide
private theorem le_w409 : ∀ n : Fin 50, dimF (n.val + 20450) ≤ 22 := by decide
private theorem pos_w409 : ∀ n : Fin 50, 0 < dimF (n.val + 20450) := by decide
private theorem le_w410 : ∀ n : Fin 50, dimF (n.val + 20500) ≤ 22 := by decide
private theorem pos_w410 : ∀ n : Fin 50, 0 < dimF (n.val + 20500) := by decide
private theorem le_w411 : ∀ n : Fin 50, dimF (n.val + 20550) ≤ 22 := by decide
private theorem pos_w411 : ∀ n : Fin 50, 0 < dimF (n.val + 20550) := by decide
private theorem le_w412 : ∀ n : Fin 50, dimF (n.val + 20600) ≤ 22 := by decide
private theorem pos_w412 : ∀ n : Fin 50, 0 < dimF (n.val + 20600) := by decide
private theorem le_w413 : ∀ n : Fin 50, dimF (n.val + 20650) ≤ 22 := by decide
private theorem pos_w413 : ∀ n : Fin 50, 0 < dimF (n.val + 20650) := by decide
private theorem le_w414 : ∀ n : Fin 50, dimF (n.val + 20700) ≤ 22 := by decide
private theorem pos_w414 : ∀ n : Fin 50, 0 < dimF (n.val + 20700) := by decide
private theorem le_w415 : ∀ n : Fin 50, dimF (n.val + 20750) ≤ 22 := by decide
private theorem pos_w415 : ∀ n : Fin 50, 0 < dimF (n.val + 20750) := by decide
private theorem le_w416 : ∀ n : Fin 50, dimF (n.val + 20800) ≤ 22 := by decide
private theorem pos_w416 : ∀ n : Fin 50, 0 < dimF (n.val + 20800) := by decide
private theorem le_w417 : ∀ n : Fin 50, dimF (n.val + 20850) ≤ 22 := by decide
private theorem pos_w417 : ∀ n : Fin 50, 0 < dimF (n.val + 20850) := by decide
private theorem le_w418 : ∀ n : Fin 50, dimF (n.val + 20900) ≤ 22 := by decide
private theorem pos_w418 : ∀ n : Fin 50, 0 < dimF (n.val + 20900) := by decide
private theorem le_w419 : ∀ n : Fin 50, dimF (n.val + 20950) ≤ 22 := by decide
private theorem pos_w419 : ∀ n : Fin 50, 0 < dimF (n.val + 20950) := by decide
private theorem le_w420 : ∀ n : Fin 50, dimF (n.val + 21000) ≤ 22 := by decide
private theorem pos_w420 : ∀ n : Fin 50, 0 < dimF (n.val + 21000) := by decide
private theorem le_w421 : ∀ n : Fin 50, dimF (n.val + 21050) ≤ 22 := by decide
private theorem pos_w421 : ∀ n : Fin 50, 0 < dimF (n.val + 21050) := by decide
private theorem le_w422 : ∀ n : Fin 50, dimF (n.val + 21100) ≤ 22 := by decide
private theorem pos_w422 : ∀ n : Fin 50, 0 < dimF (n.val + 21100) := by decide
private theorem le_w423 : ∀ n : Fin 50, dimF (n.val + 21150) ≤ 22 := by decide
private theorem pos_w423 : ∀ n : Fin 50, 0 < dimF (n.val + 21150) := by decide
private theorem le_w424 : ∀ n : Fin 50, dimF (n.val + 21200) ≤ 22 := by decide
private theorem pos_w424 : ∀ n : Fin 50, 0 < dimF (n.val + 21200) := by decide
private theorem le_w425 : ∀ n : Fin 50, dimF (n.val + 21250) ≤ 22 := by decide
private theorem pos_w425 : ∀ n : Fin 50, 0 < dimF (n.val + 21250) := by decide
private theorem le_w426 : ∀ n : Fin 50, dimF (n.val + 21300) ≤ 22 := by decide
private theorem pos_w426 : ∀ n : Fin 50, 0 < dimF (n.val + 21300) := by decide
private theorem le_w427 : ∀ n : Fin 50, dimF (n.val + 21350) ≤ 22 := by decide
private theorem pos_w427 : ∀ n : Fin 50, 0 < dimF (n.val + 21350) := by decide
private theorem le_w428 : ∀ n : Fin 50, dimF (n.val + 21400) ≤ 22 := by decide
private theorem pos_w428 : ∀ n : Fin 50, 0 < dimF (n.val + 21400) := by decide
private theorem le_w429 : ∀ n : Fin 50, dimF (n.val + 21450) ≤ 22 := by decide
private theorem pos_w429 : ∀ n : Fin 50, 0 < dimF (n.val + 21450) := by decide
private theorem le_w430 : ∀ n : Fin 50, dimF (n.val + 21500) ≤ 22 := by decide
private theorem pos_w430 : ∀ n : Fin 50, 0 < dimF (n.val + 21500) := by decide
private theorem le_w431 : ∀ n : Fin 50, dimF (n.val + 21550) ≤ 22 := by decide
private theorem pos_w431 : ∀ n : Fin 50, 0 < dimF (n.val + 21550) := by decide
private theorem le_w432 : ∀ n : Fin 50, dimF (n.val + 21600) ≤ 22 := by decide
private theorem pos_w432 : ∀ n : Fin 50, 0 < dimF (n.val + 21600) := by decide
private theorem le_w433 : ∀ n : Fin 50, dimF (n.val + 21650) ≤ 22 := by decide
private theorem pos_w433 : ∀ n : Fin 50, 0 < dimF (n.val + 21650) := by decide
private theorem le_w434 : ∀ n : Fin 50, dimF (n.val + 21700) ≤ 22 := by decide
private theorem pos_w434 : ∀ n : Fin 50, 0 < dimF (n.val + 21700) := by decide
private theorem le_w435 : ∀ n : Fin 50, dimF (n.val + 21750) ≤ 22 := by decide
private theorem pos_w435 : ∀ n : Fin 50, 0 < dimF (n.val + 21750) := by decide
private theorem le_w436 : ∀ n : Fin 50, dimF (n.val + 21800) ≤ 22 := by decide
private theorem pos_w436 : ∀ n : Fin 50, 0 < dimF (n.val + 21800) := by decide
private theorem le_w437 : ∀ n : Fin 50, dimF (n.val + 21850) ≤ 22 := by decide
private theorem pos_w437 : ∀ n : Fin 50, 0 < dimF (n.val + 21850) := by decide
private theorem le_w438 : ∀ n : Fin 50, dimF (n.val + 21900) ≤ 22 := by decide
private theorem pos_w438 : ∀ n : Fin 50, 0 < dimF (n.val + 21900) := by decide
private theorem le_w439 : ∀ n : Fin 50, dimF (n.val + 21950) ≤ 22 := by decide
private theorem pos_w439 : ∀ n : Fin 50, 0 < dimF (n.val + 21950) := by decide
private theorem le_w440 : ∀ n : Fin 50, dimF (n.val + 22000) ≤ 22 := by decide
private theorem pos_w440 : ∀ n : Fin 50, 0 < dimF (n.val + 22000) := by decide
private theorem le_w441 : ∀ n : Fin 50, dimF (n.val + 22050) ≤ 22 := by decide
private theorem pos_w441 : ∀ n : Fin 50, 0 < dimF (n.val + 22050) := by decide
private theorem le_w442 : ∀ n : Fin 50, dimF (n.val + 22100) ≤ 22 := by decide
private theorem pos_w442 : ∀ n : Fin 50, 0 < dimF (n.val + 22100) := by decide
private theorem le_w443 : ∀ n : Fin 50, dimF (n.val + 22150) ≤ 22 := by decide
private theorem pos_w443 : ∀ n : Fin 50, 0 < dimF (n.val + 22150) := by decide
private theorem le_w444 : ∀ n : Fin 50, dimF (n.val + 22200) ≤ 22 := by decide
private theorem pos_w444 : ∀ n : Fin 50, 0 < dimF (n.val + 22200) := by decide
private theorem le_w445 : ∀ n : Fin 50, dimF (n.val + 22250) ≤ 22 := by decide
private theorem pos_w445 : ∀ n : Fin 50, 0 < dimF (n.val + 22250) := by decide
private theorem le_w446 : ∀ n : Fin 50, dimF (n.val + 22300) ≤ 22 := by decide
private theorem pos_w446 : ∀ n : Fin 50, 0 < dimF (n.val + 22300) := by decide
private theorem le_w447 : ∀ n : Fin 50, dimF (n.val + 22350) ≤ 22 := by decide
private theorem pos_w447 : ∀ n : Fin 50, 0 < dimF (n.val + 22350) := by decide
private theorem le_w448 : ∀ n : Fin 50, dimF (n.val + 22400) ≤ 22 := by decide
private theorem pos_w448 : ∀ n : Fin 50, 0 < dimF (n.val + 22400) := by decide
private theorem le_w449 : ∀ n : Fin 50, dimF (n.val + 22450) ≤ 22 := by decide
private theorem pos_w449 : ∀ n : Fin 50, 0 < dimF (n.val + 22450) := by decide
private theorem le_w450 : ∀ n : Fin 50, dimF (n.val + 22500) ≤ 22 := by decide
private theorem pos_w450 : ∀ n : Fin 50, 0 < dimF (n.val + 22500) := by decide
private theorem le_w451 : ∀ n : Fin 50, dimF (n.val + 22550) ≤ 22 := by decide
private theorem pos_w451 : ∀ n : Fin 50, 0 < dimF (n.val + 22550) := by decide
private theorem le_w452 : ∀ n : Fin 50, dimF (n.val + 22600) ≤ 22 := by decide
private theorem pos_w452 : ∀ n : Fin 50, 0 < dimF (n.val + 22600) := by decide
private theorem le_w453 : ∀ n : Fin 50, dimF (n.val + 22650) ≤ 22 := by decide
private theorem pos_w453 : ∀ n : Fin 50, 0 < dimF (n.val + 22650) := by decide
private theorem le_w454 : ∀ n : Fin 50, dimF (n.val + 22700) ≤ 22 := by decide
private theorem pos_w454 : ∀ n : Fin 50, 0 < dimF (n.val + 22700) := by decide
private theorem le_w455 : ∀ n : Fin 50, dimF (n.val + 22750) ≤ 22 := by decide
private theorem pos_w455 : ∀ n : Fin 50, 0 < dimF (n.val + 22750) := by decide
private theorem le_w456 : ∀ n : Fin 50, dimF (n.val + 22800) ≤ 22 := by decide
private theorem pos_w456 : ∀ n : Fin 50, 0 < dimF (n.val + 22800) := by decide
private theorem le_w457 : ∀ n : Fin 50, dimF (n.val + 22850) ≤ 22 := by decide
private theorem pos_w457 : ∀ n : Fin 50, 0 < dimF (n.val + 22850) := by decide
private theorem le_w458 : ∀ n : Fin 50, dimF (n.val + 22900) ≤ 22 := by decide
private theorem pos_w458 : ∀ n : Fin 50, 0 < dimF (n.val + 22900) := by decide
private theorem le_w459 : ∀ n : Fin 50, dimF (n.val + 22950) ≤ 22 := by decide
private theorem pos_w459 : ∀ n : Fin 50, 0 < dimF (n.val + 22950) := by decide
private theorem le_w460 : ∀ n : Fin 50, dimF (n.val + 23000) ≤ 22 := by decide
private theorem pos_w460 : ∀ n : Fin 50, 0 < dimF (n.val + 23000) := by decide
private theorem le_w461 : ∀ n : Fin 50, dimF (n.val + 23050) ≤ 22 := by decide
private theorem pos_w461 : ∀ n : Fin 50, 0 < dimF (n.val + 23050) := by decide
private theorem le_w462 : ∀ n : Fin 50, dimF (n.val + 23100) ≤ 22 := by decide
private theorem pos_w462 : ∀ n : Fin 50, 0 < dimF (n.val + 23100) := by decide
private theorem le_w463 : ∀ n : Fin 50, dimF (n.val + 23150) ≤ 22 := by decide
private theorem pos_w463 : ∀ n : Fin 50, 0 < dimF (n.val + 23150) := by decide
private theorem le_w464 : ∀ n : Fin 50, dimF (n.val + 23200) ≤ 22 := by decide
private theorem pos_w464 : ∀ n : Fin 50, 0 < dimF (n.val + 23200) := by decide
private theorem le_w465 : ∀ n : Fin 50, dimF (n.val + 23250) ≤ 22 := by decide
private theorem pos_w465 : ∀ n : Fin 50, 0 < dimF (n.val + 23250) := by decide
private theorem le_w466 : ∀ n : Fin 50, dimF (n.val + 23300) ≤ 22 := by decide
private theorem pos_w466 : ∀ n : Fin 50, 0 < dimF (n.val + 23300) := by decide
private theorem le_w467 : ∀ n : Fin 50, dimF (n.val + 23350) ≤ 22 := by decide
private theorem pos_w467 : ∀ n : Fin 50, 0 < dimF (n.val + 23350) := by decide
private theorem le_w468 : ∀ n : Fin 50, dimF (n.val + 23400) ≤ 22 := by decide
private theorem pos_w468 : ∀ n : Fin 50, 0 < dimF (n.val + 23400) := by decide
private theorem le_w469 : ∀ n : Fin 50, dimF (n.val + 23450) ≤ 22 := by decide
private theorem pos_w469 : ∀ n : Fin 50, 0 < dimF (n.val + 23450) := by decide
private theorem le_w470 : ∀ n : Fin 50, dimF (n.val + 23500) ≤ 22 := by decide
private theorem pos_w470 : ∀ n : Fin 50, 0 < dimF (n.val + 23500) := by decide
private theorem le_w471 : ∀ n : Fin 50, dimF (n.val + 23550) ≤ 22 := by decide
private theorem pos_w471 : ∀ n : Fin 50, 0 < dimF (n.val + 23550) := by decide
private theorem le_w472 : ∀ n : Fin 50, dimF (n.val + 23600) ≤ 22 := by decide
private theorem pos_w472 : ∀ n : Fin 50, 0 < dimF (n.val + 23600) := by decide
private theorem le_w473 : ∀ n : Fin 50, dimF (n.val + 23650) ≤ 22 := by decide
private theorem pos_w473 : ∀ n : Fin 50, 0 < dimF (n.val + 23650) := by decide
private theorem le_w474 : ∀ n : Fin 50, dimF (n.val + 23700) ≤ 22 := by decide
private theorem pos_w474 : ∀ n : Fin 50, 0 < dimF (n.val + 23700) := by decide
private theorem le_w475 : ∀ n : Fin 50, dimF (n.val + 23750) ≤ 22 := by decide
private theorem pos_w475 : ∀ n : Fin 50, 0 < dimF (n.val + 23750) := by decide
private theorem le_w476 : ∀ n : Fin 50, dimF (n.val + 23800) ≤ 22 := by decide
private theorem pos_w476 : ∀ n : Fin 50, 0 < dimF (n.val + 23800) := by decide
private theorem le_w477 : ∀ n : Fin 50, dimF (n.val + 23850) ≤ 22 := by decide
private theorem pos_w477 : ∀ n : Fin 50, 0 < dimF (n.val + 23850) := by decide
private theorem le_w478 : ∀ n : Fin 50, dimF (n.val + 23900) ≤ 22 := by decide
private theorem pos_w478 : ∀ n : Fin 50, 0 < dimF (n.val + 23900) := by decide
private theorem le_w479 : ∀ n : Fin 50, dimF (n.val + 23950) ≤ 22 := by decide
private theorem pos_w479 : ∀ n : Fin 50, 0 < dimF (n.val + 23950) := by decide
private theorem le_w480 : ∀ n : Fin 50, dimF (n.val + 24000) ≤ 22 := by decide
private theorem pos_w480 : ∀ n : Fin 50, 0 < dimF (n.val + 24000) := by decide
private theorem le_w481 : ∀ n : Fin 50, dimF (n.val + 24050) ≤ 22 := by decide
private theorem pos_w481 : ∀ n : Fin 50, 0 < dimF (n.val + 24050) := by decide
private theorem le_w482 : ∀ n : Fin 50, dimF (n.val + 24100) ≤ 22 := by decide
private theorem pos_w482 : ∀ n : Fin 50, 0 < dimF (n.val + 24100) := by decide
private theorem le_w483 : ∀ n : Fin 50, dimF (n.val + 24150) ≤ 22 := by decide
private theorem pos_w483 : ∀ n : Fin 50, 0 < dimF (n.val + 24150) := by decide
private theorem le_w484 : ∀ n : Fin 50, dimF (n.val + 24200) ≤ 22 := by decide
private theorem pos_w484 : ∀ n : Fin 50, 0 < dimF (n.val + 24200) := by decide
private theorem le_w485 : ∀ n : Fin 50, dimF (n.val + 24250) ≤ 22 := by decide
private theorem pos_w485 : ∀ n : Fin 50, 0 < dimF (n.val + 24250) := by decide
private theorem le_w486 : ∀ n : Fin 50, dimF (n.val + 24300) ≤ 22 := by decide
private theorem pos_w486 : ∀ n : Fin 50, 0 < dimF (n.val + 24300) := by decide
private theorem le_w487 : ∀ n : Fin 50, dimF (n.val + 24350) ≤ 22 := by decide
private theorem pos_w487 : ∀ n : Fin 50, 0 < dimF (n.val + 24350) := by decide
private theorem le_w488 : ∀ n : Fin 50, dimF (n.val + 24400) ≤ 22 := by decide
private theorem pos_w488 : ∀ n : Fin 50, 0 < dimF (n.val + 24400) := by decide
private theorem le_w489 : ∀ n : Fin 50, dimF (n.val + 24450) ≤ 22 := by decide
private theorem pos_w489 : ∀ n : Fin 50, 0 < dimF (n.val + 24450) := by decide
private theorem le_w490 : ∀ n : Fin 50, dimF (n.val + 24500) ≤ 22 := by decide
private theorem pos_w490 : ∀ n : Fin 50, 0 < dimF (n.val + 24500) := by decide
private theorem le_w491 : ∀ n : Fin 50, dimF (n.val + 24550) ≤ 22 := by decide
private theorem pos_w491 : ∀ n : Fin 50, 0 < dimF (n.val + 24550) := by decide
private theorem le_w492 : ∀ n : Fin 50, dimF (n.val + 24600) ≤ 22 := by decide
private theorem pos_w492 : ∀ n : Fin 50, 0 < dimF (n.val + 24600) := by decide
private theorem le_w493 : ∀ n : Fin 50, dimF (n.val + 24650) ≤ 22 := by decide
private theorem pos_w493 : ∀ n : Fin 50, 0 < dimF (n.val + 24650) := by decide
private theorem le_w494 : ∀ n : Fin 50, dimF (n.val + 24700) ≤ 22 := by decide
private theorem pos_w494 : ∀ n : Fin 50, 0 < dimF (n.val + 24700) := by decide
private theorem le_w495 : ∀ n : Fin 50, dimF (n.val + 24750) ≤ 22 := by decide
private theorem pos_w495 : ∀ n : Fin 50, 0 < dimF (n.val + 24750) := by decide
private theorem le_w496 : ∀ n : Fin 50, dimF (n.val + 24800) ≤ 22 := by decide
private theorem pos_w496 : ∀ n : Fin 50, 0 < dimF (n.val + 24800) := by decide
private theorem le_w497 : ∀ n : Fin 50, dimF (n.val + 24850) ≤ 22 := by decide
private theorem pos_w497 : ∀ n : Fin 50, 0 < dimF (n.val + 24850) := by decide
private theorem le_w498 : ∀ n : Fin 50, dimF (n.val + 24900) ≤ 22 := by decide
private theorem pos_w498 : ∀ n : Fin 50, 0 < dimF (n.val + 24900) := by decide
private theorem le_w499 : ∀ n : Fin 50, dimF (n.val + 24950) ≤ 22 := by decide
private theorem pos_w499 : ∀ n : Fin 50, 0 < dimF (n.val + 24950) := by decide

theorem dimF_le_22_range : ∀ n, 20000 ≤ n → n < 25000 → dimF n ≤ 22 := by
  intro n hlo hhi
  by_cases h0 : n < 20050
  · have hr : n - 20000 < 50 := by omega
    have heq : n = (n - 20000) + 20000 := by omega
    rw [heq]
    exact le_w400 ⟨n - 20000, hr⟩
  · by_cases h1 : n < 20100
    · have hr : n - 20050 < 50 := by omega
      have heq : n = (n - 20050) + 20050 := by omega
      rw [heq]
      exact le_w401 ⟨n - 20050, hr⟩
    · by_cases h2 : n < 20150
      · have hr : n - 20100 < 50 := by omega
        have heq : n = (n - 20100) + 20100 := by omega
        rw [heq]
        exact le_w402 ⟨n - 20100, hr⟩
      · by_cases h3 : n < 20200
        · have hr : n - 20150 < 50 := by omega
          have heq : n = (n - 20150) + 20150 := by omega
          rw [heq]
          exact le_w403 ⟨n - 20150, hr⟩
        · by_cases h4 : n < 20250
          · have hr : n - 20200 < 50 := by omega
            have heq : n = (n - 20200) + 20200 := by omega
            rw [heq]
            exact le_w404 ⟨n - 20200, hr⟩
          · by_cases h5 : n < 20300
            · have hr : n - 20250 < 50 := by omega
              have heq : n = (n - 20250) + 20250 := by omega
              rw [heq]
              exact le_w405 ⟨n - 20250, hr⟩
            · by_cases h6 : n < 20350
              · have hr : n - 20300 < 50 := by omega
                have heq : n = (n - 20300) + 20300 := by omega
                rw [heq]
                exact le_w406 ⟨n - 20300, hr⟩
              · by_cases h7 : n < 20400
                · have hr : n - 20350 < 50 := by omega
                  have heq : n = (n - 20350) + 20350 := by omega
                  rw [heq]
                  exact le_w407 ⟨n - 20350, hr⟩
                · by_cases h8 : n < 20450
                  · have hr : n - 20400 < 50 := by omega
                    have heq : n = (n - 20400) + 20400 := by omega
                    rw [heq]
                    exact le_w408 ⟨n - 20400, hr⟩
                  · by_cases h9 : n < 20500
                    · have hr : n - 20450 < 50 := by omega
                      have heq : n = (n - 20450) + 20450 := by omega
                      rw [heq]
                      exact le_w409 ⟨n - 20450, hr⟩
                    · by_cases h10 : n < 20550
                      · have hr : n - 20500 < 50 := by omega
                        have heq : n = (n - 20500) + 20500 := by omega
                        rw [heq]
                        exact le_w410 ⟨n - 20500, hr⟩
                      · by_cases h11 : n < 20600
                        · have hr : n - 20550 < 50 := by omega
                          have heq : n = (n - 20550) + 20550 := by omega
                          rw [heq]
                          exact le_w411 ⟨n - 20550, hr⟩
                        · by_cases h12 : n < 20650
                          · have hr : n - 20600 < 50 := by omega
                            have heq : n = (n - 20600) + 20600 := by omega
                            rw [heq]
                            exact le_w412 ⟨n - 20600, hr⟩
                          · by_cases h13 : n < 20700
                            · have hr : n - 20650 < 50 := by omega
                              have heq : n = (n - 20650) + 20650 := by omega
                              rw [heq]
                              exact le_w413 ⟨n - 20650, hr⟩
                            · by_cases h14 : n < 20750
                              · have hr : n - 20700 < 50 := by omega
                                have heq : n = (n - 20700) + 20700 := by omega
                                rw [heq]
                                exact le_w414 ⟨n - 20700, hr⟩
                              · by_cases h15 : n < 20800
                                · have hr : n - 20750 < 50 := by omega
                                  have heq : n = (n - 20750) + 20750 := by omega
                                  rw [heq]
                                  exact le_w415 ⟨n - 20750, hr⟩
                                · by_cases h16 : n < 20850
                                  · have hr : n - 20800 < 50 := by omega
                                    have heq : n = (n - 20800) + 20800 := by omega
                                    rw [heq]
                                    exact le_w416 ⟨n - 20800, hr⟩
                                  · by_cases h17 : n < 20900
                                    · have hr : n - 20850 < 50 := by omega
                                      have heq : n = (n - 20850) + 20850 := by omega
                                      rw [heq]
                                      exact le_w417 ⟨n - 20850, hr⟩
                                    · by_cases h18 : n < 20950
                                      · have hr : n - 20900 < 50 := by omega
                                        have heq : n = (n - 20900) + 20900 := by omega
                                        rw [heq]
                                        exact le_w418 ⟨n - 20900, hr⟩
                                      · by_cases h19 : n < 21000
                                        · have hr : n - 20950 < 50 := by omega
                                          have heq : n = (n - 20950) + 20950 := by omega
                                          rw [heq]
                                          exact le_w419 ⟨n - 20950, hr⟩
                                        · by_cases h20 : n < 21050
                                          · have hr : n - 21000 < 50 := by omega
                                            have heq : n = (n - 21000) + 21000 := by omega
                                            rw [heq]
                                            exact le_w420 ⟨n - 21000, hr⟩
                                          · by_cases h21 : n < 21100
                                            · have hr : n - 21050 < 50 := by omega
                                              have heq : n = (n - 21050) + 21050 := by omega
                                              rw [heq]
                                              exact le_w421 ⟨n - 21050, hr⟩
                                            · by_cases h22 : n < 21150
                                              · have hr : n - 21100 < 50 := by omega
                                                have heq : n = (n - 21100) + 21100 := by omega
                                                rw [heq]
                                                exact le_w422 ⟨n - 21100, hr⟩
                                              · by_cases h23 : n < 21200
                                                · have hr : n - 21150 < 50 := by omega
                                                  have heq : n = (n - 21150) + 21150 := by omega
                                                  rw [heq]
                                                  exact le_w423 ⟨n - 21150, hr⟩
                                                · by_cases h24 : n < 21250
                                                  · have hr : n - 21200 < 50 := by omega
                                                    have heq : n = (n - 21200) + 21200 := by omega
                                                    rw [heq]
                                                    exact le_w424 ⟨n - 21200, hr⟩
                                                  · by_cases h25 : n < 21300
                                                    · have hr : n - 21250 < 50 := by omega
                                                      have heq : n = (n - 21250) + 21250 := by omega
                                                      rw [heq]
                                                      exact le_w425 ⟨n - 21250, hr⟩
                                                    · by_cases h26 : n < 21350
                                                      · have hr : n - 21300 < 50 := by omega
                                                        have heq : n = (n - 21300) + 21300 := by omega
                                                        rw [heq]
                                                        exact le_w426 ⟨n - 21300, hr⟩
                                                      · by_cases h27 : n < 21400
                                                        · have hr : n - 21350 < 50 := by omega
                                                          have heq : n = (n - 21350) + 21350 := by omega
                                                          rw [heq]
                                                          exact le_w427 ⟨n - 21350, hr⟩
                                                        · by_cases h28 : n < 21450
                                                          · have hr : n - 21400 < 50 := by omega
                                                            have heq : n = (n - 21400) + 21400 := by omega
                                                            rw [heq]
                                                            exact le_w428 ⟨n - 21400, hr⟩
                                                          · by_cases h29 : n < 21500
                                                            · have hr : n - 21450 < 50 := by omega
                                                              have heq : n = (n - 21450) + 21450 := by omega
                                                              rw [heq]
                                                              exact le_w429 ⟨n - 21450, hr⟩
                                                            · by_cases h30 : n < 21550
                                                              · have hr : n - 21500 < 50 := by omega
                                                                have heq : n = (n - 21500) + 21500 := by omega
                                                                rw [heq]
                                                                exact le_w430 ⟨n - 21500, hr⟩
                                                              · by_cases h31 : n < 21600
                                                                · have hr : n - 21550 < 50 := by omega
                                                                  have heq : n = (n - 21550) + 21550 := by omega
                                                                  rw [heq]
                                                                  exact le_w431 ⟨n - 21550, hr⟩
                                                                · by_cases h32 : n < 21650
                                                                  · have hr : n - 21600 < 50 := by omega
                                                                    have heq : n = (n - 21600) + 21600 := by omega
                                                                    rw [heq]
                                                                    exact le_w432 ⟨n - 21600, hr⟩
                                                                  · by_cases h33 : n < 21700
                                                                    · have hr : n - 21650 < 50 := by omega
                                                                      have heq : n = (n - 21650) + 21650 := by omega
                                                                      rw [heq]
                                                                      exact le_w433 ⟨n - 21650, hr⟩
                                                                    · by_cases h34 : n < 21750
                                                                      · have hr : n - 21700 < 50 := by omega
                                                                        have heq : n = (n - 21700) + 21700 := by omega
                                                                        rw [heq]
                                                                        exact le_w434 ⟨n - 21700, hr⟩
                                                                      · by_cases h35 : n < 21800
                                                                        · have hr : n - 21750 < 50 := by omega
                                                                          have heq : n = (n - 21750) + 21750 := by omega
                                                                          rw [heq]
                                                                          exact le_w435 ⟨n - 21750, hr⟩
                                                                        · by_cases h36 : n < 21850
                                                                          · have hr : n - 21800 < 50 := by omega
                                                                            have heq : n = (n - 21800) + 21800 := by omega
                                                                            rw [heq]
                                                                            exact le_w436 ⟨n - 21800, hr⟩
                                                                          · by_cases h37 : n < 21900
                                                                            · have hr : n - 21850 < 50 := by omega
                                                                              have heq : n = (n - 21850) + 21850 := by omega
                                                                              rw [heq]
                                                                              exact le_w437 ⟨n - 21850, hr⟩
                                                                            · by_cases h38 : n < 21950
                                                                              · have hr : n - 21900 < 50 := by omega
                                                                                have heq : n = (n - 21900) + 21900 := by omega
                                                                                rw [heq]
                                                                                exact le_w438 ⟨n - 21900, hr⟩
                                                                              · by_cases h39 : n < 22000
                                                                                · have hr : n - 21950 < 50 := by omega
                                                                                  have heq : n = (n - 21950) + 21950 := by omega
                                                                                  rw [heq]
                                                                                  exact le_w439 ⟨n - 21950, hr⟩
                                                                                · by_cases h40 : n < 22050
                                                                                  · have hr : n - 22000 < 50 := by omega
                                                                                    have heq : n = (n - 22000) + 22000 := by omega
                                                                                    rw [heq]
                                                                                    exact le_w440 ⟨n - 22000, hr⟩
                                                                                  · by_cases h41 : n < 22100
                                                                                    · have hr : n - 22050 < 50 := by omega
                                                                                      have heq : n = (n - 22050) + 22050 := by omega
                                                                                      rw [heq]
                                                                                      exact le_w441 ⟨n - 22050, hr⟩
                                                                                    · by_cases h42 : n < 22150
                                                                                      · have hr : n - 22100 < 50 := by omega
                                                                                        have heq : n = (n - 22100) + 22100 := by omega
                                                                                        rw [heq]
                                                                                        exact le_w442 ⟨n - 22100, hr⟩
                                                                                      · by_cases h43 : n < 22200
                                                                                        · have hr : n - 22150 < 50 := by omega
                                                                                          have heq : n = (n - 22150) + 22150 := by omega
                                                                                          rw [heq]
                                                                                          exact le_w443 ⟨n - 22150, hr⟩
                                                                                        · by_cases h44 : n < 22250
                                                                                          · have hr : n - 22200 < 50 := by omega
                                                                                            have heq : n = (n - 22200) + 22200 := by omega
                                                                                            rw [heq]
                                                                                            exact le_w444 ⟨n - 22200, hr⟩
                                                                                          · by_cases h45 : n < 22300
                                                                                            · have hr : n - 22250 < 50 := by omega
                                                                                              have heq : n = (n - 22250) + 22250 := by omega
                                                                                              rw [heq]
                                                                                              exact le_w445 ⟨n - 22250, hr⟩
                                                                                            · by_cases h46 : n < 22350
                                                                                              · have hr : n - 22300 < 50 := by omega
                                                                                                have heq : n = (n - 22300) + 22300 := by omega
                                                                                                rw [heq]
                                                                                                exact le_w446 ⟨n - 22300, hr⟩
                                                                                              · by_cases h47 : n < 22400
                                                                                                · have hr : n - 22350 < 50 := by omega
                                                                                                  have heq : n = (n - 22350) + 22350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact le_w447 ⟨n - 22350, hr⟩
                                                                                                · by_cases h48 : n < 22450
                                                                                                  · have hr : n - 22400 < 50 := by omega
                                                                                                    have heq : n = (n - 22400) + 22400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact le_w448 ⟨n - 22400, hr⟩
                                                                                                  · by_cases h49 : n < 22500
                                                                                                    · have hr : n - 22450 < 50 := by omega
                                                                                                      have heq : n = (n - 22450) + 22450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact le_w449 ⟨n - 22450, hr⟩
                                                                                                    · by_cases h50 : n < 22550
                                                                                                      · have hr : n - 22500 < 50 := by omega
                                                                                                        have heq : n = (n - 22500) + 22500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact le_w450 ⟨n - 22500, hr⟩
                                                                                                      · by_cases h51 : n < 22600
                                                                                                        · have hr : n - 22550 < 50 := by omega
                                                                                                          have heq : n = (n - 22550) + 22550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact le_w451 ⟨n - 22550, hr⟩
                                                                                                        · by_cases h52 : n < 22650
                                                                                                          · have hr : n - 22600 < 50 := by omega
                                                                                                            have heq : n = (n - 22600) + 22600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact le_w452 ⟨n - 22600, hr⟩
                                                                                                          · by_cases h53 : n < 22700
                                                                                                            · have hr : n - 22650 < 50 := by omega
                                                                                                              have heq : n = (n - 22650) + 22650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact le_w453 ⟨n - 22650, hr⟩
                                                                                                            · by_cases h54 : n < 22750
                                                                                                              · have hr : n - 22700 < 50 := by omega
                                                                                                                have heq : n = (n - 22700) + 22700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact le_w454 ⟨n - 22700, hr⟩
                                                                                                              · by_cases h55 : n < 22800
                                                                                                                · have hr : n - 22750 < 50 := by omega
                                                                                                                  have heq : n = (n - 22750) + 22750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact le_w455 ⟨n - 22750, hr⟩
                                                                                                                · by_cases h56 : n < 22850
                                                                                                                  · have hr : n - 22800 < 50 := by omega
                                                                                                                    have heq : n = (n - 22800) + 22800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact le_w456 ⟨n - 22800, hr⟩
                                                                                                                  · by_cases h57 : n < 22900
                                                                                                                    · have hr : n - 22850 < 50 := by omega
                                                                                                                      have heq : n = (n - 22850) + 22850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact le_w457 ⟨n - 22850, hr⟩
                                                                                                                    · by_cases h58 : n < 22950
                                                                                                                      · have hr : n - 22900 < 50 := by omega
                                                                                                                        have heq : n = (n - 22900) + 22900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact le_w458 ⟨n - 22900, hr⟩
                                                                                                                      · by_cases h59 : n < 23000
                                                                                                                        · have hr : n - 22950 < 50 := by omega
                                                                                                                          have heq : n = (n - 22950) + 22950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact le_w459 ⟨n - 22950, hr⟩
                                                                                                                        · by_cases h60 : n < 23050
                                                                                                                          · have hr : n - 23000 < 50 := by omega
                                                                                                                            have heq : n = (n - 23000) + 23000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact le_w460 ⟨n - 23000, hr⟩
                                                                                                                          · by_cases h61 : n < 23100
                                                                                                                            · have hr : n - 23050 < 50 := by omega
                                                                                                                              have heq : n = (n - 23050) + 23050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact le_w461 ⟨n - 23050, hr⟩
                                                                                                                            · by_cases h62 : n < 23150
                                                                                                                              · have hr : n - 23100 < 50 := by omega
                                                                                                                                have heq : n = (n - 23100) + 23100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact le_w462 ⟨n - 23100, hr⟩
                                                                                                                              · by_cases h63 : n < 23200
                                                                                                                                · have hr : n - 23150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 23150) + 23150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact le_w463 ⟨n - 23150, hr⟩
                                                                                                                                · by_cases h64 : n < 23250
                                                                                                                                  · have hr : n - 23200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 23200) + 23200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact le_w464 ⟨n - 23200, hr⟩
                                                                                                                                  · by_cases h65 : n < 23300
                                                                                                                                    · have hr : n - 23250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 23250) + 23250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact le_w465 ⟨n - 23250, hr⟩
                                                                                                                                    · by_cases h66 : n < 23350
                                                                                                                                      · have hr : n - 23300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 23300) + 23300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact le_w466 ⟨n - 23300, hr⟩
                                                                                                                                      · by_cases h67 : n < 23400
                                                                                                                                        · have hr : n - 23350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 23350) + 23350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact le_w467 ⟨n - 23350, hr⟩
                                                                                                                                        · by_cases h68 : n < 23450
                                                                                                                                          · have hr : n - 23400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 23400) + 23400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact le_w468 ⟨n - 23400, hr⟩
                                                                                                                                          · by_cases h69 : n < 23500
                                                                                                                                            · have hr : n - 23450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 23450) + 23450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact le_w469 ⟨n - 23450, hr⟩
                                                                                                                                            · by_cases h70 : n < 23550
                                                                                                                                              · have hr : n - 23500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 23500) + 23500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact le_w470 ⟨n - 23500, hr⟩
                                                                                                                                              · by_cases h71 : n < 23600
                                                                                                                                                · have hr : n - 23550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 23550) + 23550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact le_w471 ⟨n - 23550, hr⟩
                                                                                                                                                · by_cases h72 : n < 23650
                                                                                                                                                  · have hr : n - 23600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 23600) + 23600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact le_w472 ⟨n - 23600, hr⟩
                                                                                                                                                  · by_cases h73 : n < 23700
                                                                                                                                                    · have hr : n - 23650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 23650) + 23650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact le_w473 ⟨n - 23650, hr⟩
                                                                                                                                                    · by_cases h74 : n < 23750
                                                                                                                                                      · have hr : n - 23700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 23700) + 23700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact le_w474 ⟨n - 23700, hr⟩
                                                                                                                                                      · by_cases h75 : n < 23800
                                                                                                                                                        · have hr : n - 23750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 23750) + 23750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact le_w475 ⟨n - 23750, hr⟩
                                                                                                                                                        · by_cases h76 : n < 23850
                                                                                                                                                          · have hr : n - 23800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 23800) + 23800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact le_w476 ⟨n - 23800, hr⟩
                                                                                                                                                          · by_cases h77 : n < 23900
                                                                                                                                                            · have hr : n - 23850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 23850) + 23850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact le_w477 ⟨n - 23850, hr⟩
                                                                                                                                                            · by_cases h78 : n < 23950
                                                                                                                                                              · have hr : n - 23900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 23900) + 23900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact le_w478 ⟨n - 23900, hr⟩
                                                                                                                                                              · by_cases h79 : n < 24000
                                                                                                                                                                · have hr : n - 23950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 23950) + 23950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact le_w479 ⟨n - 23950, hr⟩
                                                                                                                                                                · by_cases h80 : n < 24050
                                                                                                                                                                  · have hr : n - 24000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 24000) + 24000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact le_w480 ⟨n - 24000, hr⟩
                                                                                                                                                                  · by_cases h81 : n < 24100
                                                                                                                                                                    · have hr : n - 24050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 24050) + 24050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact le_w481 ⟨n - 24050, hr⟩
                                                                                                                                                                    · by_cases h82 : n < 24150
                                                                                                                                                                      · have hr : n - 24100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 24100) + 24100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact le_w482 ⟨n - 24100, hr⟩
                                                                                                                                                                      · by_cases h83 : n < 24200
                                                                                                                                                                        · have hr : n - 24150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 24150) + 24150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact le_w483 ⟨n - 24150, hr⟩
                                                                                                                                                                        · by_cases h84 : n < 24250
                                                                                                                                                                          · have hr : n - 24200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 24200) + 24200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact le_w484 ⟨n - 24200, hr⟩
                                                                                                                                                                          · by_cases h85 : n < 24300
                                                                                                                                                                            · have hr : n - 24250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 24250) + 24250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact le_w485 ⟨n - 24250, hr⟩
                                                                                                                                                                            · by_cases h86 : n < 24350
                                                                                                                                                                              · have hr : n - 24300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 24300) + 24300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact le_w486 ⟨n - 24300, hr⟩
                                                                                                                                                                              · by_cases h87 : n < 24400
                                                                                                                                                                                · have hr : n - 24350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 24350) + 24350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact le_w487 ⟨n - 24350, hr⟩
                                                                                                                                                                                · by_cases h88 : n < 24450
                                                                                                                                                                                  · have hr : n - 24400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 24400) + 24400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact le_w488 ⟨n - 24400, hr⟩
                                                                                                                                                                                  · by_cases h89 : n < 24500
                                                                                                                                                                                    · have hr : n - 24450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 24450) + 24450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact le_w489 ⟨n - 24450, hr⟩
                                                                                                                                                                                    · by_cases h90 : n < 24550
                                                                                                                                                                                      · have hr : n - 24500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 24500) + 24500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact le_w490 ⟨n - 24500, hr⟩
                                                                                                                                                                                      · by_cases h91 : n < 24600
                                                                                                                                                                                        · have hr : n - 24550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 24550) + 24550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact le_w491 ⟨n - 24550, hr⟩
                                                                                                                                                                                        · by_cases h92 : n < 24650
                                                                                                                                                                                          · have hr : n - 24600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 24600) + 24600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact le_w492 ⟨n - 24600, hr⟩
                                                                                                                                                                                          · by_cases h93 : n < 24700
                                                                                                                                                                                            · have hr : n - 24650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 24650) + 24650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact le_w493 ⟨n - 24650, hr⟩
                                                                                                                                                                                            · by_cases h94 : n < 24750
                                                                                                                                                                                              · have hr : n - 24700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 24700) + 24700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact le_w494 ⟨n - 24700, hr⟩
                                                                                                                                                                                              · by_cases h95 : n < 24800
                                                                                                                                                                                                · have hr : n - 24750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 24750) + 24750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact le_w495 ⟨n - 24750, hr⟩
                                                                                                                                                                                                · by_cases h96 : n < 24850
                                                                                                                                                                                                  · have hr : n - 24800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 24800) + 24800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact le_w496 ⟨n - 24800, hr⟩
                                                                                                                                                                                                  · by_cases h97 : n < 24900
                                                                                                                                                                                                    · have hr : n - 24850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 24850) + 24850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact le_w497 ⟨n - 24850, hr⟩
                                                                                                                                                                                                    · by_cases h98 : n < 24950
                                                                                                                                                                                                      · have hr : n - 24900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 24900) + 24900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact le_w498 ⟨n - 24900, hr⟩
                                                                                                                                                                                                      · by_cases h99 : n < 25000
                                                                                                                                                                                                        · have hr : n - 24950 < 50 := by omega
                                                                                                                                                                                                          have heq : n = (n - 24950) + 24950 := by omega
                                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                                          exact le_w499 ⟨n - 24950, hr⟩
                                                                                                                                                                                                        · omega

theorem dimF_pos_range : ∀ n, 20000 ≤ n → n < 25000 → 0 < dimF n := by
  intro n hlo hhi
  by_cases h0 : n < 20050
  · have hr : n - 20000 < 50 := by omega
    have heq : n = (n - 20000) + 20000 := by omega
    rw [heq]
    exact pos_w400 ⟨n - 20000, hr⟩
  · by_cases h1 : n < 20100
    · have hr : n - 20050 < 50 := by omega
      have heq : n = (n - 20050) + 20050 := by omega
      rw [heq]
      exact pos_w401 ⟨n - 20050, hr⟩
    · by_cases h2 : n < 20150
      · have hr : n - 20100 < 50 := by omega
        have heq : n = (n - 20100) + 20100 := by omega
        rw [heq]
        exact pos_w402 ⟨n - 20100, hr⟩
      · by_cases h3 : n < 20200
        · have hr : n - 20150 < 50 := by omega
          have heq : n = (n - 20150) + 20150 := by omega
          rw [heq]
          exact pos_w403 ⟨n - 20150, hr⟩
        · by_cases h4 : n < 20250
          · have hr : n - 20200 < 50 := by omega
            have heq : n = (n - 20200) + 20200 := by omega
            rw [heq]
            exact pos_w404 ⟨n - 20200, hr⟩
          · by_cases h5 : n < 20300
            · have hr : n - 20250 < 50 := by omega
              have heq : n = (n - 20250) + 20250 := by omega
              rw [heq]
              exact pos_w405 ⟨n - 20250, hr⟩
            · by_cases h6 : n < 20350
              · have hr : n - 20300 < 50 := by omega
                have heq : n = (n - 20300) + 20300 := by omega
                rw [heq]
                exact pos_w406 ⟨n - 20300, hr⟩
              · by_cases h7 : n < 20400
                · have hr : n - 20350 < 50 := by omega
                  have heq : n = (n - 20350) + 20350 := by omega
                  rw [heq]
                  exact pos_w407 ⟨n - 20350, hr⟩
                · by_cases h8 : n < 20450
                  · have hr : n - 20400 < 50 := by omega
                    have heq : n = (n - 20400) + 20400 := by omega
                    rw [heq]
                    exact pos_w408 ⟨n - 20400, hr⟩
                  · by_cases h9 : n < 20500
                    · have hr : n - 20450 < 50 := by omega
                      have heq : n = (n - 20450) + 20450 := by omega
                      rw [heq]
                      exact pos_w409 ⟨n - 20450, hr⟩
                    · by_cases h10 : n < 20550
                      · have hr : n - 20500 < 50 := by omega
                        have heq : n = (n - 20500) + 20500 := by omega
                        rw [heq]
                        exact pos_w410 ⟨n - 20500, hr⟩
                      · by_cases h11 : n < 20600
                        · have hr : n - 20550 < 50 := by omega
                          have heq : n = (n - 20550) + 20550 := by omega
                          rw [heq]
                          exact pos_w411 ⟨n - 20550, hr⟩
                        · by_cases h12 : n < 20650
                          · have hr : n - 20600 < 50 := by omega
                            have heq : n = (n - 20600) + 20600 := by omega
                            rw [heq]
                            exact pos_w412 ⟨n - 20600, hr⟩
                          · by_cases h13 : n < 20700
                            · have hr : n - 20650 < 50 := by omega
                              have heq : n = (n - 20650) + 20650 := by omega
                              rw [heq]
                              exact pos_w413 ⟨n - 20650, hr⟩
                            · by_cases h14 : n < 20750
                              · have hr : n - 20700 < 50 := by omega
                                have heq : n = (n - 20700) + 20700 := by omega
                                rw [heq]
                                exact pos_w414 ⟨n - 20700, hr⟩
                              · by_cases h15 : n < 20800
                                · have hr : n - 20750 < 50 := by omega
                                  have heq : n = (n - 20750) + 20750 := by omega
                                  rw [heq]
                                  exact pos_w415 ⟨n - 20750, hr⟩
                                · by_cases h16 : n < 20850
                                  · have hr : n - 20800 < 50 := by omega
                                    have heq : n = (n - 20800) + 20800 := by omega
                                    rw [heq]
                                    exact pos_w416 ⟨n - 20800, hr⟩
                                  · by_cases h17 : n < 20900
                                    · have hr : n - 20850 < 50 := by omega
                                      have heq : n = (n - 20850) + 20850 := by omega
                                      rw [heq]
                                      exact pos_w417 ⟨n - 20850, hr⟩
                                    · by_cases h18 : n < 20950
                                      · have hr : n - 20900 < 50 := by omega
                                        have heq : n = (n - 20900) + 20900 := by omega
                                        rw [heq]
                                        exact pos_w418 ⟨n - 20900, hr⟩
                                      · by_cases h19 : n < 21000
                                        · have hr : n - 20950 < 50 := by omega
                                          have heq : n = (n - 20950) + 20950 := by omega
                                          rw [heq]
                                          exact pos_w419 ⟨n - 20950, hr⟩
                                        · by_cases h20 : n < 21050
                                          · have hr : n - 21000 < 50 := by omega
                                            have heq : n = (n - 21000) + 21000 := by omega
                                            rw [heq]
                                            exact pos_w420 ⟨n - 21000, hr⟩
                                          · by_cases h21 : n < 21100
                                            · have hr : n - 21050 < 50 := by omega
                                              have heq : n = (n - 21050) + 21050 := by omega
                                              rw [heq]
                                              exact pos_w421 ⟨n - 21050, hr⟩
                                            · by_cases h22 : n < 21150
                                              · have hr : n - 21100 < 50 := by omega
                                                have heq : n = (n - 21100) + 21100 := by omega
                                                rw [heq]
                                                exact pos_w422 ⟨n - 21100, hr⟩
                                              · by_cases h23 : n < 21200
                                                · have hr : n - 21150 < 50 := by omega
                                                  have heq : n = (n - 21150) + 21150 := by omega
                                                  rw [heq]
                                                  exact pos_w423 ⟨n - 21150, hr⟩
                                                · by_cases h24 : n < 21250
                                                  · have hr : n - 21200 < 50 := by omega
                                                    have heq : n = (n - 21200) + 21200 := by omega
                                                    rw [heq]
                                                    exact pos_w424 ⟨n - 21200, hr⟩
                                                  · by_cases h25 : n < 21300
                                                    · have hr : n - 21250 < 50 := by omega
                                                      have heq : n = (n - 21250) + 21250 := by omega
                                                      rw [heq]
                                                      exact pos_w425 ⟨n - 21250, hr⟩
                                                    · by_cases h26 : n < 21350
                                                      · have hr : n - 21300 < 50 := by omega
                                                        have heq : n = (n - 21300) + 21300 := by omega
                                                        rw [heq]
                                                        exact pos_w426 ⟨n - 21300, hr⟩
                                                      · by_cases h27 : n < 21400
                                                        · have hr : n - 21350 < 50 := by omega
                                                          have heq : n = (n - 21350) + 21350 := by omega
                                                          rw [heq]
                                                          exact pos_w427 ⟨n - 21350, hr⟩
                                                        · by_cases h28 : n < 21450
                                                          · have hr : n - 21400 < 50 := by omega
                                                            have heq : n = (n - 21400) + 21400 := by omega
                                                            rw [heq]
                                                            exact pos_w428 ⟨n - 21400, hr⟩
                                                          · by_cases h29 : n < 21500
                                                            · have hr : n - 21450 < 50 := by omega
                                                              have heq : n = (n - 21450) + 21450 := by omega
                                                              rw [heq]
                                                              exact pos_w429 ⟨n - 21450, hr⟩
                                                            · by_cases h30 : n < 21550
                                                              · have hr : n - 21500 < 50 := by omega
                                                                have heq : n = (n - 21500) + 21500 := by omega
                                                                rw [heq]
                                                                exact pos_w430 ⟨n - 21500, hr⟩
                                                              · by_cases h31 : n < 21600
                                                                · have hr : n - 21550 < 50 := by omega
                                                                  have heq : n = (n - 21550) + 21550 := by omega
                                                                  rw [heq]
                                                                  exact pos_w431 ⟨n - 21550, hr⟩
                                                                · by_cases h32 : n < 21650
                                                                  · have hr : n - 21600 < 50 := by omega
                                                                    have heq : n = (n - 21600) + 21600 := by omega
                                                                    rw [heq]
                                                                    exact pos_w432 ⟨n - 21600, hr⟩
                                                                  · by_cases h33 : n < 21700
                                                                    · have hr : n - 21650 < 50 := by omega
                                                                      have heq : n = (n - 21650) + 21650 := by omega
                                                                      rw [heq]
                                                                      exact pos_w433 ⟨n - 21650, hr⟩
                                                                    · by_cases h34 : n < 21750
                                                                      · have hr : n - 21700 < 50 := by omega
                                                                        have heq : n = (n - 21700) + 21700 := by omega
                                                                        rw [heq]
                                                                        exact pos_w434 ⟨n - 21700, hr⟩
                                                                      · by_cases h35 : n < 21800
                                                                        · have hr : n - 21750 < 50 := by omega
                                                                          have heq : n = (n - 21750) + 21750 := by omega
                                                                          rw [heq]
                                                                          exact pos_w435 ⟨n - 21750, hr⟩
                                                                        · by_cases h36 : n < 21850
                                                                          · have hr : n - 21800 < 50 := by omega
                                                                            have heq : n = (n - 21800) + 21800 := by omega
                                                                            rw [heq]
                                                                            exact pos_w436 ⟨n - 21800, hr⟩
                                                                          · by_cases h37 : n < 21900
                                                                            · have hr : n - 21850 < 50 := by omega
                                                                              have heq : n = (n - 21850) + 21850 := by omega
                                                                              rw [heq]
                                                                              exact pos_w437 ⟨n - 21850, hr⟩
                                                                            · by_cases h38 : n < 21950
                                                                              · have hr : n - 21900 < 50 := by omega
                                                                                have heq : n = (n - 21900) + 21900 := by omega
                                                                                rw [heq]
                                                                                exact pos_w438 ⟨n - 21900, hr⟩
                                                                              · by_cases h39 : n < 22000
                                                                                · have hr : n - 21950 < 50 := by omega
                                                                                  have heq : n = (n - 21950) + 21950 := by omega
                                                                                  rw [heq]
                                                                                  exact pos_w439 ⟨n - 21950, hr⟩
                                                                                · by_cases h40 : n < 22050
                                                                                  · have hr : n - 22000 < 50 := by omega
                                                                                    have heq : n = (n - 22000) + 22000 := by omega
                                                                                    rw [heq]
                                                                                    exact pos_w440 ⟨n - 22000, hr⟩
                                                                                  · by_cases h41 : n < 22100
                                                                                    · have hr : n - 22050 < 50 := by omega
                                                                                      have heq : n = (n - 22050) + 22050 := by omega
                                                                                      rw [heq]
                                                                                      exact pos_w441 ⟨n - 22050, hr⟩
                                                                                    · by_cases h42 : n < 22150
                                                                                      · have hr : n - 22100 < 50 := by omega
                                                                                        have heq : n = (n - 22100) + 22100 := by omega
                                                                                        rw [heq]
                                                                                        exact pos_w442 ⟨n - 22100, hr⟩
                                                                                      · by_cases h43 : n < 22200
                                                                                        · have hr : n - 22150 < 50 := by omega
                                                                                          have heq : n = (n - 22150) + 22150 := by omega
                                                                                          rw [heq]
                                                                                          exact pos_w443 ⟨n - 22150, hr⟩
                                                                                        · by_cases h44 : n < 22250
                                                                                          · have hr : n - 22200 < 50 := by omega
                                                                                            have heq : n = (n - 22200) + 22200 := by omega
                                                                                            rw [heq]
                                                                                            exact pos_w444 ⟨n - 22200, hr⟩
                                                                                          · by_cases h45 : n < 22300
                                                                                            · have hr : n - 22250 < 50 := by omega
                                                                                              have heq : n = (n - 22250) + 22250 := by omega
                                                                                              rw [heq]
                                                                                              exact pos_w445 ⟨n - 22250, hr⟩
                                                                                            · by_cases h46 : n < 22350
                                                                                              · have hr : n - 22300 < 50 := by omega
                                                                                                have heq : n = (n - 22300) + 22300 := by omega
                                                                                                rw [heq]
                                                                                                exact pos_w446 ⟨n - 22300, hr⟩
                                                                                              · by_cases h47 : n < 22400
                                                                                                · have hr : n - 22350 < 50 := by omega
                                                                                                  have heq : n = (n - 22350) + 22350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact pos_w447 ⟨n - 22350, hr⟩
                                                                                                · by_cases h48 : n < 22450
                                                                                                  · have hr : n - 22400 < 50 := by omega
                                                                                                    have heq : n = (n - 22400) + 22400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact pos_w448 ⟨n - 22400, hr⟩
                                                                                                  · by_cases h49 : n < 22500
                                                                                                    · have hr : n - 22450 < 50 := by omega
                                                                                                      have heq : n = (n - 22450) + 22450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact pos_w449 ⟨n - 22450, hr⟩
                                                                                                    · by_cases h50 : n < 22550
                                                                                                      · have hr : n - 22500 < 50 := by omega
                                                                                                        have heq : n = (n - 22500) + 22500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact pos_w450 ⟨n - 22500, hr⟩
                                                                                                      · by_cases h51 : n < 22600
                                                                                                        · have hr : n - 22550 < 50 := by omega
                                                                                                          have heq : n = (n - 22550) + 22550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact pos_w451 ⟨n - 22550, hr⟩
                                                                                                        · by_cases h52 : n < 22650
                                                                                                          · have hr : n - 22600 < 50 := by omega
                                                                                                            have heq : n = (n - 22600) + 22600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact pos_w452 ⟨n - 22600, hr⟩
                                                                                                          · by_cases h53 : n < 22700
                                                                                                            · have hr : n - 22650 < 50 := by omega
                                                                                                              have heq : n = (n - 22650) + 22650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact pos_w453 ⟨n - 22650, hr⟩
                                                                                                            · by_cases h54 : n < 22750
                                                                                                              · have hr : n - 22700 < 50 := by omega
                                                                                                                have heq : n = (n - 22700) + 22700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact pos_w454 ⟨n - 22700, hr⟩
                                                                                                              · by_cases h55 : n < 22800
                                                                                                                · have hr : n - 22750 < 50 := by omega
                                                                                                                  have heq : n = (n - 22750) + 22750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact pos_w455 ⟨n - 22750, hr⟩
                                                                                                                · by_cases h56 : n < 22850
                                                                                                                  · have hr : n - 22800 < 50 := by omega
                                                                                                                    have heq : n = (n - 22800) + 22800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact pos_w456 ⟨n - 22800, hr⟩
                                                                                                                  · by_cases h57 : n < 22900
                                                                                                                    · have hr : n - 22850 < 50 := by omega
                                                                                                                      have heq : n = (n - 22850) + 22850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact pos_w457 ⟨n - 22850, hr⟩
                                                                                                                    · by_cases h58 : n < 22950
                                                                                                                      · have hr : n - 22900 < 50 := by omega
                                                                                                                        have heq : n = (n - 22900) + 22900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact pos_w458 ⟨n - 22900, hr⟩
                                                                                                                      · by_cases h59 : n < 23000
                                                                                                                        · have hr : n - 22950 < 50 := by omega
                                                                                                                          have heq : n = (n - 22950) + 22950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact pos_w459 ⟨n - 22950, hr⟩
                                                                                                                        · by_cases h60 : n < 23050
                                                                                                                          · have hr : n - 23000 < 50 := by omega
                                                                                                                            have heq : n = (n - 23000) + 23000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact pos_w460 ⟨n - 23000, hr⟩
                                                                                                                          · by_cases h61 : n < 23100
                                                                                                                            · have hr : n - 23050 < 50 := by omega
                                                                                                                              have heq : n = (n - 23050) + 23050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact pos_w461 ⟨n - 23050, hr⟩
                                                                                                                            · by_cases h62 : n < 23150
                                                                                                                              · have hr : n - 23100 < 50 := by omega
                                                                                                                                have heq : n = (n - 23100) + 23100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact pos_w462 ⟨n - 23100, hr⟩
                                                                                                                              · by_cases h63 : n < 23200
                                                                                                                                · have hr : n - 23150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 23150) + 23150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact pos_w463 ⟨n - 23150, hr⟩
                                                                                                                                · by_cases h64 : n < 23250
                                                                                                                                  · have hr : n - 23200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 23200) + 23200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact pos_w464 ⟨n - 23200, hr⟩
                                                                                                                                  · by_cases h65 : n < 23300
                                                                                                                                    · have hr : n - 23250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 23250) + 23250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact pos_w465 ⟨n - 23250, hr⟩
                                                                                                                                    · by_cases h66 : n < 23350
                                                                                                                                      · have hr : n - 23300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 23300) + 23300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact pos_w466 ⟨n - 23300, hr⟩
                                                                                                                                      · by_cases h67 : n < 23400
                                                                                                                                        · have hr : n - 23350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 23350) + 23350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact pos_w467 ⟨n - 23350, hr⟩
                                                                                                                                        · by_cases h68 : n < 23450
                                                                                                                                          · have hr : n - 23400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 23400) + 23400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact pos_w468 ⟨n - 23400, hr⟩
                                                                                                                                          · by_cases h69 : n < 23500
                                                                                                                                            · have hr : n - 23450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 23450) + 23450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact pos_w469 ⟨n - 23450, hr⟩
                                                                                                                                            · by_cases h70 : n < 23550
                                                                                                                                              · have hr : n - 23500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 23500) + 23500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact pos_w470 ⟨n - 23500, hr⟩
                                                                                                                                              · by_cases h71 : n < 23600
                                                                                                                                                · have hr : n - 23550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 23550) + 23550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact pos_w471 ⟨n - 23550, hr⟩
                                                                                                                                                · by_cases h72 : n < 23650
                                                                                                                                                  · have hr : n - 23600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 23600) + 23600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact pos_w472 ⟨n - 23600, hr⟩
                                                                                                                                                  · by_cases h73 : n < 23700
                                                                                                                                                    · have hr : n - 23650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 23650) + 23650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact pos_w473 ⟨n - 23650, hr⟩
                                                                                                                                                    · by_cases h74 : n < 23750
                                                                                                                                                      · have hr : n - 23700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 23700) + 23700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact pos_w474 ⟨n - 23700, hr⟩
                                                                                                                                                      · by_cases h75 : n < 23800
                                                                                                                                                        · have hr : n - 23750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 23750) + 23750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact pos_w475 ⟨n - 23750, hr⟩
                                                                                                                                                        · by_cases h76 : n < 23850
                                                                                                                                                          · have hr : n - 23800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 23800) + 23800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact pos_w476 ⟨n - 23800, hr⟩
                                                                                                                                                          · by_cases h77 : n < 23900
                                                                                                                                                            · have hr : n - 23850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 23850) + 23850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact pos_w477 ⟨n - 23850, hr⟩
                                                                                                                                                            · by_cases h78 : n < 23950
                                                                                                                                                              · have hr : n - 23900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 23900) + 23900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact pos_w478 ⟨n - 23900, hr⟩
                                                                                                                                                              · by_cases h79 : n < 24000
                                                                                                                                                                · have hr : n - 23950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 23950) + 23950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact pos_w479 ⟨n - 23950, hr⟩
                                                                                                                                                                · by_cases h80 : n < 24050
                                                                                                                                                                  · have hr : n - 24000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 24000) + 24000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact pos_w480 ⟨n - 24000, hr⟩
                                                                                                                                                                  · by_cases h81 : n < 24100
                                                                                                                                                                    · have hr : n - 24050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 24050) + 24050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact pos_w481 ⟨n - 24050, hr⟩
                                                                                                                                                                    · by_cases h82 : n < 24150
                                                                                                                                                                      · have hr : n - 24100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 24100) + 24100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact pos_w482 ⟨n - 24100, hr⟩
                                                                                                                                                                      · by_cases h83 : n < 24200
                                                                                                                                                                        · have hr : n - 24150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 24150) + 24150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact pos_w483 ⟨n - 24150, hr⟩
                                                                                                                                                                        · by_cases h84 : n < 24250
                                                                                                                                                                          · have hr : n - 24200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 24200) + 24200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact pos_w484 ⟨n - 24200, hr⟩
                                                                                                                                                                          · by_cases h85 : n < 24300
                                                                                                                                                                            · have hr : n - 24250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 24250) + 24250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact pos_w485 ⟨n - 24250, hr⟩
                                                                                                                                                                            · by_cases h86 : n < 24350
                                                                                                                                                                              · have hr : n - 24300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 24300) + 24300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact pos_w486 ⟨n - 24300, hr⟩
                                                                                                                                                                              · by_cases h87 : n < 24400
                                                                                                                                                                                · have hr : n - 24350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 24350) + 24350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact pos_w487 ⟨n - 24350, hr⟩
                                                                                                                                                                                · by_cases h88 : n < 24450
                                                                                                                                                                                  · have hr : n - 24400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 24400) + 24400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact pos_w488 ⟨n - 24400, hr⟩
                                                                                                                                                                                  · by_cases h89 : n < 24500
                                                                                                                                                                                    · have hr : n - 24450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 24450) + 24450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact pos_w489 ⟨n - 24450, hr⟩
                                                                                                                                                                                    · by_cases h90 : n < 24550
                                                                                                                                                                                      · have hr : n - 24500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 24500) + 24500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact pos_w490 ⟨n - 24500, hr⟩
                                                                                                                                                                                      · by_cases h91 : n < 24600
                                                                                                                                                                                        · have hr : n - 24550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 24550) + 24550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact pos_w491 ⟨n - 24550, hr⟩
                                                                                                                                                                                        · by_cases h92 : n < 24650
                                                                                                                                                                                          · have hr : n - 24600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 24600) + 24600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact pos_w492 ⟨n - 24600, hr⟩
                                                                                                                                                                                          · by_cases h93 : n < 24700
                                                                                                                                                                                            · have hr : n - 24650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 24650) + 24650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact pos_w493 ⟨n - 24650, hr⟩
                                                                                                                                                                                            · by_cases h94 : n < 24750
                                                                                                                                                                                              · have hr : n - 24700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 24700) + 24700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact pos_w494 ⟨n - 24700, hr⟩
                                                                                                                                                                                              · by_cases h95 : n < 24800
                                                                                                                                                                                                · have hr : n - 24750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 24750) + 24750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact pos_w495 ⟨n - 24750, hr⟩
                                                                                                                                                                                                · by_cases h96 : n < 24850
                                                                                                                                                                                                  · have hr : n - 24800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 24800) + 24800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact pos_w496 ⟨n - 24800, hr⟩
                                                                                                                                                                                                  · by_cases h97 : n < 24900
                                                                                                                                                                                                    · have hr : n - 24850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 24850) + 24850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact pos_w497 ⟨n - 24850, hr⟩
                                                                                                                                                                                                    · by_cases h98 : n < 24950
                                                                                                                                                                                                      · have hr : n - 24900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 24900) + 24900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact pos_w498 ⟨n - 24900, hr⟩
                                                                                                                                                                                                      · by_cases h99 : n < 25000
                                                                                                                                                                                                        · have hr : n - 24950 < 50 := by omega
                                                                                                                                                                                                          have heq : n = (n - 24950) + 24950 := by omega
                                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                                          exact pos_w499 ⟨n - 24950, hr⟩
                                                                                                                                                                                                        · omega

end IntMul.Kappa.R8.Bit.Oppbank.DimBound4


