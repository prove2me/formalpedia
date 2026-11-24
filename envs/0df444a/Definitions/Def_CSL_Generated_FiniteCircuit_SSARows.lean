-- Prove2me | Definitions.Def_CSL_Generated_FiniteCircuit_SSARows
-- name    : CSL_Generated_FiniteCircuit_SSARows
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:35:23.075308+00:00
-- url     : https://prove2.me/theorems/3cec3558-9125-44bb-b170-fac49a95b893
-- title:
--   Coded sorting library: Generated / FiniteCircuit / SSARows
-- statement:
--   Module `CodedSorting.Generated.FiniteCircuit.SSARows` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.FiniteCircuit.SSARows

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Generated_FiniteCircuit_SSARows_Part0
import Definitions.Def_CSL_Generated_FiniteCircuit_SSARows_Part1
import Definitions.Def_CSL_Generated_FiniteCircuit_SSARows_Part2
import Definitions.Def_CSL_Generated_FiniteCircuit_SSARows_Part3

namespace CSL.Construction.FiniteSSA

noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0



































































































def rows (i : Nat) : Nat :=
  if i < 6245 then (if i < 3136 then (if i < 1536 then (if i < 768 then (if i < 384 then (if i < 192 then (if i < 64 then rowsBlock0 i else (if i < 128 then rowsBlock1 i else rowsBlock2 i)) else (if i < 256 then rowsBlock3 i else (if i < 320 then rowsBlock4 i else rowsBlock5 i))) else (if i < 576 then (if i < 448 then rowsBlock6 i else (if i < 512 then rowsBlock7 i else rowsBlock8 i)) else (if i < 640 then rowsBlock9 i else (if i < 704 then rowsBlock10 i else rowsBlock11 i)))) else (if i < 1152 then (if i < 960 then (if i < 832 then rowsBlock12 i else (if i < 896 then rowsBlock13 i else rowsBlock14 i)) else (if i < 1024 then rowsBlock15 i else (if i < 1088 then rowsBlock16 i else rowsBlock17 i))) else (if i < 1344 then (if i < 1216 then rowsBlock18 i else (if i < 1280 then rowsBlock19 i else rowsBlock20 i)) else (if i < 1408 then rowsBlock21 i else (if i < 1472 then rowsBlock22 i else rowsBlock23 i))))) else (if i < 2304 then (if i < 1920 then (if i < 1728 then (if i < 1600 then rowsBlock24 i else (if i < 1664 then rowsBlock25 i else rowsBlock26 i)) else (if i < 1792 then rowsBlock27 i else (if i < 1856 then rowsBlock28 i else rowsBlock29 i))) else (if i < 2112 then (if i < 1984 then rowsBlock30 i else (if i < 2048 then rowsBlock31 i else rowsBlock32 i)) else (if i < 2176 then rowsBlock33 i else (if i < 2240 then rowsBlock34 i else rowsBlock35 i)))) else (if i < 2688 then (if i < 2496 then (if i < 2368 then rowsBlock36 i else (if i < 2432 then rowsBlock37 i else rowsBlock38 i)) else (if i < 2560 then rowsBlock39 i else (if i < 2624 then rowsBlock40 i else rowsBlock41 i))) else (if i < 2880 then (if i < 2752 then rowsBlock42 i else (if i < 2816 then rowsBlock43 i else rowsBlock44 i)) else (if i < 3008 then (if i < 2944 then rowsBlock45 i else rowsBlock46 i) else (if i < 3072 then rowsBlock47 i else rowsBlock48 i)))))) else (if i < 4672 then (if i < 3904 then (if i < 3520 then (if i < 3328 then (if i < 3200 then rowsBlock49 i else (if i < 3264 then rowsBlock50 i else rowsBlock51 i)) else (if i < 3392 then rowsBlock52 i else (if i < 3456 then rowsBlock53 i else rowsBlock54 i))) else (if i < 3712 then (if i < 3584 then rowsBlock55 i else (if i < 3648 then rowsBlock56 i else rowsBlock57 i)) else (if i < 3776 then rowsBlock58 i else (if i < 3840 then rowsBlock59 i else rowsBlock60 i)))) else (if i < 4288 then (if i < 4096 then (if i < 3968 then rowsBlock61 i else (if i < 4032 then rowsBlock62 i else rowsBlock63 i)) else (if i < 4160 then rowsBlock64 i else (if i < 4224 then rowsBlock65 i else rowsBlock66 i))) else (if i < 4480 then (if i < 4352 then rowsBlock67 i else (if i < 4416 then rowsBlock68 i else rowsBlock69 i)) else (if i < 4544 then rowsBlock70 i else (if i < 4608 then rowsBlock71 i else rowsBlock72 i))))) else (if i < 5440 then (if i < 5056 then (if i < 4864 then (if i < 4736 then rowsBlock73 i else (if i < 4800 then rowsBlock74 i else rowsBlock75 i)) else (if i < 4928 then rowsBlock76 i else (if i < 4992 then rowsBlock77 i else rowsBlock78 i))) else (if i < 5248 then (if i < 5120 then rowsBlock79 i else (if i < 5184 then rowsBlock80 i else rowsBlock81 i)) else (if i < 5312 then rowsBlock82 i else (if i < 5376 then rowsBlock83 i else rowsBlock84 i)))) else (if i < 5824 then (if i < 5632 then (if i < 5504 then rowsBlock85 i else (if i < 5568 then rowsBlock86 i else rowsBlock87 i)) else (if i < 5696 then rowsBlock88 i else (if i < 5760 then rowsBlock89 i else rowsBlock90 i))) else (if i < 6016 then (if i < 5888 then rowsBlock91 i else (if i < 5952 then rowsBlock92 i else rowsBlock93 i)) else (if i < 6144 then (if i < 6080 then rowsBlock94 i else rowsBlock95 i) else (if i < 6208 then rowsBlock96 i else rowsBlock97 i))))))) else 0

theorem rows_zero : rows 0 = 0 := by decide +kernel

end
end CSL.Construction.FiniteSSA


