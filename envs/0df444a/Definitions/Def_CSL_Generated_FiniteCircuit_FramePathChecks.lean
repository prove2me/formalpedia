-- Prove2me | Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks
-- name    : CSL_Generated_FiniteCircuit_FramePathChecks
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T18:44:01.284554+00:00
-- url     : https://prove2.me/theorems/78aa80a8-681b-4354-8642-233617224ffa
-- title:
--   Coded sorting library: Generated / FiniteCircuit / FramePathChecks
-- statement:
--   Module `CodedSorting.Generated.FiniteCircuit.FramePathChecks` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Generated physical-frame checks. Uncompiled until a build record exists.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.FiniteCircuit.FramePathChecks

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Paths_Batch00
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Paths_Batch01
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Paths_Batch02
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Paths_Batch03
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Paths_Batch04
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Paths_Batch05

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem allForwardPathValid (f : Nat) (hf : f < 661) : forwardPathValid f = true := by
  by_cases h328 : f < 328
  ·
    by_cases h160 : f < 160
    ·
      by_cases h80 : f < 80
      ·
        by_cases h40 : f < 40
        ·
          by_cases h16 : f < 16
          ·
            by_cases h8 : f < 8
            ·
              exact forwardPathBlock000 f (by omega) (by omega)
            ·
              exact forwardPathBlock001 f (by omega) (by omega)
          ·
            by_cases h24 : f < 24
            ·
              exact forwardPathBlock002 f (by omega) (by omega)
            ·
              by_cases h32 : f < 32
              ·
                exact forwardPathBlock003 f (by omega) (by omega)
              ·
                exact forwardPathBlock004 f (by omega) (by omega)
        ·
          by_cases h56 : f < 56
          ·
            by_cases h48 : f < 48
            ·
              exact forwardPathBlock005 f (by omega) (by omega)
            ·
              exact forwardPathBlock006 f (by omega) (by omega)
          ·
            by_cases h64 : f < 64
            ·
              exact forwardPathBlock007 f (by omega) (by omega)
            ·
              by_cases h72 : f < 72
              ·
                exact forwardPathBlock008 f (by omega) (by omega)
              ·
                exact forwardPathBlock009 f (by omega) (by omega)
      ·
        by_cases h120 : f < 120
        ·
          by_cases h96 : f < 96
          ·
            by_cases h88 : f < 88
            ·
              exact forwardPathBlock010 f (by omega) (by omega)
            ·
              exact forwardPathBlock011 f (by omega) (by omega)
          ·
            by_cases h104 : f < 104
            ·
              exact forwardPathBlock012 f (by omega) (by omega)
            ·
              by_cases h112 : f < 112
              ·
                exact forwardPathBlock013 f (by omega) (by omega)
              ·
                exact forwardPathBlock014 f (by omega) (by omega)
        ·
          by_cases h136 : f < 136
          ·
            by_cases h128 : f < 128
            ·
              exact forwardPathBlock015 f (by omega) (by omega)
            ·
              exact forwardPathBlock016 f (by omega) (by omega)
          ·
            by_cases h144 : f < 144
            ·
              exact forwardPathBlock017 f (by omega) (by omega)
            ·
              by_cases h152 : f < 152
              ·
                exact forwardPathBlock018 f (by omega) (by omega)
              ·
                exact forwardPathBlock019 f (by omega) (by omega)
    ·
      by_cases h240 : f < 240
      ·
        by_cases h200 : f < 200
        ·
          by_cases h176 : f < 176
          ·
            by_cases h168 : f < 168
            ·
              exact forwardPathBlock020 f (by omega) (by omega)
            ·
              exact forwardPathBlock021 f (by omega) (by omega)
          ·
            by_cases h184 : f < 184
            ·
              exact forwardPathBlock022 f (by omega) (by omega)
            ·
              by_cases h192 : f < 192
              ·
                exact forwardPathBlock023 f (by omega) (by omega)
              ·
                exact forwardPathBlock024 f (by omega) (by omega)
        ·
          by_cases h216 : f < 216
          ·
            by_cases h208 : f < 208
            ·
              exact forwardPathBlock025 f (by omega) (by omega)
            ·
              exact forwardPathBlock026 f (by omega) (by omega)
          ·
            by_cases h224 : f < 224
            ·
              exact forwardPathBlock027 f (by omega) (by omega)
            ·
              by_cases h232 : f < 232
              ·
                exact forwardPathBlock028 f (by omega) (by omega)
              ·
                exact forwardPathBlock029 f (by omega) (by omega)
      ·
        by_cases h280 : f < 280
        ·
          by_cases h256 : f < 256
          ·
            by_cases h248 : f < 248
            ·
              exact forwardPathBlock030 f (by omega) (by omega)
            ·
              exact forwardPathBlock031 f (by omega) (by omega)
          ·
            by_cases h264 : f < 264
            ·
              exact forwardPathBlock032 f (by omega) (by omega)
            ·
              by_cases h272 : f < 272
              ·
                exact forwardPathBlock033 f (by omega) (by omega)
              ·
                exact forwardPathBlock034 f (by omega) (by omega)
        ·
          by_cases h304 : f < 304
          ·
            by_cases h288 : f < 288
            ·
              exact forwardPathBlock035 f (by omega) (by omega)
            ·
              by_cases h296 : f < 296
              ·
                exact forwardPathBlock036 f (by omega) (by omega)
              ·
                exact forwardPathBlock037 f (by omega) (by omega)
          ·
            by_cases h312 : f < 312
            ·
              exact forwardPathBlock038 f (by omega) (by omega)
            ·
              by_cases h320 : f < 320
              ·
                exact forwardPathBlock039 f (by omega) (by omega)
              ·
                exact forwardPathBlock040 f (by omega) (by omega)
  ·
    by_cases h496 : f < 496
    ·
      by_cases h408 : f < 408
      ·
        by_cases h368 : f < 368
        ·
          by_cases h344 : f < 344
          ·
            by_cases h336 : f < 336
            ·
              exact forwardPathBlock041 f (by omega) (by omega)
            ·
              exact forwardPathBlock042 f (by omega) (by omega)
          ·
            by_cases h352 : f < 352
            ·
              exact forwardPathBlock043 f (by omega) (by omega)
            ·
              by_cases h360 : f < 360
              ·
                exact forwardPathBlock044 f (by omega) (by omega)
              ·
                exact forwardPathBlock045 f (by omega) (by omega)
        ·
          by_cases h384 : f < 384
          ·
            by_cases h376 : f < 376
            ·
              exact forwardPathBlock046 f (by omega) (by omega)
            ·
              exact forwardPathBlock047 f (by omega) (by omega)
          ·
            by_cases h392 : f < 392
            ·
              exact forwardPathBlock048 f (by omega) (by omega)
            ·
              by_cases h400 : f < 400
              ·
                exact forwardPathBlock049 f (by omega) (by omega)
              ·
                exact forwardPathBlock050 f (by omega) (by omega)
      ·
        by_cases h448 : f < 448
        ·
          by_cases h424 : f < 424
          ·
            by_cases h416 : f < 416
            ·
              exact forwardPathBlock051 f (by omega) (by omega)
            ·
              exact forwardPathBlock052 f (by omega) (by omega)
          ·
            by_cases h432 : f < 432
            ·
              exact forwardPathBlock053 f (by omega) (by omega)
            ·
              by_cases h440 : f < 440
              ·
                exact forwardPathBlock054 f (by omega) (by omega)
              ·
                exact forwardPathBlock055 f (by omega) (by omega)
        ·
          by_cases h472 : f < 472
          ·
            by_cases h456 : f < 456
            ·
              exact forwardPathBlock056 f (by omega) (by omega)
            ·
              by_cases h464 : f < 464
              ·
                exact forwardPathBlock057 f (by omega) (by omega)
              ·
                exact forwardPathBlock058 f (by omega) (by omega)
          ·
            by_cases h480 : f < 480
            ·
              exact forwardPathBlock059 f (by omega) (by omega)
            ·
              by_cases h488 : f < 488
              ·
                exact forwardPathBlock060 f (by omega) (by omega)
              ·
                exact forwardPathBlock061 f (by omega) (by omega)
    ·
      by_cases h576 : f < 576
      ·
        by_cases h536 : f < 536
        ·
          by_cases h512 : f < 512
          ·
            by_cases h504 : f < 504
            ·
              exact forwardPathBlock062 f (by omega) (by omega)
            ·
              exact forwardPathBlock063 f (by omega) (by omega)
          ·
            by_cases h520 : f < 520
            ·
              exact forwardPathBlock064 f (by omega) (by omega)
            ·
              by_cases h528 : f < 528
              ·
                exact forwardPathBlock065 f (by omega) (by omega)
              ·
                exact forwardPathBlock066 f (by omega) (by omega)
        ·
          by_cases h552 : f < 552
          ·
            by_cases h544 : f < 544
            ·
              exact forwardPathBlock067 f (by omega) (by omega)
            ·
              exact forwardPathBlock068 f (by omega) (by omega)
          ·
            by_cases h560 : f < 560
            ·
              exact forwardPathBlock069 f (by omega) (by omega)
            ·
              by_cases h568 : f < 568
              ·
                exact forwardPathBlock070 f (by omega) (by omega)
              ·
                exact forwardPathBlock071 f (by omega) (by omega)
      ·
        by_cases h616 : f < 616
        ·
          by_cases h592 : f < 592
          ·
            by_cases h584 : f < 584
            ·
              exact forwardPathBlock072 f (by omega) (by omega)
            ·
              exact forwardPathBlock073 f (by omega) (by omega)
          ·
            by_cases h600 : f < 600
            ·
              exact forwardPathBlock074 f (by omega) (by omega)
            ·
              by_cases h608 : f < 608
              ·
                exact forwardPathBlock075 f (by omega) (by omega)
              ·
                exact forwardPathBlock076 f (by omega) (by omega)
        ·
          by_cases h640 : f < 640
          ·
            by_cases h624 : f < 624
            ·
              exact forwardPathBlock077 f (by omega) (by omega)
            ·
              by_cases h632 : f < 632
              ·
                exact forwardPathBlock078 f (by omega) (by omega)
              ·
                exact forwardPathBlock079 f (by omega) (by omega)
          ·
            by_cases h648 : f < 648
            ·
              exact forwardPathBlock080 f (by omega) (by omega)
            ·
              by_cases h656 : f < 656
              ·
                exact forwardPathBlock081 f (by omega) (by omega)
              ·
                exact forwardPathBlock082 f (by omega) (by omega)

#print axioms allForwardPathValid
end CSL.Construction.PhysicalFramePaths


