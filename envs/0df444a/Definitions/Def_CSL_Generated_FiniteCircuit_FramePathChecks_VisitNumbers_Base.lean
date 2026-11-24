-- Prove2me | Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_VisitNumbers_Base
-- name    : CSL_Generated_FiniteCircuit_FramePathChecks_VisitNumbers_Base
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:09:20.664217+00:00
-- url     : https://prove2.me/theorems/931b6290-ce5b-4b34-9c9f-aed2ddb8c542
-- title:
--   Coded sorting library: Generated / FiniteCircuit / FramePathChecks / VisitNumbers / Base
-- statement:
--   Module `CodedSorting.Generated.FiniteCircuit.FramePathChecks.VisitNumbers.Base` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Generated physical-frame checks. Uncompiled until a build record exists.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.FiniteCircuit.FramePathChecks.VisitNumbers.Base

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Generated_MemoryAccess_Events0000To0031
import Definitions.Def_CSL_Generated_MemoryAccess_Events0032To0063
import Definitions.Def_CSL_Generated_MemoryAccess_Events0064To0095
import Definitions.Def_CSL_Generated_MemoryAccess_Events0096To0127
import Definitions.Def_CSL_Generated_MemoryAccess_Group00
import Definitions.Def_CSL_Generated_MemoryAccess_Group01
import Definitions.Def_CSL_Generated_MemoryAccess_Group02
import Definitions.Def_CSL_Generated_MemoryAccess_Group03
import Definitions.Def_CSL_Generated_MemoryAccess_Group04
import Definitions.Def_CSL_Generated_MemoryAccess_Group05
import Definitions.Def_CSL_Generated_MemoryAccess_Group06
import Definitions.Def_CSL_Generated_MemoryAccess_Group07
import Definitions.Def_CSL_Generated_MemoryAccess_Group08
import Definitions.Def_CSL_Generated_MemoryAccess_Group09
import Definitions.Def_CSL_Generated_MemoryAccess_Group10

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def computedForwardVisits (r : Nat) : List Nat :=
  fastForwardChunkVisits000 r ++ (fastForwardChunkVisits001 r ++ (fastForwardChunkVisits002 r ++ (fastForwardChunkVisits003 r ++ (fastForwardChunkVisits004 r ++ (fastForwardChunkVisits005 r ++ (fastForwardChunkVisits006 r ++ (fastForwardChunkVisits007 r ++ (fastForwardChunkVisits008 r ++ (fastForwardChunkVisits009 r ++ (fastForwardChunkVisits010 r ++ (fastForwardChunkVisits011 r ++ (fastForwardChunkVisits012 r ++ (fastForwardChunkVisits013 r ++ (fastForwardChunkVisits014 r ++ (fastForwardChunkVisits015 r ++ (fastForwardChunkVisits016 r ++ (fastForwardChunkVisits017 r ++ (fastForwardChunkVisits018 r ++ (fastForwardChunkVisits019 r ++ (fastForwardChunkVisits020 r ++ (fastForwardChunkVisits021 r ++ (fastForwardChunkVisits022 r ++ (fastForwardChunkVisits023 r ++ (fastForwardChunkVisits024 r ++ (fastForwardChunkVisits025 r ++ (fastForwardChunkVisits026 r ++ (fastForwardChunkVisits027 r ++ (fastForwardChunkVisits028 r ++ (fastForwardChunkVisits029 r ++ (fastForwardChunkVisits030 r ++ (fastForwardChunkVisits031 r ++ (fastForwardChunkVisits032 r ++ (fastForwardChunkVisits033 r ++ (fastForwardChunkVisits034 r ++ (fastForwardChunkVisits035 r ++ (fastForwardChunkVisits036 r ++ (fastForwardChunkVisits037 r ++ (fastForwardChunkVisits038 r ++ (fastForwardChunkVisits039 r ++ (fastForwardChunkVisits040 r ++ (fastForwardChunkVisits041 r ++ (fastForwardChunkVisits042 r ++ (fastForwardChunkVisits043 r ++ (fastForwardChunkVisits044 r ++ (fastForwardChunkVisits045 r ++ (fastForwardChunkVisits046 r ++ (fastForwardChunkVisits047 r ++ (fastForwardChunkVisits048 r ++ (fastForwardChunkVisits049 r ++ (fastForwardChunkVisits050 r ++ (fastForwardChunkVisits051 r ++ (fastForwardChunkVisits052 r ++ (fastForwardChunkVisits053 r ++ (fastForwardChunkVisits054 r ++ (fastForwardChunkVisits055 r ++ (fastForwardChunkVisits056 r ++ (fastForwardChunkVisits057 r ++ (fastForwardChunkVisits058 r ++ (fastForwardChunkVisits059 r ++ (fastForwardChunkVisits060 r ++ (fastForwardChunkVisits061 r ++ (fastForwardChunkVisits062 r ++ (fastForwardChunkVisits063 r ++ (fastForwardChunkVisits064 r ++ (fastForwardChunkVisits065 r ++ (fastForwardChunkVisits066 r ++ (fastForwardChunkVisits067 r ++ (fastForwardChunkVisits068 r ++ (fastForwardChunkVisits069 r ++ (fastForwardChunkVisits070 r ++ (fastForwardChunkVisits071 r ++ (fastForwardChunkVisits072 r ++ (fastForwardChunkVisits073 r ++ (fastForwardChunkVisits074 r ++ (fastForwardChunkVisits075 r ++ (fastForwardChunkVisits076 r ++ (fastForwardChunkVisits077 r ++ (fastForwardChunkVisits078 r ++ (fastForwardChunkVisits079 r ++ (fastForwardChunkVisits080 r ++ (fastForwardChunkVisits081 r ++ (fastForwardChunkVisits082 r ++ (fastForwardChunkVisits083 r ++ (fastForwardChunkVisits084 r ++ (fastForwardChunkVisits085 r ++ (fastForwardChunkVisits086 r ++ (fastForwardChunkVisits087 r ++ (fastForwardChunkVisits088 r ++ (fastForwardChunkVisits089 r ++ (fastForwardChunkVisits090 r ++ (fastForwardChunkVisits091 r ++ (fastForwardChunkVisits092 r ++ (fastForwardChunkVisits093 r ++ (fastForwardChunkVisits094 r ++ (fastForwardChunkVisits095 r ++ (fastForwardChunkVisits096 r ++ (fastForwardChunkVisits097 r ++ (fastForwardChunkVisits098 r ++ (fastForwardChunkVisits099 r ++ (fastForwardChunkVisits100 r ++ (fastForwardChunkVisits101 r ++ (fastForwardChunkVisits102 r ++ (fastForwardChunkVisits103 r ++ (fastForwardChunkVisits104 r ++ (fastForwardChunkVisits105 r ++ (fastForwardChunkVisits106 r ++ (fastForwardChunkVisits107 r ++ (fastForwardChunkVisits108 r ++ (fastForwardChunkVisits109 r ++ (fastForwardChunkVisits110 r ++ (fastForwardChunkVisits111 r ++ (fastForwardChunkVisits112 r ++ (fastForwardChunkVisits113 r ++ (fastForwardChunkVisits114 r ++ (fastForwardChunkVisits115 r ++ (fastForwardChunkVisits116 r ++ (fastForwardChunkVisits117 r ++ (fastForwardChunkVisits118 r ++ (fastForwardChunkVisits119 r ++ (fastForwardChunkVisits120 r ++ (fastForwardChunkVisits121 r ++ (fastForwardChunkVisits122 r ++ (fastForwardChunkVisits123 r ++ (fastForwardChunkVisits124 r ++ (fastForwardChunkVisits125 r ++ (fastForwardChunkVisits126 r ++ (fastForwardChunkVisits127 r ++ (fastForwardChunkVisits128 r ++ (fastForwardChunkVisits129 r ++ (fastForwardChunkVisits130 r ++ (fastForwardChunkVisits131 r ++ (fastForwardChunkVisits132 r ++ (fastForwardChunkVisits133 r ++ (fastForwardChunkVisits134 r ++ (fastForwardChunkVisits135 r ++ (fastForwardChunkVisits136 r ++ (fastForwardChunkVisits137 r ++ (fastForwardChunkVisits138 r ++ (fastForwardChunkVisits139 r ++ (fastForwardChunkVisits140 r ++ (fastForwardChunkVisits141 r ++ (fastForwardChunkVisits142 r ++ (fastForwardChunkVisits143 r ++ (fastForwardChunkVisits144 r ++ (fastForwardChunkVisits145 r ++ (fastForwardChunkVisits146 r ++ (fastForwardChunkVisits147 r ++ (fastForwardChunkVisits148 r ++ (fastForwardChunkVisits149 r ++ (fastForwardChunkVisits150 r ++ (fastForwardChunkVisits151 r ++ (fastForwardChunkVisits152 r ++ (fastForwardChunkVisits153 r ++ (fastForwardChunkVisits154 r ++ (fastForwardChunkVisits155 r ++ (fastForwardChunkVisits156 r ++ (fastForwardChunkVisits157 r ++ (fastForwardChunkVisits158 r ++ (fastForwardChunkVisits159 r ++ (fastForwardChunkVisits160 r ++ (fastForwardChunkVisits161 r ++ (fastForwardChunkVisits162 r ++ (fastForwardChunkVisits163 r ++ (fastForwardChunkVisits164 r ++ (fastForwardChunkVisits165 r ++ (fastForwardChunkVisits166 r ++ (fastForwardChunkVisits167 r ++ (fastForwardChunkVisits168 r ++ (fastForwardChunkVisits169 r ++ (fastForwardChunkVisits170 r ++ (fastForwardChunkVisits171 r ++ (fastForwardChunkVisits172 r ++ (fastForwardChunkVisits173 r ++ (fastForwardChunkVisits174 r ++ (fastForwardChunkVisits175 r ++ (fastForwardChunkVisits176 r ++ (fastForwardChunkVisits177 r)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
end CSL.Construction.PhysicalFramePaths


