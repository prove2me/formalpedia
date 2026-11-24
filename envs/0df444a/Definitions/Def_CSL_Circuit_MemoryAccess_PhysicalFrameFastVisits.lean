-- Prove2me | Definitions.Def_CSL_Circuit_MemoryAccess_PhysicalFrameFastVisits
-- name    : CSL_Circuit_MemoryAccess_PhysicalFrameFastVisits
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:00:08.691369+00:00
-- url     : https://prove2.me/theorems/2e4ec98d-1b16-4514-a69a-036d263ce70c
-- title:
--   Coded sorting library: Circuit / MemoryAccess / PhysicalFrameFastVisits
-- statement:
--   Module `CodedSorting.Circuit.MemoryAccess.PhysicalFrameFastVisits` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.MemoryAccess.PhysicalFrameFastVisits

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_MemoryAccess_PhysicalFrameEventChunks
import Definitions.Def_CSL_Generated_MemoryAccess_Concat
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

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] eventVisits forwardEvents
  forwardEventChunk000 forwardEventChunk001 forwardEventChunk002 forwardEventChunk003 forwardEventChunk004 forwardEventChunk005 forwardEventChunk006 forwardEventChunk007 forwardEventChunk008 forwardEventChunk009 forwardEventChunk010 forwardEventChunk011 forwardEventChunk012 forwardEventChunk013 forwardEventChunk014 forwardEventChunk015 forwardEventChunk016 forwardEventChunk017 forwardEventChunk018 forwardEventChunk019 forwardEventChunk020 forwardEventChunk021 forwardEventChunk022 forwardEventChunk023 forwardEventChunk024 forwardEventChunk025 forwardEventChunk026 forwardEventChunk027 forwardEventChunk028 forwardEventChunk029 forwardEventChunk030 forwardEventChunk031 forwardEventChunk032 forwardEventChunk033 forwardEventChunk034 forwardEventChunk035 forwardEventChunk036 forwardEventChunk037 forwardEventChunk038 forwardEventChunk039 forwardEventChunk040 forwardEventChunk041 forwardEventChunk042 forwardEventChunk043 forwardEventChunk044 forwardEventChunk045 forwardEventChunk046 forwardEventChunk047 forwardEventChunk048 forwardEventChunk049 forwardEventChunk050 forwardEventChunk051 forwardEventChunk052 forwardEventChunk053 forwardEventChunk054 forwardEventChunk055 forwardEventChunk056 forwardEventChunk057 forwardEventChunk058 forwardEventChunk059 forwardEventChunk060 forwardEventChunk061 forwardEventChunk062 forwardEventChunk063 forwardEventChunk064 forwardEventChunk065 forwardEventChunk066 forwardEventChunk067 forwardEventChunk068 forwardEventChunk069 forwardEventChunk070 forwardEventChunk071 forwardEventChunk072 forwardEventChunk073 forwardEventChunk074 forwardEventChunk075 forwardEventChunk076 forwardEventChunk077 forwardEventChunk078 forwardEventChunk079 forwardEventChunk080 forwardEventChunk081 forwardEventChunk082 forwardEventChunk083 forwardEventChunk084 forwardEventChunk085 forwardEventChunk086 forwardEventChunk087 forwardEventChunk088 forwardEventChunk089 forwardEventChunk090 forwardEventChunk091 forwardEventChunk092 forwardEventChunk093 forwardEventChunk094 forwardEventChunk095 forwardEventChunk096 forwardEventChunk097 forwardEventChunk098 forwardEventChunk099 forwardEventChunk100 forwardEventChunk101 forwardEventChunk102 forwardEventChunk103 forwardEventChunk104 forwardEventChunk105 forwardEventChunk106 forwardEventChunk107 forwardEventChunk108 forwardEventChunk109 forwardEventChunk110 forwardEventChunk111 forwardEventChunk112 forwardEventChunk113 forwardEventChunk114 forwardEventChunk115 forwardEventChunk116 forwardEventChunk117 forwardEventChunk118 forwardEventChunk119 forwardEventChunk120 forwardEventChunk121 forwardEventChunk122 forwardEventChunk123 forwardEventChunk124 forwardEventChunk125 forwardEventChunk126 forwardEventChunk127 forwardEventChunk128 forwardEventChunk129 forwardEventChunk130 forwardEventChunk131 forwardEventChunk132 forwardEventChunk133 forwardEventChunk134 forwardEventChunk135 forwardEventChunk136 forwardEventChunk137 forwardEventChunk138 forwardEventChunk139 forwardEventChunk140 forwardEventChunk141 forwardEventChunk142 forwardEventChunk143 forwardEventChunk144 forwardEventChunk145 forwardEventChunk146 forwardEventChunk147 forwardEventChunk148 forwardEventChunk149 forwardEventChunk150 forwardEventChunk151 forwardEventChunk152 forwardEventChunk153 forwardEventChunk154 forwardEventChunk155 forwardEventChunk156 forwardEventChunk157 forwardEventChunk158 forwardEventChunk159 forwardEventChunk160 forwardEventChunk161 forwardEventChunk162 forwardEventChunk163 forwardEventChunk164 forwardEventChunk165 forwardEventChunk166 forwardEventChunk167 forwardEventChunk168 forwardEventChunk169 forwardEventChunk170 forwardEventChunk171 forwardEventChunk172 forwardEventChunk173 forwardEventChunk174 forwardEventChunk175 forwardEventChunk176 forwardEventChunk177
  fastForwardChunkVisits000 fastForwardChunkVisits001 fastForwardChunkVisits002 fastForwardChunkVisits003 fastForwardChunkVisits004 fastForwardChunkVisits005 fastForwardChunkVisits006 fastForwardChunkVisits007 fastForwardChunkVisits008 fastForwardChunkVisits009 fastForwardChunkVisits010 fastForwardChunkVisits011 fastForwardChunkVisits012 fastForwardChunkVisits013 fastForwardChunkVisits014 fastForwardChunkVisits015 fastForwardChunkVisits016 fastForwardChunkVisits017 fastForwardChunkVisits018 fastForwardChunkVisits019 fastForwardChunkVisits020 fastForwardChunkVisits021 fastForwardChunkVisits022 fastForwardChunkVisits023 fastForwardChunkVisits024 fastForwardChunkVisits025 fastForwardChunkVisits026 fastForwardChunkVisits027 fastForwardChunkVisits028 fastForwardChunkVisits029 fastForwardChunkVisits030 fastForwardChunkVisits031 fastForwardChunkVisits032 fastForwardChunkVisits033 fastForwardChunkVisits034 fastForwardChunkVisits035 fastForwardChunkVisits036 fastForwardChunkVisits037 fastForwardChunkVisits038 fastForwardChunkVisits039 fastForwardChunkVisits040 fastForwardChunkVisits041 fastForwardChunkVisits042 fastForwardChunkVisits043 fastForwardChunkVisits044 fastForwardChunkVisits045 fastForwardChunkVisits046 fastForwardChunkVisits047 fastForwardChunkVisits048 fastForwardChunkVisits049 fastForwardChunkVisits050 fastForwardChunkVisits051 fastForwardChunkVisits052 fastForwardChunkVisits053 fastForwardChunkVisits054 fastForwardChunkVisits055 fastForwardChunkVisits056 fastForwardChunkVisits057 fastForwardChunkVisits058 fastForwardChunkVisits059 fastForwardChunkVisits060 fastForwardChunkVisits061 fastForwardChunkVisits062 fastForwardChunkVisits063 fastForwardChunkVisits064 fastForwardChunkVisits065 fastForwardChunkVisits066 fastForwardChunkVisits067 fastForwardChunkVisits068 fastForwardChunkVisits069 fastForwardChunkVisits070 fastForwardChunkVisits071 fastForwardChunkVisits072 fastForwardChunkVisits073 fastForwardChunkVisits074 fastForwardChunkVisits075 fastForwardChunkVisits076 fastForwardChunkVisits077 fastForwardChunkVisits078 fastForwardChunkVisits079 fastForwardChunkVisits080 fastForwardChunkVisits081 fastForwardChunkVisits082 fastForwardChunkVisits083 fastForwardChunkVisits084 fastForwardChunkVisits085 fastForwardChunkVisits086 fastForwardChunkVisits087 fastForwardChunkVisits088 fastForwardChunkVisits089 fastForwardChunkVisits090 fastForwardChunkVisits091 fastForwardChunkVisits092 fastForwardChunkVisits093 fastForwardChunkVisits094 fastForwardChunkVisits095 fastForwardChunkVisits096 fastForwardChunkVisits097 fastForwardChunkVisits098 fastForwardChunkVisits099 fastForwardChunkVisits100 fastForwardChunkVisits101 fastForwardChunkVisits102 fastForwardChunkVisits103 fastForwardChunkVisits104 fastForwardChunkVisits105 fastForwardChunkVisits106 fastForwardChunkVisits107 fastForwardChunkVisits108 fastForwardChunkVisits109 fastForwardChunkVisits110 fastForwardChunkVisits111 fastForwardChunkVisits112 fastForwardChunkVisits113 fastForwardChunkVisits114 fastForwardChunkVisits115 fastForwardChunkVisits116 fastForwardChunkVisits117 fastForwardChunkVisits118 fastForwardChunkVisits119 fastForwardChunkVisits120 fastForwardChunkVisits121 fastForwardChunkVisits122 fastForwardChunkVisits123 fastForwardChunkVisits124 fastForwardChunkVisits125 fastForwardChunkVisits126 fastForwardChunkVisits127 fastForwardChunkVisits128 fastForwardChunkVisits129 fastForwardChunkVisits130 fastForwardChunkVisits131 fastForwardChunkVisits132 fastForwardChunkVisits133 fastForwardChunkVisits134 fastForwardChunkVisits135 fastForwardChunkVisits136 fastForwardChunkVisits137 fastForwardChunkVisits138 fastForwardChunkVisits139 fastForwardChunkVisits140 fastForwardChunkVisits141 fastForwardChunkVisits142 fastForwardChunkVisits143 fastForwardChunkVisits144 fastForwardChunkVisits145 fastForwardChunkVisits146 fastForwardChunkVisits147 fastForwardChunkVisits148 fastForwardChunkVisits149 fastForwardChunkVisits150 fastForwardChunkVisits151 fastForwardChunkVisits152 fastForwardChunkVisits153 fastForwardChunkVisits154 fastForwardChunkVisits155 fastForwardChunkVisits156 fastForwardChunkVisits157 fastForwardChunkVisits158 fastForwardChunkVisits159 fastForwardChunkVisits160 fastForwardChunkVisits161 fastForwardChunkVisits162 fastForwardChunkVisits163 fastForwardChunkVisits164 fastForwardChunkVisits165 fastForwardChunkVisits166 fastForwardChunkVisits167 fastForwardChunkVisits168 fastForwardChunkVisits169 fastForwardChunkVisits170 fastForwardChunkVisits171 fastForwardChunkVisits172 fastForwardChunkVisits173 fastForwardChunkVisits174 fastForwardChunkVisits175 fastForwardChunkVisits176 fastForwardChunkVisits177

/-- Exact visits in the physical word: 5583 original gates and nine copy
events, via independently checked sparse lookup trees. Concatenation is
right-associated to avoid repeated scans. -/
theorem forward_visits_fast (r : Nat) : eventVisits r forwardEvents =
    fastForwardChunkVisits000 r ++ (fastForwardChunkVisits001 r ++ (fastForwardChunkVisits002 r ++ (fastForwardChunkVisits003 r ++ (fastForwardChunkVisits004 r ++ (fastForwardChunkVisits005 r ++ (fastForwardChunkVisits006 r ++ (fastForwardChunkVisits007 r ++ (fastForwardChunkVisits008 r ++ (fastForwardChunkVisits009 r ++ (fastForwardChunkVisits010 r ++ (fastForwardChunkVisits011 r ++ (fastForwardChunkVisits012 r ++ (fastForwardChunkVisits013 r ++ (fastForwardChunkVisits014 r ++ (fastForwardChunkVisits015 r ++ (fastForwardChunkVisits016 r ++ (fastForwardChunkVisits017 r ++ (fastForwardChunkVisits018 r ++ (fastForwardChunkVisits019 r ++ (fastForwardChunkVisits020 r ++ (fastForwardChunkVisits021 r ++ (fastForwardChunkVisits022 r ++ (fastForwardChunkVisits023 r ++ (fastForwardChunkVisits024 r ++ (fastForwardChunkVisits025 r ++ (fastForwardChunkVisits026 r ++ (fastForwardChunkVisits027 r ++ (fastForwardChunkVisits028 r ++ (fastForwardChunkVisits029 r ++ (fastForwardChunkVisits030 r ++ (fastForwardChunkVisits031 r ++ (fastForwardChunkVisits032 r ++ (fastForwardChunkVisits033 r ++ (fastForwardChunkVisits034 r ++ (fastForwardChunkVisits035 r ++ (fastForwardChunkVisits036 r ++ (fastForwardChunkVisits037 r ++ (fastForwardChunkVisits038 r ++ (fastForwardChunkVisits039 r ++ (fastForwardChunkVisits040 r ++ (fastForwardChunkVisits041 r ++ (fastForwardChunkVisits042 r ++ (fastForwardChunkVisits043 r ++ (fastForwardChunkVisits044 r ++ (fastForwardChunkVisits045 r ++ (fastForwardChunkVisits046 r ++ (fastForwardChunkVisits047 r ++ (fastForwardChunkVisits048 r ++ (fastForwardChunkVisits049 r ++ (fastForwardChunkVisits050 r ++ (fastForwardChunkVisits051 r ++ (fastForwardChunkVisits052 r ++ (fastForwardChunkVisits053 r ++ (fastForwardChunkVisits054 r ++ (fastForwardChunkVisits055 r ++ (fastForwardChunkVisits056 r ++ (fastForwardChunkVisits057 r ++ (fastForwardChunkVisits058 r ++ (fastForwardChunkVisits059 r ++ (fastForwardChunkVisits060 r ++ (fastForwardChunkVisits061 r ++ (fastForwardChunkVisits062 r ++ (fastForwardChunkVisits063 r ++ (fastForwardChunkVisits064 r ++ (fastForwardChunkVisits065 r ++ (fastForwardChunkVisits066 r ++ (fastForwardChunkVisits067 r ++ (fastForwardChunkVisits068 r ++ (fastForwardChunkVisits069 r ++ (fastForwardChunkVisits070 r ++ (fastForwardChunkVisits071 r ++ (fastForwardChunkVisits072 r ++ (fastForwardChunkVisits073 r ++ (fastForwardChunkVisits074 r ++ (fastForwardChunkVisits075 r ++ (fastForwardChunkVisits076 r ++ (fastForwardChunkVisits077 r ++ (fastForwardChunkVisits078 r ++ (fastForwardChunkVisits079 r ++ (fastForwardChunkVisits080 r ++ (fastForwardChunkVisits081 r ++ (fastForwardChunkVisits082 r ++ (fastForwardChunkVisits083 r ++ (fastForwardChunkVisits084 r ++ (fastForwardChunkVisits085 r ++ (fastForwardChunkVisits086 r ++ (fastForwardChunkVisits087 r ++ (fastForwardChunkVisits088 r ++ (fastForwardChunkVisits089 r ++ (fastForwardChunkVisits090 r ++ (fastForwardChunkVisits091 r ++ (fastForwardChunkVisits092 r ++ (fastForwardChunkVisits093 r ++ (fastForwardChunkVisits094 r ++ (fastForwardChunkVisits095 r ++ (fastForwardChunkVisits096 r ++ (fastForwardChunkVisits097 r ++ (fastForwardChunkVisits098 r ++ (fastForwardChunkVisits099 r ++ (fastForwardChunkVisits100 r ++ (fastForwardChunkVisits101 r ++ (fastForwardChunkVisits102 r ++ (fastForwardChunkVisits103 r ++ (fastForwardChunkVisits104 r ++ (fastForwardChunkVisits105 r ++ (fastForwardChunkVisits106 r ++ (fastForwardChunkVisits107 r ++ (fastForwardChunkVisits108 r ++ (fastForwardChunkVisits109 r ++ (fastForwardChunkVisits110 r ++ (fastForwardChunkVisits111 r ++ (fastForwardChunkVisits112 r ++ (fastForwardChunkVisits113 r ++ (fastForwardChunkVisits114 r ++ (fastForwardChunkVisits115 r ++ (fastForwardChunkVisits116 r ++ (fastForwardChunkVisits117 r ++ (fastForwardChunkVisits118 r ++ (fastForwardChunkVisits119 r ++ (fastForwardChunkVisits120 r ++ (fastForwardChunkVisits121 r ++ (fastForwardChunkVisits122 r ++ (fastForwardChunkVisits123 r ++ (fastForwardChunkVisits124 r ++ (fastForwardChunkVisits125 r ++ (fastForwardChunkVisits126 r ++ (fastForwardChunkVisits127 r ++ (fastForwardChunkVisits128 r ++ (fastForwardChunkVisits129 r ++ (fastForwardChunkVisits130 r ++ (fastForwardChunkVisits131 r ++ (fastForwardChunkVisits132 r ++ (fastForwardChunkVisits133 r ++ (fastForwardChunkVisits134 r ++ (fastForwardChunkVisits135 r ++ (fastForwardChunkVisits136 r ++ (fastForwardChunkVisits137 r ++ (fastForwardChunkVisits138 r ++ (fastForwardChunkVisits139 r ++ (fastForwardChunkVisits140 r ++ (fastForwardChunkVisits141 r ++ (fastForwardChunkVisits142 r ++ (fastForwardChunkVisits143 r ++ (fastForwardChunkVisits144 r ++ (fastForwardChunkVisits145 r ++ (fastForwardChunkVisits146 r ++ (fastForwardChunkVisits147 r ++ (fastForwardChunkVisits148 r ++ (fastForwardChunkVisits149 r ++ (fastForwardChunkVisits150 r ++ (fastForwardChunkVisits151 r ++ (fastForwardChunkVisits152 r ++ (fastForwardChunkVisits153 r ++ (fastForwardChunkVisits154 r ++ (fastForwardChunkVisits155 r ++ (fastForwardChunkVisits156 r ++ (fastForwardChunkVisits157 r ++ (fastForwardChunkVisits158 r ++ (fastForwardChunkVisits159 r ++ (fastForwardChunkVisits160 r ++ (fastForwardChunkVisits161 r ++ (fastForwardChunkVisits162 r ++ (fastForwardChunkVisits163 r ++ (fastForwardChunkVisits164 r ++ (fastForwardChunkVisits165 r ++ (fastForwardChunkVisits166 r ++ (fastForwardChunkVisits167 r ++ (fastForwardChunkVisits168 r ++ (fastForwardChunkVisits169 r ++ (fastForwardChunkVisits170 r ++ (fastForwardChunkVisits171 r ++ (fastForwardChunkVisits172 r ++ (fastForwardChunkVisits173 r ++ (fastForwardChunkVisits174 r ++ (fastForwardChunkVisits175 r ++ (fastForwardChunkVisits176 r ++ (fastForwardChunkVisits177 r))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  have h := forward_visits_chunks r
  simp only [eventVisits_forwardChunk000, eventVisits_forwardChunk001, eventVisits_forwardChunk002, eventVisits_forwardChunk003, eventVisits_forwardChunk004, eventVisits_forwardChunk005, eventVisits_forwardChunk006, eventVisits_forwardChunk007, eventVisits_forwardChunk008, eventVisits_forwardChunk009, eventVisits_forwardChunk010, eventVisits_forwardChunk011, eventVisits_forwardChunk012, eventVisits_forwardChunk013, eventVisits_forwardChunk014, eventVisits_forwardChunk015, eventVisits_forwardChunk016, eventVisits_forwardChunk017, eventVisits_forwardChunk018, eventVisits_forwardChunk019, eventVisits_forwardChunk020, eventVisits_forwardChunk021, eventVisits_forwardChunk022, eventVisits_forwardChunk023, eventVisits_forwardChunk024, eventVisits_forwardChunk025, eventVisits_forwardChunk026, eventVisits_forwardChunk027, eventVisits_forwardChunk028, eventVisits_forwardChunk029, eventVisits_forwardChunk030, eventVisits_forwardChunk031, eventVisits_forwardChunk032, eventVisits_forwardChunk033, eventVisits_forwardChunk034, eventVisits_forwardChunk035, eventVisits_forwardChunk036, eventVisits_forwardChunk037, eventVisits_forwardChunk038, eventVisits_forwardChunk039, eventVisits_forwardChunk040, eventVisits_forwardChunk041, eventVisits_forwardChunk042, eventVisits_forwardChunk043, eventVisits_forwardChunk044, eventVisits_forwardChunk045, eventVisits_forwardChunk046, eventVisits_forwardChunk047, eventVisits_forwardChunk048, eventVisits_forwardChunk049, eventVisits_forwardChunk050, eventVisits_forwardChunk051, eventVisits_forwardChunk052, eventVisits_forwardChunk053, eventVisits_forwardChunk054, eventVisits_forwardChunk055, eventVisits_forwardChunk056, eventVisits_forwardChunk057, eventVisits_forwardChunk058, eventVisits_forwardChunk059, eventVisits_forwardChunk060, eventVisits_forwardChunk061, eventVisits_forwardChunk062, eventVisits_forwardChunk063, eventVisits_forwardChunk064, eventVisits_forwardChunk065, eventVisits_forwardChunk066, eventVisits_forwardChunk067, eventVisits_forwardChunk068, eventVisits_forwardChunk069, eventVisits_forwardChunk070, eventVisits_forwardChunk071, eventVisits_forwardChunk072, eventVisits_forwardChunk073, eventVisits_forwardChunk074, eventVisits_forwardChunk075, eventVisits_forwardChunk076, eventVisits_forwardChunk077, eventVisits_forwardChunk078, eventVisits_forwardChunk079, eventVisits_forwardChunk080, eventVisits_forwardChunk081, eventVisits_forwardChunk082, eventVisits_forwardChunk083, eventVisits_forwardChunk084, eventVisits_forwardChunk085, eventVisits_forwardChunk086, eventVisits_forwardChunk087, eventVisits_forwardChunk088, eventVisits_forwardChunk089, eventVisits_forwardChunk090, eventVisits_forwardChunk091, eventVisits_forwardChunk092, eventVisits_forwardChunk093, eventVisits_forwardChunk094, eventVisits_forwardChunk095, eventVisits_forwardChunk096, eventVisits_forwardChunk097, eventVisits_forwardChunk098, eventVisits_forwardChunk099, eventVisits_forwardChunk100, eventVisits_forwardChunk101, eventVisits_forwardChunk102, eventVisits_forwardChunk103, eventVisits_forwardChunk104, eventVisits_forwardChunk105, eventVisits_forwardChunk106, eventVisits_forwardChunk107, eventVisits_forwardChunk108, eventVisits_forwardChunk109, eventVisits_forwardChunk110, eventVisits_forwardChunk111, eventVisits_forwardChunk112, eventVisits_forwardChunk113, eventVisits_forwardChunk114, eventVisits_forwardChunk115, eventVisits_forwardChunk116, eventVisits_forwardChunk117, eventVisits_forwardChunk118, eventVisits_forwardChunk119, eventVisits_forwardChunk120, eventVisits_forwardChunk121, eventVisits_forwardChunk122, eventVisits_forwardChunk123, eventVisits_forwardChunk124, eventVisits_forwardChunk125, eventVisits_forwardChunk126, eventVisits_forwardChunk127, eventVisits_forwardChunk128, eventVisits_forwardChunk129, eventVisits_forwardChunk130, eventVisits_forwardChunk131, eventVisits_forwardChunk132, eventVisits_forwardChunk133, eventVisits_forwardChunk134, eventVisits_forwardChunk135, eventVisits_forwardChunk136, eventVisits_forwardChunk137, eventVisits_forwardChunk138, eventVisits_forwardChunk139, eventVisits_forwardChunk140, eventVisits_forwardChunk141, eventVisits_forwardChunk142, eventVisits_forwardChunk143, eventVisits_forwardChunk144, eventVisits_forwardChunk145, eventVisits_forwardChunk146, eventVisits_forwardChunk147, eventVisits_forwardChunk148, eventVisits_forwardChunk149, eventVisits_forwardChunk150, eventVisits_forwardChunk151, eventVisits_forwardChunk152, eventVisits_forwardChunk153, eventVisits_forwardChunk154, eventVisits_forwardChunk155, eventVisits_forwardChunk156, eventVisits_forwardChunk157, eventVisits_forwardChunk158, eventVisits_forwardChunk159, eventVisits_forwardChunk160, eventVisits_forwardChunk161, eventVisits_forwardChunk162, eventVisits_forwardChunk163, eventVisits_forwardChunk164, eventVisits_forwardChunk165, eventVisits_forwardChunk166, eventVisits_forwardChunk167, eventVisits_forwardChunk168, eventVisits_forwardChunk169, eventVisits_forwardChunk170, eventVisits_forwardChunk171, eventVisits_forwardChunk172, eventVisits_forwardChunk173, eventVisits_forwardChunk174, eventVisits_forwardChunk175, eventVisits_forwardChunk176, eventVisits_forwardChunk177] at h
  exact h.trans (SparseVisitCompose.visits_append_right
    (fastForwardChunkVisits000 r)
    (fastForwardChunkVisits001 r)
    (fastForwardChunkVisits002 r)
    (fastForwardChunkVisits003 r)
    (fastForwardChunkVisits004 r)
    (fastForwardChunkVisits005 r)
    (fastForwardChunkVisits006 r)
    (fastForwardChunkVisits007 r)
    (fastForwardChunkVisits008 r)
    (fastForwardChunkVisits009 r)
    (fastForwardChunkVisits010 r)
    (fastForwardChunkVisits011 r)
    (fastForwardChunkVisits012 r)
    (fastForwardChunkVisits013 r)
    (fastForwardChunkVisits014 r)
    (fastForwardChunkVisits015 r)
    (fastForwardChunkVisits016 r)
    (fastForwardChunkVisits017 r)
    (fastForwardChunkVisits018 r)
    (fastForwardChunkVisits019 r)
    (fastForwardChunkVisits020 r)
    (fastForwardChunkVisits021 r)
    (fastForwardChunkVisits022 r)
    (fastForwardChunkVisits023 r)
    (fastForwardChunkVisits024 r)
    (fastForwardChunkVisits025 r)
    (fastForwardChunkVisits026 r)
    (fastForwardChunkVisits027 r)
    (fastForwardChunkVisits028 r)
    (fastForwardChunkVisits029 r)
    (fastForwardChunkVisits030 r)
    (fastForwardChunkVisits031 r)
    (fastForwardChunkVisits032 r)
    (fastForwardChunkVisits033 r)
    (fastForwardChunkVisits034 r)
    (fastForwardChunkVisits035 r)
    (fastForwardChunkVisits036 r)
    (fastForwardChunkVisits037 r)
    (fastForwardChunkVisits038 r)
    (fastForwardChunkVisits039 r)
    (fastForwardChunkVisits040 r)
    (fastForwardChunkVisits041 r)
    (fastForwardChunkVisits042 r)
    (fastForwardChunkVisits043 r)
    (fastForwardChunkVisits044 r)
    (fastForwardChunkVisits045 r)
    (fastForwardChunkVisits046 r)
    (fastForwardChunkVisits047 r)
    (fastForwardChunkVisits048 r)
    (fastForwardChunkVisits049 r)
    (fastForwardChunkVisits050 r)
    (fastForwardChunkVisits051 r)
    (fastForwardChunkVisits052 r)
    (fastForwardChunkVisits053 r)
    (fastForwardChunkVisits054 r)
    (fastForwardChunkVisits055 r)
    (fastForwardChunkVisits056 r)
    (fastForwardChunkVisits057 r)
    (fastForwardChunkVisits058 r)
    (fastForwardChunkVisits059 r)
    (fastForwardChunkVisits060 r)
    (fastForwardChunkVisits061 r)
    (fastForwardChunkVisits062 r)
    (fastForwardChunkVisits063 r)
    (fastForwardChunkVisits064 r)
    (fastForwardChunkVisits065 r)
    (fastForwardChunkVisits066 r)
    (fastForwardChunkVisits067 r)
    (fastForwardChunkVisits068 r)
    (fastForwardChunkVisits069 r)
    (fastForwardChunkVisits070 r)
    (fastForwardChunkVisits071 r)
    (fastForwardChunkVisits072 r)
    (fastForwardChunkVisits073 r)
    (fastForwardChunkVisits074 r)
    (fastForwardChunkVisits075 r)
    (fastForwardChunkVisits076 r)
    (fastForwardChunkVisits077 r)
    (fastForwardChunkVisits078 r)
    (fastForwardChunkVisits079 r)
    (fastForwardChunkVisits080 r)
    (fastForwardChunkVisits081 r)
    (fastForwardChunkVisits082 r)
    (fastForwardChunkVisits083 r)
    (fastForwardChunkVisits084 r)
    (fastForwardChunkVisits085 r)
    (fastForwardChunkVisits086 r)
    (fastForwardChunkVisits087 r)
    (fastForwardChunkVisits088 r)
    (fastForwardChunkVisits089 r)
    (fastForwardChunkVisits090 r)
    (fastForwardChunkVisits091 r)
    (fastForwardChunkVisits092 r)
    (fastForwardChunkVisits093 r)
    (fastForwardChunkVisits094 r)
    (fastForwardChunkVisits095 r)
    (fastForwardChunkVisits096 r)
    (fastForwardChunkVisits097 r)
    (fastForwardChunkVisits098 r)
    (fastForwardChunkVisits099 r)
    (fastForwardChunkVisits100 r)
    (fastForwardChunkVisits101 r)
    (fastForwardChunkVisits102 r)
    (fastForwardChunkVisits103 r)
    (fastForwardChunkVisits104 r)
    (fastForwardChunkVisits105 r)
    (fastForwardChunkVisits106 r)
    (fastForwardChunkVisits107 r)
    (fastForwardChunkVisits108 r)
    (fastForwardChunkVisits109 r)
    (fastForwardChunkVisits110 r)
    (fastForwardChunkVisits111 r)
    (fastForwardChunkVisits112 r)
    (fastForwardChunkVisits113 r)
    (fastForwardChunkVisits114 r)
    (fastForwardChunkVisits115 r)
    (fastForwardChunkVisits116 r)
    (fastForwardChunkVisits117 r)
    (fastForwardChunkVisits118 r)
    (fastForwardChunkVisits119 r)
    (fastForwardChunkVisits120 r)
    (fastForwardChunkVisits121 r)
    (fastForwardChunkVisits122 r)
    (fastForwardChunkVisits123 r)
    (fastForwardChunkVisits124 r)
    (fastForwardChunkVisits125 r)
    (fastForwardChunkVisits126 r)
    (fastForwardChunkVisits127 r)
    (fastForwardChunkVisits128 r)
    (fastForwardChunkVisits129 r)
    (fastForwardChunkVisits130 r)
    (fastForwardChunkVisits131 r)
    (fastForwardChunkVisits132 r)
    (fastForwardChunkVisits133 r)
    (fastForwardChunkVisits134 r)
    (fastForwardChunkVisits135 r)
    (fastForwardChunkVisits136 r)
    (fastForwardChunkVisits137 r)
    (fastForwardChunkVisits138 r)
    (fastForwardChunkVisits139 r)
    (fastForwardChunkVisits140 r)
    (fastForwardChunkVisits141 r)
    (fastForwardChunkVisits142 r)
    (fastForwardChunkVisits143 r)
    (fastForwardChunkVisits144 r)
    (fastForwardChunkVisits145 r)
    (fastForwardChunkVisits146 r)
    (fastForwardChunkVisits147 r)
    (fastForwardChunkVisits148 r)
    (fastForwardChunkVisits149 r)
    (fastForwardChunkVisits150 r)
    (fastForwardChunkVisits151 r)
    (fastForwardChunkVisits152 r)
    (fastForwardChunkVisits153 r)
    (fastForwardChunkVisits154 r)
    (fastForwardChunkVisits155 r)
    (fastForwardChunkVisits156 r)
    (fastForwardChunkVisits157 r)
    (fastForwardChunkVisits158 r)
    (fastForwardChunkVisits159 r)
    (fastForwardChunkVisits160 r)
    (fastForwardChunkVisits161 r)
    (fastForwardChunkVisits162 r)
    (fastForwardChunkVisits163 r)
    (fastForwardChunkVisits164 r)
    (fastForwardChunkVisits165 r)
    (fastForwardChunkVisits166 r)
    (fastForwardChunkVisits167 r)
    (fastForwardChunkVisits168 r)
    (fastForwardChunkVisits169 r)
    (fastForwardChunkVisits170 r)
    (fastForwardChunkVisits171 r)
    (fastForwardChunkVisits172 r)
    (fastForwardChunkVisits173 r)
    (fastForwardChunkVisits174 r)
    (fastForwardChunkVisits175 r)
    (fastForwardChunkVisits176 r)
    (fastForwardChunkVisits177 r))

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.forward_visits_fast


