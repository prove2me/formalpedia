-- Prove2me | Definitions.Def_CSL_Generated_MemoryAccess_Concat
-- name    : CSL_Generated_MemoryAccess_Concat
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:10:26.487431+00:00
-- url     : https://prove2.me/theorems/c9fd645c-51e4-4cc0-baa9-7592bc4eba3e
-- title:
--   Coded sorting library: Generated / MemoryAccess / Concat
-- statement:
--   Module `CodedSorting.Generated.MemoryAccess.Concat` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.MemoryAccess.Concat

import Definitions.Def_CSL_Compat
import Std

namespace CSL.Construction.PhysicalFramePaths.SparseVisitCompose
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem visits_append_right (v000 v001 v002 v003 v004 v005 v006 v007 v008 v009 v010 v011 v012 v013 v014 v015 v016 v017 v018 v019 v020 v021 v022 v023 v024 v025 v026 v027 v028 v029 v030 v031 v032 v033 v034 v035 v036 v037 v038 v039 v040 v041 v042 v043 v044 v045 v046 v047 v048 v049 v050 v051 v052 v053 v054 v055 v056 v057 v058 v059 v060 v061 v062 v063 v064 v065 v066 v067 v068 v069 v070 v071 v072 v073 v074 v075 v076 v077 v078 v079 v080 v081 v082 v083 v084 v085 v086 v087 v088 v089 v090 v091 v092 v093 v094 v095 v096 v097 v098 v099 v100 v101 v102 v103 v104 v105 v106 v107 v108 v109 v110 v111 v112 v113 v114 v115 v116 v117 v118 v119 v120 v121 v122 v123 v124 v125 v126 v127 v128 v129 v130 v131 v132 v133 v134 v135 v136 v137 v138 v139 v140 v141 v142 v143 v144 v145 v146 v147 v148 v149 v150 v151 v152 v153 v154 v155 v156 v157 v158 v159 v160 v161 v162 v163 v164 v165 v166 v167 v168 v169 v170 v171 v172 v173 v174 v175 v176 v177 : List Nat) :
    v000 ++ v001 ++ v002 ++ v003 ++ v004 ++ v005 ++ v006 ++ v007 ++ v008 ++ v009 ++ v010 ++ v011 ++ v012 ++ v013 ++ v014 ++ v015 ++ v016 ++ v017 ++ v018 ++ v019 ++ v020 ++ v021 ++ v022 ++ v023 ++ v024 ++ v025 ++ v026 ++ v027 ++ v028 ++ v029 ++ v030 ++ v031 ++ v032 ++ v033 ++ v034 ++ v035 ++ v036 ++ v037 ++ v038 ++ v039 ++ v040 ++ v041 ++ v042 ++ v043 ++ v044 ++ v045 ++ v046 ++ v047 ++ v048 ++ v049 ++ v050 ++ v051 ++ v052 ++ v053 ++ v054 ++ v055 ++ v056 ++ v057 ++ v058 ++ v059 ++ v060 ++ v061 ++ v062 ++ v063 ++ v064 ++ v065 ++ v066 ++ v067 ++ v068 ++ v069 ++ v070 ++ v071 ++ v072 ++ v073 ++ v074 ++ v075 ++ v076 ++ v077 ++ v078 ++ v079 ++ v080 ++ v081 ++ v082 ++ v083 ++ v084 ++ v085 ++ v086 ++ v087 ++ v088 ++ v089 ++ v090 ++ v091 ++ v092 ++ v093 ++ v094 ++ v095 ++ v096 ++ v097 ++ v098 ++ v099 ++ v100 ++ v101 ++ v102 ++ v103 ++ v104 ++ v105 ++ v106 ++ v107 ++ v108 ++ v109 ++ v110 ++ v111 ++ v112 ++ v113 ++ v114 ++ v115 ++ v116 ++ v117 ++ v118 ++ v119 ++ v120 ++ v121 ++ v122 ++ v123 ++ v124 ++ v125 ++ v126 ++ v127 ++ v128 ++ v129 ++ v130 ++ v131 ++ v132 ++ v133 ++ v134 ++ v135 ++ v136 ++ v137 ++ v138 ++ v139 ++ v140 ++ v141 ++ v142 ++ v143 ++ v144 ++ v145 ++ v146 ++ v147 ++ v148 ++ v149 ++ v150 ++ v151 ++ v152 ++ v153 ++ v154 ++ v155 ++ v156 ++ v157 ++ v158 ++ v159 ++ v160 ++ v161 ++ v162 ++ v163 ++ v164 ++ v165 ++ v166 ++ v167 ++ v168 ++ v169 ++ v170 ++ v171 ++ v172 ++ v173 ++ v174 ++ v175 ++ v176 ++ v177 =
    v000 ++ (v001 ++ (v002 ++ (v003 ++ (v004 ++ (v005 ++ (v006 ++ (v007 ++ (v008 ++ (v009 ++ (v010 ++ (v011 ++ (v012 ++ (v013 ++ (v014 ++ (v015 ++ (v016 ++ (v017 ++ (v018 ++ (v019 ++ (v020 ++ (v021 ++ (v022 ++ (v023 ++ (v024 ++ (v025 ++ (v026 ++ (v027 ++ (v028 ++ (v029 ++ (v030 ++ (v031 ++ (v032 ++ (v033 ++ (v034 ++ (v035 ++ (v036 ++ (v037 ++ (v038 ++ (v039 ++ (v040 ++ (v041 ++ (v042 ++ (v043 ++ (v044 ++ (v045 ++ (v046 ++ (v047 ++ (v048 ++ (v049 ++ (v050 ++ (v051 ++ (v052 ++ (v053 ++ (v054 ++ (v055 ++ (v056 ++ (v057 ++ (v058 ++ (v059 ++ (v060 ++ (v061 ++ (v062 ++ (v063 ++ (v064 ++ (v065 ++ (v066 ++ (v067 ++ (v068 ++ (v069 ++ (v070 ++ (v071 ++ (v072 ++ (v073 ++ (v074 ++ (v075 ++ (v076 ++ (v077 ++ (v078 ++ (v079 ++ (v080 ++ (v081 ++ (v082 ++ (v083 ++ (v084 ++ (v085 ++ (v086 ++ (v087 ++ (v088 ++ (v089 ++ (v090 ++ (v091 ++ (v092 ++ (v093 ++ (v094 ++ (v095 ++ (v096 ++ (v097 ++ (v098 ++ (v099 ++ (v100 ++ (v101 ++ (v102 ++ (v103 ++ (v104 ++ (v105 ++ (v106 ++ (v107 ++ (v108 ++ (v109 ++ (v110 ++ (v111 ++ (v112 ++ (v113 ++ (v114 ++ (v115 ++ (v116 ++ (v117 ++ (v118 ++ (v119 ++ (v120 ++ (v121 ++ (v122 ++ (v123 ++ (v124 ++ (v125 ++ (v126 ++ (v127 ++ (v128 ++ (v129 ++ (v130 ++ (v131 ++ (v132 ++ (v133 ++ (v134 ++ (v135 ++ (v136 ++ (v137 ++ (v138 ++ (v139 ++ (v140 ++ (v141 ++ (v142 ++ (v143 ++ (v144 ++ (v145 ++ (v146 ++ (v147 ++ (v148 ++ (v149 ++ (v150 ++ (v151 ++ (v152 ++ (v153 ++ (v154 ++ (v155 ++ (v156 ++ (v157 ++ (v158 ++ (v159 ++ (v160 ++ (v161 ++ (v162 ++ (v163 ++ (v164 ++ (v165 ++ (v166 ++ (v167 ++ (v168 ++ (v169 ++ (v170 ++ (v171 ++ (v172 ++ (v173 ++ (v174 ++ (v175 ++ (v176 ++ (v177))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  simp only [List.append_assoc]

end CSL.Construction.PhysicalFramePaths.SparseVisitCompose


