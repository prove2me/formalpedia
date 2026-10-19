-- Prove2me | Definitions.Def_dusart_theta_mesh_compact_interval01
-- name    : dusart_theta_mesh_compact_interval01
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-17T02:57:15.532147+00:00
-- url     : https://prove2.me/theorems/eb5e1500-6382-4d11-9f88-6ce1338e3380
-- title:
--   Certified theta upper interval from 401989888 to 1609949440
-- statement:
--   Put $a=401989888$, $b=1609949440$, $u=401971882499010$, and $v=1609919129810472$. The Chebyshev theta function satisfies
--
--   $$10^6\theta(a)\le u\ \Longrightarrow\ \left(10^6\theta(b)\le v\quad\text{and}\quad\forall x\in[a,b),\ \theta(x)\le x+100000+x/10000\right).$$
--
--   This certifies one contiguous interval of the upper bound used in the finite fourth-power logarithmic theta estimate. The endpoint carry can be passed to the next interval.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Complete finite interval certificate.

import Definitions.Def_dusart_theta_mesh_compact_soundness
import Theorems.Thm_dusart_theta_mesh_generic_group096
import Theorems.Thm_dusart_theta_mesh_generic_group097
import Theorems.Thm_dusart_theta_mesh_generic_group098
import Theorems.Thm_dusart_theta_mesh_generic_group099
import Theorems.Thm_dusart_theta_mesh_generic_group100
import Theorems.Thm_dusart_theta_mesh_generic_group101
import Theorems.Thm_dusart_theta_mesh_generic_group102
import Theorems.Thm_dusart_theta_mesh_generic_group103
import Theorems.Thm_dusart_theta_mesh_generic_group104
import Theorems.Thm_dusart_theta_mesh_generic_group105
import Theorems.Thm_dusart_theta_mesh_generic_group106
import Theorems.Thm_dusart_theta_mesh_generic_group107
import Theorems.Thm_dusart_theta_mesh_generic_group108
import Theorems.Thm_dusart_theta_mesh_generic_group109
import Theorems.Thm_dusart_theta_mesh_generic_group110
import Theorems.Thm_dusart_theta_mesh_generic_group111
import Theorems.Thm_dusart_theta_mesh_generic_group112
import Theorems.Thm_dusart_theta_mesh_generic_group113
import Theorems.Thm_dusart_theta_mesh_generic_group114
import Theorems.Thm_dusart_theta_mesh_generic_group115
import Theorems.Thm_dusart_theta_mesh_generic_group116
import Theorems.Thm_dusart_theta_mesh_generic_group117
import Theorems.Thm_dusart_theta_mesh_generic_group118
import Theorems.Thm_dusart_theta_mesh_generic_group119
import Theorems.Thm_dusart_theta_mesh_generic_group120
import Theorems.Thm_dusart_theta_mesh_generic_group121
import Theorems.Thm_dusart_theta_mesh_generic_group122
import Theorems.Thm_dusart_theta_mesh_generic_group123
import Theorems.Thm_dusart_theta_mesh_generic_group124
import Theorems.Thm_dusart_theta_mesh_generic_group125
import Theorems.Thm_dusart_theta_mesh_generic_group126
import Theorems.Thm_dusart_theta_mesh_generic_group127
import Theorems.Thm_dusart_theta_mesh_generic_group128
import Theorems.Thm_dusart_theta_mesh_generic_group129
import Theorems.Thm_dusart_theta_mesh_generic_group130
import Theorems.Thm_dusart_theta_mesh_generic_group131
import Theorems.Thm_dusart_theta_mesh_generic_group132
import Theorems.Thm_dusart_theta_mesh_generic_group133
import Theorems.Thm_dusart_theta_mesh_generic_group134
import Theorems.Thm_dusart_theta_mesh_generic_group135
import Theorems.Thm_dusart_theta_mesh_generic_group136
import Theorems.Thm_dusart_theta_mesh_generic_group137
import Theorems.Thm_dusart_theta_mesh_generic_group138
import Theorems.Thm_dusart_theta_mesh_generic_group139
import Theorems.Thm_dusart_theta_mesh_generic_group140
import Theorems.Thm_dusart_theta_mesh_generic_group141
import Theorems.Thm_dusart_theta_mesh_generic_group142
import Theorems.Thm_dusart_theta_mesh_generic_group143
import Theorems.Thm_dusart_theta_mesh_generic_group144
import Theorems.Thm_dusart_theta_mesh_generic_group145
import Theorems.Thm_dusart_theta_mesh_generic_group146
import Theorems.Thm_dusart_theta_mesh_generic_group147
import Theorems.Thm_dusart_theta_mesh_generic_group148
import Theorems.Thm_dusart_theta_mesh_generic_group149
import Theorems.Thm_dusart_theta_mesh_generic_group150
import Theorems.Thm_dusart_theta_mesh_generic_group151
import Theorems.Thm_dusart_theta_mesh_generic_group152
import Theorems.Thm_dusart_theta_mesh_generic_group153
import Theorems.Thm_dusart_theta_mesh_generic_group154
import Theorems.Thm_dusart_theta_mesh_generic_group155
import Theorems.Thm_dusart_theta_mesh_generic_group156
import Theorems.Thm_dusart_theta_mesh_generic_group157
import Theorems.Thm_dusart_theta_mesh_generic_group158
import Theorems.Thm_dusart_theta_mesh_generic_group159
import Theorems.Thm_dusart_theta_mesh_generic_group160
import Theorems.Thm_dusart_theta_mesh_generic_group161
import Theorems.Thm_dusart_theta_mesh_generic_group162
import Theorems.Thm_dusart_theta_mesh_generic_group163
import Theorems.Thm_dusart_theta_mesh_generic_group164
import Theorems.Thm_dusart_theta_mesh_generic_group165
import Theorems.Thm_dusart_theta_mesh_generic_group166
import Theorems.Thm_dusart_theta_mesh_generic_group167
import Theorems.Thm_dusart_theta_mesh_generic_group168
import Theorems.Thm_dusart_theta_mesh_generic_group169
import Theorems.Thm_dusart_theta_mesh_generic_group170
import Theorems.Thm_dusart_theta_mesh_generic_group171
import Theorems.Thm_dusart_theta_mesh_generic_group172
import Theorems.Thm_dusart_theta_mesh_generic_group173
import Theorems.Thm_dusart_theta_mesh_generic_group174
import Theorems.Thm_dusart_theta_mesh_generic_group175
import Theorems.Thm_dusart_theta_mesh_generic_group176
import Theorems.Thm_dusart_theta_mesh_generic_group177
import Theorems.Thm_dusart_theta_mesh_generic_group178
import Theorems.Thm_dusart_theta_mesh_generic_group179
import Theorems.Thm_dusart_theta_mesh_generic_group180
import Theorems.Thm_dusart_theta_mesh_generic_group181
import Theorems.Thm_dusart_theta_mesh_generic_group182
import Theorems.Thm_dusart_theta_mesh_generic_group183
import Theorems.Thm_dusart_theta_mesh_generic_group184
import Theorems.Thm_dusart_theta_mesh_generic_group185
import Theorems.Thm_dusart_theta_mesh_generic_group186
import Theorems.Thm_dusart_theta_mesh_generic_group187
import Theorems.Thm_dusart_theta_mesh_generic_group188
import Theorems.Thm_dusart_theta_mesh_generic_group189
import Theorems.Thm_dusart_theta_mesh_generic_group190
import Theorems.Thm_dusart_theta_mesh_generic_group191
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartCompactIntervals
theorem interval1_generic : DusartNumeric.GenericSpec 401989888 1609949440 401971882499010 1609919129810472 := by
 intro S step compose
 exact (compose (compose (compose (compose (compose (compose (dusart_theta_mesh_generic_group096 S step @compose) (compose (dusart_theta_mesh_generic_group097 S step @compose) (dusart_theta_mesh_generic_group098 S step @compose))) (compose (dusart_theta_mesh_generic_group099 S step @compose) (compose (dusart_theta_mesh_generic_group100 S step @compose) (dusart_theta_mesh_generic_group101 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group102 S step @compose) (compose (dusart_theta_mesh_generic_group103 S step @compose) (dusart_theta_mesh_generic_group104 S step @compose))) (compose (dusart_theta_mesh_generic_group105 S step @compose) (compose (dusart_theta_mesh_generic_group106 S step @compose) (dusart_theta_mesh_generic_group107 S step @compose))))) (compose (compose (compose (dusart_theta_mesh_generic_group108 S step @compose) (compose (dusart_theta_mesh_generic_group109 S step @compose) (dusart_theta_mesh_generic_group110 S step @compose))) (compose (dusart_theta_mesh_generic_group111 S step @compose) (compose (dusart_theta_mesh_generic_group112 S step @compose) (dusart_theta_mesh_generic_group113 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group114 S step @compose) (compose (dusart_theta_mesh_generic_group115 S step @compose) (dusart_theta_mesh_generic_group116 S step @compose))) (compose (dusart_theta_mesh_generic_group117 S step @compose) (compose (dusart_theta_mesh_generic_group118 S step @compose) (dusart_theta_mesh_generic_group119 S step @compose)))))) (compose (compose (compose (compose (dusart_theta_mesh_generic_group120 S step @compose) (compose (dusart_theta_mesh_generic_group121 S step @compose) (dusart_theta_mesh_generic_group122 S step @compose))) (compose (dusart_theta_mesh_generic_group123 S step @compose) (compose (dusart_theta_mesh_generic_group124 S step @compose) (dusart_theta_mesh_generic_group125 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group126 S step @compose) (compose (dusart_theta_mesh_generic_group127 S step @compose) (dusart_theta_mesh_generic_group128 S step @compose))) (compose (dusart_theta_mesh_generic_group129 S step @compose) (compose (dusart_theta_mesh_generic_group130 S step @compose) (dusart_theta_mesh_generic_group131 S step @compose))))) (compose (compose (compose (dusart_theta_mesh_generic_group132 S step @compose) (compose (dusart_theta_mesh_generic_group133 S step @compose) (dusart_theta_mesh_generic_group134 S step @compose))) (compose (dusart_theta_mesh_generic_group135 S step @compose) (compose (dusart_theta_mesh_generic_group136 S step @compose) (dusart_theta_mesh_generic_group137 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group138 S step @compose) (compose (dusart_theta_mesh_generic_group139 S step @compose) (dusart_theta_mesh_generic_group140 S step @compose))) (compose (dusart_theta_mesh_generic_group141 S step @compose) (compose (dusart_theta_mesh_generic_group142 S step @compose) (dusart_theta_mesh_generic_group143 S step @compose))))))) (compose (compose (compose (compose (compose (dusart_theta_mesh_generic_group144 S step @compose) (compose (dusart_theta_mesh_generic_group145 S step @compose) (dusart_theta_mesh_generic_group146 S step @compose))) (compose (dusart_theta_mesh_generic_group147 S step @compose) (compose (dusart_theta_mesh_generic_group148 S step @compose) (dusart_theta_mesh_generic_group149 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group150 S step @compose) (compose (dusart_theta_mesh_generic_group151 S step @compose) (dusart_theta_mesh_generic_group152 S step @compose))) (compose (dusart_theta_mesh_generic_group153 S step @compose) (compose (dusart_theta_mesh_generic_group154 S step @compose) (dusart_theta_mesh_generic_group155 S step @compose))))) (compose (compose (compose (dusart_theta_mesh_generic_group156 S step @compose) (compose (dusart_theta_mesh_generic_group157 S step @compose) (dusart_theta_mesh_generic_group158 S step @compose))) (compose (dusart_theta_mesh_generic_group159 S step @compose) (compose (dusart_theta_mesh_generic_group160 S step @compose) (dusart_theta_mesh_generic_group161 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group162 S step @compose) (compose (dusart_theta_mesh_generic_group163 S step @compose) (dusart_theta_mesh_generic_group164 S step @compose))) (compose (dusart_theta_mesh_generic_group165 S step @compose) (compose (dusart_theta_mesh_generic_group166 S step @compose) (dusart_theta_mesh_generic_group167 S step @compose)))))) (compose (compose (compose (compose (dusart_theta_mesh_generic_group168 S step @compose) (compose (dusart_theta_mesh_generic_group169 S step @compose) (dusart_theta_mesh_generic_group170 S step @compose))) (compose (dusart_theta_mesh_generic_group171 S step @compose) (compose (dusart_theta_mesh_generic_group172 S step @compose) (dusart_theta_mesh_generic_group173 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group174 S step @compose) (compose (dusart_theta_mesh_generic_group175 S step @compose) (dusart_theta_mesh_generic_group176 S step @compose))) (compose (dusart_theta_mesh_generic_group177 S step @compose) (compose (dusart_theta_mesh_generic_group178 S step @compose) (dusart_theta_mesh_generic_group179 S step @compose))))) (compose (compose (compose (dusart_theta_mesh_generic_group180 S step @compose) (compose (dusart_theta_mesh_generic_group181 S step @compose) (dusart_theta_mesh_generic_group182 S step @compose))) (compose (dusart_theta_mesh_generic_group183 S step @compose) (compose (dusart_theta_mesh_generic_group184 S step @compose) (dusart_theta_mesh_generic_group185 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group186 S step @compose) (compose (dusart_theta_mesh_generic_group187 S step @compose) (dusart_theta_mesh_generic_group188 S step @compose))) (compose (dusart_theta_mesh_generic_group189 S step @compose) (compose (dusart_theta_mesh_generic_group190 S step @compose) (dusart_theta_mesh_generic_group191 S step @compose))))))))
theorem interval1 : DusartMeshUpper.Literal.Spec 401989888 1609949440 401971882499010 1609919129810472 :=
 DusartProvedBridge.interpret interval1_generic
end DusartCompactIntervals


