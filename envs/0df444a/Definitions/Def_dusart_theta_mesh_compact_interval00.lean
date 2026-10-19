-- Prove2me | Definitions.Def_dusart_theta_mesh_compact_interval00
-- name    : dusart_theta_mesh_compact_interval00
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-17T02:57:05.029837+00:00
-- url     : https://prove2.me/theorems/112ddd97-715e-4d94-881c-69d611e0f297
-- title:
--   Certified theta upper interval from 100000000 to 401989888
-- statement:
--   Put $a=100000000$, $b=401989888$, $u=99989691935170$, and $v=401971882499010$. The Chebyshev theta function satisfies
--
--   $$10^6\theta(a)\le u\ \Longrightarrow\ \left(10^6\theta(b)\le v\quad\text{and}\quad\forall x\in[a,b),\ \theta(x)\le x+100000+x/10000\right).$$
--
--   This certifies one contiguous interval of the upper bound used in the finite fourth-power logarithmic theta estimate. The endpoint carry can be passed to the next interval.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Complete finite interval certificate.

import Definitions.Def_dusart_theta_mesh_compact_soundness
import Theorems.Thm_dusart_theta_mesh_generic_group000
import Theorems.Thm_dusart_theta_mesh_generic_group001
import Theorems.Thm_dusart_theta_mesh_generic_group002
import Theorems.Thm_dusart_theta_mesh_generic_group003
import Theorems.Thm_dusart_theta_mesh_generic_group004
import Theorems.Thm_dusart_theta_mesh_generic_group005
import Theorems.Thm_dusart_theta_mesh_generic_group006
import Theorems.Thm_dusart_theta_mesh_generic_group007
import Theorems.Thm_dusart_theta_mesh_generic_group008
import Theorems.Thm_dusart_theta_mesh_generic_group009
import Theorems.Thm_dusart_theta_mesh_generic_group010
import Theorems.Thm_dusart_theta_mesh_generic_group011
import Theorems.Thm_dusart_theta_mesh_generic_group012
import Theorems.Thm_dusart_theta_mesh_generic_group013
import Theorems.Thm_dusart_theta_mesh_generic_group014
import Theorems.Thm_dusart_theta_mesh_generic_group015
import Theorems.Thm_dusart_theta_mesh_generic_group016
import Theorems.Thm_dusart_theta_mesh_generic_group017
import Theorems.Thm_dusart_theta_mesh_generic_group018
import Theorems.Thm_dusart_theta_mesh_generic_group019
import Theorems.Thm_dusart_theta_mesh_generic_group020
import Theorems.Thm_dusart_theta_mesh_generic_group021
import Theorems.Thm_dusart_theta_mesh_generic_group022
import Theorems.Thm_dusart_theta_mesh_generic_group023
import Theorems.Thm_dusart_theta_mesh_generic_group024
import Theorems.Thm_dusart_theta_mesh_generic_group025
import Theorems.Thm_dusart_theta_mesh_generic_group026
import Theorems.Thm_dusart_theta_mesh_generic_group027
import Theorems.Thm_dusart_theta_mesh_generic_group028
import Theorems.Thm_dusart_theta_mesh_generic_group029
import Theorems.Thm_dusart_theta_mesh_generic_group030
import Theorems.Thm_dusart_theta_mesh_generic_group031
import Theorems.Thm_dusart_theta_mesh_generic_group032
import Theorems.Thm_dusart_theta_mesh_generic_group033
import Theorems.Thm_dusart_theta_mesh_generic_group034
import Theorems.Thm_dusart_theta_mesh_generic_group035
import Theorems.Thm_dusart_theta_mesh_generic_group036
import Theorems.Thm_dusart_theta_mesh_generic_group037
import Theorems.Thm_dusart_theta_mesh_generic_group038
import Theorems.Thm_dusart_theta_mesh_generic_group039
import Theorems.Thm_dusart_theta_mesh_generic_group040
import Theorems.Thm_dusart_theta_mesh_generic_group041
import Theorems.Thm_dusart_theta_mesh_generic_group042
import Theorems.Thm_dusart_theta_mesh_generic_group043
import Theorems.Thm_dusart_theta_mesh_generic_group044
import Theorems.Thm_dusart_theta_mesh_generic_group045
import Theorems.Thm_dusart_theta_mesh_generic_group046
import Theorems.Thm_dusart_theta_mesh_generic_group047
import Theorems.Thm_dusart_theta_mesh_generic_group048
import Theorems.Thm_dusart_theta_mesh_generic_group049
import Theorems.Thm_dusart_theta_mesh_generic_group050
import Theorems.Thm_dusart_theta_mesh_generic_group051
import Theorems.Thm_dusart_theta_mesh_generic_group052
import Theorems.Thm_dusart_theta_mesh_generic_group053
import Theorems.Thm_dusart_theta_mesh_generic_group054
import Theorems.Thm_dusart_theta_mesh_generic_group055
import Theorems.Thm_dusart_theta_mesh_generic_group056
import Theorems.Thm_dusart_theta_mesh_generic_group057
import Theorems.Thm_dusart_theta_mesh_generic_group058
import Theorems.Thm_dusart_theta_mesh_generic_group059
import Theorems.Thm_dusart_theta_mesh_generic_group060
import Theorems.Thm_dusart_theta_mesh_generic_group061
import Theorems.Thm_dusart_theta_mesh_generic_group062
import Theorems.Thm_dusart_theta_mesh_generic_group063
import Theorems.Thm_dusart_theta_mesh_generic_group064
import Theorems.Thm_dusart_theta_mesh_generic_group065
import Theorems.Thm_dusart_theta_mesh_generic_group066
import Theorems.Thm_dusart_theta_mesh_generic_group067
import Theorems.Thm_dusart_theta_mesh_generic_group068
import Theorems.Thm_dusart_theta_mesh_generic_group069
import Theorems.Thm_dusart_theta_mesh_generic_group070
import Theorems.Thm_dusart_theta_mesh_generic_group071
import Theorems.Thm_dusart_theta_mesh_generic_group072
import Theorems.Thm_dusart_theta_mesh_generic_group073
import Theorems.Thm_dusart_theta_mesh_generic_group074
import Theorems.Thm_dusart_theta_mesh_generic_group075
import Theorems.Thm_dusart_theta_mesh_generic_group076
import Theorems.Thm_dusart_theta_mesh_generic_group077
import Theorems.Thm_dusart_theta_mesh_generic_group078
import Theorems.Thm_dusart_theta_mesh_generic_group079
import Theorems.Thm_dusart_theta_mesh_generic_group080
import Theorems.Thm_dusart_theta_mesh_generic_group081
import Theorems.Thm_dusart_theta_mesh_generic_group082
import Theorems.Thm_dusart_theta_mesh_generic_group083
import Theorems.Thm_dusart_theta_mesh_generic_group084
import Theorems.Thm_dusart_theta_mesh_generic_group085
import Theorems.Thm_dusart_theta_mesh_generic_group086
import Theorems.Thm_dusart_theta_mesh_generic_group087
import Theorems.Thm_dusart_theta_mesh_generic_group088
import Theorems.Thm_dusart_theta_mesh_generic_group089
import Theorems.Thm_dusart_theta_mesh_generic_group090
import Theorems.Thm_dusart_theta_mesh_generic_group091
import Theorems.Thm_dusart_theta_mesh_generic_group092
import Theorems.Thm_dusart_theta_mesh_generic_group093
import Theorems.Thm_dusart_theta_mesh_generic_group094
import Theorems.Thm_dusart_theta_mesh_generic_group095
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartCompactIntervals
theorem interval0_generic : DusartNumeric.GenericSpec 100000000 401989888 99989691935170 401971882499010 := by
 intro S step compose
 exact (compose (compose (compose (compose (compose (compose (dusart_theta_mesh_generic_group000 S step @compose) (compose (dusart_theta_mesh_generic_group001 S step @compose) (dusart_theta_mesh_generic_group002 S step @compose))) (compose (dusart_theta_mesh_generic_group003 S step @compose) (compose (dusart_theta_mesh_generic_group004 S step @compose) (dusart_theta_mesh_generic_group005 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group006 S step @compose) (compose (dusart_theta_mesh_generic_group007 S step @compose) (dusart_theta_mesh_generic_group008 S step @compose))) (compose (dusart_theta_mesh_generic_group009 S step @compose) (compose (dusart_theta_mesh_generic_group010 S step @compose) (dusart_theta_mesh_generic_group011 S step @compose))))) (compose (compose (compose (dusart_theta_mesh_generic_group012 S step @compose) (compose (dusart_theta_mesh_generic_group013 S step @compose) (dusart_theta_mesh_generic_group014 S step @compose))) (compose (dusart_theta_mesh_generic_group015 S step @compose) (compose (dusart_theta_mesh_generic_group016 S step @compose) (dusart_theta_mesh_generic_group017 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group018 S step @compose) (compose (dusart_theta_mesh_generic_group019 S step @compose) (dusart_theta_mesh_generic_group020 S step @compose))) (compose (dusart_theta_mesh_generic_group021 S step @compose) (compose (dusart_theta_mesh_generic_group022 S step @compose) (dusart_theta_mesh_generic_group023 S step @compose)))))) (compose (compose (compose (compose (dusart_theta_mesh_generic_group024 S step @compose) (compose (dusart_theta_mesh_generic_group025 S step @compose) (dusart_theta_mesh_generic_group026 S step @compose))) (compose (dusart_theta_mesh_generic_group027 S step @compose) (compose (dusart_theta_mesh_generic_group028 S step @compose) (dusart_theta_mesh_generic_group029 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group030 S step @compose) (compose (dusart_theta_mesh_generic_group031 S step @compose) (dusart_theta_mesh_generic_group032 S step @compose))) (compose (dusart_theta_mesh_generic_group033 S step @compose) (compose (dusart_theta_mesh_generic_group034 S step @compose) (dusart_theta_mesh_generic_group035 S step @compose))))) (compose (compose (compose (dusart_theta_mesh_generic_group036 S step @compose) (compose (dusart_theta_mesh_generic_group037 S step @compose) (dusart_theta_mesh_generic_group038 S step @compose))) (compose (dusart_theta_mesh_generic_group039 S step @compose) (compose (dusart_theta_mesh_generic_group040 S step @compose) (dusart_theta_mesh_generic_group041 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group042 S step @compose) (compose (dusart_theta_mesh_generic_group043 S step @compose) (dusart_theta_mesh_generic_group044 S step @compose))) (compose (dusart_theta_mesh_generic_group045 S step @compose) (compose (dusart_theta_mesh_generic_group046 S step @compose) (dusart_theta_mesh_generic_group047 S step @compose))))))) (compose (compose (compose (compose (compose (dusart_theta_mesh_generic_group048 S step @compose) (compose (dusart_theta_mesh_generic_group049 S step @compose) (dusart_theta_mesh_generic_group050 S step @compose))) (compose (dusart_theta_mesh_generic_group051 S step @compose) (compose (dusart_theta_mesh_generic_group052 S step @compose) (dusart_theta_mesh_generic_group053 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group054 S step @compose) (compose (dusart_theta_mesh_generic_group055 S step @compose) (dusart_theta_mesh_generic_group056 S step @compose))) (compose (dusart_theta_mesh_generic_group057 S step @compose) (compose (dusart_theta_mesh_generic_group058 S step @compose) (dusart_theta_mesh_generic_group059 S step @compose))))) (compose (compose (compose (dusart_theta_mesh_generic_group060 S step @compose) (compose (dusart_theta_mesh_generic_group061 S step @compose) (dusart_theta_mesh_generic_group062 S step @compose))) (compose (dusart_theta_mesh_generic_group063 S step @compose) (compose (dusart_theta_mesh_generic_group064 S step @compose) (dusart_theta_mesh_generic_group065 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group066 S step @compose) (compose (dusart_theta_mesh_generic_group067 S step @compose) (dusart_theta_mesh_generic_group068 S step @compose))) (compose (dusart_theta_mesh_generic_group069 S step @compose) (compose (dusart_theta_mesh_generic_group070 S step @compose) (dusart_theta_mesh_generic_group071 S step @compose)))))) (compose (compose (compose (compose (dusart_theta_mesh_generic_group072 S step @compose) (compose (dusart_theta_mesh_generic_group073 S step @compose) (dusart_theta_mesh_generic_group074 S step @compose))) (compose (dusart_theta_mesh_generic_group075 S step @compose) (compose (dusart_theta_mesh_generic_group076 S step @compose) (dusart_theta_mesh_generic_group077 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group078 S step @compose) (compose (dusart_theta_mesh_generic_group079 S step @compose) (dusart_theta_mesh_generic_group080 S step @compose))) (compose (dusart_theta_mesh_generic_group081 S step @compose) (compose (dusart_theta_mesh_generic_group082 S step @compose) (dusart_theta_mesh_generic_group083 S step @compose))))) (compose (compose (compose (dusart_theta_mesh_generic_group084 S step @compose) (compose (dusart_theta_mesh_generic_group085 S step @compose) (dusart_theta_mesh_generic_group086 S step @compose))) (compose (dusart_theta_mesh_generic_group087 S step @compose) (compose (dusart_theta_mesh_generic_group088 S step @compose) (dusart_theta_mesh_generic_group089 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group090 S step @compose) (compose (dusart_theta_mesh_generic_group091 S step @compose) (dusart_theta_mesh_generic_group092 S step @compose))) (compose (dusart_theta_mesh_generic_group093 S step @compose) (compose (dusart_theta_mesh_generic_group094 S step @compose) (dusart_theta_mesh_generic_group095 S step @compose))))))))
theorem interval0 : DusartMeshUpper.Literal.Spec 100000000 401989888 99989691935170 401971882499010 :=
 DusartProvedBridge.interpret interval0_generic
end DusartCompactIntervals


