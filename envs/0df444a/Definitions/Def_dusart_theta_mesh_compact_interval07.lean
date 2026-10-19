-- Prove2me | Definitions.Def_dusart_theta_mesh_compact_interval07
-- name    : dusart_theta_mesh_compact_interval07
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-17T03:00:11.938258+00:00
-- url     : https://prove2.me/theorems/a3340ab7-9048-43f2-b178-735c4a1feaf7
-- title:
--   Certified theta upper interval from 9663013120 to 10000064768
-- statement:
--   Put $a=9663013120$, $b=10000064768$, $u=9662936651771238$, and $v=10000013784295984$. The Chebyshev theta function satisfies
--
--   $$10^6\theta(a)\le u\ \Longrightarrow\ \left(10^6\theta(b)\le v\quad\text{and}\quad\forall x\in[a,b),\ \theta(x)\le x+100000+x/10000\right).$$
--
--   This certifies one contiguous interval of the upper bound used in the finite fourth-power logarithmic theta estimate. The endpoint carry can be passed to the next interval.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Complete finite interval certificate.

import Definitions.Def_dusart_theta_mesh_compact_soundness
import Theorems.Thm_dusart_theta_mesh_generic_group672
import Theorems.Thm_dusart_theta_mesh_generic_group673
import Theorems.Thm_dusart_theta_mesh_generic_group674
import Theorems.Thm_dusart_theta_mesh_generic_group675
import Theorems.Thm_dusart_theta_mesh_generic_group676
import Theorems.Thm_dusart_theta_mesh_generic_group677
import Theorems.Thm_dusart_theta_mesh_generic_group678
import Theorems.Thm_dusart_theta_mesh_generic_group679
import Theorems.Thm_dusart_theta_mesh_generic_group680
import Theorems.Thm_dusart_theta_mesh_generic_group681
import Theorems.Thm_dusart_theta_mesh_generic_group682
import Theorems.Thm_dusart_theta_mesh_generic_group683
import Theorems.Thm_dusart_theta_mesh_generic_group684
import Theorems.Thm_dusart_theta_mesh_generic_group685
import Theorems.Thm_dusart_theta_mesh_generic_group686
import Theorems.Thm_dusart_theta_mesh_generic_group687
import Theorems.Thm_dusart_theta_mesh_generic_group688
import Theorems.Thm_dusart_theta_mesh_generic_group689
import Theorems.Thm_dusart_theta_mesh_generic_group690
import Theorems.Thm_dusart_theta_mesh_generic_group691
import Theorems.Thm_dusart_theta_mesh_generic_group692
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartCompactIntervals
theorem interval7_generic : DusartNumeric.GenericSpec 9663013120 10000064768 9662936651771238 10000013784295984 := by
 intro S step compose
 exact (compose (compose (compose (compose (dusart_theta_mesh_generic_group672 S step @compose) (dusart_theta_mesh_generic_group673 S step @compose)) (compose (dusart_theta_mesh_generic_group674 S step @compose) (compose (dusart_theta_mesh_generic_group675 S step @compose) (dusart_theta_mesh_generic_group676 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group677 S step @compose) (dusart_theta_mesh_generic_group678 S step @compose)) (compose (dusart_theta_mesh_generic_group679 S step @compose) (compose (dusart_theta_mesh_generic_group680 S step @compose) (dusart_theta_mesh_generic_group681 S step @compose))))) (compose (compose (compose (dusart_theta_mesh_generic_group682 S step @compose) (dusart_theta_mesh_generic_group683 S step @compose)) (compose (dusart_theta_mesh_generic_group684 S step @compose) (compose (dusart_theta_mesh_generic_group685 S step @compose) (dusart_theta_mesh_generic_group686 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group687 S step @compose) (compose (dusart_theta_mesh_generic_group688 S step @compose) (dusart_theta_mesh_generic_group689 S step @compose))) (compose (dusart_theta_mesh_generic_group690 S step @compose) (compose (dusart_theta_mesh_generic_group691 S step @compose) (dusart_theta_mesh_generic_group692 S step @compose))))))
theorem interval7 : DusartMeshUpper.Literal.Spec 9663013120 10000064768 9662936651771238 10000013784295984 :=
 DusartProvedBridge.interpret interval7_generic
end DusartCompactIntervals


