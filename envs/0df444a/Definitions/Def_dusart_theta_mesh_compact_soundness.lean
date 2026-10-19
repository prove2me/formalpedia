-- Prove2me | Definitions.Def_dusart_theta_mesh_compact_soundness
-- name    : dusart_theta_mesh_compact_soundness
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-17T00:47:10.685885+00:00
-- url     : https://prove2.me/theorems/e4a6a6aa-a511-4b89-82bc-27db2a004d75
-- title:
--   Soundness of compact finite theta interval certificates
-- statement:
--   For natural endpoints and scaled carries $a,b,u,v$, a universal numerical interval certificate implies the following Chebyshev theta bound: $$10^6\theta(a)\le u\ \Longrightarrow\ \bigl(10^6\theta(b)\le v\ \text{ and }\ \forall x\in[a,b),\ \theta(x)\le x+100000+x/10000\bigr).$$
--
--   This module also gives the concrete first interval from 100000000 to 102097152 with carries 99989691935170 and 102087562006788. It provides the interpretation used to turn verified numerical certificates into the finite upper estimate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Finite-certificate soundness formalization.

import Definitions.Def_dusart_theta_mesh_soundness
import Theorems.Thm_dusart_theta_mesh_generic_group000
set_option maxHeartbeats 0
namespace DusartProvedBridge
theorem first_group : DusartMeshUpper.Literal.Spec 100000000 102097152 99989691935170 102087562006788 :=
 DusartNumericBridge.generic_to_theta dusart_theta_mesh_generic_group000
theorem interpret {a b u v : Nat} (h : DusartNumeric.GenericSpec a b u v) : DusartMeshUpper.Literal.Spec a b u v :=
 DusartNumericBridge.generic_to_theta h
end DusartProvedBridge


