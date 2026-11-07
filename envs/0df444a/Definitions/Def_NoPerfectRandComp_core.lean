-- Prove2me | Definitions.Def_NoPerfectRandComp_core
-- name    : NoPerfectRandComp_core
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:44:36.756196+00:00
-- url     : https://prove2.me/theorems/5813d46b-e4ef-4d97-a495-48c13adc3616
-- title:
--   The partial core $S_q$
-- statement:
--   The **partial core** $S_q$ is a $u \times u$ array of seed inputs evaluated by the partial AND–OR rule:
--   $$
--   S_q = 1 \ :\ \text{every row contains a promised seed of value } 1; \qquad S_q = 0 \ :\ \text{some row consists entirely of promised seeds of value } 0 .
--   $$
--   All other inputs are outside its domain; seeds not needed for a witness need not satisfy their promise. With $(k, r, u) = (k_q, r_q, u_q)$ this is $S_q$.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §4.2, p.13

import Mathlib
import Definitions.Def_NoPerfectRandComp_seed
import Definitions.Def_NoPerfectRandComp_andOr

namespace NoPerfectRandComp

/-- The partial core `S_q` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §4.2, p.13): a `u × u` array of seed inputs under the
partial AND–OR rule. `S_q = 1` when every row contains a promised seed of value one; `S_q = 0`
when some row consists entirely of promised seeds of value zero; all other inputs are outside the
domain. Generic in `(k, r, u)`; `S_q` is `core (k_q) (r_q) (u_q)`. -/
noncomputable def core (k r u : ℕ) : PartialFn (Fin u × Fin u × SeedIdx k) :=
  andOr u (fun _ => seed k r)

end NoPerfectRandComp


