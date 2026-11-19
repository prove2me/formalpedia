-- Prove2me | Definitions.Def_KoanaKPaths_Runtime_LiftNative
-- name    : KoanaKPaths_Runtime_LiftNative
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T07:50:36.877733+00:00
-- url     : https://prove2.me/theorems/c5a959a1-19ad-4994-bf1d-c4e947a78650
-- title:
--   Embedding closed native programs
-- statement:
--   A closed native statement has no procedure calls. This bundle defines its recursive embedding into the same instruction language with an arbitrary number of available procedures, preserving primitive operations, sequential composition, branches, and loops. The impossible closed-call case is eliminated by the empty finite type.
--
--   $$
--   \operatorname{lift}(p;q)=\operatorname{lift}(p);\operatorname{lift}(q).
--   $$
--
--   The embedding lets arithmetic, parsing, and array primitives appear inside the estimator that has one recursive exterior procedure.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/LiftNative.lean; source snapshot SHA-256 896f0585327babe04e0087e4638f66793842015e22cd6a534e937770abb8c33c.

import Definitions.Def_IntMul_SS_Defs2
import Mathlib
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

namespace KoanaKPaths.Machine
open NLogN
variable {S P : ℕ}

def liftClosed : IStmt S 0 → IStmt S P
  | .skip => .skip
  | .op o => .op o
  | .seq p q => .seq (liftClosed p) (liftClosed q)
  | .ite i f p q => .ite i f (liftClosed p) (liftClosed q)
  | .loop i f p => .loop i f (liftClosed p)
  | .call j => Fin.elim0 j





end KoanaKPaths.Machine

end


