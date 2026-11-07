-- Prove2me | Definitions.Def_NoPerfectRandComp_witVerifies
-- name    : NoPerfectRandComp_witVerifies
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:44:52.840626+00:00
-- url     : https://prove2.me/theorems/5fe1cf59-0bcd-4196-9a60-b957de5412f9
-- title:
--   The exact witness verifier for the core
-- statement:
--   Given a core input $X$ (a $u\times u$ array of seed inputs), a proposed value $z$ and a witness $w \in W_q$, the **exact verifier** reads the $u$ indicated seeds in full:
--   1. a value-one witness $w = \mathrm{col}$ verifies $z = 1$ when every seed $(i, \mathrm{col}(i))$ is promised with value one;
--   2. a value-zero witness $w = i$ verifies $z = 0$ when every seed $(i, j)$ of row $i$ is promised with value zero;
--   3. a witness of the wrong type is rejected.
--
--   Soundness holds on every Boolean input: a verified witness forces the core to be defined with the proposed value.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §4.2, p.13

import Mathlib
import Definitions.Def_NoPerfectRandComp_seed
import Definitions.Def_NoPerfectRandComp_Wit

namespace NoPerfectRandComp

/-- The exact witness verifier for the core (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §4.2, p.13): given a core input `X`, a
proposed value `z` and a witness `w`, the verifier reads the `u` indicated seeds in full. A
value-one witness `col` verifies when every seed `(i, col i)` is promised with value one; a
value-zero witness `i` verifies when every seed `(i, j)` of row `i` is promised with value zero.
A witness of the wrong type is rejected. -/
def witVerifies (k r u : ℕ) (X : Fin u × Fin u × SeedIdx k → Bool) : Bool → Wit u → Prop
  | true, Sum.inl col => ∀ i, (fun t => X (i, col i, t)) ∈ (seed k r).dom ∧
      (seed k r).val (fun t => X (i, col i, t)) = true
  | false, Sum.inr i => ∀ j, (fun t => X (i, j, t)) ∈ (seed k r).dom ∧
      (seed k r).val (fun t => X (i, j, t)) = false
  | true, Sum.inr _ => False
  | false, Sum.inl _ => False

end NoPerfectRandComp


