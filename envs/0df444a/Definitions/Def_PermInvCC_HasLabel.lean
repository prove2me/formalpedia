-- Prove2me | Definitions.Def_PermInvCC_HasLabel
-- name    : PermInvCC_HasLabel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:23:57.003278+00:00
-- url     : https://prove2.me/theorems/79ed5d4b-9748-47bb-85b2-c816011e9952
-- title:
--   Promised types and their labels
-- statement:
--   A type $T$ is **promised** for $f$ if it is realized by a promised input pair, and its **label** is the value of $f$ on such a pair. The predicate says: *some input pair $(x,y)$ of joint type $T$ has $f(x,y)=b$*.
--
--   For a permutation-invariant $f$ all pairs of one type have the same value, so a promised type has exactly one label. The separation parameter $h_g$ and the decoder of Lemma 3.6 are stated in terms of promised types with labels.
--
--   **Formalization Note** The predicate itself does not assume permutation invariance; the theorems that use it do.
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), p.10

import Mathlib
import Definitions.Def_PermInvCC_PartialFn
import Definitions.Def_PermInvCC_jointType

namespace PermInvCC

/-- The type `T` is **promised with label `b`** for `f`: some promised input pair of joint type `T`
has value `b` (Y. Huang and Z. Ye, arXiv:2609.40116, held version sha256 fe1797dd…, p.10: "A type
is promised if it is realized by a promised input pair. Its label is the common function value on
that type").

**Formalization Note.** For a permutation-invariant `f` all pairs of one type have the same value,
so a promised type has exactly one label; the definition itself does not assume invariance. -/
def HasLabel {n q : ℕ} (f : PartialFn n q) (T : Fin q → Fin q → ℕ) (b : Bool) : Prop :=
  ∃ x y : Fin n → Fin q, jointType x y = T ∧ f x y = some b

end PermInvCC


