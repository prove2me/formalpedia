-- Prove2me | Definitions.Def_XOSMax_Supplement_ConditionStar
-- name    : XOSMax_Supplement_ConditionStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:31:56.032002+00:00
-- url     : https://prove2.me/theorems/aeba6e99-ecf6-59db-8712-a1a60bfc3aeb
-- title:
--   Condition $(*)$ for exact XOS maximization
-- statement:
--   A width-$k$ representation $w_1,\ldots,w_k$ of $f$ satisfies **condition $(*)$** when, for every ground element $v$ and every clause $i$,
--   $$
--   w_i(v)=f(\{v\})\quad\text{or}\quad w_i(v)\le0.
--   $$
--   The condition belongs to a representation, since one XOS function may admit several representations.
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, Theorem 13, pp.8-9, condition (*)

import Mathlib

namespace XOSMax.Supplement

/-- Condition `(∗)` on a width-`k` representation: every singleton clause value either attains the
XOS value or is nonpositive (Filmus, Kawase, Kobayashi & Yamaguchi, arXiv:1811.09045v3,
Theorem 13, pp.8–9).

**Formalization Note** The condition belongs to the chosen representation `w`, not merely to `f`:
one XOS function may have several representations. The ground set is the whole finite type. -/
def ConditionStar {E : Type} [Fintype E] {k : ℕ} (w : Fin k → E → ℝ)
    (f : Finset E → ℝ) : Prop :=
  ∀ v : E, ∀ i : Fin k, w i v = f {v} ∨ w i v ≤ 0

end XOSMax.Supplement


