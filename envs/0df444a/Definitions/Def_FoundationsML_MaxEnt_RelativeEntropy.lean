-- Prove2me | Definitions.Def_FoundationsML_MaxEnt_RelativeEntropy
-- name    : FoundationsML_MaxEnt_RelativeEntropy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:11:23.041498+00:00
-- url     : https://prove2.me/theorems/f6ca504f-abd5-43e7-8c8b-416e7ecf3612
-- title:
--   Relative entropy (KL divergence)
-- statement:
--   **§12.1, p. 296, PDF p. 313 onward.** For $p,q:X\to\mathbb R$ over a finite set $X$,
--   $D(p\|q) = \sum_{x\in X} p(x)\log\frac{p(x)}{q(x)}$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, §12.1, p. 296 (PDF p. 313)

import Mathlib

namespace FoundationsML.MaxEnt

/-- The relative entropy (KL divergence) `D(p‖q)` between two functions `p, q : X → ℝ` over a
finite set `X` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, used from §12.1, p. 296, PDF p. 313 onward): `D(p‖q) = ∑_{x∈X} p(x) log(p(x)/q(x))`.

**Formalization Note.** As is standard, `0·log(0/q(x)) = 0` is handled automatically by Lean's
convention `Real.log 0 = 0` (so the `x`-th summand is `0·0 = 0` whenever `p x = 0`), matching
the usual information-theoretic convention `0 log 0 := 0`. -/
noncomputable def RelativeEntropy {X : Type*} [Fintype X] (p q : X → ℝ) : ℝ :=
  ∑ x, p x * Real.log (p x / q x)

end FoundationsML.MaxEnt


