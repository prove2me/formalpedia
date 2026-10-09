-- Prove2me | Definitions.Def_RamanujanNotebooks_shared_shiftedFactorial
-- name    : RamanujanNotebooks_shared_shiftedFactorial
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T21:18:11.394082+00:00
-- url     : https://prove2.me/theorems/dbcf8b1c-0857-40ee-a3eb-dbeaf22eb13e
-- title:
--   Ramanujan's Notebooks, shared: shiftedFactorial
-- statement:
--   Shifted factorial (rising factorial) `(a)_k = a (a + 1) ⋯ (a + k - 1)`, `(a)_0 = 1`
--   (Part I, (I7), p. 13; Part III, (0.1), p. 87).
--   The product is the definition for every complex `a`. When `a` is not a nonpositive integer,
--   it also equals `Γ(a+k)/Γ(a)`; at nonpositive integers the finite product supplies the value
--   without interpreting a quotient of Gamma poles.
--   A polynomial in `a`: no domain restriction, no junk; `(a)_k = 0` exactly when `a` is one of
--   `0, -1, …, -(k - 1)`.  (Not the q-Pochhammer symbol `(a)_k = (a; q)_k`, which is `qPoch`.)
--   Reference: `(1)_k = k!`, `(1/2)_2 = 3/4`, `(-3)_5 = 0`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks.

import Mathlib

noncomputable section

namespace RamanujanNotebooks

/-- Shifted factorial (rising factorial) `(a)_k = a (a + 1) ⋯ (a + k - 1)`, `(a)_0 = 1`
(Part I, (I7), p. 13; Part III, (0.1), p. 87).
The product is the definition for every complex `a`. When `a` is not a nonpositive integer,
it also equals `Γ(a+k)/Γ(a)`; at nonpositive integers the finite product supplies the value
without interpreting a quotient of Gamma poles.
A polynomial in `a`: no domain restriction, no junk; `(a)_k = 0` exactly when `a` is one of
`0, -1, …, -(k - 1)`.  (Not the q-Pochhammer symbol `(a)_k = (a; q)_k`, which is `qPoch`.)
Reference: `(1)_k = k!`, `(1/2)_2 = 3/4`, `(-3)_5 = 0`. -/
def shiftedFactorial (a : ℂ) (k : ℕ) : ℂ :=
  ∏ j ∈ Finset.range k, (a + (j : ℂ))

end RamanujanNotebooks

end


