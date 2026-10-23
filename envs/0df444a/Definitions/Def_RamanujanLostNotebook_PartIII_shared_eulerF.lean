-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_shared_eulerF
-- name    : RamanujanLostNotebook_PartIII_shared_eulerF
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T02:24:04.789919+00:00
-- url     : https://prove2.me/theorems/9a069136-3fe6-44be-a235-e39cf1a3e87b
-- title:
--   Ramanujan's Lost Notebook Part III, shared: eulerF
-- statement:
--   Ramanujan's `f(-q) = (q; q)_∞`.  In (3.2.3), p. 48, it is introduced as
--   `f(-q, -q^2) = (q; q)_∞`, and in (8.2.9), p. 220, as
--   `f(-q, -q^2) = ∑_{n ∈ ℤ} (-1)^n q^{n(3n-1)/2} = (q; q)_∞` (Euler's pentagonal number
--   theorem); on p. 115 it is set equal to `(q; q)_∞` directly.  The definition
--   here is the product; the series form is the pentagonal number theorem, a theorem about it.
--   The relation `f(-q) = q^{-1/24} η(τ)`, `q = e^{2πiτ}`, of (8.2.9) uses the
--   normalization `q^{1/24} = e^{2πiτ/24}` (and `q ≠ 0`), rather than an arbitrary
--   24th root; it is not part of this definition.
--
--   Argument convention: `eulerF q` is the book's `f(-q)`.  Hence the book's `f(-q^5)` is
--   `eulerF (q ^ 5)`, and the book's one-argument `f(q)` (as in (8.2.13), (8.2.14)) is
--   `eulerF (-q) = (-q; -q)_∞`, which is the two-argument `f(q, -q^2)`.
--   Domain: `‖q‖ < 1`.  Totalization: that of `qPochInf`; `eulerF 0 = 1`.
--   Reference: Taylor expansion `1 - q - q^2 + q^5 + q^7 - q^12 - q^15 + …`;
--   `eulerF (1/5) = 0.76033279587123242010…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_shared_qPochInf

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- Ramanujan's `f(-q) = (q; q)_∞`.  In (3.2.3), p. 48, it is introduced as
`f(-q, -q^2) = (q; q)_∞`, and in (8.2.9), p. 220, as
`f(-q, -q^2) = ∑_{n ∈ ℤ} (-1)^n q^{n(3n-1)/2} = (q; q)_∞` (Euler's pentagonal number
theorem); on p. 115 it is set equal to `(q; q)_∞` directly.  The definition
here is the product; the series form is the pentagonal number theorem, a theorem about it.
The relation `f(-q) = q^{-1/24} η(τ)`, `q = e^{2πiτ}`, of (8.2.9) uses the
normalization `q^{1/24} = e^{2πiτ/24}` (and `q ≠ 0`), rather than an arbitrary
24th root; it is not part of this definition.

Argument convention: `eulerF q` is the book's `f(-q)`.  Hence the book's `f(-q^5)` is
`eulerF (q ^ 5)`, and the book's one-argument `f(q)` (as in (8.2.13), (8.2.14)) is
`eulerF (-q) = (-q; -q)_∞`, which is the two-argument `f(q, -q^2)`.
Domain: `‖q‖ < 1`.  Totalization: that of `qPochInf`; `eulerF 0 = 1`.
Reference: Taylor expansion `1 - q - q^2 + q^5 + q^7 - q^12 - q^15 + …`;
`eulerF (1/5) = 0.76033279587123242010…`. -/
def eulerF (q : ℂ) : ℂ :=
  qPochInf q q

end RamanujanLostNotebook.PartIII

end


