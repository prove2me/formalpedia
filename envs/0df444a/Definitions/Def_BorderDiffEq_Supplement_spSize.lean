-- Prove2me | Definitions.Def_BorderDiffEq_Supplement_spSize
-- name    : BorderDiffEq_Supplement_spSize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:49:06.788708+00:00
-- url     : https://prove2.me/theorems/f61b6bff-5397-4998-b3f2-0266fc637b96
-- title:
--   Size of a polynomial given as a sum of monomials
-- statement:
--   For a polynomial $P=\sum_{m}c_m x^m$ over a commutative semiring, given as a sum of the monomials in its support,
--   $$
--   \mathrm{size}(P)=\sum_{m\in\mathrm{supp}(P)}\bigl(1+\#\{i : x_i \text{ occurs in } x^m\}\bigr),
--   $$
--   one product gate per monomial plus one wire for each variable it uses.
--
--   The paper uses $\mathrm{size}(P_i)$ in the definition of $\Sigma^{[k]}\wedge\Sigma\Pi^{[\delta]}(s)$ without defining it; this measure is at most the usual count of gates and wires of the sum-of-monomials representation, and it bounds both the number of monomials and the number of variables used.
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), §2.2, p.8, item 1 ("polynomials of degree at most δ, given as sums of monomials")

import Mathlib

namespace BorderDiffEq.Supplement

/-- **The size of a polynomial given as a sum of monomials** (Bhat–Dutta–Kaplan–Shpilka–Shringi,
*Demystifying Border of Structured Algebraic Circuits via Differential Equations*, manuscript (STOC
2027 submission), §2.2, p.8, item 1: "polynomials of degree at most δ, given as sums of monomials",
with `size(Pᵢ)` entering the size of `Σ^{[k]} ∧ ΣΠ^{[δ]}(s)`).

**Formalization Note.** The paper does not define `size(P)`. Here
`spSize P = ∑_{m ∈ supp P} (1 + #{variables occurring in m})`: one product gate per monomial of
the support plus one wire for each variable it uses. This is at most the usual count of gates and
wires of the ΣΠ representation, so the classes defined with it contain the paper's; it bounds the
number of monomials and the number of variables used. -/
noncomputable def spSize {K σ : Type} [CommSemiring K] (P : MvPolynomial σ K) : ℕ :=
  ∑ m ∈ P.support, (1 + m.support.card)

end BorderDiffEq.Supplement


