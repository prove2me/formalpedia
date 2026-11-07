-- Prove2me | Definitions.Def_PCNonBool_pcSize
-- name    : PCNonBool_pcSize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:04.32853+00:00
-- url     : https://prove2.me/theorems/18a02299-7538-4c44-a54c-d00153821bdb
-- title:
--   Monomial size of a refutation
-- statement:
--   The **size** of a polynomial $p$, $\mathrm{size}(p)$, is its number of monomials when written as a linear combination of distinct monomials. The **size** of a refutation $\pi=(p_1,\dots,p_\tau)$ is
--   $$|\pi|=\sum_{k=1}^{\tau}\mathrm{size}(p_k).$$
--   Since lines are kept in reduced (multilinear) form, sizes are those of the multilinear representatives.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §3.4 (monomial size), p.11 (PDF p.14)

import Mathlib

namespace PCNonBool

/-- The (monomial) size of a sequence of polynomials: the sum over the lines of the number of
monomials of each line (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §3.4, p.11 (PDF p.14): "The size of a polynomial calculus
refutation π is the sum of the sizes of the polynomials in it"). Lines are in reduced form, so
this counts the monomials of the multilinear representatives. -/
noncomputable def pcSize {σ F : Type*} [Field F] (π : List (MvPolynomial σ F)) : ℕ :=
  (π.map fun p => p.support.card).sum

end PCNonBool


