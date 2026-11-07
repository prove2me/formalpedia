-- Prove2me | Definitions.Def_PCNonBool_qset
-- name    : PCNonBool_qset
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:03.983414+00:00
-- url     : https://prove2.me/theorems/0d5e0044-f946-4f67-bcaa-e7e5637c8257
-- title:
--   Quadratic set $\mathrm{Qset}(p)$
-- statement:
--   The **Qset** (quadratic set) of a polynomial $p$ is the set of all unordered pairs of monomials of $p$. It is extended to a set of polynomials by union.
--
--   **Formalization Note** Diagonal pairs $\{m,m\}$ are included; they have pairwise pigeon degree $0$.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Definition 4.8 (Qsets), p.15 (PDF p.18)

import Mathlib

namespace PCNonBool

/-- The Qset (quadratic set) of a polynomial `p`: all unordered pairs of monomials of `p`
(Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Definition 4.8, p.15 (PDF p.18)).

**Formalization Note** `Finset.sym2` includes the diagonal pairs `(m, m)`; their product is a
square, which has pairwise pigeon degree `0`, so they never enter `PPHigh_D` for `D > 0`. -/
noncomputable def qset {σ F : Type*} [Field F] [DecidableEq σ] (p : MvPolynomial σ F) :
    Finset (Sym2 (σ →₀ ℕ)) :=
  p.support.sym2

end PCNonBool


