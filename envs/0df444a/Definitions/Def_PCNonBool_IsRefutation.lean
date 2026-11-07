-- Prove2me | Definitions.Def_PCNonBool_IsRefutation
-- name    : PCNonBool_IsRefutation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:28:01.050507+00:00
-- url     : https://prove2.me/theorems/e2f44f6b-c8b5-4ea8-8787-db403b2998de
-- title:
--   Polynomial calculus refutation
-- statement:
--   A **polynomial calculus refutation** of a set $P$ of polynomials is a polynomial calculus derivation from $P$ in which the constant polynomial $1$ is derived. Since $1$ has no common root, a refutation certifies that the polynomials of $P$ have no common root.
--
--   **Formalization Note** The sequence is required to contain the line $1$ rather than to end in it; truncating after the first $1$ gives a refutation in the paper's sense of no larger size.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §3.4 (refutation), p.11 (PDF p.14)

import Mathlib
import Definitions.Def_PCNonBool_IsDerivation

namespace PCNonBool

/-- A polynomial calculus refutation of `P` (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §3.4, p.11 (PDF p.14)): a derivation
(`IsDerivation`) that contains the constant polynomial `1`.

**Formalization Note** The paper's refutation is "a derivation of the constant polynomial 1",
i.e. it ends in `1`. Requiring that `1` occurs as a line is equivalent for size lower bounds
(cut the sequence after its first `1`), and is closed under PigeonSplit, which maps the line `1`
to the two lines `1, 0`. -/
def IsRefutation {σ F : Type*} [Field F] (red : MvPolynomial σ F →ₗ[F] MvPolynomial σ F)
    (P : Set (MvPolynomial σ F)) (π : List (MvPolynomial σ F)) : Prop :=
  IsDerivation red P π ∧ (1 : MvPolynomial σ F) ∈ π

end PCNonBool


