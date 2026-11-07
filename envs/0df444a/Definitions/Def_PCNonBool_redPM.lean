-- Prove2me | Definitions.Def_PCNonBool_redPM
-- name    : PCNonBool_redPM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:02.173872+00:00
-- url     : https://prove2.me/theorems/393a031a-4c72-49e7-96cc-c0f5887be85e
-- title:
--   Multilinear reduction modulo $\{x^2-1\}$
-- statement:
--   For variables ranging over $\{\pm1\}$ the range axioms are $x_v^2-1$. The paper represents every line of a refutation in the quotient ring $\mathbb F[x]/\langle x_v^2-1\rangle$, so that every variable occurs with individual degree at most $1$. The **multilinear reduction** $\mathrm{red}_{\pm}$ is the $\mathbb F$-linear map
--   $$\prod_v x_v^{k_v}\ \longmapsto\ \prod_v x_v^{\,k_v \bmod 2},$$
--   which sends a polynomial to its unique multilinear representative modulo $\langle x_v^2-1\rangle$. The size of a line is the number of monomials of this representative.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §3.4 (quotient-ring convention for range axioms $x^k-1$), p.11 (PDF p.14)

import Mathlib

namespace PCNonBool

/-- Reduction modulo the range axioms `x² - 1` of every variable (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §3.4, p.11
(PDF p.14)): the `F`-linear map sending the monomial `∏ x_v^{k_v}` to `∏ x_v^{k_v mod 2}`. Its
value on `p` is the unique multilinear representative of `p` in the quotient ring
`F[x]/⟨x_v² - 1 : v⟩`, in which "we always think of the lines in a polynomial calculus
refutation" (p.11). -/
noncomputable def redPM {σ F : Type*} [Field F] : MvPolynomial σ F →ₗ[F] MvPolynomial σ F :=
  (MvPolynomial.basisMonomials σ F).constr F
    (fun m => MvPolynomial.monomial (m.mapRange (fun k : ℕ => k % 2) (by simp)) (1 : F))

end PCNonBool


