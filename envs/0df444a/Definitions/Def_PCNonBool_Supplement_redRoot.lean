-- Prove2me | Definitions.Def_PCNonBool_Supplement_redRoot
-- name    : PCNonBool_Supplement_redRoot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:24:50.209654+00:00
-- url     : https://prove2.me/theorems/805555ed-599a-4b21-848d-140bac4e4cb8
-- title:
--   Reduction modulo the range axioms $x_v^k-1$
-- statement:
--   For an integer $k\ge1$, the **reduction modulo $x_v^k-1$** is the $\mathbb F$-linear map on $\mathbb F[x_v : v\in V]$ that sends a monomial $\prod_v x_v^{a_v}$ to $\prod_v x_v^{a_v \bmod k}$. Its value on a polynomial $p$ is the unique representative of $p$ in the quotient ring
--   $$\mathbb F[x_v : v\in V]\,/\,\langle x_v^k-1 : v\in V\rangle$$
--   in which every variable has individual degree at most $k-1$.
--
--   For lower bounds the paper always represents the lines of a polynomial calculus refutation in this quotient ring when the variables range over the $k$-th roots of unity; this map is that representation, and size is counted on its output. For $k=2$ it is the base mission's multilinearization modulo $x^2-1$.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §3.4, p.11 (PDF p.14); §6, (50a), p.33 (PDF p.36)

import Mathlib

namespace PCNonBool.Supplement

/-- Reduction modulo the range axioms `x_v^k - 1` of every variable (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §3.4, p.11 (PDF p.14),
used for `Col(G, k)` in §6, p.33 (PDF p.36)): the `F`-linear map sending the monomial
`∏ x_v^{a_v}` to `∏ x_v^{a_v mod k}`. Its value on `p` is the unique representative of `p` in
the quotient ring `F[x]/⟨x_v^k - 1 : v⟩` whose individual degrees are at most `k - 1`, the ring in
which "we always think of the lines in a polynomial calculus refutation" for these lower bounds
(p.11).

**Formalization Note** For `k = 2` this is the base mission's `PCNonBool.redPM`. It is only used
with `k ≥ 3`. -/
noncomputable def redRoot {σ F : Type*} [Field F] (k : ℕ) :
    MvPolynomial σ F →ₗ[F] MvPolynomial σ F :=
  (MvPolynomial.basisMonomials σ F).constr F
    (fun m => MvPolynomial.monomial (m.mapRange (fun a : ℕ => a % k) (by simp)) (1 : F))

end PCNonBool.Supplement


