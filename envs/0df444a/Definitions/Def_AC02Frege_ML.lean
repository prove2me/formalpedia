-- Prove2me | Definitions.Def_AC02Frege_ML
-- name    : AC02Frege_ML
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:46:34.047041+00:00
-- url     : https://prove2.me/theorems/e3e20f14-0fc0-40fb-acd4-64d42f55cad4
-- title:
--   Multilinear polynomials over $\mathbb F_2$, multilinearization $\mathrm{ML}$ and monomials $x_A$
-- statement:
--   Throughout, all polynomials are over $\mathbb F_2$. A polynomial is **multilinear** if no variable occurs in any of its monomials with exponent $2$ or more. Every function on a Boolean cube has a unique multilinear polynomial, and a function is identified with it.
--
--   For an arbitrary (formal) polynomial $p$, its **multilinearization** $\mathrm{ML}(p)$ is obtained by replacing every positive power $z^k$, $k\ge1$, of a variable by $z$ itself; $\mathrm{ML}$ is $\mathbb F_2$-linear and does not change the function on the cube. Products used as identities of functions are multilinearized: the product of the functions $p$ and $q$ is $\mathrm{ML}(pq)$.
--
--   For a finite set $A$ of variables, $x_A=\prod_{v\in A}x_v$ is the corresponding multilinear monomial.
--
--   These are the basic objects of every statement of the mission.
--
--   **Formalization Note** Polynomials are `MvPolynomial V (ZMod 2)`. `ML` is the linear map sending the monomial with exponent vector $s$ to the monomial with exponent vector $\min(s,1)$ (coordinatewise).
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds (manuscript dated November 3, 2026, STOC 2027 submission, sha256 88d149fa2bcae702e55a6b72efecda2b4137fd18dca3e23a056c3db5da0ece61), Definition 2.1, p.9; Definition 4.4, p.21

import Mathlib

namespace AC02Frege

open MvPolynomial

/-- A polynomial over `𝔽₂` is **multilinear** if no variable occurs with exponent `≥ 2` in any of
its monomials (Alekseev–Gryaznov–Pitassi–Robere–Shekhovtsov–Tzameret, *Progress on AC0[2]-Frege
Lower Bounds*, manuscript (sha256 88d149fa…), Definition 2.1, p.9). Multilinear polynomials are
the unique representatives of functions on the Boolean cube.

**Formalization Note** `𝔽₂` is `ZMod 2`; polynomials are `MvPolynomial V (ZMod 2)` for a type
of variables `V`. -/
def IsMultilinear {V : Type*} (p : MvPolynomial V (ZMod 2)) : Prop :=
  ∀ s ∈ p.support, ∀ v, s v ≤ 1

/-- The squarefree part of an exponent vector: every positive exponent becomes `1`. -/
noncomputable def sqfree {V : Type*} (s : V →₀ ℕ) : V →₀ ℕ :=
  s.mapRange (fun k => min k 1) (by simp)

/-- **Multilinearization** `ML(p)` (Definition 2.1, p.9): "replacing every positive power of a
variable by that variable". It is the `𝔽₂`-linear map sending each monomial `∏ x_v^{s_v}` to
`∏_{s_v ≥ 1} x_v` (coefficients of monomials with the same image are added).

**Formalization Note** Defined as the linear map that sends the basis monomial with exponent
vector `s` to the monomial with exponent vector `sqfree s` (`Module.Basis.constr` on the monomial
basis), so it is linear by construction. The multilinear product of `p` and `q` is written `ML (p * q)`. -/
noncomputable def ML {V : Type*} : MvPolynomial V (ZMod 2) →ₗ[ZMod 2] MvPolynomial V (ZMod 2) :=
  (basisMonomials V (ZMod 2)).constr (ZMod 2) (fun s => monomial (sqfree s) 1)

/-- The monomial `x_A = ∏_{v ∈ A} x_v` of a finite set `A` of variables (Definition 4.4, p.21). -/
noncomputable def xMon {V : Type*} (A : Finset V) : MvPolynomial V (ZMod 2) :=
  ∏ v ∈ A, X v

end AC02Frege


