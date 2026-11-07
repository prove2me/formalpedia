-- Prove2me | Definitions.Def_PCNonBool_restrict
-- name    : PCNonBool_restrict
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:03.242984+00:00
-- url     : https://prove2.me/theorems/5a8935a1-cd7e-4208-bfdc-10e355e219c0
-- title:
--   Partial variable restriction $p\restriction\rho$
-- statement:
--   A **restriction** $\rho$ is a partial assignment of field values to variables. The restricted polynomial $p\restriction\rho$ is obtained from $p$ by substituting $\rho(x)$ for every assigned variable $x$ and leaving the other variables untouched. Restricting by $\pm1$ values maps multilinear polynomials to multilinear polynomials.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Definition 5.8 and Algorithm 1 (restrictions), pp.28, 30 (PDF pp.31, 33)

import Mathlib

namespace PCNonBool

/-- The restriction `p↾ρ` of a polynomial by a partial assignment `ρ` (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Definition 5.8,
p.28 (PDF p.31), and Algorithm 1, p.30 (PDF p.33)): every variable `v` with `ρ v = some a` is
replaced by the constant `a`; the other variables are left untouched. -/
noncomputable def restrict {σ F : Type*} [Field F] (ρ : σ → Option F) :
    MvPolynomial σ F →ₐ[F] MvPolynomial σ F :=
  MvPolynomial.aeval (fun v => match ρ v with
    | some a => MvPolynomial.C a
    | none => MvPolynomial.X v)

end PCNonBool


