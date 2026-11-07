-- Prove2me | Definitions.Def_PCNonBool_redBool
-- name    : PCNonBool_redBool
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:02.54413+00:00
-- url     : https://prove2.me/theorems/6868e668-ff94-4de0-8acf-be9567693c85
-- title:
--   Multilinear reduction modulo $\{x^2-x\}$
-- statement:
--   For variables ranging over $\{0,1\}$ the range axioms are $x_v^2-x_v$, and lines are represented in $\mathbb F[x]/\langle x_v^2-x_v\rangle$. The **Boolean multilinear reduction** $\mathrm{red}_{01}$ is the $\mathbb F$-linear map
--   $$\prod_v x_v^{k_v}\ \longmapsto\ \prod_{v:\,k_v\ge1} x_v .$$
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §3.4 (quotient-ring convention for range axioms $x^k-x$), p.11 (PDF p.14)

import Mathlib

namespace PCNonBool

/-- Reduction modulo the Boolean range axioms `x² - x` (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §3.4, p.11 (PDF p.14)): the
`F`-linear map sending `∏ x_v^{k_v}` to `∏_{k_v ≥ 1} x_v`, the multilinear representative in
`F[x]/⟨x_v² - x_v : v⟩`. Used for the Boolean encoding FPHP(G)_bool. -/
noncomputable def redBool {σ F : Type*} [Field F] : MvPolynomial σ F →ₗ[F] MvPolynomial σ F :=
  (MvPolynomial.basisMonomials σ F).constr F
    (fun m => MvPolynomial.monomial (m.mapRange (fun k : ℕ => min k 1) (by simp)) (1 : F))

end PCNonBool


