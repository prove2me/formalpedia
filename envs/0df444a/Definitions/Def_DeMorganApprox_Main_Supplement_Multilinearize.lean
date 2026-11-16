-- Prove2me | Definitions.Def_DeMorganApprox_Main_Supplement_Multilinearize
-- name    : DeMorganApprox_Main_Supplement_Multilinearize
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:44:44.67281+00:00
-- url     : https://prove2.me/theorems/f66fd1c7-2d1b-4df5-8242-e0757c5bea8d
-- title:
--   §3.1 — multilinearization of a real polynomial on the Boolean cube
-- statement:
--   Let $P$ be a real polynomial in the variables $(x_i)_{i\in\sigma}$, written in the monomial basis as $P=\sum_{s} p_s \prod_i x_i^{s_i}$. Its **multilinearization** $\operatorname{ml}(P)$ is obtained by replacing every monomial $\prod_i x_i^{s_i}$ with $\prod_{i:\,s_i\ge 1} x_i$, i.e. lowering every positive exponent to $1$, and keeping the coefficient:
--
--   $$
--   \operatorname{ml}(P)\;=\;\sum_{s} p_s \prod_{i:\,s_i\ge1} x_i .
--   $$
--
--   Coefficients of monomials that become identical are added. Since $x_i^k=x_i$ for $x_i\in\{0,1\}$ and $k\ge1$, $\operatorname{ml}(P)$ agrees with $P$ on the Boolean cube, and it is multilinear.
--
--   The paper's coefficient $\ell_1$-norm $\|P\|_1$ (§3.1) is the sum of the absolute values of the coefficients of $P$ in the $\{0,1\}$-monomial basis *after* multilinearization on the Boolean cube, i.e. $\|P\|_1=\sum_T|\operatorname{ml}(P)_T|$. With the published coefficient sum `coeffL1` of the base mission's definitions, this is `coeffL1 (multilinearize P)`; for a polynomial that is already multilinear the two coincide.
--
--   **Formalization Note** The exponent vector $s$ is a finitely supported map $\sigma\to\mathbb N$, and the new exponent vector is $s$ with every entry replaced by $\min(s_i,1)$.
-- source:
--   Yichuan Wang, STOC 2027 submission #76 (October 2026), §3.1 Notation (definition of the coefficient ℓ1-norm, "after multilinearization on the Boolean cube"), PDF p. 10 (printed p. 8), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/76.pdf

import Mathlib
import Definitions.Def_DeMorganApprox_Main_Basic

namespace DeMorganApprox.Main.Supplement

/-- Multilinearization on the Boolean cube (§3.1, PDF p. 10): every monomial `∏ xᵢ^{sᵢ}` is
replaced by `∏_{sᵢ ≥ 1} xᵢ` (exponent `min sᵢ 1`), keeping its coefficient; coefficients of
monomials that become identical add up. The result agrees with `P` on `{0,1}^σ`. -/
noncomputable def multilinearize {σ : Type} (P : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  ∑ s ∈ P.support, MvPolynomial.monomial (s.mapRange (fun k => min k 1) (by simp)) (P.coeff s)

end DeMorganApprox.Main.Supplement


