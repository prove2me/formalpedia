-- Prove2me | Definitions.Def_OAI_LinearAlgebra_Hadamard_Polynomials
-- name    : OAI_LinearAlgebra_Hadamard_Polynomials
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T18:16:03.35599+00:00
-- url     : https://prove2.me/theorems/26731bd9-4ae5-4503-9ac4-6af5fe1da86f
-- title:
--   Elementary symmetric functions of a vector in $\mathbb{C}^6$
-- statement:
--   Index the coordinates of $\mathbb{C}^{6}$ by $\{0,1,\dots,5\}$ and let $v=(v_0,\dots,v_5)\in\mathbb{C}^{6}$. The file defines the elementary symmetric functions of the six entries of $v$: for every natural number $m$,
--   $$e_m(v)=\sum_{\substack{S\subseteq\{0,\dots,5\}\\ |S|=m}}\ \prod_{i\in S} v_i .$$
--   This is the $m$-th elementary symmetric polynomial evaluated at $v_0,\dots,v_5$, with the entries counted with multiplicity (equal entries at different positions are not merged). In particular $e_0(v)=1$, $e_1(v)=v_0+\dots+v_5$, $e_6(v)=v_0v_1\cdots v_5$, and $e_m(v)=0$ for $m>6$.
--
--   By Vieta's formulas these are, up to sign, the coefficients of the monic polynomial with roots $v_0,\dots,v_5$,
--   $$\prod_{i=0}^{5}(X-v_i)=\sum_{m=0}^{6}(-1)^{m}e_m(v)\,X^{6-m},$$
--   and Newton's identities relate them to the power sums $p_m(v)=\sum_i v_i^{m}$. In the study of $6\times 6$ complex Hadamard matrices, $v$ is typically the vector of row ratios $H_{ik}\overline{H_{jk}}$ of two rows; the functions $e_m$ translate the vanishing of power sums of these ratios, which comes from orthogonality relations, into vanishing of polynomial coefficients and back. Here they are used to show that six unimodular numbers with $p_1=p_2=0$ also have $p_4=0$.
--
--   **Formalization Note** `elementary v m` is `Multiset.esymm` of the multiset `Finset.univ.val.map v`, the image of `Finset.univ` under `v : Index → ℂ` with `Index = Fin 6` kept as a multiset; the values for $m=0$ and $m>6$ come from this definition (the empty product is $1$, and there are no subsets of size larger than $6$).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/Hadamard/Polynomials.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/Hadamard/Polynomials.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HadamardCubeFiber mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HadamardCubeFiber

namespace OAI

/-! Fourier kernel identities and symmetric polynomials of row ratios. -/

open scoped BigOperators Matrix

namespace HadamardSix

noncomputable def elementary (v : Index → ℂ) (k : ℕ) : ℂ :=
  (Finset.univ.val.map v).esymm k

end HadamardSix

end OAI


