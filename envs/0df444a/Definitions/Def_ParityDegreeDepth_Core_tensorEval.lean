-- Prove2me | Definitions.Def_ParityDegreeDepth_Core_tensorEval
-- name    : ParityDegreeDepth_Core_tensorEval
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-27T03:57:22.649849+00:00
-- url     : https://prove2.me/theorems/e42911c8-0d29-5711-ae7e-3e5abc2f455f
-- title:
--   Multilinear form on $R^n$ with coefficient tensor over $\mathbb F_2$
-- statement:
--   Let $R$ be a commutative $\mathbb F_2$-algebra (for instance $\mathbb F_2$ itself, a polynomial ring $\mathbb F_2[t]$, or a rational function field $\mathbb F_2(t)$), and let $c:[n]^d\to\mathbb F_2$ be a coefficient tensor. The **evaluation** of the $d$-linear form with coefficients $c$ at vectors $x_1,\dots,x_d\in R^n$ is
--
--   $$
--   T_c(x_1,\dots,x_d)\;=\;\sum_{a:[d]\to[n]} c(a)\,\prod_{j=1}^{d} x_j\big(a(j)\big)\in R .
--   $$
--
--   This is the standard way of extending a multilinear form over $\mathbb F_2$ to any field (or ring) extension "by the same coefficients", as done throughout §§2–3 and Appendix A.1 of the source: the top finite-difference form $T=\Delta^d p$ of a Boolean polynomial is evaluated at formal anchor vectors (Theorem 3.5) and at vectors over rational function fields (Lemma 3.7). Every ring homomorphism of $\mathbb F_2$-algebras commutes with $T_c$, so polynomial identities proved for $T_c$ survive specialisation.
--
--   **Formalization Note** The coefficient $c(a)\in\mathbb F_2$ is mapped into $R$ by `algebraMap (ZMod 2) R`; vectors are functions `Fin n → R`.
-- source:
--   Zhang, Parity Decision Trees of Depth O(4^d log ||f^||_1) for Boolean Functions f of F2-Degree d, STOC 2027 submission #798, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, §2 (Notation: 'Forms extend to larger fields using the same coefficients') and Appendix A.1 ('Vector spaces and extension of scalars'), pp. 4, 15

import Mathlib

namespace ParityDegreeDepth.Core

/-- Evaluation of the `d`-linear form on `R^n` whose coefficient tensor is `c` (with coefficients in
`𝔽₂`, mapped into the `𝔽₂`-algebra `R`):
`T(x₁, …, x_d) = ∑_{a : [d] → [n]} c(a) · ∏_j x_j(a_j)`.
This is how the source extends a form over `𝔽₂` to any field extension "by the same coefficients"
(Zhang, STOC 2027 submission #798, §2 and Appendix A.1). -/
noncomputable def tensorEval {R : Type*} [CommSemiring R] [Algebra (ZMod 2) R] {d n : ℕ}
    (c : (Fin d → Fin n) → ZMod 2) (x : Fin d → Fin n → R) : R :=
  ∑ a : Fin d → Fin n, algebraMap (ZMod 2) R (c a) * ∏ j, x j (a j)

end ParityDegreeDepth.Core


