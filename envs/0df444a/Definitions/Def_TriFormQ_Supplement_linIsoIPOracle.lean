-- Prove2me | Definitions.Def_TriFormQ_Supplement_linIsoIPOracle
-- name    : TriFormQ_Supplement_linIsoIPOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:59:15.416518+00:00
-- url     : https://prove2.me/theorems/cbe2a117-d715-4dd9-abf2-0d36088aa0da
-- title:
--   Linear Isomorphism-$\mathrm{IP}_q$ oracle function $(x,y)\mapsto \mathrm{IP}_q(Ax,y)$
-- statement:
--   Let $A\in\mathbb F_q^{n\times n}$ and write $\mathrm{IP}_q(u,v)=\sum_{i=1}^n u_iv_i$ for the standard inner product on $\mathbb F_q^n$. In the **Linear Isomorphism-$\mathrm{IP}_q$ problem** (Definition 4) the function $f(x,y)=\mathrm{IP}_q(Ax,y)$ on $\mathbb F_q^{2n}$ is hidden, under the promise that $\mathrm{rk}(A)=n$ or $\mathrm{rk}(A)=n-1$, and the task is to decide which holds. A query is
--
--   $$O_{LI}:\ |x\rangle|y\rangle|b\rangle|w\rangle\ \mapsto\ |x\rangle|y\rangle|b+\mathrm{IP}_q(Ax,y)\rangle|w\rangle,\qquad x,y\in\mathbb F_q^n,\ b\in\mathbb F_q .$$
--
--   This definition is the function $(x,y)\mapsto\mathrm{IP}_q(Ax,y)$ that $O_{LI}$ evaluates.
--
--   It is the oracle of the source problem in the reduction of Theorem 10.
--
--   **Formalization Note** $\mathrm{IP}_q(u,v)$ is `u ⬝ᵥ v` (the paper does not define $\mathrm{IP}_q$; bilinearity is the only property it uses), and the input $(x,y)\in\mathbb F_q^{2n}$ is a pair in $\mathbb F_q^n\times\mathbb F_q^n$. An adaptive query algorithm with this oracle function queries `QAlgorithms.xorOracle (linIsoIPOracle A)`, the permutation matrix of $((x,y),b)\mapsto((x,y),b+\mathrm{IP}_q(Ax,y))$, i.e. $O_{LI}$.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Definition 4, p.41 (PDF p.44)

import Definitions.Def_TriFormQ_TriForm
open Matrix

namespace TriFormQ.Supplement

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Definition 4, p.41 (PDF p.44):
"Let f : 𝔽_q^{2n} → 𝔽_q be a function such that there is a matrix A ∈ 𝔽_q^{n×n} such that
f(x, y) = IP_q(Ax, y) for all x, y ∈ 𝔽_q^n … A quantum query for the Linear Isomorphism-IP_q
problem can be written as O_LI : |x⟩|y⟩|b⟩|w⟩ ↦ |x⟩|y⟩|b + IP_q(Ax, y)⟩|w⟩, thinking of x, y ∈ 𝔽_q^n
as the query input, b ∈ 𝔽_q as the query output, and w as the workspace." The function
`(x, y) ↦ IP_q(Ax, y)` that `O_LI` evaluates.

**Formalization Note.** `IP_q(u, v) = Σ_{i ∈ [n]} u_i v_i` is the standard inner product of
`𝔽_q^n` (the paper does not define it; its bilinearity is the only property it uses), written
`u ⬝ᵥ v`. The input `(x, y) ∈ 𝔽_q^{2n}` is the pair `(x, y) : 𝔽_q^n × 𝔽_q^n`. An adaptive algorithm
with oracle function `linIsoIPOracle A` queries `QAlgorithms.xorOracle (linIsoIPOracle A)`, the
permutation matrix of `((x, y), b) ↦ ((x, y), b + IP_q(Ax, y))` over the additive group of `𝔽_q`,
i.e. `O_LI`; the workspace is that of `QAlgorithms.QueryAlg`. -/
def linIsoIPOracle {F : Type} [Field F] {n : ℕ} (A : Matrix (Fin n) (Fin n) F) :
    Vec F n × Vec F n → F :=
  fun p => (A *ᵥ p.1) ⬝ᵥ p.2

end TriFormQ.Supplement


