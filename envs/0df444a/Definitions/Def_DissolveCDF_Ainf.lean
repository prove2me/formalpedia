-- Prove2me | Definitions.Def_DissolveCDF_Ainf
-- name    : DissolveCDF_Ainf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:30:16.544727+00:00
-- url     : https://prove2.me/theorems/dcea082d-3577-41c5-b8a0-9c5e08c73dc4
-- title:
--   §2.1 — $\mathcal A^\infty(x)=\lim_k\mathcal A^k(x)$
-- statement:
--   For $\mathcal A:\mathbb R^n\to\mathbb R^n$ and $x\in\mathbb R^n$, let $\mathcal A^0(x):=x$ and $\mathcal A^k(x):=\mathcal A(\mathcal A^{k-1}(x))$ be the $k$-fold composition, and
--
--   $$
--   \mathcal A^\infty(x):=\lim_{k\to+\infty}\mathcal A^k(x).
--   $$
--
--   Lemma 3.4 shows the limit exists near $\mathcal M$ and is feasible; it is the post-processing step of the constraint dissolving approach.
--
--   **Formalization Note** The limit is Mathlib's `limUnder`; it is the paper's $\mathcal A^\infty(x)$ only when the iterates converge, which the statements that use it assert separately.
-- source:
--   Xiao, Liu & Toh, Dissolving Constraints for Riemannian Optimization, arXiv:2203.10319v3, §2.1, p.5

import Mathlib
open Filter

namespace DissolveCDF

/-- Xiao, Liu & Toh, *Dissolving Constraints for Riemannian Optimization*, arXiv:2203.10319v3, §2.1 (p.5): `A^∞(x) := lim_{k→+∞} A^k(x)`, with `A^0(x) := x` and `A^k` the
`k`-fold composition of `A`.

**Formalization Note** The limit is `limUnder atTop (fun k => A^[k] x)`. It is the paper's
`A^∞(x)` only when the iterates converge; statements that use `Ainf` assert that convergence
separately (Lemma 3.4). -/
noncomputable def Ainf {n : ℕ} (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  limUnder atTop (fun k : ℕ => A^[k] x)

end DissolveCDF


