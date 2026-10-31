-- Prove2me | Definitions.Def_DissolveCDF_betaX
-- name    : DissolveCDF_betaX
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:34:24.237003+00:00
-- url     : https://prove2.me/theorems/e1e866eb-2cce-44d8-9ee6-cbe0d77d7464
-- title:
--   Definition 2.9 — the penalty threshold $\beta_x$
-- statement:
--   For $x\in\mathcal M$,
--
--   $$
--   \beta_x:=\max\Big\{\frac{128L_{x,g}(M_{x,A}+1)^2}{\sigma_{x,c}^2},\ \frac{64M_{x,f}(M_{x,A}+1)L_{x,b}}{\sigma_{x,c}^3},\ \frac{16M_{x,f}L_{x,A}(2M_{x,A}+1)}{\sigma_{x,c}^2}\Big\}.
--   $$
--
--   For $\beta\ge\beta_x$ the constraint dissolving function is an exact penalty near $x$ (Theorems 3.10 and 3.18).
--
--   **Formalization Note** For $x\in\mathcal M$ (and $p\ge1$) the denominators are powers of $\sigma_{x,c}>0$, so Lean's division is the paper's.
-- source:
--   Xiao, Liu & Toh, Dissolving Constraints for Riemannian Optimization, arXiv:2203.10319v3, Definition 2.9, p.8

import Mathlib
import Definitions.Def_DissolveCDF_sigmaXC
import Definitions.Def_DissolveCDF_MXf
import Definitions.Def_DissolveCDF_MXA
import Definitions.Def_DissolveCDF_LXg
import Definitions.Def_DissolveCDF_LXA
import Definitions.Def_DissolveCDF_LXb

namespace DissolveCDF

/-- Xiao, Liu & Toh, *Dissolving Constraints for Riemannian Optimization*, arXiv:2203.10319v3, Definition 2.9 (p.8): for `x ∈ M`,
`β_x := max { 128 L_{x,g}(M_{x,A} + 1)² / σ_{x,c}², 64 M_{x,f}(M_{x,A} + 1) L_{x,b} / σ_{x,c}³,
16 M_{x,f} L_{x,A}(2M_{x,A} + 1) / σ_{x,c}² }`.

**Formalization Note** For `x ∈ M` the denominators are powers of `σ_{x,c} > 0`, so Lean's
division is the paper's. -/
noncomputable def betaX {n p : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p))
    (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  max (max (128 * LXg f c A x * (MXA c A x + 1) ^ 2 / sigmaXC c x ^ 2)
      (64 * MXf f c A x * (MXA c A x + 1) * LXb c A x / sigmaXC c x ^ 3))
    (16 * MXf f c A x * LXA c A x * (2 * MXA c A x + 1) / sigmaXC c x ^ 2)

end DissolveCDF


