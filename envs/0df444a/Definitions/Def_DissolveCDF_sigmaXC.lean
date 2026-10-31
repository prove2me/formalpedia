-- Prove2me | Definitions.Def_DissolveCDF_sigmaXC
-- name    : DissolveCDF_sigmaXC
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:30:52.148296+00:00
-- url     : https://prove2.me/theorems/5656b2dd-784e-463f-87ad-f73a07d043fa
-- title:
--   §2.3 — $\sigma_{x,c}=\sigma_{\min}(J_c(x))$
-- statement:
--   For $x\in\mathbb R^n$,
--
--   $$
--   \sigma_{x,c}:=\sigma_{\min}(J_c(x)).
--   $$
--
--   Under Assumption 1.1 (LICQ), $\sigma_{x,c}>0$ for every $x\in\mathcal M$ when $p\ge1$. It is the curvature-free constant that controls the error bound $\operatorname{dist}(y,\mathcal M)\le\frac{2}{\sigma_{x,c}}\|c(y)\|$.
-- source:
--   Xiao, Liu & Toh, Dissolving Constraints for Riemannian Optimization, arXiv:2203.10319v3, §2.3, p.7

import Mathlib
import Definitions.Def_DissolveCDF_transJac
import Definitions.Def_DissolveCDF_sigmaMin

namespace DissolveCDF

/-- Xiao, Liu & Toh, *Dissolving Constraints for Riemannian Optimization*, arXiv:2203.10319v3, §2.3 (p.7): `σ_{x,c} := σ_min(J_c(x))`. -/
noncomputable def sigmaXC {n p : ℕ} (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sigmaMin (transJac c x)

end DissolveCDF


