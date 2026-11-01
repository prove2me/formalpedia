-- Prove2me | Definitions.Def_ManIAL_zbar
-- name    : ManIAL_zbar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:01.757405+00:00
-- url     : https://prove2.me/theorems/3235cf1d-59c2-473d-8a9b-d40aad10edf9
-- title:
--   Auxiliary multiplier $\bar z^{k+1}$ (3.27)
-- statement:
--   Given $\sigma_k$, $z^k$, $x^{k+1}$ and $y^{k+1}$, the **auxiliary multiplier** is
--
--   $$
--   \bar z^{k+1}:=z^k-\sigma_k(\mathcal Ax^{k+1}-y^{k+1}).
--   $$
--
--   It is the multiplier of an exact augmented Lagrangian step; the complexity theorems certify the triple $(x^{K+1},y^{K+1},\bar z^{K+1})$ as an $\epsilon$-KKT point pair, while ManIAL itself carries the damped multipliers $z^k$.
-- source:
--   Deng, Hu, Wu & Wen, Oracle complexities of augmented Lagrangian methods for nonsmooth manifold optimization, arXiv:2404.05121v2, display (3.27), p.12

import Mathlib

namespace ManIAL

/-- The auxiliary multiplier (3.27) (Deng–Hu–Wu–Wen, arXiv:2404.05121v2, p.12):
`z̄^{k+1} := z^k − σ_k(Ax^{k+1} − y^{k+1})`, here `zbar σ z A x y = z − σ • (A x − y)` with
`σ = σ_k`, `z = z^k`, `x = x^{k+1}`, `y = y^{k+1}`. -/
def zbar {n m : ℕ} (σ : ℝ) (z : EuclideanSpace ℝ (Fin m))
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) :=
  z - σ • (A x - y)

end ManIAL


