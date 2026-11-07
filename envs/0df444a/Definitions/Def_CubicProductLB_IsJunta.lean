-- Prove2me | Definitions.Def_CubicProductLB_IsJunta
-- name    : CubicProductLB_IsJunta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:14:14.857806+00:00
-- url     : https://prove2.me/theorems/a209e8ef-9c57-4f37-aa62-85122cf2ad4a
-- title:
--   $k$-juntas on the sign cube
-- statement:
--   A function $f$ is a **$k$-junta** on $X_n$ if there is a set $S$ of at most $k$ coordinates such that $f(x) = f(y)$ whenever $x, y \in X_n$ agree on $S$. An *eight-junta* is the case $k = 8$.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Section 6, p.15

import Mathlib
import Definitions.Def_CubicProductLB_signCube

namespace CubicProductLB

/-- `f` is a `k`-junta on `X_n`: it is determined there by a set of at most `k` coordinates
(Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Section 6, p.15: "A junta is a function determined by a specified bounded set of
coordinates"). -/
def IsJunta {n : ℕ} (k : ℕ) (f : (Fin n → ZMod 3) → ZMod 3) : Prop :=
  ∃ S : Finset (Fin n), S.card ≤ k ∧
    ∀ x ∈ signCube n, ∀ y ∈ signCube n, (∀ i ∈ S, x i = y i) → f x = f y

end CubicProductLB


