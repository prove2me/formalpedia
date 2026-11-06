-- Prove2me | Definitions.Def_PADMPriv_IsContraction
-- name    : PADMPriv_IsContraction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:23.184272+00:00
-- url     : https://prove2.me/theorems/765d17ea-071b-48ae-aa43-3dc6b3bf9b54
-- title:
--   $\tau$-contractive operator
-- statement:
--   An operator $T:\mathbb R^m\to\mathbb R^m$ is **$\tau$-contractive** if
--   $$
--   \|T(u)-T(v)\|_2 \le \tau\,\|u-v\|_2 \qquad \text{for all } u,v\in\mathbb R^m.
--   $$
--   The paper uses the term for factors $0<\tau<1$ (Theorem 5.1) without a separate definition; this is the bound its proofs use. Proposition 5.1 gives such factors for $T_F$ under induced strong convexity.
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Proposition 5.1 and Theorem 5.1, p.11; A.13, p.29

import Mathlib

namespace PADMPriv

/-- An operator `T` is `τ`-contractive (Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d), Proposition 5.1, p.11, and
Theorem 5.1, p.11): `‖T(u) − T(v)‖₂ ≤ τ ‖u − v‖₂` for all `u, v`. The paper does not define the
term separately; this is the bound its proofs use (A.13, p.29). -/
def IsContraction {m : ℕ} (τ : ℝ) (T : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) :
    Prop :=
  ∀ u v : EuclideanSpace ℝ (Fin m), ‖T u - T v‖ ≤ τ * ‖u - v‖

end PADMPriv


