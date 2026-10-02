-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibrium_Nondecreasing
-- name    : DiscreteConvex_EconomicEquilibrium_Nondecreasing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:49:35.545056+00:00
-- url     : https://prove2.me/theorems/ccd81282-1f96-4565-a58a-824f22a5c968
-- title:
--   Monotone (nondecreasing) utility
-- statement:
--   $U : \mathbb Z^K \to \mathbb R \cup \{-\infty\}$ is nondecreasing: $x \le y$ (pointwise) implies $U(x) \le U(y)$. This is a hypothesis of Theorem 11.13 genuinely separate from M$^\natural$-concavity itself (more of a good is always weakly preferred).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.337.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.337

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.337 (the "nondecreasing" hypothesis of Theorem
11.13): monotonicity of a utility-type function, in `DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

/-- `U : Zᴷ → R ∪ {−∞}` is nondecreasing: `x ≤ y` pointwise implies `U(x) ≤ U(y)`. -/
def Nondecreasing {K : Type*} (U : (K → ℤ) → WithBot ℝ) : Prop :=
  ∀ x y : K → ℤ, (∀ k, x k ≤ y k) → U x ≤ U y

end DiscreteConvex.EconomicEquilibrium


