-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibrium_UDom
-- name    : DiscreteConvex_EconomicEquilibrium_UDom
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:49:15.938306+00:00
-- url     : https://prove2.me/theorems/437d71ea-9c8c-4a45-8aa9-7209eb99724a
-- title:
--   Effective domain of a utility-type function
-- statement:
--   The effective domain $\operatorname{dom} U = \{x \in \mathbb Z^K : U(x) \ne -\infty\}$ of a utility-type function $U : \mathbb Z^K \to \mathbb R \cup \{-\infty\}$. The `WithBot ℝ`-valued counterpart of chunk 06's `DomZ` (stated for `WithTop ℝ`-valued cost-type functions).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.325.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.325

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.325 (general notation `dom U`, e.g. used in
Theorem 11.4, p.330): the effective domain of a utility-type function `U : ZK → R ∪ {−∞}`, in
`DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

/-- The effective domain `dom U = {x ∈ Zᴷ : U(x) ≠ −∞}` of a utility-type function
`U : Zᴷ → R ∪ {−∞}`. The `WithBot ℝ`-valued counterpart of `DiscreteConvex.MConvexFunctions.DomZ`
(which is stated for `WithTop ℝ`-valued cost-type functions). -/
def UDom {K : Type*} (U : (K → ℤ) → WithBot ℝ) : Set (K → ℤ) :=
  {x | U x ≠ ⊥}

end DiscreteConvex.EconomicEquilibrium


