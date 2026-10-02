-- Prove2me | Definitions.Def_DiscreteConvex_Combinatorial_IsValuation
-- name    : DiscreteConvex_Combinatorial_IsValuation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T20:27:29.180177+00:00
-- url     : https://prove2.me/theorems/477e69e5-b164-49f6-8e7b-092440aba2cd
-- title:
--   Valuation of a matroid base family (axiom VM)
-- statement:
--   Given a matroid base family $\mathcal B$, a function $\omega$ (only its restriction to $\mathcal B$ mattering) is a **valuation** of $\mathcal B$ if it satisfies Murota's axiom (VM): for every $J, J' \in \mathcal B$ and $i \in J \setminus J'$, there is $j \in J' \setminus J$ with $J - i + j,\ J' + i - j \in \mathcal B$ and $\omega(J) + \omega(J') \le \omega(J - i + j) + \omega(J' + i - j)$. A pair $(V, \omega)$ where $\omega$ is a valuation of some matroid's base family is a **valuated matroid**.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.71-72, axiom (VM).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.71-72, axiom (VM)

import Mathlib
import Definitions.Def_DiscreteConvex_Combinatorial_ExchangeFamily

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.71-72, axiom (VM), restricted to a fixed
base family `𝓑`, as used in the hypothesis of Theorem 2.32 ("`ω : B → R` is a valuation") in
`DiscreteConvex.Combinatorial`.
-/

namespace DiscreteConvex.Combinatorial

/-- Given a matroid base family `𝓑`, a function `ω` on `Finset V` (only its values on `𝓑`
matter) **is a valuation** of `𝓑` if it satisfies axiom (VM): for every `J, J' ∈ 𝓑` and every
`i ∈ J \ J'` there is `j ∈ J' \ J` with `J - i + j, J' + i - j ∈ 𝓑` and
`ω(J) + ω(J') ≤ ω(J - i + j) + ω(J' + i - j)`. -/
def IsValuation {V : Type*} [DecidableEq V] (𝓑 : Finset (Finset V)) (ω : Finset V → ℝ) : Prop :=
  ∀ J ∈ 𝓑, ∀ J' ∈ 𝓑, ∀ i ∈ J \ J', ∃ j ∈ J' \ J,
    insert j (J.erase i) ∈ 𝓑 ∧ insert i (J'.erase j) ∈ 𝓑 ∧
      ω J + ω J' ≤ ω (insert j (J.erase i)) + ω (insert i (J'.erase j))

end DiscreteConvex.Combinatorial


