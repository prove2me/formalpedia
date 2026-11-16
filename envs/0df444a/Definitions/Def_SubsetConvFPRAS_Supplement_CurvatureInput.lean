-- Prove2me | Definitions.Def_SubsetConvFPRAS_Supplement_CurvatureInput
-- name    : SubsetConvFPRAS_Supplement_CurvatureInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:48:03.851251+00:00
-- url     : https://prove2.me/theorems/acd3cf7f-01e9-41d7-bc83-c0dca55bb9bd
-- title:
--   Input layout of Theorem 1.16 in the arithmetic model
-- statement:
--   This file fixes the initial state of the arithmetic model (the published unit-cost real RAM with fair coins and two value oracles for $\mu,\nu$) for Theorem 1.16.
--
--   Integer cell $0$ holds $n=|U|$ and integer cell $1+u$ holds the exponent $\alpha_u\in\{0,1,2\}$ of the requested coefficient $Z_\alpha$. Real cells $0,\dots,5$ hold, in order, the accuracy $\varepsilon$, the upper bounds $R_\mu,R_\nu$ on the coefficient ranges, the curvature parameters $\eta,\kappa$ and the growth bound $\chi$; every other cell is $0$. No set is placed in the bitmaps: Theorem 1.16 supplies no starting sets, since downward closed supports contain $\emptyset$ whenever the weight is nonzero.
-- source:
--   Chen, Liu, An FPRAS for Counting Common Bases of Two Matroids, arXiv:2610.06724 (version held, sha256 6c1d68c2…919476), Theorem 1.16, p.7; proof in Appendix A.1, pp.35–37

import Mathlib
import Definitions.Def_SubsetConvFPRAS_Machine

open scoped Classical

namespace SubsetConvFPRAS.Supplement

/-!
# Input layout of Theorem 1.16 in the arithmetic model

X. Chen, K. Liu, *An FPRAS for Counting Common Bases of Two Matroids*, arXiv:2610.06724 (version held,
sha256 6c1d68c2…), Theorem 1.16, p.7; proof in Appendix A.1, pp.35–37.

The machine is the published `SubsetConvFPRAS.Machine` (unit-cost real RAM with fair coins and the two
value oracles), the model of Theorem 1.6.

**Formalization Note.**
* Integer cell `0` holds `n`; integer cell `1 + u` holds `α u`.
* No bitmap is filled: Theorem 1.16 supplies no starting sets (its supports are downward closed).
* Real cells `0, …, 5` hold `ε, R_μ, R_ν, η, κ, χ`; every other real cell is `0`.
-/

/-- The initial state of Theorem 1.16: `I 0 = n`, `I (1+u) = α u`; no bitmaps; `M 0 = ε`, `M 1 = R_μ`,
`M 2 = R_ν`, `M 3 = η`, `M 4 = κ`, `M 5 = χ`. -/
noncomputable def initCurvature {n : ℕ} (α : Fin n → Fin 3) (ε Rμ Rν η κ χ : ℝ) : State n :=
  mkInit
    (fun i => if i = 0 then (n : ℤ)
      else if h : 0 ≤ i - 1 ∧ (i - 1).toNat < n then ((α ⟨(i - 1).toNat, h.2⟩ : ℕ) : ℤ) else 0)
    (bitmapsOf []) (realsOf [ε, Rμ, Rν, η, κ, χ] (fun _ : Fin 0 => 0))

end SubsetConvFPRAS.Supplement


