-- Prove2me | Definitions.Def_SongZipkinFluct_Monotone_Bounds
-- name    : SongZipkinFluct_Monotone_Bounds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:39:13.291673+00:00
-- url     : https://prove2.me/theorems/986785d2-5c83-403e-b5bc-06f49622d625
-- title:
--   §3.2, p. 358 — the critical numbers y⁺, y*, y⁺_min and the bounds S⁺(i), r⁺(i), r⁻(i), r⁻⁻(i)
-- statement:
--   Let $y^+(i)$ be the smallest minimizer of the myopic cost $G^+(i,\cdot)$, $y^*(i)$ the smallest minimizer of $G_0(i,\cdot) = G_\infty(i,\cdot)$ of the linear-cost model ($K = 0$, $W_0 \equiv 0$), and $y^+_{\min} = \min_i y^+(i)$. With $K = \bar K\,\tilde F_L(\alpha)$ the fixed order cost, the paper defines
--   $$S^+(i) = \min\{y \ge y^+(i) : G^+(i,y) - G^+(i,y^+(i)) > \gamma K\},$$
--   $$r^+(i) = \max\{y < y^+(i) : G^+(i,y) - G^+(i,y^+(i)) > (1-\gamma)K\},$$
--   $$r^-(i) = \max\{y < y^*(i) : G_0(i,y) - G_0(i,y^*(i)) > K\},$$
--   $$r^{--}(i) = \max\{y < y^+_{\min} : G^+(i,y) - G^+(i,y^+_{\min}) > K\}.$$
--   The predicate `IsBounds` holds of $(y^+, y^*, y^+_{\min}, S^+, r^+, r^-, r^{--})$ exactly when each of them is the value just described.
--
--   These numbers bound the optimal $(r,S)$ parameters of the fixed-cost model (Theorems 4 and 6 of the paper); §4.3 shows that they are monotone in the world state.
--
--   **Formalization Note.** Each minimum or maximum is characterized as the least or greatest element of its set, rather than computed with an infimum or supremum on $\mathbb Z$, which would return a default value on an empty or unbounded set.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 356 (y⁺), p. 357 (y⁺_min, y*), p. 358 (G₀, S⁺, r⁺, r⁻, r⁻⁻)

import Mathlib
import Definitions.Def_SongZipkinFluct_Monotone_Recursion

namespace SongZipkinFluct.Monotone

namespace Model

variable {I : Type} (M : Model I)

/-- **The critical numbers of the linear-cost model and the bounds `S⁺(i)`, `r⁺(i)`, `r⁻(i)`,
`r⁻⁻(i)` of the fixed-cost model** (Song and Zipkin 1993, p. 356, p. 357, p. 358).

`IsBounds yplus ystar ymin Splus rplus rminus rminus2` says that
* `y⁺(i)` is the smallest minimizer of `G⁺(i, ·)` (p. 356);
* `y*(i)` is the smallest minimizer of `G₀(i, ·) = G_∞(i, ·)`, the limit of the linear-cost model
  (`K = 0`, `W₀ ≡ 0`) (Theorem 2(b), p. 357; "let `G₀` be the `G_∞` in the linear cost model", p. 358);
* `y⁺_min = min_i y⁺(i)` (p. 357);
* `S⁺(i) = min{y ≥ y⁺(i) : G⁺(i, y) − G⁺(i, y⁺(i)) > γK}`;
* `r⁺(i) = max{y < y⁺(i) : G⁺(i, y) − G⁺(i, y⁺(i)) > (1 − γ)K}`;
* `r⁻(i) = max{y < y*(i) : G₀(i, y) − G₀(i, y*(i)) > K}`;
* `r⁻⁻(i) = max{y < y⁺_min : G⁺(i, y) − G⁺(i, y⁺_min) > K}` (all four on p. 358),
where `K = K̄ F̃_L(α)` is the model's fixed order cost.

**Formalization Note.** Minima and maxima over sets of integers are `IsLeast`/`IsGreatest`
characterizations of the named values, not `sInf`/`sSup` (which return junk on empty or unbounded
sets). -/
def IsBounds (yplus ystar : I → ℤ) (ymin : ℤ) (Splus rplus rminus rminus2 : I → ℤ) : Prop :=
  (∀ i, IsSmallestMinimizer (M.Gplus i) (yplus i)) ∧
  (∀ i, IsSmallestMinimizer (M.Ginf 0 0 i) (ystar i)) ∧
  IsLeast (Set.range yplus) ymin ∧
  (∀ i, IsLeast {y : ℤ | yplus i ≤ y ∧ M.Gplus i y - M.Gplus i (yplus i) > M.γ * M.K}
    (Splus i)) ∧
  (∀ i, IsGreatest {y : ℤ | y < yplus i ∧ M.Gplus i y - M.Gplus i (yplus i) > (1 - M.γ) * M.K}
    (rplus i)) ∧
  (∀ i, IsGreatest {y : ℤ | y < ystar i ∧ M.Ginf 0 0 i y - M.Ginf 0 0 i (ystar i) > M.K}
    (rminus i)) ∧
  (∀ i, IsGreatest {y : ℤ | y < ymin ∧ M.Gplus i y - M.Gplus i ymin > M.K} (rminus2 i))

end Model

end SongZipkinFluct.Monotone


