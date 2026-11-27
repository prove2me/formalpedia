-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_TradeExec
-- name    : BauerleRiederMDP_LQ_Supplement_TradeExec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:37:51.020165+00:00
-- url     : https://prove2.me/theorems/2e31e875-3ce3-4c7a-918d-fe3e1ec3bb0d
-- title:
--   The trade execution problem in an illiquid market
-- statement:
--   **The trade execution problem in an illiquid market** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §9.4, pp.293–294, PDF 303–304): shares can be sold only at the jump times of a Poisson process with intensity $\lambda  > 0$, within the horizon $T > 0$; the cost of selling $a$ shares is $C(a)$, where $C : \mathbb N _0 \to  \mathbb R _+$ is strictly increasing and strictly convex, $C(x) - C(x - 1) < C(x + 1) - C(x)$ for $x \in  \mathbb N $ (9.19), with $C(0) = 0$.
--
--   **Formalization Note.** $C$ is a function $\mathbb N  \to  \mathbb R $; nonnegativity follows from $C(0) = 0$ and monotonicity.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §9.4, pp.293–294, PDF 303–304

import Mathlib

namespace BauerleRiederMDP.LQ.Supplement

/-- **The trade execution problem in an illiquid market** (Bäuerle & Rieder, *Markov Decision
Processes with Applications to Finance* (2011), §9.4, pp.293–294, PDF 303–304): shares can be sold
only at the jump times of a Poisson process with intensity `λ > 0`, within the horizon `T > 0`;
the cost of selling `a` shares is `C(a)`, where `C : ℕ_0 → ℝ_+` is strictly increasing and strictly
convex, `C(x) − C(x − 1) < C(x + 1) − C(x)` for `x ∈ ℕ` (9.19), with `C(0) = 0`.

**Formalization Note.** `C` is a function `ℕ → ℝ`; nonnegativity follows from `C(0) = 0` and
monotonicity. -/
structure TradeExec where
  lam : ℝ
  lam_pos : 0 < lam
  T : ℝ
  T_pos : 0 < T
  C : ℕ → ℝ
  C_zero : C 0 = 0
  C_strictMono : StrictMono C
  C_strictConvex : ∀ x : ℕ, 1 ≤ x → C x - C (x - 1) < C (x + 1) - C x

end BauerleRiederMDP.LQ.Supplement


