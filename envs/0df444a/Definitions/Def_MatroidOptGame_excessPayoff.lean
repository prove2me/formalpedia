-- Prove2me | Definitions.Def_MatroidOptGame_excessPayoff
-- name    : MatroidOptGame_excessPayoff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:56:14.940483+00:00
-- url     : https://prove2.me/theorems/e5df8d1e-ffe6-4ab3-af9f-08f0a9da597e
-- title:
--   MAX's excess payoff
-- statement:
--   MAX's **excess payoff** for strategies $c, s$ is
--   $$
--   p(c, s) - w(B_{\min}(M, w)),
--   $$
--   MAX's payoff minus the weight of a minimum-weight base. It is $\infty$ when MAX deletes a cut and otherwise nonnegative.
--
--   **Formalization Note** Computed in the extended reals through the published embedding `NKtLB.toEReal` of $\mathbb N \cup \{\infty\}$ ($\infty \mapsto +\infty$, $k \mapsto k$); $\infty$ minus a finite number is $\infty$.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3

import Mathlib
import Definitions.Def_MatroidOptGame_minBaseWeight
import Definitions.Def_MatroidOptGame_Strategy
import Definitions.Def_MatroidOptGame_payoff
import Definitions.Def_NKtLB_toEReal

namespace MatroidOptGame

/-- MAX's excess payoff `p(c, s) − w(B_min(M, w))`.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3 ("It will be convenient to subtract the weight of B_min(M, w)
from MAX's payoff … We shall refer to this quantity as MAX's excess payoff").

**Formalization Note.** In `EReal`, through the published embedding `NKtLB.toEReal : ℕ∞ → EReal`
(`⊤ ↦ ⊤`, `k ↦ k`); `⊤` minus a real is `⊤`. -/
noncomputable def excessPayoff {α : Type*} [Fintype α] [DecidableEq α] (M : Matroid α)
    (w : α → ℕ) (c s : Strategy α) : EReal :=
  NKtLB.toEReal (payoff M w c s) - ((minBaseWeight M w : ℝ) : EReal)

end MatroidOptGame


