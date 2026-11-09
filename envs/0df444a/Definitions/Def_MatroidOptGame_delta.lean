-- Prove2me | Definitions.Def_MatroidOptGame_delta
-- name    : MatroidOptGame_delta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:52:11.776048+00:00
-- url     : https://prove2.me/theorems/428eed40-b3f1-4124-83d7-2f738cd80f19
-- title:
--   The approximation parameter $\delta(M,w)$
-- statement:
--   For a matroid $M$ on $E$ and weights $w : E \to \mathbb N$,
--   $$
--   \delta(M, w) = \begin{cases} \tfrac12\, w(B_{\min}(M \vee M, w)) - w(B_{\min}(M, w)) & \text{if } r_{M\vee M}(E) = 2\, r_M(E),\\[2pt] \infty & \text{if } r_{M\vee M}(E) < 2\, r_M(E). \end{cases}
--   $$
--   Theorem 1 shows that the excess value of the matroid base minimization game lies in $[\delta(M, w), 2\delta(M, w)]$ and that both ends can be secured efficiently.
--
--   **Formalization Note** Valued in the extended reals; the finite case is computed in $\mathbb R$. The second case is written as "otherwise": since $r_{M\vee M}(E) \le 2\,r_M(E)$ always, "otherwise" is exactly the printed strict inequality.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.1, p.4 (definition of δ(M, w))

import Mathlib
import Definitions.Def_MatroidOptGame_minBaseWeight
import Definitions.Def_MatroidOptGame_rankOf
import Definitions.Def_MatroidOptGame_unionRank
import Definitions.Def_MatroidOptGame_unionMinBaseWeight

namespace MatroidOptGame

/-- The quantity `δ(M, w)`:
`δ(M, w) = ½ w(B_min(M ∨ M, w)) − w(B_min(M, w))` if `r_{M∨M}(E) = 2·r_M(E)`, and `∞` if
`r_{M∨M}(E) < 2·r_M(E)`.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.1, p.4 (display defining δ(M, w)).

**Formalization Note.** Valued in `EReal`; the finite case is computed in `ℝ` and coerced. The
printed second case is `r_{M∨M}(E) < 2·r_M(E)`; here it is the `else` branch. The two agree
because `r_{M∨M}(E) ≤ 2·r_M(E)` always (a union of two independent sets has at most `2·r_M(E)`
elements). `r_M(E)` is `rankOf M Finset.univ`, which is the rank of `M` when `M.E = Set.univ`. -/
noncomputable def delta {α : Type*} [Fintype α] [DecidableEq α] (M : Matroid α) (w : α → ℕ) : EReal :=
  if unionRank M = 2 * rankOf M Finset.univ then
    (((unionMinBaseWeight M w : ℝ) / 2 - (minBaseWeight M w : ℝ) : ℝ) : EReal)
  else ⊤

end MatroidOptGame


