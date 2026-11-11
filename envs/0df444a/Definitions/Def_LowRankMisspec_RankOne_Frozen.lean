-- Prove2me | Definitions.Def_LowRankMisspec_RankOne_Frozen
-- name    : LowRankMisspec_RankOne_Frozen
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T23:15:43.401303+00:00
-- url     : https://prove2.me/theorems/88dbdcba-764c-47e8-be33-1bafaf5f35c6
-- title:
--   The frozen-trajectory product law $R_x$ (§5.1)
-- statement:
--   For a reference trajectory $x$ with $P[x]>0$, the **frozen-trajectory product distribution** is
--   $$R_x=\bigotimes_{t=0}^{T-1}\big(P[b\mid x_{1:t}]\big)_{b\in[\sigma]},\qquad R_x[y]=\prod_{t=1}^T P[y_t\mid x_{<t}].$$
--   The conditioning histories come from the fixed trajectory $x$, not from $y$, so $R_x$ is a product law even when $P$ has arbitrary dependencies.
--
--   **Formalization Note.** `frozenRow P x t b` $=P[b\mid x_{1:t}]$ for `t : Fin T` (the paper's coordinate $t+1$). When $P[x]>0$ every prefix of $x$ has positive mass; for $P[x]=0$ the formula is still evaluated with $\cdot/0=0$, and no statement uses $R_x$ there.
-- source:
--   Hasrati, Risteski, Understanding Model Misspecification in Low-Rank Distributions: Tolerant Testing and Agnostic Learning, STOC 2027 submission (manuscript sha256 235f2a4f…), p. 8 (PDF 9), §5.1

import Mathlib
import Definitions.Def_LowRankMisspec_RankOne_Laws

set_option autoImplicit false

open scoped Classical

noncomputable section

namespace LowRankMisspec.RankOne

/-!
# The frozen-trajectory product law `R_x` (§5.1)

Hasrati, Risteski, *Understanding Model Misspecification in Low-Rank Distributions: Tolerant
Testing and Agnostic Learning*, STOC 2027 submission (manuscript sha256 235f2a4f…), §5.1, p. 8
(PDF 9).

For a reference trajectory `x` with `P[x] > 0`,
`R_x = ⊗_{t=0}^{T−1} (P[b | x_{1:t}])_{b ∈ [σ]}`, i.e. `R_x[y] = Π_{t=1}^{T} P[y_t | x_{<t}]`:
the conditioning histories come from the fixed trajectory `x`, not from `y`.
`frozenRow P x t b = P[b | x_{1:t}]` (coordinate `t : Fin T` is the paper's `t + 1`, its history is
the first `t` symbols of `x`). When `P[x] > 0` every prefix of `x` has positive mass and the rows
are laws; for `P[x] = 0` the formula is still evaluated (with `·/0 = 0`), but every statement uses
`R_x` only for `P[x] > 0`.
-/

/-- The frozen row `P[b | x_{1:t}]`. -/
def frozenRow {σ T : ℕ} (P : Str σ T → ℝ) (x : Str σ T) (t : Fin T) (b : Fin σ) : ℝ :=
  condProb P ((strCells x).take t.val) [b.val]

/-- The frozen-trajectory product law `R_x[y] = Π_{t=1}^{T} P[y_t | x_{<t}]`. -/
def frozenLaw {σ T : ℕ} (P : Str σ T → ℝ) (x : Str σ T) : Str σ T → ℝ :=
  prodLaw (frozenRow P x)

end LowRankMisspec.RankOne


