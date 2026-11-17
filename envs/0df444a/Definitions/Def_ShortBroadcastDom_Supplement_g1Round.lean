-- Prove2me | Definitions.Def_ShortBroadcastDom_Supplement_g1Round
-- name    : ShortBroadcastDom_Supplement_g1Round
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:40:50.198684+00:00
-- url     : https://prove2.me/theorems/8e46b536-6f05-41ac-90c6-60c68663401b
-- title:
--   The rounding of App. G.1: $W$, $R$, $h$, $H$ (threshold four), $U$ and $D=W\cup H\cup U$
-- statement:
--   With $Z,R_0,F,c$ as in the transformation of App. G.1, let $x\in[0,1]^Z$ be a fractional cover of $R_0$. The rounding is
--
--   $$
--   \begin{aligned}
--   W&=\{v\in Z: c(v)=3,\ x_v>1/2\}, & R&=R_0\setminus N_G[W], & h(v)&=|N_G[v]\cap R|,\\
--   H&=\{v\in Z\setminus W: h(v)\ge4\}, & U&=R\setminus N_G[H], & D&=W\cup H\cup U,
--   \end{aligned}
--   $$
--
--   and its fractional cost is $\mathcal C(x)=\sum_{v\in Z}c(v)x_v$. The algorithm outputs $F\cup D$.
--
--   Unlike the threshold rounding of §7.1, the second step selects only candidates covering at least four remaining demands.
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), App. G.1, p.90 (PDF p.93)

import Mathlib
import Definitions.Def_ShortBroadcastDom_closedNbhd
import Definitions.Def_ShortBroadcastDom_Supplement_g1Sel

namespace ShortBroadcastDom.Supplement

/-! The rounding of App. G.1, p.90 (PDF 93) of Amiri, Siebertz, Wawrzyniak, *Paying for Fractional
Error* (arXiv:2611.02057, sha256 prefix f4dc98d2): "Let x ∈ [0, 1]^Z be a feasible fractional cover
of R0. The rounding consists of the three steps of Section 7 with C = Z, the cost b = 3, and the
threshold t = 1/2, with one change: the second step selects only candidates that cover at least
four demands. Thus W = {v ∈ Z : c(v) = 3, xv > 1/2}, R = R0 \ NG[W], h(v) = |NG[v] ∩ R|,
H = {v ∈ Z \ W : h(v) ≥ 4}, U = R \ NG[H], D = W ∪ H ∪ U."

The base mission's `RoundingData` uses the threshold `b = 2a + 1` in the second step, not `4`, so
the rule is defined here. Only the values of `x` on `Z` are used. -/

open Classical in
/-- Step 1: `W = {v ∈ Z : c(v) = 3, x_v > 1/2}`. -/
noncomputable def g1W {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V → ℝ) : Finset V :=
  (g1Z G).filter fun v => g1Cost G v = 3 ∧ 1 / 2 < x v

open Classical in
/-- The remaining demands `R = R₀ \ N_G[W]`. -/
noncomputable def g1R {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V → ℝ) : Finset V :=
  (g1R0 G).filter fun r => ∀ w ∈ g1W G x, r ∉ closedNbhd G w

/-- `h(v) = |N_G[v] ∩ R|`. -/
noncomputable def g1h {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V → ℝ) (v : V) : ℕ :=
  (closedNbhd G v ∩ g1R G x).card

open Classical in
/-- Step 2: `H = {v ∈ Z \ W : h(v) ≥ 4}`. -/
noncomputable def g1H {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V → ℝ) : Finset V :=
  (g1Z G \ g1W G x).filter fun v => 4 ≤ g1h G x v

open Classical in
/-- Step 3: `U = R \ N_G[H]`. -/
noncomputable def g1U {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V → ℝ) : Finset V :=
  (g1R G x).filter fun r => ∀ v ∈ g1H G x, r ∉ closedNbhd G v

/-- **The rounded set `D = W ∪ H ∪ U` of App. G.1** (the algorithm outputs `F ∪ D`). -/
noncomputable def g1D {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V → ℝ) : Finset V :=
  g1W G x ∪ g1H G x ∪ g1U G x

/-- The cost `𝒞(x) = ∑_{v ∈ Z} c(v) x_v` of the fractional cover (App. G.1, p.90, with
`C = Z`). -/
noncomputable def g1CostOf {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V → ℝ) : ℝ :=
  ∑ v ∈ g1Z G, g1Cost G v * x v

end ShortBroadcastDom.Supplement


