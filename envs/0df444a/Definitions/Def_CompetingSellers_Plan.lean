-- Prove2me | Definitions.Def_CompetingSellers_Plan
-- name    : CompetingSellers_Plan
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:54.753802+00:00
-- url     : https://prove2.me/theorems/a776dc30-921d-426f-884f-57da94e811ed
-- title:
--   Buyer action plan $\pi=(i,\sigma_i,\sigma^W_{-i},\sigma^L_{-i})$ and its payoffs
-- statement:
--   Given Alice's mechanism $M_A$ and Bob's mechanism $M_B$, the buyer (value $a$ for Alice's good, $b$ for Bob's, $\max\{a,b\}$ for both) chooses an **action plan** $\pi=(i,\sigma_i,\sigma^W_{-i},\sigma^L_{-i})\in\{A,B\}\times\Sigma^3$: the seller $i$ approached first, the message $\sigma_i$ sent to it, and the messages sent to the other seller after winning ($W$) or losing ($L$) the first good.
--
--   With first seller $f$, second seller $s$, buyer values $v_f,v_s$, first option $(x,p)$ and continuation options $(y_W,p_W)$, $(y_L,p_L)$, the plan gives
--   $$\mathrm{util}(\pi)=v_f x-p+x\big((v_s-v_f)^+y_W-p_W\big)+(1-x)\big(v_s y_L-p_L\big),$$
--   the expectation of $\max\{a q_A,b q_B\}-t_A-t_B$; the first seller's revenue is $p$ and the second's $x p_W+(1-x)p_L$; the overall allocation probabilities are $x$ and $x y_W+(1-x)y_L$.
--
--   These payoffs drive the buyer's tie-broken choice and hence every revenue in the game.
--
--   **Formalization Note** The utility is computed in the extended reals, so a plan that pays an infinite expected transfer on a reached branch has utility $-\infty$; revenues are in $[0,\infty]$ with $0\cdot\infty=0$ on unreached branches.
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), §2 The Buyer's Strategy, pp.14–15 (PDF 17–18); proof of Observation 2.2, p.54

import Mathlib
import Definitions.Def_CompetingSellers_Mech

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

/-- The two sellers, Alice (`A`, the incumbent, moving first) and Bob (`B`). -/
inductive Seller
  | alice
  | bob
  deriving DecidableEq

/-- The remaining seller `−i`. -/
def Seller.other : Seller → Seller
  | .alice => .bob
  | .bob => .alice

/-- **Buyer action plan** (§2 "The Buyer's Strategy", p.15).
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), §2, p.15 (PDF 18): "Such an action plan `π` for the buyer can
therefore be described as a tuple `(i, σ_i, σ^W_{−i}, σ^L_{−i}) ∈ Π = {A, B} × Σ³`, where `i` is
the seller approached first, `σ_i` is the message sent to `i`, `σ^W_{−i}` is the message sent to
`−i` when `q_i = 1` (Wins the good), and `σ^L_{−i}` is the message sent to `−i` when `q_i = 0`
(Loses the good)."

The payoffs of a plan (`Plan.util`, `Plan.rev`, `Plan.totalAlloc`) follow the timing of p.14:
Alice receives `t_A`, Bob `t_B`, and the buyer `max{a·q_A, b·q_B} − t_A − t_B`. -/
structure Plan (S : Type) where
  /-- The seller `i` approached first. -/
  first : Seller
  /-- The message `σ_i` sent to the first seller. -/
  msg1 : S
  /-- The message `σ^W_{−i}` sent to the second seller after winning the first good. -/
  msgW : S
  /-- The message `σ^L_{−i}` sent to the second seller after losing the first good. -/
  msgL : S

namespace Plan

variable {S : Type} [MeasurableSpace S] {null : S}

/-- The mechanism of seller `i` when Alice uses `A` and Bob uses `B`. -/
def mechOf (A B : Mech S null) : Seller → Mech S null
  | .alice => A
  | .bob => B

/-- The buyer's value for seller `i`'s good: `a` for Alice's, `b` for Bob's. -/
def valueOf (a b : ℝ) : Seller → ℝ
  | .alice => a
  | .bob => b

/-- Allocation probability `x_i` of the first seller under the plan. -/
noncomputable def firstAlloc (A B : Mech S null) (π : Plan S) : ℝ :=
  (mechOf A B π.first).alloc π.msg1

/-- Conditional allocation probability `x^W_{−i}` of the second seller after winning the first
good (the message `σ^W_{−i}`). -/
noncomputable def allocW (A B : Mech S null) (π : Plan S) : ℝ :=
  (mechOf A B π.first.other).alloc π.msgW

/-- Conditional allocation probability `x^L_{−i}` of the second seller after losing the first
good (the message `σ^L_{−i}`). -/
noncomputable def allocL (A B : Mech S null) (π : Plan S) : ℝ :=
  (mechOf A B π.first.other).alloc π.msgL

/-- The buyer's expected utility `util(A, B, π) = E[max{a q_A, b q_B} − t_A − t_B]`, in `EReal`
(an infinite expected transfer on a reached branch gives `−∞`). With first seller `f`, second
seller `s`, first option `(x, p)` and continuation options `(y_W, p_W)`, `(y_L, p_L)` it equals
`v_f x − p + x((v_s − v_f)⁺ y_W − p_W) + (1 − x)(v_s y_L − p_L)` (proof of Observation 2.2,
p.54). -/
noncomputable def util (a b : ℝ) (A B : Mech S null) (π : Plan S) : EReal :=
  let x := π.firstAlloc A B
  let vf := valueOf a b π.first
  let vs := valueOf a b π.first.other
  ((vf * x : ℝ) : EReal) - ((mechOf A B π.first).pay π.msg1 : EReal)
    + (x : EReal) * (((max (vs - vf) 0 * π.allocW A B : ℝ) : EReal)
        - ((mechOf A B π.first.other).pay π.msgW : EReal))
    + ((1 - x : ℝ) : EReal) * (((vs * π.allocL A B : ℝ) : EReal)
        - ((mechOf A B π.first.other).pay π.msgL : EReal))

/-- Seller `i`'s expected revenue `rev_i(A, B, π) = E[t_i]` under the plan (in `ℝ≥0∞`): the
first seller receives `p`, the second `x p_W + (1 − x) p_L`. -/
noncomputable def rev (A B : Mech S null) (π : Plan S) (i : Seller) : ℝ≥0∞ :=
  if π.first = i then (mechOf A B i).pay π.msg1
  else ENNReal.ofReal (π.firstAlloc A B) * (mechOf A B i).pay π.msgW
    + ENNReal.ofReal (1 - π.firstAlloc A B) * (mechOf A B i).pay π.msgL

/-- Seller `i`'s overall allocation probability `X_i(A, B, π)`: `x` for the first seller,
`x y_W + (1 − x) y_L` for the second. -/
noncomputable def totalAlloc (A B : Mech S null) (π : Plan S) (i : Seller) : ℝ :=
  if π.first = i then π.firstAlloc A B
  else π.firstAlloc A B * π.allocW A B + (1 - π.firstAlloc A B) * π.allocL A B

end Plan

end CompetingSellers


