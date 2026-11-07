-- Prove2me | Definitions.Def_BilateralOptRegret_BinS
-- name    : BilateralOptRegret_BinS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:40:25.581974+00:00
-- url     : https://prove2.me/theorems/451c7bb4-cf5d-4f85-9e59-7a444318a4d0
-- title:
--   Algorithm 4 — BinS, binary search with fixed endpoints
-- statement:
--   **BinS**$(a,b,\beta,\delta_0,Q,W)$ estimates $P_{a,b}(w)=F(x_{b,w})-F(x_{a,w})$ on a set of rows $W=\{w_0<\dots<w_M\}$. Let $n_B=\lceil 32\beta^{-2}\log(4K/\delta_0)\rceil$. **Estimate**$(i)$ posts each of the two endpoints at row $w_i$ for $n_B$ fresh rounds and returns the difference of the two fractions of trades. The algorithm sets $\hat P(w_0)$ by Estimate$(0)$; if $M\ge1$, it sets $\hat P(w_M)$ by Estimate$(M)$ and calls **Split**$(0,M)$. Split$(i,j)$ returns if $j=i+1$; if $\hat P(w_j)-\hat P(w_i)\le\beta$ it sets $\hat P(w_k)$ to $(\hat P(w_i)+\hat P(w_j))/2$ for all $i<k<j$ and returns; otherwise, with $k=\lfloor(i+j)/2\rfloor$, it sets $\hat P(w_k)$ by Estimate$(k)$ and calls Split$(i,k)$ and Split$(k,j)$.
--
--   This procedure exploits the monotonicity of $P_{a,b}$ in the row.
--
--   **Formalization Note** The argument $Q$ of the printed signature is not read by the pseudocode, so it is omitted; it enters only through the choice of $W$. Posting $(z_c,1-z_w)$ is the action index $(c,w)$ in the transformed coordinates. $\log$ is natural. The estimates are a function of the row with the value $0$ off $W$.
-- source:
--   Castiglioni, Lunghi, Marchesi, Optimal Regret for Profit Maximization in Bilateral Trade (manuscript, sha256 aafed174…), Algorithm 4, p.44

import Mathlib
import Definitions.Def_BilateralProfit_QueryRoutine
import Definitions.Def_BilateralOptRegret_Model
import Definitions.Def_BilateralOptRegret_Program

namespace BilateralOptRegret

open BilateralProfit

/-! # Algorithm 4, BinS

Castiglioni, Lunghi, Marchesi (manuscript, sha256 aafed174…), Algorithm 4, p.44.

**Formalization Note.** Posting the prices `(z_c, 1 − z_w)` is the action index `(c, w)` in `X`-coordinates. The
argument `Q` of the page's signature is not read by the pseudocode (the rows `W` already encode it), so
it is not an argument here. `log` is natural: `n_B = ⌈32 β⁻² log(4K/δ₀)⌉₊` is forced by the Hoeffding step of
p.45. The estimates are a function of the row, with the value `0` off `W`; `Phat w` plays `P̂_{a,b}(w)`.
`w i` is the element of index `i` of `W` in increasing order. The test `j = i + 1` of Split is written
`j ≤ i + 1`; the calls of the algorithm always have `i < j`. -/

/-- The sum of `m` fresh observations at the action `q`. -/
def sumObs {n : ℕ} (q : Act n) : ℕ → QTree (Act n) ℝ
  | 0 => .done 0
  | m + 1 => .query q fun o => qBind (sumObs q m) fun s => .done (o + s)

/-- The fraction of trades in `m` fresh rounds at the action `q`. -/
noncomputable def sampleMean {n : ℕ} (q : Act n) (m : ℕ) : QTree (Act n) ℝ :=
  qBind (sumObs q m) fun s => .done (s / (m : ℝ))

/-- `Estimate` of Algorithm 4, lines 9–15, at the row `w`: `F̂_b(w) − F̂_a(w)`. -/
noncomputable def estimate {n : ℕ} (a b : Idx n) (nB : ℕ) (w : Idx n) : QTree (Act n) ℝ :=
  qBind (sampleMean (a, w) nB) fun Fa => qBind (sampleMean (b, w) nB) fun Fb => .done (Fb - Fa)

/-- `Split(i, j)` of Algorithm 4, lines 16–28. -/
noncomputable def splitRows {n : ℕ} (a b : Idx n) (nB : ℕ) (β : ℝ) (w : ℕ → Idx n) (i j : ℕ)
    (Phat : Idx n → ℝ) : QTree (Act n) (Idx n → ℝ) :=
  if j ≤ i + 1 then
    .done Phat
  else if Phat (w j) - Phat (w i) ≤ β then
    .done fun u =>
      if ∃ k ∈ Finset.Ioo i j, w k = u then (Phat (w i) + Phat (w j)) / 2 else Phat u
  else
    qBind (estimate a b nB (w ((i + j) / 2))) fun e =>
      qBind (splitRows a b nB β w i ((i + j) / 2) (Function.update Phat (w ((i + j) / 2)) e))
        fun P' => splitRows a b nB β w ((i + j) / 2) j P'
termination_by j - i
decreasing_by all_goals omega

/-- `n_B = ⌈32 β⁻² log(4K/δ₀)⌉` (Algorithm 4, line 2). -/
noncomputable def nBOf (n : ℕ) (β δ₀ : ℝ) : ℕ :=
  ⌈32 * β ^ (-2 : ℤ) * Real.log (4 * (Kof n : ℝ) / δ₀)⌉₊

/-- **Algorithm 4, p.44**, `BinS(a, b, β, δ₀, Q, W)`. -/
noncomputable def binS {n : ℕ} (a b : Idx n) (β δ₀ : ℝ) (W : Finset (Idx n)) :
    QTree (Act n) (Idx n → ℝ) :=
  let ws := W.sort (· ≤ ·)
  let w : ℕ → Idx n := fun i => ws.getD i 0
  let M := ws.length - 1
  let nB := nBOf n β δ₀
  qBind (estimate a b nB (w 0)) fun e₀ =>
    let P₀ : Idx n → ℝ := Function.update (fun _ => 0) (w 0) e₀
    if 1 ≤ M then
      qBind (estimate a b nB (w M)) fun e₁ => splitRows a b nB β w 0 M (Function.update P₀ (w M) e₁)
    else
      .done P₀

/-- The rows at which a list of queries collects observations. -/
def rowsOf {n : ℕ} (tr : List (Act n)) : Finset (Idx n) := (tr.map Prod.snd).toFinset

end BilateralOptRegret


