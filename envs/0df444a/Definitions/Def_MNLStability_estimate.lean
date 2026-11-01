-- Prove2me | Definitions.Def_MNLStability_estimate
-- name    : MNLStability_estimate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:59.642653+00:00
-- url     : https://prove2.me/theorems/3a78aea3-1834-4678-b756-778b16c86ef8
-- title:
--   Program 2: the sampling evaluation oracle of §2.3
-- statement:
--   `estimate w r p_M U e δ̂` returns a random estimate of $\mathbb E[R(U)]$.
--
--   1. Compute $P_1=\Pr[M\ge1]$ by a scan of the support. If $P_1=0$ or $U=0$, return $0$.
--   2. Set $q=w_{\min}/(w_0+n\,w_{\max})$ and $\zeta=\bigl\lceil(\|U\|_1/(qe))^2\log(2/\hat\delta)/2\bigr\rceil$.
--   3. Repeat $\zeta$ times, independently: draw $m$ from the law of $M$ conditioned on $M\ge1$, and simulate one sample path with $m$ customers. A simulated round computes the assortment $S$ in stock and $g=w(S)/(w_0+w(S))$, draws the number $T$ of no-purchase customers before the next purchase (geometric with parameter $g$), stops if fewer than $T+1$ customers remain, and otherwise draws the purchased product with masses $w_i/w(S)$, removes one unit and collects its price.
--   4. Return $P_1$ times the average of the $\zeta$ simulated revenues.
--
--   The paper cites this oracle from Aouad et al. (2018b, App. A.2); the program is the standard Monte Carlo estimator with a Hoeffding sample size.
--
--   **Formalization Note** The law of $M$ is read only through its support list and values, one unit per entry. A simulated run uses at most $\|U\|_1+1$ rounds, since every round that does not end the run sells a unit.
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), §2.3, p.13 (cited from Aouad et al. 2018b, App. A.2)

import Mathlib
import Definitions.Def_MNLStability_Prog
import Definitions.Def_MNLStability_step

namespace MNLStability

variable {n : ℕ}

/-- The state of one simulated run: the remaining stock `V`, the number `t` of customers still to
arrive, the revenue `Y` collected so far, and whether the run has ended. -/
structure SimState (n : ℕ) where
  /-- Remaining stock. -/
  V : Fin n → ℕ
  /-- Customers still to arrive. -/
  t : ℕ
  /-- Revenue so far. -/
  Y : ℝ
  /-- The run has ended. -/
  done : Bool

/-- One round of the simulator: if the run is not over, compute the assortment `S` in stock and
`g = w(S)/(w₀ + w(S))`, the probability that a customer purchases; draw the number `T` of
no-purchase customers before the next purchase (geometric, cost `1`); if `T + 1 > t` the run ends;
otherwise `T + 1` customers are used up, the purchased product `i ∈ S` is drawn with masses
`wᵢ/w(S)` (cost `|S| + 1`), one unit of `i` is removed and `rᵢ` is collected. -/
noncomputable def simRound (wts : Weights n) (r : Fin n → ℝ) (st : SimState n) :
    Prog (SimState n) := do
  if st.done then opn 1 st
  else do
    let S ← opn (2 * n + 2) ((List.finRange n).filter fun i => 0 < st.V i)
    let wS ← opn (2 * n + 2) (S.map wts.w).sum
    let ended ← opn 2 (decide (S = [] ∨ st.t = 0))
    if ended then opn 1 { st with done := true }
    else do
      let g ← opn 2 (wS / (wts.w0 + wS))
      let T ← drawGeom g
      let late ← opn 2 (decide (st.t < T + 1))
      if late then opn 1 { st with done := true }
      else do
        let masses ← opn (2 * S.length + 1) (S.map fun i => wts.w i / wS)
        let k ← drawCat masses
        match S[k]? with
        | none => opn 1 { st with done := true }
        | some i =>
          opn 6 (SimState.mk (Function.update st.V i (st.V i - 1)) (st.t - (T + 1)) (st.Y + r i) false)

/-- The revenue of one simulated sample path with `m` customers from the inventory vector `U`
(`‖U‖₁ = nU`): `nU + 1` rounds of `simRound` suffice, since every round that does not end the run
sells a unit. -/
noncomputable def simulate (wts : Weights n) (r : Fin n → ℝ) (U : Fin n → ℕ) (m nU : ℕ) :
    Prog ℝ := do
  let st ← foldP (List.range (nU + 1)) (fun st _ => simRound wts r st)
    (SimState.mk U m 0 false)
  pure st.Y

/-- **Program 2: the evaluation oracle** of SSRN:3498325, §2.3, p.13 (cited from Aouad et al. 2018b,
App. A.2): a random estimate of `E[R(U)]` by independent simulations.

1. `P₁ = Pr[M ≥ 1]`, by a scan of the support of `M`. If `P₁ = 0` or `U = 0`, return `0`.
2. `q = w_min/(w₀ + n·w_max)` and `ζ = ⌈(‖U‖₁/(q·e))² · log(2/δ̂) / 2⌉`.
3. Repeat `ζ` times: draw `m` from the law of `M` conditioned on `M ≥ 1` (cost `s + 1`) and simulate
   one sample path with `m` customers.
4. Return `P₁` times the average of the `ζ` simulated revenues.

**Formalization Note.** The law of `M` is read only through its support list and values, at one
unit per entry. A simulated run skips the customers who buy nothing with one geometric draw per
purchase, so its cost does not depend on the value of `m`. -/
noncomputable def estimate (wts : Weights n) (r : Fin n → ℝ) (pM : ℕ →₀ ℝ) (U : Fin n → ℕ)
    (e δh : ℝ) : Prog ℝ := do
  let supp ← opn (pM.support.card + 1) (pM.support.sort (· ≤ ·))
  let P1 ← foldP supp (fun acc m => opn 3 (if 1 ≤ m then acc + pM m else acc)) 0
  let nU ← foldP (List.finRange n) (fun acc i => opn 2 (acc + U i)) 0
  let triv ← opn 2 (decide (P1 ≤ 0 ∨ nU = 0))
  if triv then pure 0
  else do
    let wmax ← foldP (List.finRange n) (fun acc i => opn 2 (max acc (wts.w i))) 0
    let wmin ← foldP (List.finRange n) (fun acc i => opn 2 (min acc (wts.w i))) wmax
    let q ← opn 3 (wmin / (wts.w0 + n * wmax))
    let ζ ← opn 10 ⌈((nU : ℝ) / (q * e)) ^ 2 * Real.log (2 / δh) / 2⌉₊
    let pos ← opn (2 * supp.length + 1) (supp.filter (1 ≤ ·))
    let masses ← opn (2 * pos.length + 1) (pos.map fun m => pM m / P1)
    let total ← foldP (List.range ζ) (fun acc _ => do
      let k ← drawCat masses
      let m ← opn 1 (pos.getD k 0)
      let Y ← simulate wts r U m nU
      opn 1 (acc + Y)) 0
    opn 3 (P1 * (total / ζ))

end MNLStability


