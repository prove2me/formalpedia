-- Prove2me | Definitions.Def_MNLStability_dpSolve
-- name    : MNLStability_dpSolve
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:23.09666+00:00
-- url     : https://prove2.me/theorems/9668039c-3e94-4198-9663-88dbab89e225
-- title:
--   Program 3: the dynamic program of the DP-amenable regime
-- statement:
--   `dpSolve w r p_M C` maximizes the separable surrogate $G(U)=\sum_ir_i\,\mathbb E[\min(U_i,\mathrm{Bin}(M,w_i/w_0))]$ over the vectors with $\sum_iU_i\le C$.
--
--   1. For each product $i$ and each support point $m$ of $M$, compute $\Pr[\mathrm{Bin}(m,p_i)=k]$ for $k\le C$: $(1-p_i)^m$ by repeated squaring, then $\Pr[\cdot=k+1]=\Pr[\cdot=k]\cdot\frac{m-k}{k+1}\cdot\frac{p_i}{1-p_i}$. Accumulate the tails $\Pr[\mathrm{Bin}(M,p_i)\ge j]$ and the prefix sums $g_i(u)=\mathbb E[\min(u,\mathrm{Bin}(M,p_i))]$.
--   2. Knapsack recursion $D_i(c)=\max_{u\le c}\bigl(D_{i-1}(c-u)+r_ig_i(u)\bigr)$ with $D_0\equiv0$, recording the least maximizing $u$.
--   3. Backtrack from $c=C$ to read off a maximizer.
--
--   The paper cites the dynamic program from Aouad et al. (2018b, App. A.3).
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), §2.3, p.13 (cited from Aouad et al. 2018b, App. A.3)

import Mathlib
import Definitions.Def_MNLStability_Prog
import Definitions.Def_MNLStability_Weights

namespace MNLStability

variable {n : ℕ}

/-- The binomial probabilities `Pr[Bin(m, p) = k]`, `k = 0, …, C`: `(1 − p)^m` by repeated squaring,
then `Pr[Bin(m,p) = k+1] = Pr[Bin(m,p) = k] · ((m − k)/(k + 1)) · (p/(1 − p))`. -/
noncomputable def binRow (p : ℝ) (m C : ℕ) : Prog (List ℝ) := do
  let b0 ← powP (1 - p) m
  let ratio ← opn 3 (p / (1 - p))
  let st ← foldP (List.range C) (fun (acc : List ℝ × ℝ) k =>
    let b := acc.2 * (((m : ℝ) - k) / (k + 1)) * ratio
    opn (acc.1.length + 6) (acc.1 ++ [b], b)) ([b0], b0)
  pure st.1

/-- `g(u) = E[min(u, Bin(M, p))]` for `u = 0, …, C`, from `Pr[Bin(M, p) ≥ j]`,
`j = 1, …, C`: for each support point `m` of `M` (in the list `supp`), the tail probabilities
`1 − Σ_{k<j} Pr[Bin(m,p) = k]`, weighted by `Pr[M = m]` and accumulated; then prefix sums. -/
noncomputable def gRow (p : ℝ) (pM : ℕ →₀ ℝ) (supp : List ℕ) (C : ℕ) : Prog (List ℝ) := do
  let T ← foldP supp (fun (T : List ℝ) m => do
    let row ← binRow p m C
    let pm ← opn 1 (pM m)
    opn (6 * (C + 1)) ((List.range C).map fun j =>
      T.getD j 0 + pm * (1 - ((row.take (j + 1)).sum)))) (List.replicate C 0)
  opn (3 * (C + 1)) ((List.range (C + 1)).map fun u => (T.take u).sum)

/-- **Program 3: the dynamic program of the DP-amenable regime** (SSRN:3498325, §2.3, p.13; cited
from Aouad et al. 2018b, App. A.3): maximize `G(U) = Σ_i r_i · E[min(U_i, Bin(M, w_i/w₀))]` over
the vectors with `Σ_i U_i ≤ C`.

1. For each product, `g_i(u) = E[min(u, Bin(M, w_i/w₀))]` for `u ≤ C` (`gRow`).
2. Knapsack recursion `D_i(c) = max_{u ≤ c} (D_{i−1}(c − u) + r_i·g_i(u))`, `D_0 ≡ 0`, with the least
   maximizing `u` recorded.
3. Backtrack from `c = C` to read off a maximizer.

**Formalization Note.** The law of `M` is read through its support list and values only. Storing
the row of maximizing choices of product `i` in the table costs `C + 2` (one write per entry). -/
noncomputable def dpSolve (wts : Weights n) (r : Fin n → ℝ) (pM : ℕ →₀ ℝ) (C : ℕ) :
    Prog (Fin n → ℕ) := do
  let supp ← opn (pM.support.card + 1) (pM.support.sort (· ≤ ·))
  let tabs ← foldP (List.finRange n) (fun (st : List ℝ × List (List ℕ)) i => do
    let p ← opn 2 (wts.w i / wts.w0)
    let g ← gRow p pM supp C
    let ri ← opn 1 (r i)
    let row ← foldP (List.range (C + 1)) (fun (acc : List ℝ × List ℕ) c => do
      let best ← foldP (List.range (c + 1)) (fun (b : Option (ℝ × ℕ)) u =>
        let v := st.1.getD (c - u) 0 + ri * g.getD u 0
        opn 8 (match b with
          | none => some (v, u)
          | some (bv, bu) => if bv < v then some (v, u) else some (bv, bu))) none
      let bp := best.getD (0, 0)
      opn (acc.1.length + acc.2.length + 2) (acc.1 ++ [bp.1], acc.2 ++ [bp.2])) ([], [])
    opn (C + 2) (row.1, st.2 ++ [row.2])) (List.replicate (C + 1) 0, [])
  let res ← foldP (List.finRange n).reverse (fun (acc : (Fin n → ℕ) × ℕ) i => do
    let u ← opn 3 ((tabs.2.getD i.val []).getD acc.2 0)
    opn 3 (Function.update acc.1 i u, acc.2 - u)) (0, C)
  pure res.1

end MNLStability


