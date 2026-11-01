-- Prove2me | Definitions.Def_MNLStability_ptas
-- name    : MNLStability_ptas
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:29:05.875059+00:00
-- url     : https://prove2.me/theorems/e1bad4c0-3660-4645-8aa8-0153e6dd2ae9
-- title:
--   Program 4: the approximation scheme of Theorem 1
-- statement:
--   `ptas I ε δ` is the algorithm of Theorem 1.
--
--   1. If $\varepsilon\ge1$, return $0$. If $nC\le1$, return $C$ units of every product (for a valid instance, the only product at full stock).
--   2. Set $e=\varepsilon/5$ and compute $w_{\max}$, $w_{\min}$.
--   3. **DP-amenable regime** $w_{\max}\le e\,w_0/n$: return `dpSolve`.
--   4. **Sampling-amenable regime** $w_{\max}>e\,w_0/n$:
--      - *Rounding* (§3.1): $k_i=\lfloor\log_{1+e}(w_i/w_{\min})\rfloor+1$ and $w^\downarrow_i=(1+e)^{k_i-1}w_{\min}$, with $w_0$ unchanged; the classes $W_k=\{i:k_i=k\}$ have uniform rounded weights.
--      - *Universal families* (§4): $\mathcal U_k=$ `family` for each nonempty class, listed by non-increasing price.
--      - *Candidates* (§3.3): one vector from each $\mathcal U_k$, glued by class swapping; kept if it stocks at most $C$ units.
--      - *Selection* (§3.3): with $N$ the product of the family sizes and $\hat\delta=\delta/N$, estimate each candidate's expected revenue under $(w_0,w^\downarrow)$ with `estimate` at accuracy $e$, and return a candidate with the largest estimate.
--
--   **Formalization Note** All information about expected revenues reaches the program through `estimate` and `dpSolve`; it never evaluates the exact expected revenue or the optimum. The constant $e=\varepsilon/5$ is the paper's chain (1−ε)(1−2ε)(1−ε)(1−ε) ≥ 1−5ε, pp.17–18.
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), Theorem 1, pp.5–6; §3, pp.14–18; §2.3, p.13

import Mathlib
import Definitions.Def_MNLStability_Inst
import Definitions.Def_MNLStability_swap
import Definitions.Def_MNLStability_family
import Definitions.Def_MNLStability_estimate
import Definitions.Def_MNLStability_dpSolve

namespace MNLStability

variable {n : ℕ}

/-- The products of class `k` (those with `kcl i = k`), sorted by non-increasing price, ties by
index: one scan of the `n` products, then an insertion sort. -/
noncomputable def classOrder (r : Fin n → ℝ) (kcl : Fin n → ℕ) (k : ℕ) : List (Fin n) :=
  (((List.finRange n).filter fun i => kcl i = k).mergeSort fun i j =>
    decide (r j < r i ∨ (r j = r i ∧ i ≤ j)))

/-- **Program 4: the approximation scheme of Theorem 1** (SSRN:3498325, Theorem 1, pp.5–6; §3,
pp.14–18; §2.3, p.13).

1. If `1 ≤ ε`, return `0`. If `n·C ≤ 1`, stock `C` units of every product (for a valid instance:
   the only product, full stock).
2. `e = ε/5`; `w_max`, `w_min` by scans.
3. **DP-amenable regime** `w_max ≤ e·w₀/n`: return `dpSolve`.
4. **Sampling-amenable regime** `w_max > e·w₀/n`:
   * rounding (§3.1, p.14): `kᵢ = ⌊log(wᵢ/w_min)/log(1 + e)⌋ + 1` and `w↓ᵢ = (1 + e)^{kᵢ−1}·w_min`;
     `w₀` unchanged;
   * universal families (§4): `𝒰_k = family r ord_k C e` for each nonempty class `W_k`, listed
     by `ord_k` (non-increasing price, ties by index);
   * candidates (§3.3, p.16): one vector from each `𝒰_k`, glued by swapping class by class into
     `0`; kept when it has at most `C` units;
   * selection (§3.3, p.17): with `N` the product of the family sizes and `δ̂ = δ/N`, estimate
     the expected revenue of each candidate under `(w₀, w↓)` with `estimate … e δ̂`, and return a
     candidate with the largest estimate (the first one among ties).

**Formalization Note.** All knowledge of the expected revenue comes through `estimate` and
`dpSolve`; the program never evaluates `expR` or `opt`. -/
noncomputable def ptas (I : Inst n) (ε δ : ℝ) : Prog (Fin n → ℕ) := do
  let big ← opn 1 (decide (1 ≤ ε))
  if big then pure 0
  else do
    let tiny ← opn 2 (decide (n * I.C ≤ 1))
    if tiny then opn (n + 1) (fun _ => I.C)
    else do
      let e ← opn 1 (ε / 5)
      let wmax ← foldP (List.finRange n) (fun acc i => opn 2 (max acc (I.wts.w i))) 0
      let wmin ← foldP (List.finRange n) (fun acc i => opn 2 (min acc (I.wts.w i))) wmax
      let dp ← opn 4 (decide (wmax ≤ e * I.wts.w0 / n))
      if dp then dpSolve I.wts I.r I.pM I.C
      else do
        let kcl ← foldP (List.finRange n) (fun (acc : Fin n → ℕ) i =>
          opn 8 (Function.update acc i
            (⌊Real.log (I.wts.w i / wmin) / Real.log (1 + e)⌋₊ + 1))) (fun _ => 0)
        let wdown ← foldP (List.finRange n) (fun (acc : Fin n → ℝ) i =>
          opn (kcl i + 3) (Function.update acc i ((1 + e) ^ (kcl i - 1) * wmin))) (fun _ => 0)
        let K ← foldP (List.finRange n) (fun acc i => opn 2 (max acc (kcl i))) 0
        let ords ← foldP (List.range (K + 1)) (fun (acc : List (List (Fin n))) k => do
          let o ← opn (2 * (n + 1) * (n + 1)) (classOrder I.r kcl k)
          opn (acc.length + 2) (if o = [] then acc else acc ++ [o])) []
        let fams ← foldP ords (fun (acc : List (List (Fin n → ℕ))) o => do
          let F ← family I.r o I.C e
          opn (acc.length + 1) (acc ++ [F])) []
        let N ← foldP fams (fun acc F => opn (F.length + 2) (acc * F.length)) 1
        let δh ← opn 1 (δ / N)
        let best ← foldProd fams (fun (best : (Fin n → ℕ) × Option ℝ) Vs => do
          let cand ← opn (2 * (n + 1) * (Vs.length + 1))
            ((ords.zip Vs).foldl (fun U p => swap p.1.toFinset U p.2) 0)
          let fits ← opn (2 * n + 2) (decide (∑ i, cand i ≤ I.C))
          if fits then do
            let est ← estimate ⟨I.wts.w0, wdown⟩ I.r I.pM cand e δh
            opn 2 (match best.2 with
              | none => (cand, some est)
              | some b => if b < est then (cand, some est) else best)
          else pure best) (0, none)
        pure best.1

end MNLStability


