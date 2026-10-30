-- Prove2me | Definitions.Def_KUMultimodular_fpEval
-- name    : KUMultimodular_fpEval
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:57:37.976887+00:00
-- url     : https://prove2.me/theorems/01d9d3d6-2d1c-4fde-84d6-181a8e8b0621
-- title:
--   The algorithm of Theorem 4.1: multipoint evaluation over a prime field
-- statement:
--   Let $p$ be a prime, $f \in \mathbb F_p[X_0,\dots,X_{m-1}]$ with degree at most $d-1$ in each variable, given by its dense coefficient list, and $\alpha_0,\dots,\alpha_{N-1} \in \mathbb F_p^m$. The algorithm of the proof of Theorem 4.1 computes $f(\alpha_0),\dots,f(\alpha_{N-1})$ as follows.
--
--   1. **Reduce** $f$ modulo $X_j^p - X_j$ for $j = 0,\dots,m-1$, one variable at a time: the slices of the coefficients of $X_j^i$ are added into slot $i$ for $i < p$ and into slot $((i-1) \bmod (p-1)) + 1$ for $i \ge p$. The result $\bar f$ has degree at most $p-1$ in each variable and agrees with $f$ on $\mathbb F_p^m$.
--   2. **Evaluate** $\bar f$ at all of $\mathbb F_p^m$ recursively: write $\bar f = \sum_{i<p} X_0^i f_i(X_1,\dots,X_{m-1})$, evaluate every $f_i$ on all of $\mathbb F_p^{m-1}$, and for each $\beta \in \mathbb F_p^{m-1}$ evaluate the univariate polynomial $\sum_i X_0^i f_i(\beta)$ at all of $\mathbb F_p$ with fast univariate multipoint evaluation. The values are stored in a table of length $p^m$ in lexicographic order.
--   3. **Look up** $\bar f(\alpha_i)$ in the table for $i = 0,\dots,N-1$.
--
--   If $d = 0$ (the zero polynomial) it returns $0$ for every point. Every step is written in the bit-cost model `KUMultimodular.Timed`: each traversal, addition in $\mathbb F_p$, call of fast univariate multipoint evaluation and table look-up is charged.
--
--   **Formalization Note** `fpEval p m d N c α : Timed (Fin N → ZMod p)` reads the coefficient table `c` and the points (charged their bit size) and runs `fpEvalL`, which works on dense lists (`reduceAllT`, `evalAllT`, `readC`). The verification file `Solutions/verification/KUMultimodular_fpEval_check.lean` checks the output against brute-force evaluation on 252 small instances.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (2008), proof of Theorem 4.1, pp. 11–12 (Steps 1–3 and the recursion for Step 2)

import Mathlib
import Definitions.Def_KUMultimodular_Timed
import Definitions.Def_KUMultimodular_densePoly

namespace KUMultimodular

/-! # The algorithm of Theorem 4.1 (multipoint evaluation over a prime field)

Kedlaya–Umans, Dagstuhl Seminar Proceedings 08381 (2008), proof of Theorem 4.1, pp. 11–12:
1. reduce `f` modulo `X_j^p - X_j` for every `j`;
2. compute `f̄(α)` for all `α ∈ 𝔽_p^m`, one variable at a time, by fast univariate multipoint
   evaluation;
3. look up `f̄(α_i)` for `i = 0, …, N-1`.

Polynomials and tables are dense lists in lexicographic order (first variable / first coordinate
most significant). Every traversal pays its ticks in the cost model of `Def_KUMultimodular_Timed`. -/

/-- Coordinatewise sum of two slices in `𝔽_p` (one `fpAddC` and one tick per entry). -/
def vecAddT {p : ℕ} (s g : List (ZMod p)) : Timed (List (ZMod p)) :=
  mapT (fun q => fpAddC q.1 q.2) (List.zip s g)

/-- Add the slices of `g` into the first `g.length` slices of `ss`. -/
def addIntoT {p : ℕ} : List (List (ZMod p)) → List (List (ZMod p)) → Timed (List (List (ZMod p)))
  | s :: ss, g :: gs => do
      let s' ← vecAddT s g
      let r ← addIntoT ss gs
      pure (s' :: r)
  | ss, _ => pure ss

/-- **Step 1, one variable.** `red = [s_0, s_1, …, s_{D-1}]` are the slices of the coefficients of
`X^0, …, X^{D-1}` in the outermost variable `X`. Reducing modulo `X^p - X` sends `X^i` to `X^i` for
`i < p` and to `X^{((i-1) mod (p-1)) + 1}` for `i ≥ p`. The result has exactly `p` slices (zero
slices are added when `D < p`), concatenated. -/
def foldSlicesT (p : ℕ) (red : List (List (ZMod p))) : Timed (List (ZMod p)) := do
  let len := (red.headD []).length
  tick (p * (len * bits p + 1) + 1)
  let first := red.take p
  let slots := first ++ List.replicate (p - first.length) (List.replicate len (0 : ZMod p))
  let groups ← chunksT (fun _ => 0) (p - 1) (red.drop p)
  let slots' ← groups.foldlM (fun acc g => do
      tick 1
      match acc with
      | [] => pure []
      | s0 :: ss => do
          let ss' ← addIntoT ss g
          pure (s0 :: ss')) slots
  flattenT zw slots'

/-- **Step 1** of the proof of Theorem 4.1: the reduction of a dense polynomial modulo
`X_j^p - X_j` for every variable. `pw = [D^{k-1}, …, D^1, D^0]` lists the slice sizes of the
input (degree `< D` in each of `k` variables); the output has degree `< p` in each variable,
stored as a dense list of length `p^k`. -/
def reduceAllT (p : ℕ) : List ℕ → List (ZMod p) → Timed (List (ZMod p))
  | [], l => pure l
  | sz :: rest, l => do
      let slices ← chunksT zw sz l
      let red ← mapT (reduceAllT p rest) slices
      foldSlicesT p red

/-- **Step 2** of the proof of Theorem 4.1 (the recursion on p. 12): the values of a dense
polynomial with degree `< p` in each of `k` variables at all points of `𝔽_p^k`, as a table in
lexicographic order. `pw = [p^{k-1}, …, p^0]`. Write `f = Σ_{i<p} X_0^i f_i`; evaluate every `f_i`
on `𝔽_p^{k-1}` recursively; then for every `β ∈ 𝔽_p^{k-1}` evaluate `Σ_i X_0^i f_i(β)` on all of
`𝔽_p` with one call of fast univariate multipoint evaluation. -/
def evalAllT (p : ℕ) : List ℕ → List (ZMod p) → Timed (List (ZMod p))
  | [], l => pure l
  | sz :: rest, l => do
      let slices ← chunksT zw sz l
      let tabs ← mapT (evalAllT p rest) slices
      let cols ← transposeT zw tabs
      let evs ← mapT (uniEvalAllC p) cols
      let rows ← transposeT zw evs
      flattenT zw rows

/-- `[b^{k-1}, …, b^1, b^0]`, computed with `mulC`. -/
def powsDownT (b k : ℕ) : Timed (List ℕ) := do
  let up ← go k 1
  reverseT up
where
  /-- `go k x = [x, x b, …, x b^{k-1}]`. -/
  go : ℕ → ℕ → Timed (List ℕ)
    | 0, _ => pure []
    | k + 1, x => do
        let y ← mulC x b
        let r ← go k y
        pure (x :: r)

/-- **The algorithm of Theorem 4.1 on dense lists.** Input: the coefficient list `cs` of an
`m`-variate polynomial over `𝔽_p` with degree `< d` in each variable (length `d^m`, lexicographic)
and the points `pts` (each a list of `m` coordinates). Output: the list of values. -/
def fpEvalL (p m d : ℕ) (cs : List (ZMod p)) (pts : List (List (ZMod p))) :
    Timed (List (ZMod p)) := do
  tick (bits d)
  if d = 0 then
    -- the zero polynomial
    mapT (fun _ => pure (0 : ZMod p)) pts
  else do
    -- Step 1: reduce modulo `X_j^p - X_j`
    let pwd ← powsDownT d m
    let red ← reduceAllT p pwd cs
    -- Step 2: all values on `𝔽_p^m`
    let pwp ← powsDownT p m
    let tab ← evalAllT p pwp red
    -- Step 3: look up
    mapT (fun a => readC zw tab 0 (a.map ZMod.val) p) pts

/-- **The algorithm of Theorem 4.1** (Kedlaya–Umans 2008, Theorem 4.1 and its proof, pp. 11–12),
on the paper's input: the coefficient table `c` of `f ∈ 𝔽_p[X_0, …, X_{m-1}]` with degree at most
`d - 1` in each variable and the points `α_0, …, α_{N-1} ∈ 𝔽_p^m`. Reading the input is charged
its bit size. The output is the function `i ↦ f(α_i)` computed by `fpEvalL`. -/
def fpEval (p m d N : ℕ) (c : (Fin m → Fin d) → ZMod p) (α : Fin N → Fin m → ZMod p) :
    Timed (Fin N → ZMod p) := do
  let cs ← mapT (fun a => do tick (zw (c a)); pure (c a)) (lexEnum d m)
  let pts ← mapT (fun i => mapT (fun j => do tick (zw (α i j)); pure (α i j)) (List.finRange m))
    (List.finRange N)
  let out ← fpEvalL p m d cs pts
  pure (fun i => out.getD i 0)

end KUMultimodular


