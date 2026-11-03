-- Prove2me | Definitions.Def_FreeOrderEPTAS_freeOrder
-- name    : FreeOrderEPTAS_freeOrder
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:27:17.105008+00:00
-- url     : https://prove2.me/theorems/2645ca67-c49f-4ea7-97ad-f23fabfab972
-- title:
--   The Free-Order Prophets algorithm as a program
-- statement:
--   The algorithm of Theorem 3.1 at accuracy $\varepsilon$, as an instrumented program with an oracle $o$:
--
--   1. $\epsilon=1/q$ with $q=\lceil14/\min\{\varepsilon,1\}\rceil$;
--   2. $\sigma_0$ is the identity and $v_0=V(\sigma_0)$ is computed by the recursion; if $v_0=0$, return $\sigma_0$;
--   3. for each estimate $E=v_0(1+\epsilon)^k$, $0\le k\le\lceil\log2/\log(1+\epsilon)\rceil$, each $K\le q$, and each vector of BaseGuess and DeltaGuess values on the grid $\{k\epsilon^2E:0\le k\le\lceil1/(\epsilon^2(1-\epsilon))\rceil\}$: compute the loads $\ell_{ij}=o(j,b_i)-b_i$, build the scaled instance, run `santaClaus` at accuracy $\epsilon$, and on an assignment build $\sigma$ and compute its value by the recursion;
--   4. return the candidate, $\sigma_0$ included, with the largest value.
--
--   `recursionP` is the recursion through the oracle, `guessGrid` the grid and `candidate` one pass of step 3.
--
--   **Formalization Note** The program has no access to the laws: it receives a function `o`, called through the counted `callOrc`. The printed grid stops below $\mathrm{OPT}$ and is extended.
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, §§3.2–3.5, pp.17–20

import Mathlib
import Definitions.Def_FreeOrderEPTAS_santaClaus
import Definitions.Def_FreeOrderEPTAS_prophetInstance
import Definitions.Def_FreeOrderEPTAS_orderOf

namespace FreeOrderEPTAS

variable {n : ℕ}

/-- The recursion `R_{n+1} = 0`, `R_t = E[max{X_{σ(t)}, R_{t+1}}]` (p.20), run backwards through the
oracle: `n` queries, each with a read of `σ t`. -/
noncomputable def recursionP (o : Fin n → ℝ → ℝ) (σ : Equiv.Perm (Fin n)) : Prog ℝ :=
  foldP (List.finRange n).reverse (fun v t => do
    let j ← opn 1 (σ t)
    callOrc o j v) 0

/-- The guess grid `{k ϵ²E : 0 ≤ k ≤ G}` (the printed grid stops at `(1 - ϵ²) E`, below `OPT`). -/
noncomputable def guessGrid (ϵ E : ℝ) (G : ℕ) : List ℝ :=
  (List.range (G + 1)).map fun k => (k : ℝ) * (ϵ ^ 2 * E)

/-- One candidate of §§3.4–3.5 (arXiv:2007.13121v3, pp.18–20), for `m` machines and the guess list
`g`, whose entries `0, …, m - 1` are BaseGuess and whose entries `m, …, 2m - 1` are DeltaGuess.

The loads `ℓ_ij = E[max{X_j, b_i}] - b_i` take one oracle query each. The scaled instance takes at
most 4 operations per `(i, j)`. On an assignment `x` from `santaClaus ϵ`, the permutation `σ`
is built (key table: at most `m` reads per job; insertion sort: at most `(n + 1)²` operations), and
`σ` replaces the best candidate so far if its recursion value is larger. -/
noncomputable def candidate (ϵ : ℝ) (o : Fin n → ℝ → ℝ) (lp : LPSolver) (rnd : Rounding) (m : ℕ)
    (best : Equiv.Perm (Fin n) × ℝ) (g : List ℝ) : Prog (Equiv.Perm (Fin n) × ℝ) := do
  let w : Fin m → Fin n → ℝ ← tabP fun i => tabP fun j => do
    let bi ← opn 1 (g.getD i.val 0)
    let v ← callOrc o j bi
    opn 1 (v - bi)
  tick (4 * (m + 1) * (n + 1))
  let Δ : Fin m → ℝ := fun i => g.getD (m + i.val) 0
  match ← santaClaus ϵ (prophetInstance w Δ) lp rnd with
  | none => pure best
  | some x => do
    tick ((n + 1) * (m + 1) + (n + 1) * (n + 1))
    let σ := orderOf x
    let v ← recursionP o σ
    let keep ← opn 1 (decide (v ≤ best.2))
    pure (if keep then best else (σ, v))

/-- The algorithm of §3 (arXiv:2007.13121v3, pp.17–20) for Theorem 3.1, at accuracy `ε`.

1. `ϵ = 1/q` with `q = ⌈14 / min{ε, 1}⌉`.
2. `σ₀` is the identity, and `v₀ = V(σ₀)` is computed by the recursion. If `v₀ = 0`, return `σ₀`.
3. For each estimate `E = v₀ (1 + ϵ)^k`, `0 ≤ k ≤ ⌈log 2 / log(1 + ϵ)⌉`; each `K ≤ q`; and each
   vector of `2 (2K + 1)` guesses on the grid `{k ϵ²E : 0 ≤ k ≤ ⌈1/(ϵ²(1 - ϵ))⌉}`: run `candidate`.
4. Return the candidate, `σ₀` included, with the largest recursion value.

The program receives the laws only through `o`, a function it calls with `callOrc`. -/
noncomputable def freeOrder (ε : ℝ) (o : Fin n → ℝ → ℝ) (lp : LPSolver) (rnd : Rounding) :
    Prog (Equiv.Perm (Fin n)) := do
  let q ← opn 3 ⌈14 / min ε 1⌉₊
  let ϵ ← opn 1 (1 / (q : ℝ))
  let v₀ ← recursionP o 1
  let stop ← opn 1 (decide (v₀ ≤ 0))
  if stop then
    pure 1
  else do
    let kmax ← opn 5 ⌈Real.log 2 / Real.log (1 + ϵ)⌉₊
    let G ← opn 6 ⌈1 / (ϵ ^ 2 * (1 - ϵ))⌉₊
    let best ← foldP (List.range (kmax + 1)) (fun best k => do
      let E ← opn (k + 2) (v₀ * (1 + ϵ) ^ k)
      foldP (List.range (q + 1)) (fun best K => do
        let grid ← opn (3 * (G + 2)) (guessGrid ϵ E G)
        foldProd (List.replicate (2 * (2 * K + 1)) grid) (candidate ϵ o lp rnd (2 * K + 1)) best)
        best) ((1 : Equiv.Perm (Fin n)), v₀)
    pure best.1

end FreeOrderEPTAS


