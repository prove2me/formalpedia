-- Prove2me | Definitions.Def_FracPackCover_Covering_Driver
-- name    : FracPackCover_Covering_Driver
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:48:41.06398+00:00
-- url     : https://prove2.me/theorems/86f493d8-36b6-4c7d-8d37-d5c63d3f0123
-- title:
--   The covering algorithm of §3: initial solution (m oracle calls), phase $\varepsilon=1/6$, and $\varepsilon$-scaling
-- statement:
--   The paper describes in prose (pp. 20–21) how repeated calls to IMPROVE-COVER find an $\varepsilon_0$-approximate solution. This module writes that algorithm down.
--
--   1. **Initial solution.** For each row $i$, call subroutine (7) with $y=e_i$ (costs $a_i$), obtaining $x_i\in P$ maximizing $a_ix$ over $P$; this is $m$ calls. If $a_ix_i<b_i$ for some $i$, stop: there is no exact solution. Otherwise start from $x=\frac1m\sum_i x_i$.
--   2. **First phase ($\varepsilon=1/6$).** If $\lambda(x)\ge1$, output $x$. Otherwise call IMPROVE-COVER$(x,1/6)$, obtaining $x'$. If $\lambda(x')\ge 1$, output $x'$. If $\lambda(x')>2\lambda(x)$ (the call stopped because $\lambda_0$ doubled), repeat the first phase from $x'$. Otherwise the call stopped with $\mathcal C2$: if $\lambda(x')\le 1-3\cdot\frac16=\frac12$, stop with "no exact solution"; else, if $\varepsilon_0\ge\frac12$, output $x'$; else go to step 3 with $x'$.
--   3. **$\varepsilon$-scaling.** In phase $k=1,2,\dots$ let $\varepsilon_k=\frac16 2^{-k}$ and call IMPROVE-COVER$(x,\varepsilon_k)$ once, obtaining $x'$. If $\lambda(x')\ge1-\varepsilon_0$, output $x'$. If the call stopped with $\mathcal C2$ (that is, $\lambda(x')\le2\lambda(x)$) and $\lambda(x')\le1-3\varepsilon_k$, stop with "no exact solution". Otherwise go to phase $k+1$ with $x'$.
--
--   The total number of oracle calls counted is $m$ for the initial solution plus the calls of every IMPROVE-COVER invocation.
--
--   **Formalization Note** One fuel parameter bounds every loop: the while-tests of each IMPROVE-COVER call, the number of calls in the first phase, and the number of scaling phases; `none` means some loop did not finish within the fuel. The checks "$\lambda\ge1$" before each first-phase call and "$\lambda(x')\ge1$" after it are the paper's "IMPROVE-COVER must output an exact solution"; "the call ended with $\mathcal C2$" is read off as $\lambda(x')\le2\lambda(x)$, since the while-test of Figure 3 checks $\lambda\le2\lambda_0$ first. The choices the prose leaves open are listed in the mission's moderation notes.
-- source:
--   Plotkin, Shmoys, Tardos, Fast Approximation Algorithms for Fractional Packing and Covering Problems, Cornell ORIE Tech. Rep. 999 (1992), pp. 20–21, the initial solution before Lemma 3.6 and the driver before Theorem 3.7

import Mathlib
import Definitions.Def_FracPackCover_Covering_Basic
import Definitions.Def_FracPackCover_Covering_ImproveCover

namespace FracPackCover.Covering

/-! # The covering algorithm of §3 (pp. 20–21): initial solution, phase `ε = 1/6`, `ε`-scaling

The paper describes the driver in prose. This file writes it down. -/

/-- The outcome of the covering algorithm: an approximate solution `x`, or the claim that no exact
solution exists. -/
inductive CoverOutcome (n : ℕ) where
  | approx (x : Fin n → ℝ)
  | infeasible

open Classical in
/-- The initial solution (p. 20, before Lemma 3.6). For each row `i` call subroutine (7) with
`y = e_i` (costs `a_i`), getting `x_i = orc e_i`, a maximizer of `a_i x` over `P`: `m` calls in all.
If `a_i x_i < b_i` for some `i`, return `none` ("no exact solution"); otherwise return
`some ((1/m) ∑_i x_i)`. -/
noncomputable def initCover {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (orc : (Fin m → ℝ) → (Fin n → ℝ)) : Option (Fin n → ℝ) :=
  if ∃ i, rowVal A (orc (Pi.single i 1)) i < b i then none
  else some ((1 / (m : ℝ)) • ∑ i, orc (Pi.single i 1))

/-- `ε_k = (1/6) 2^{−k}`, the error parameter of the `k`-th `ε`-scaling phase (`k ≥ 1`); `ε_0 = 1/6`
is the first phase's. -/
noncomputable def scaleEps (k : ℕ) : ℝ := (1 / 6) * (1 / 2) ^ k

open Classical in
/-- The `ε`-scaling phases (pp. 20–21) with target `ε₀`, starting at phase `k`. Each phase calls
IMPROVE-COVER(x, ε_k) once (with `innerFuel` while-tests) on the current `x`, getting `x'` with `c`
oracle calls. If `λ(x') ≥ 1 − ε₀`, output `x'`. Else, if the call ended with 𝒞2 (that is,
`λ(x') ≤ 2λ(x)`, the stopping test of Figure 3 did not fail on its first clause) and
`λ(x') ≤ 1 − 3ε_k`, stop: no exact solution. Otherwise go to phase `k + 1` with `x'`. `fuel` bounds the
number of phases; `none` means a call or the phase loop ran out of fuel. `calls` accumulates the oracle
calls. -/
noncomputable def scalingPhases {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (orc : (Fin m → ℝ) → (Fin n → ℝ)) (ρ ε₀ : ℝ) (innerFuel : ℕ) :
    ℕ → ℕ → (Fin n → ℝ) → ℕ → Option (CoverOutcome n × ℕ)
  | 0, _, _, _ => none
  | fuel + 1, k, x, calls =>
    match improveCover A b orc ρ (scaleEps k) x innerFuel with
    | none => none
    | some (x', c) =>
      if 1 - ε₀ ≤ lam A b x' then some (.approx x', calls + c)
      else if lam A b x' ≤ 2 * lam A b x ∧ lam A b x' ≤ 1 - 3 * scaleEps k then
        some (.infeasible, calls + c)
      else scalingPhases A b orc ρ ε₀ innerFuel fuel (k + 1) x' (calls + c)

open Classical in
/-- The first phase, `ε = 1/6` (p. 20). If `λ(x) ≥ 1`, output `x` (an exact solution). Otherwise call
IMPROVE-COVER(x, 1/6), getting `x'` with `c` oracle calls. If `λ(x') ≥ 1`, output `x'`. If
`λ(x') > 2λ(x)` (the call stopped because `λ0` doubled), repeat the first phase with `x'`. Otherwise the
call ended with 𝒞2: if `λ(x') ≤ 1 − 3·(1/6) = 1/2`, stop (no exact solution, Lemma 3.1); else, if
`ε₀ ≥ 1/2`, output `x'`; else start the `ε`-scaling phases at `k = 1` with `x'`. -/
noncomputable def firstPhase {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (orc : (Fin m → ℝ) → (Fin n → ℝ)) (ρ ε₀ : ℝ) (innerFuel : ℕ) :
    ℕ → (Fin n → ℝ) → ℕ → Option (CoverOutcome n × ℕ)
  | 0, _, _ => none
  | fuel + 1, x, calls =>
    if 1 ≤ lam A b x then some (.approx x, calls)
    else
      match improveCover A b orc ρ (1 / 6) x innerFuel with
      | none => none
      | some (x', c) =>
        if 1 ≤ lam A b x' then some (.approx x', calls + c)
        else if 2 * lam A b x < lam A b x' then
          firstPhase A b orc ρ ε₀ innerFuel fuel x' (calls + c)
        else if lam A b x' ≤ 1 / 2 then some (.infeasible, calls + c)
        else if 1 / 2 ≤ ε₀ then some (.approx x', calls + c)
        else scalingPhases A b orc ρ ε₀ innerFuel innerFuel 1 x' (calls + c)

/-- The whole covering algorithm of §3 for target `ε₀` (the algorithm of Theorem 3.7), with `fuel`
bounding every loop (the while-tests of each IMPROVE-COVER call, and the number of calls in each
phase). It returns `some (outcome, calls)` if it stops within the fuel, `calls` being the total number
of calls to subroutine (7): `m` for the initial solution plus those of every IMPROVE-COVER call. -/
noncomputable def coverAlgorithm {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (orc : (Fin m → ℝ) → (Fin n → ℝ)) (ρ ε₀ : ℝ) (fuel : ℕ) :
    Option (CoverOutcome n × ℕ) :=
  match initCover A b orc with
  | none => some (.infeasible, m)
  | some x => firstPhase A b orc ρ ε₀ fuel fuel x m

end FracPackCover.Covering


