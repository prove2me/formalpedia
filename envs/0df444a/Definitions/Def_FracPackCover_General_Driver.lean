-- Prove2me | Definitions.Def_FracPackCover_General_Driver
-- name    : FracPackCover_General_Driver
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:19.85007+00:00
-- url     : https://prove2.me/theorems/2157c9dd-7518-4971-956b-0d5f50cd59da
-- title:
--   The driver of §4: repeated calls to IMPROVE-GENERAL until an ε-approximate solution or an infeasibility certificate
-- statement:
--   The **driver** (p. 27) solves the GENERAL problem to accuracy $\varepsilon$ by repeated calls to IMPROVE-GENERAL, starting from any point $x \in P$:
--
--   1. If $\lambda(x) \le \varepsilon$, output the $\varepsilon$-approximate solution $x$ and stop.
--   2. Otherwise call IMPROVE-GENERAL on $x$; let $x'$ be its output.
--   3. If the call ended because $x'$ and its dual solution satisfy $(\mathcal G2)$ (with $\lambda(x') \ge \lambda_0/2$): output $x'$ if $\lambda(x') \le \varepsilon$; otherwise report that no exact solution exists, and stop.
--   4. Otherwise (the call ended with $\lambda(x') < \lambda_0/2$), repeat from step 1 with $x \leftarrow x'$.
--
--   The total number of oracle calls is the sum over the calls of IMPROVE-GENERAL.
--
--   **Choices the prose leaves open.** The paper checks $\lambda \le \varepsilon$ on each output; the driver here also checks it before the first call, so no call is ever made with $\lambda_0 \le \varepsilon$ (in particular never with $\lambda_0 \le 0$, where $\alpha$ is undefined). The infeasibility exit is taken only when the call stopped on its own $(\mathcal G2)$ test, where $(\mathcal G1)$ holds by Lemma 4.2; an output with $\lambda(x') < \lambda_0/2$ leads to another call.
--
--   **Formalization Note.** A single fuel bound limits both the number of driver rounds and the loop tests of each call; the main theorem asserts that a fuel at least its call bound suffices.
-- source:
--   Plotkin, Shmoys, Tardos, Fast Approximation Algorithms for Fractional Packing and Covering Problems, Cornell ORIE Tech. Rep. 999 (1992), p. 27, paragraph before Theorem 4.5

import Mathlib
import Definitions.Def_FracPackCover_General_Improve

namespace FracPackCover.General

/-!
# The driver of §4 (p. 27): repeated calls to IMPROVE-GENERAL
-/

/-- What the driver reports. -/
inductive DriverOutcome (n : ℕ)
  /-- an ε-approximate solution `x` (`λ(x) ≤ ε`) -/
  | approx (x : Fin n → ℝ)
  /-- "there does not exist an exact solution" -/
  | infeasible
  /-- the fuel bound was reached before either termination condition -/
  | outOfFuel

/-- Outcome of the driver and the total number of oracle calls. -/
structure DriverResult (n : ℕ) where
  outcome : DriverOutcome n
  calls : ℕ

open Classical in
/-- The driver loop. Before each call it checks `λ(x) ≤ ε` and, if so, outputs `x` (so no call is
made with `λ₀ ≤ ε`). Otherwise it calls IMPROVE-GENERAL (inner fuel `inner`) on `x`. If that call
ended on its (𝒢2) test, the output `x'` satisfies (𝒢2) with `λ(x') ≥ λ₀/2`: the driver outputs `x'`
if `λ(x') ≤ ε` and otherwise reports that no exact solution exists. If the call ended with
`λ(x') < λ₀/2`, the driver repeats with input `x'`. `c` accumulates oracle calls. -/
noncomputable def driverLoop {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ)
    (b d : Fin m → ℝ) (ρ ε : ℝ) (orc : (Fin m → ℝ) → (Fin n → ℝ)) (inner : ℕ) :
    ℕ → (Fin n → ℝ) → ℕ → DriverResult n
  | 0, _, c => ⟨.outOfFuel, c⟩
  | k + 1, x, c =>
    if lam A b d x ≤ ε then ⟨.approx x, c⟩
    else
      let r := improveGeneral A b d ρ orc inner x
      match r.exit with
      | .outOfFuel => ⟨.outOfFuel, c + r.calls⟩
      | .relaxedOpt =>
        if lam A b d r.point ≤ ε then ⟨.approx r.point, c + r.calls⟩
        else ⟨.infeasible, c + r.calls⟩
      | .lambdaHalved => driverLoop A b d ρ ε orc inner k r.point (c + r.calls)

/-- The algorithm of Theorem 4.5 started at `x₀ ∈ P`, with `fuel` bounding both the number of
driver rounds and each call's loop tests. -/
noncomputable def generalDriver {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ)
    (b d : Fin m → ℝ) (ρ ε : ℝ) (orc : (Fin m → ℝ) → (Fin n → ℝ)) (fuel : ℕ)
    (x0 : Fin n → ℝ) : DriverResult n :=
  driverLoop A b d ρ ε orc fuel fuel x0 0

end FracPackCover.General


