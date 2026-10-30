-- Prove2me | Definitions.Def_PlotkinShmoysTardos_improveGeneral
-- name    : PlotkinShmoysTardos_improveGeneral
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:51:17.596609+00:00
-- url     : https://prove2.me/theorems/bdd51d10-e935-452e-95f4-0ffeffcc488f
-- title:
--   Procedure IMPROVE-GENERAL and the relaxed decision procedure of Theorem 4.5, as state machines with call counters
-- statement:
--   **IMPROVE-GENERAL** (Figure 4). On input $x\in P$ with $\lambda_0=\lambda(x)$, set
--   $$
--   \alpha=4\lambda_0^{-1}\ln(6m\rho\lambda_0^{-1}),\qquad \sigma=\frac{\lambda_0}{24\alpha\rho^2}.
--   $$
--   While $\lambda(x)\ge\lambda_0/2$ and $x$ and its dual $y$ do not satisfy G2: let $y_i=\frac1{d_i}e^{\alpha(a_ix-b_i)/d_i}$, find a minimum-cost point $\tilde x\in P$ for the costs $y^tA$ by one call to subroutine (10), and set $x\leftarrow(1-\sigma)x+\sigma\tilde x$. Return $x$.
--
--   One step of the machine, at the current iterate $x$:
--   1. if $\lambda(x)<\lambda_0/2$, the call returns (exit reason *halved*);
--   2. otherwise it computes $y$, makes one call $\tilde x=O(y)$, and takes $C_{\mathcal G}(y)=y^t(A\tilde x-b)$; if G2 holds, the call returns (exit reason *G2*);
--   3. otherwise it moves to $(1-\sigma)x+\sigma\tilde x$.
--
--   **The driver** (p. 27). Starting from $x_0\in P$: if $\lambda(x)\le\varepsilon$, output the $\varepsilon$-approximate solution $x$ and stop; otherwise, if the last call returned because G2 held, output *infeasible* and stop; otherwise call IMPROVE-GENERAL on the current point, with new $\lambda_0$, $\alpha$, $\sigma$.
--
--   The machine counts the two costs named in Theorem 4.5: the number of calls to the subroutine, and the number of iterates whose $Ax$ is computed (the start point and every new iterate). Arithmetic and exponentiation are free, as in the paper's model of computation (§1, p. 5).
--
--   **Formalization Note** `callStep`/`callRun` are one call (counters from zero, exit tag `running`/`halved`/`g2`); `runStep`/`run` are the driver, whose counters are cumulative; both are iterated with `Nat.iterate`, so termination is a statement about some step count. The driver tests $\lambda\le\varepsilon$ before the first call as well; the paper's first call would be undefined when $\lambda(x_0)\le0$. The algorithm sees $P$ only through the subroutine $O$.
-- source:
--   Plotkin, Shmoys, Tardos, Fast Approximation Algorithms for Fractional Packing and Covering Problems, Cornell ORIE Technical Report No. 999 (Feb. 1992), Figure 4, p. 25 (IMPROVE-GENERAL); §4, p. 27 (driver paragraph); §1, p. 5 (model of computation)

import Mathlib
import Definitions.Def_PlotkinShmoysTardos_relaxedOptimality

namespace PlotkinShmoysTardos

/-! # Procedure IMPROVE-GENERAL and the driver of Theorem 4.5
(Plotkin–Shmoys–Tardos, TR 999, 1992, Figure 4, p. 25, and §4, p. 27)

Both are deterministic state machines, iterated with `Nat.iterate`. The algorithm sees the convex
set `P` only through a minimization subroutine `O` (subroutine (10)), and sees `A` only through
`A x` at its own iterates. Computation model (§1, p. 5): exact real arithmetic, exponentiation as
a single step; the machine counts the two costs of Theorem 4.5, the calls to `O` (`calls`) and
the iterates whose `A x` is computed (`evals`). -/

/-- Why a call of IMPROVE-GENERAL is (not yet) finished. -/
inductive Tag
  /-- the while loop is still running -/
  | running
  /-- the loop exited because `maxᵢ (aᵢ x − bᵢ)/dᵢ < λ₀/2` -/
  | halved
  /-- the loop exited because `x` and its dual `y` satisfy (G2) -/
  | g2
  deriving DecidableEq

/-- State of IMPROVE-GENERAL: the current iterate, the exit tag, the number of oracle calls and
the number of new iterates whose `A x` was computed. -/
structure CallState (n : ℕ) where
  x : Fin n → ℝ
  tag : Tag
  calls : ℕ
  evals : ℕ

/-- `α ← 4 λ₀⁻¹ ln(6 m ρ λ₀⁻¹)` (Figure 4). -/
noncomputable def alphaOf (m : ℕ) (ρ lam0 : ℝ) : ℝ :=
  4 / lam0 * Real.log (6 * m * ρ / lam0)

/-- `σ ← λ₀ / (24 α ρ²)` (Figure 4). -/
noncomputable def sigmaOf (m : ℕ) (ρ lam0 : ℝ) : ℝ :=
  lam0 / (24 * alphaOf m ρ lam0 * ρ ^ 2)

/-- **One step of IMPROVE-GENERAL** (Figure 4, p. 25), for the call whose input value is `lam0`
(`λ₀`, so `α = alphaOf m ρ lam0`, `σ = sigmaOf m ρ lam0` are fixed for the whole call).
At the current iterate `x`, with `λ = maxᵢ (aᵢ x − bᵢ)/dᵢ`:
* if `λ < λ₀/2`, the loop exits (tag `halved`);
* otherwise `yᵢ = (1/dᵢ) e^{α (aᵢ x − bᵢ)/dᵢ}` and one call `x̃ = O y` to subroutine (10) is made;
  `C_G(y)` is the cost `yᵗ(A x̃ − b)` of that point; if (G2) holds the loop exits (tag `g2`);
* otherwise `x ← (1 − σ) x + σ x̃`.
A finished state is left unchanged. -/
noncomputable def callStep {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (ρ : ℝ) (O : (Fin m → ℝ) → (Fin n → ℝ)) (lam0 : ℝ) (s : CallState n) : CallState n :=
  match s.tag with
  | .running =>
    if lam A b d s.x < lam0 / 2 then { s with tag := .halved }
    else
      let y := dual A b d (alphaOf m ρ lam0) s.x
      let xt := O y
      if y ⬝ᵥ (A.mulVec s.x - b) - y ⬝ᵥ (A.mulVec xt - b) ≤ lam A b d s.x / 5 * (y ⬝ᵥ d) then
        { s with tag := .g2, calls := s.calls + 1 }
      else
        { x := (1 - sigmaOf m ρ lam0) • s.x + sigmaOf m ρ lam0 • xt
          tag := .running
          calls := s.calls + 1
          evals := s.evals + 1 }
  | .halved => s
  | .g2 => s

/-- **A single call IMPROVE-GENERAL(x)**: the state after `k` steps of the call started at `x`,
with `λ₀ = maxᵢ (aᵢ x − bᵢ)/dᵢ` and counters at zero. The call has returned when the tag is not
`running`; its output is then the state's `x`. -/
noncomputable def callRun {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (ρ : ℝ) (O : (Fin m → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) (k : ℕ) : CallState n :=
  (callStep A b d ρ O (lam A b d x))^[k] { x := x, tag := .running, calls := 0, evals := 0 }

/-- Output of the relaxed decision procedure. -/
inductive Output (n : ℕ)
  /-- an `ε`-approximate solution -/
  | approx (x : Fin n → ℝ)
  /-- the claim that no exact solution exists -/
  | infeasible

/-- Phase of the driver. -/
inductive Phase (n : ℕ)
  /-- between two calls (or before the first): the termination tests are made -/
  | between
  /-- inside a call of IMPROVE-GENERAL -/
  | inCall
  /-- stopped with an output -/
  | done (o : Output n)

/-- State of the driver: the current call state (its `x` is the current point, its `tag` the exit
reason of the last call, its counters are cumulative over the whole run), the current call's `λ₀`,
and the phase. -/
structure RunState (n : ℕ) where
  cs : CallState n
  lam0 : ℝ
  phase : Phase n

/-- **One step of the driver** (§4, p. 27): "We start by calling IMPROVE-GENERAL with any point in
`P` and let `(x, λ)` denote its output. We check if `λ ≤ ε`, and if so output the ε-approximate
solution `x`, and stop. If `λ > ε` and condition G2 is satisfied, then we conclude that there does
not exist a solution and stop. If neither termination condition is satisfied, then this process is
repeated, where the new input to IMPROVE-GENERAL is its previous output."
The test `λ ≤ ε` is also made before the first call; "condition G2 is satisfied" is the exit of
the last call through (G2). -/
noncomputable def runStep {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (ρ : ℝ) (O : (Fin m → ℝ) → (Fin n → ℝ)) (ε : ℝ) (s : RunState n) : RunState n :=
  match s.phase with
  | .between =>
    if lam A b d s.cs.x ≤ ε then { s with phase := .done (.approx s.cs.x) }
    else if s.cs.tag = .g2 then { s with phase := .done .infeasible }
    else { cs := { s.cs with tag := .running }, lam0 := lam A b d s.cs.x, phase := .inCall }
  | .inCall =>
    let cs' := callStep A b d ρ O s.lam0 s.cs
    if cs'.tag = .running then { s with cs := cs' } else { s with cs := cs', phase := .between }
  | .done _ => s

/-- **The relaxed decision procedure of Theorem 4.5**: the state after `k` steps, started at
`x₀` with no oracle call made and one `A x` evaluation (that of `x₀`). The run has stopped when
the phase is `done o`; `o` is its output. -/
noncomputable def run {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (ρ : ℝ) (O : (Fin m → ℝ) → (Fin n → ℝ)) (ε : ℝ) (x₀ : Fin n → ℝ) (k : ℕ) : RunState n :=
  (runStep A b d ρ O ε)^[k]
    { cs := { x := x₀, tag := .running, calls := 0, evals := 1 }, lam0 := 0, phase := .between }

end PlotkinShmoysTardos


