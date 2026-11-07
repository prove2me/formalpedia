-- Prove2me | Definitions.Def_FreeSpencer_fullRun
-- name    : FreeSpencer_fullRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:08:57.588226+00:00
-- url     : https://prove2.me/theorems/9326debe-4215-4638-b85d-c9d2f9657a9c
-- title:
--   The law of Algorithm 3
-- statement:
--   The acceptance test (7.11) at a terminal state: $d\le\ell/32$, $\hat\Psi\le8.001\sqrt\ell$, $\hat M\le1.501\sqrt\ell$, with $\hat\Psi=\hat E-\hat f_*-\mathrm{Tr}(\hat S_*(H-H_*))$ and $\hat M=\mathrm{Tr}(\hat S_*Y)$. An epoch request runs at most $r=M+b+1$ independent trials and keeps the first accepted endpoint. A phase makes at most $K$ requests while the live count exceeds half its starting value, and with fewer than $32$ live coordinates rounds them to nearest signs and returns. Algorithm 3 runs at most $\lfloor\log_2n\rfloor+1$ phases from $x=0$, where $M=K(\lfloor\log_2n\rfloor+1)$, returning the all-positive signing on the trivial inputs $n=0$, $m=0$, $n<32$. The result is a law on outputs, with `none` for a report of failure.
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eq. (7.11), p.53; Algorithm 3, p.79; Section 7.2, p.50

import Mathlib
import Definitions.Def_FreeSpencer_trialLaw
open scoped Matrix Matrix.Norms.L2Operator

namespace FreeSpencer

open Classical in
/-- The acceptance test (7.11) at the terminal state `s` of a trial from `xs`:
`d ≤ ℓ/32`, `Ψ̂ ≤ 8.001 √ℓ`, `M̂ ≤ 1.501 √ℓ`, where `Ψ̂ = Ê - f̂∗ - Tr(Ŝ∗ (H - H∗))` and
`M̂ = Tr(Ŝ∗ Y)`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eq. (7.11), p.53; Algorithm 2, p.78. -/
noncomputable def accepts {n m : ℕ} (P : Procs n m) (A : Fin n → Matrix (Fin m) (Fin m) ℝ)
    (xs : Fin n → ℝ) (s : TrialState n) : Prop :=
  let ℓ : ℝ := ((liveSet xs).card : ℝ)
  let Hs := center A xs
  let H := center A s.x
  s.a + s.u ≤ ℓ / 32 ∧
  P.solveE H s.C - (P.solveF Hs).1 - Matrix.trace ((P.solveF Hs).2 * (H - Hs)) ≤ 8.001 * Real.sqrt ℓ ∧
  Matrix.trace ((P.solveF Hs).2 * center A s.y) ≤ 1.501 * Real.sqrt ℓ

open Classical in
/-- An epoch request (line 15 of Algorithm 3): at most `r` independent trials from `xs`, keeping the
first accepted endpoint; `none` when all fail. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Algorithm 3, p.79. -/
noncomputable def runTrials {n m : ℕ} (P : Procs n m) (A : Fin n → Matrix (Fin m) (Fin m) ℝ)
    (par : Params) (xs : Fin n → ℝ) : ℕ → PMF (Option (Fin n → ℝ))
  | 0 => PMF.pure none
  | r + 1 => (trialLaw P A par xs).bind fun s =>
      if accepts P A xs s then PMF.pure (some s.x) else runTrials P A par xs r

/-- The outcome of the inner loop of Algorithm 3. -/
inductive LoopOut (n : ℕ) where
  | fail : LoopOut n
  | done : (Fin n → ℝ) → LoopOut n
  | cont : (Fin n → ℝ) → LoopOut n

open Classical in
/-- Lines 10–19 of Algorithm 3: at most `fuel` saved epoch requests while the live count exceeds
`k/2`; with fewer than `32` live coordinates, round them to nearest signs and return.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Algorithm 3, p.79. -/
noncomputable def requestLoop {n m : ℕ} (P : Procs n m) (A : Fin n → Matrix (Fin m) (Fin m) ℝ)
    (par : Params) (r k : ℕ) : ℕ → (Fin n → ℝ) → PMF (LoopOut n)
  | 0, x => PMF.pure (LoopOut.cont x)
  | fuel + 1, x =>
    if 2 * (liveSet x).card ≤ k then PMF.pure (LoopOut.cont x)
    else if (liveSet x).card < 32 then PMF.pure (LoopOut.done fun i => nearestSign (x i))
    else (runTrials P A par x r).bind fun o =>
      match o with
      | none => PMF.pure LoopOut.fail
      | some x' => requestLoop P A par r k fuel x'

open Classical in
/-- Lines 8–23 of Algorithm 3: at most `phases` phases; after a phase, return `x` if all coordinates
are signs. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Algorithm 3, p.79. -/
noncomputable def phaseLoop {n m : ℕ} (P : Procs n m) (A : Fin n → Matrix (Fin m) (Fin m) ℝ)
    (par : Params) (r : ℕ) : ℕ → (Fin n → ℝ) → PMF (Option (Fin n → ℝ))
  | 0, _ => PMF.pure none
  | phases + 1, x => (requestLoop P A par r (liveSet x).card par.K x).bind fun o =>
      match o with
      | LoopOut.fail => PMF.pure none
      | LoopOut.done x' => PMF.pure (some x')
      | LoopOut.cont x' =>
        if ∀ i, |x' i| = 1 then PMF.pure (some x') else phaseLoop P A par r phases x'

/-- Algorithm 3 at confidence `b` for the procedures `P`, as a law on its output: `some x` is a
returned signing and `none` a report of failure. The trivial inputs (`n = 0`, `m = 0`, `n < 32`) return
the all-positive signing; otherwise the parameters are those of the mode, `M = K(⌊log₂ n⌋ + 1)`,
`r = M + b + 1`, and the walk starts at `x = 0`.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Algorithm 3, p.79; Section 7.2, p.50.

**Formalization Note** Fresh draws at each retry are the independent factors of the `PMF.bind`.
The law has finite support, since every loop is bounded and each draw has finitely many outcomes. -/
noncomputable def fullRun {n m : ℕ} (P : Procs n m) (A : Fin n → Matrix (Fin m) (Fin m) ℝ) (b : ℕ) :
    PMF (Option (Fin n → ℝ)) :=
  if n = 0 ∨ m = 0 ∨ n < 32 then PMF.pure (some fun _ => 1)
  else
    let par := params n m
    let phases := Nat.log 2 n + 1
    phaseLoop P A par (par.K * phases + b + 1) phases 0

end FreeSpencer


