-- Prove2me | Definitions.Def_DeltaSLearning_algState__6eb4c5
-- name    : DeltaSLearning_algState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:09:15.894795+00:00
-- url     : https://prove2.me/theorems/6eb4c52f-f906-467d-916c-755d519dd937
-- title:
--   The $(\delta,S)$ learning algorithm, epoch by epoch
-- statement:
--   The $(\delta,S)$ learning algorithm with $J$ grid points, step sizes $(\eta^n)$, confidence sizes $(\Delta^n)$ and initial targets $S^1_j$, run on a demand path: the state after $n$ epochs. Initially the first period is period 1, the inventory is $x^1=0$, $\hat G^0_j=\hat L^0_j=0$, $\mathcal A^1=[J]$ and no cost has been incurred; epoch $n$ is one epoch step with $\eta^n$ and $\Delta^n$.
--
--   After $N$ epochs the state records the number $T_N$ of periods elapsed and the total pseudo cost of those periods.
--
--   **Formalization Note** $\eta$ and $\Delta$ are indexed by the 1-based epoch number. "We assume $x_0=0$ and we order $S^1$ at the first period" (p.19).
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), §3.3 steps (0a)–(0d), p.13; Algorithm 1, p.15; p.19

import Mathlib
import Definitions.Def_DeltaSLearning_epochStep

namespace DeltaSLearning

/-- The `(δ, S)` learning algorithm with `J` grid points, step sizes `η`, confidence sizes `Δ`
and initial targets `S₁`, run on the demand path `d`: `algState … n` is the state at the
beginning of epoch `n + 1`, i.e. after `n` epochs. Initially (epoch 1) the first period is `0`,
the inventory is `x¹ = 0`, the targets are `S¹_j = S₁ j`, `Ĝ⁰ = L̂⁰ = 0`, `𝒜¹ = {1, …, J}`
and no cost has been incurred. Epoch `k + 1` uses `η (k + 1)` and `Δ (k + 1)`.
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), §3.3 steps
(0a)–(0d), p.13, Algorithm 1, p.15, and "we assume x0 = 0 and we order S¹ at the first period",
p.19.

**Formalization Note** `η` and `Δ` are indexed by the paper's 1-based epoch number; `η 0`, `Δ 0`
are never used. After `N` epochs, `(algState … N).t` is the number of periods `T_N` and
`(algState … N).cost` the total pseudo cost of those periods. -/
noncomputable def algState (cp : Params) (J : ℕ) (η Δ : ℕ → ℝ) (S₁ : ℕ → ℝ) (d : ℕ → ℝ)
    (n : ℕ) : AlgState :=
  Nat.rec (motive := fun _ => AlgState)
    { t := 0, x := 0, S := S₁, Ghat := fun _ => 0, Lhat := fun _ => 0, A := Finset.Icc 1 J,
      cost := 0 }
    (fun k st => epochStep cp J η Δ (k + 1) d st) n

end DeltaSLearning


