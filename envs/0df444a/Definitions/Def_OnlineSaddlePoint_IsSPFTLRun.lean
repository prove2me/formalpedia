-- Prove2me | Definitions.Def_OnlineSaddlePoint_IsSPFTLRun
-- name    : OnlineSaddlePoint_IsSPFTLRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:13:00.246102+00:00
-- url     : https://prove2.me/theorems/f434af2e-f59e-46c8-9d9e-4c93937ce422
-- title:
--   A run of Saddle-Point Follow-the-Leader (Algorithm 1)
-- statement:
--   **Saddle-Point Follow-the-Leader** (SP-FTL) starts from arbitrary $x_1\in X$, $y_1\in Y$. In round $t=1,\dots,T$ the players play $(x_t,y_t)$, observe $\mathcal L_t$, and set
--
--   $$
--   x_{t+1}\in\arg\min_{x\in X}\max_{y\in Y}\sum_{\tau=1}^{t}\mathcal L_\tau(x,y),\qquad
--   y_{t+1}\in\arg\max_{y\in Y}\min_{x\in X}\sum_{\tau=1}^{t}\mathcal L_\tau(x,y).
--   $$
--
--   A pair of sequences $(x_t)$, $(y_t)$ is a **run** of SP-FTL over $T$ rounds if it arises this way, with any choice among tied minimizers and maximizers.
--
--   Both players update jointly from the sum of all games seen so far; the run is the object of Lemmas 1 and 2 and Theorem 1.
--
--   **Formalization Note** Iterates are indexed $1,\dots,T+1$ (index $0$ is unused). The inner max and min are `sSup`/`sInf` of images, attained under the compactness and Lipschitz hypotheses of the statements that use the run. That the iterates are saddle points is a separate theorem, not part of the definition.
-- source:
--   Rivera Cardoso, Wang, Xu, The Online Saddle Point Problem and Online Convex Optimization with Knapsacks, arXiv:1806.08301v3, Algorithm 1, p.6

import Mathlib
import Definitions.Def_OnlineSaddlePoint_cumPayoff

namespace OnlineSaddlePoint

/-- **A run of Saddle-Point Follow-the-Leader (SP-FTL)** over `T` rounds. Rivera Cardoso, Wang,
Xu, arXiv:1806.08301v3, Algorithm 1, p.6:
```
input: x₁ ∈ X, y₁ ∈ Y
for t = 1, ..., T do
  Choose actions (x_t, y_t); Observe function 𝓛_t
  Set x_{t+1} ← arg min_{x∈X} max_{y∈Y} ∑_{τ=1}^t 𝓛_τ(x, y)
  Set y_{t+1} ← arg max_{y∈Y} min_{x∈X} ∑_{τ=1}^t 𝓛_τ(x, y)
end for
```
The pair of sequences `(x, y)` is a run when `x₁ ∈ X`, `y₁ ∈ Y` are arbitrary, and for every
`t = 1, …, T`, `x_{t+1} ∈ X` minimizes `x' ↦ max_{y∈Y} ∑_{τ≤t} 𝓛_τ(x', y)` over `X` and
`y_{t+1} ∈ Y` maximizes `y' ↦ min_{x∈X} ∑_{τ≤t} 𝓛_τ(x, y')` over `Y`.

**Formalization Note.** Rounds are `1, …, T` and iterates `1, …, T + 1` (index `0` of the
sequences is unused). Ties in the `arg min`/`arg max` are allowed: any minimizer/maximizer is a
valid choice. The inner `max`/`min` are `sSup`/`sInf` over the image of `Y`/`X`, which are
attained under the compactness and Lipschitz hypotheses of every statement using this predicate.
The run is defined literally by Algorithm 1; that its iterates are saddle points is a theorem
(`spftl_isSaddlePoint`), not part of the definition. -/
def IsSPFTLRun {E F : Type*} (L : ℕ → E → F → ℝ) (X : Set E) (Y : Set F) (T : ℕ)
    (x : ℕ → E) (y : ℕ → F) : Prop :=
  x 1 ∈ X ∧ y 1 ∈ Y ∧
    ∀ t ∈ Finset.Icc 1 T, x (t + 1) ∈ X ∧ y (t + 1) ∈ Y ∧
      (∀ x' ∈ X, sSup ((fun y' => cumPayoff L t (x (t + 1)) y') '' Y) ≤
        sSup ((fun y' => cumPayoff L t x' y') '' Y)) ∧
      (∀ y' ∈ Y, sInf ((fun x' => cumPayoff L t x' y') '' X) ≤
        sInf ((fun x' => cumPayoff L t x' (y (t + 1))) '' X))

end OnlineSaddlePoint


