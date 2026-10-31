-- Prove2me | Definitions.Def_DivideChooseBayes_algRun
-- name    : DivideChooseBayes_algRun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:27:46.713731+00:00
-- url     : https://prove2.me/theorems/985c9113-3185-4d05-ae26-c35a94fa8b5a
-- title:
--   State of Algorithm 1 after $k$ iterations
-- statement:
--   Algorithm 1 keeps a pair $(u,p)$: the best objective value found so far, initially $u=-\infty$, and the current division $p$. On iteration $k$ it takes an optimal solution $q$ of $\mathcal C_{P_k}$ with value $u_{P_k}$; if $u_{P_k}>u$ it sets $u\leftarrow u_{P_k}$ and $p_i\leftarrow (q_i+1)/2$, and otherwise it keeps the state.
--
--   **Formalization Note** Line 5 takes *an* optimal solution, so the run is parametrized by a selection $k\mapsto q^{(k)}$; the theorems require $q^{(k)}$ to be optimal for $\mathcal C_{P_k}$ on every iteration run. The value $u$ lives in $\mathbb R\cup\{-\infty\}$. The paper leaves $p$ uninitialized; it is set to $(1/2,\dots,1/2)$, and the first iteration always overwrites it.
-- source:
--   Tucker-Foltz & Zeckhauser, Playing Divide-and-Choose Given Uncertain Preferences, arXiv:2207.03076v2, Algorithm 1, lines 3, 5–10, p.9

import Mathlib
import Definitions.Def_DivideChooseBayes_cpObjective
import Definitions.Def_DivideChooseBayes_algP

namespace DivideChooseBayes

/-- **State of Algorithm 1 after `k` iterations of the main loop.**
Tucker-Foltz & Zeckhauser, *Playing Divide-and-Choose Given Uncertain Preferences*,
arXiv:2207.03076v2, Algorithm 1, lines 3 and 5–10, p.9.

The state is the pair `(u, p)`: the best objective value found so far, in `WithBot ℝ` with
`u = −∞` initially (line 3), and the current division `p`. On iteration `k` the program `C_{P_k}`
is solved; `sol k` is the optimal solution taken on line 5 and `u_{P_k}` its objective value. If
`u_{P_k} > u` (strictly) the state becomes `(u_{P_k}, (q + 1)/2)` (lines 6–9), else it is unchanged.

**Formalization Note.** Line 5 takes *an* optimal solution, so the run is parametrized by a
selection `sol : ℕ → ι → ℝ`; the theorems require `sol k` to be optimal for `C_{P_k}` for every
iteration `k` actually run. The paper leaves `p` uninitialized; it is set to `(1/2, …, 1/2)` here,
and the first iteration always overwrites it because `u_{P_0} > −∞`. -/
noncomputable def algRun {ι : Type*} [Fintype ι] (gD : ι → ℝ) (γ : ℝ) (sol : ℕ → ι → ℝ) :
    ℕ → WithBot ℝ × (ι → ℝ)
  | 0 => (⊥, fun _ => 1 / 2)
  | k + 1 =>
      if (algRun gD γ sol k).1 < ((cpObjective gD (algP gD γ k) (sol k) : ℝ) : WithBot ℝ) then
        (((cpObjective gD (algP gD γ k) (sol k) : ℝ) : WithBot ℝ), fun i => (sol k i + 1) / 2)
      else algRun gD γ sol k

end DivideChooseBayes


