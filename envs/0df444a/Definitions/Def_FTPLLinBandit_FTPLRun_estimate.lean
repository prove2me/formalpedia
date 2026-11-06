-- Prove2me | Definitions.Def_FTPLLinBandit_FTPLRun_estimate
-- name    : FTPLLinBandit_FTPLRun_estimate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:06:41.538947+00:00
-- url     : https://prove2.me/theorems/f3ee827c-3853-42f6-9268-6d3a40c4eeb7
-- title:
--   Geometric-resampling estimator $\hat\theta_t=H_t(a_t-\bar a_t)y_t$
-- statement:
--   Given a run and the estimates of rounds $\tau<t$, let $a_j$ be the action of slot $j$ of round $t$, so $a_t=a_0$ is played and $\bar a_t=a_1$. The learner observes $y_t=\langle a_t,\theta_t\rangle+b_t$, forms
--   $$Q_i=I-\frac\beta2(u_i-v_i)(u_i-v_i)^\top\ \ (i=1,\dots,N),\qquad H_t=\beta I+\beta\sum_{k=1}^{N}Q_1\cdots Q_k=\beta\sum_{k=0}^{N}Q_1\cdots Q_k,$$
--   from the pairs $u_i,v_i$ (slots $2i$, $2i+1$), and returns the estimate
--   $$\hat\theta_t=H_t(a_t-\bar a_t)\,y_t .$$
--   This is lines 5–8 and the procedure GeometricResampling (lines 17–21) of Algorithm 1; $H_t$ estimates the inverse covariance $\widetilde M_t^{-1}$ of the sampling law.
--
--   **Formalization Note** The products are ordered with $Q_1$ leftmost; the empty product is $I$ (form (GR), p.45).
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Algorithm 1, lines 5–8 and 17–21, p.8; (GR), p.45

import Mathlib
import Definitions.Def_FTPLLinBandit_FTPLRun_slotAction

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace FTPLLinBandit

variable {d : ℕ} {A : Set (EuclideanSpace ℝ (Fin d))} {ν : Measure (EuclideanSpace ℝ (Fin d))}
  {x : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {s : Scheme} {γ β : ℝ} {N : ℕ}
  {lam : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The geometric-resampling estimator `θ̂_t = H_t (a_t − ā_t) y_t` of Algorithm 1.** Wei,
arXiv:2610.17818, Algorithm 1, lines 5–8 and 17–21, p.8: "Set a_t ← SampleAction(Θ̂_t, ρ_t), play
a_t, and observe y_t = ⟨a_t, θ_t⟩ + b_t. ā_t ← SampleAction(Θ̂_t, ρ_t).
H_t ← GeometricResampling(Θ̂_t, ρ_t, β, N). θ̂_t ← H_t(a_t − ā_t)y_t", where GeometricResampling
draws `u_i, v_i ← SampleAction(Θ, ρ)` for `i = 1, …, N`, sets `Q_i ← I − (β/2)(u_i − v_i)(u_i − v_i)ᵀ`
and returns `βI + β ∑_{k=1}^N Q_1 ⋯ Q_k`.

With `a_j` the action of slot `j` of round `t` (`FTPLRun.slotAction`), this is
`y_t H_t (a_0 − a_1)` with `y_t = ⟨a_0, θ_t⟩ + b_t`, `Q_i` built from slots `2i + 2` and `2i + 3`,
and `H_t = β ∑_{k=0}^{N} Q_1 ⋯ Q_k` (the empty product is `I`).

**Formalization Note.** `βI + β∑_{k=1}^N Q_1⋯Q_k = β∑_{k=0}^N Q_1⋯Q_k`, the form (GR) of p.45.
The products are ordered (`Q_1` leftmost). Indices are `0`-based: `Q i` is the paper's `Q_{i+1}`. -/
noncomputable def FTPLRun.estimate (run : FTPLRun A ν x s γ β N lam Ω P)
    (past : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin d) :=
  let a : Fin (2 * N + 2) → EuclideanSpace ℝ (Fin d) := fun j => run.slotAction past t j ω
  let y : ℝ := ⟪a ⟨0, by omega⟩, run.θ t ω⟫_ℝ + run.b t ω
  let Q : ℕ → Matrix (Fin d) (Fin d) ℝ := fun i =>
    if h : i < N then
      1 - (β / 2) • vecMulVec (WithLp.ofLp (a ⟨2 * i + 2, by omega⟩ - a ⟨2 * i + 3, by omega⟩))
        (WithLp.ofLp (a ⟨2 * i + 2, by omega⟩ - a ⟨2 * i + 3, by omega⟩))
    else 1
  let H : Matrix (Fin d) (Fin d) ℝ := β • ∑ k ∈ Finset.range (N + 1), ((List.range k).map Q).prod
  y • Matrix.toEuclideanLin H (a ⟨0, by omega⟩ - a ⟨1, by omega⟩)

end FTPLLinBandit


