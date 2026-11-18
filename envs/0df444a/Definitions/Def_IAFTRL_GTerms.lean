-- Prove2me | Definitions.Def_IAFTRL_GTerms
-- name    : IAFTRL_GTerms
-- status  : Definition
-- author  : @Canzhe Zhao
-- created : 2026-11-17T13:43:39.76334+00:00
-- url     : https://prove2.me/theorems/a064d2db-3715-4c69-9289-6aaaaa84733f
-- title:
--   GIA-FTRL corrupted analysis: exponential weights, relative entropy, mixability gap, and the four regret sums I₁–I₄
-- statement:
--   This file names the four expectation sums in the corrupted analysis of GIA-FTRL, Appendix G.1.1, (G.3)–(G.5). A run's round $t$ (counted from $0$) is the paper's round $t+1$, played with $\beta_{t+1}=16d+\sqrt{t+1}$.
--
--   **Definitions.**
--   - **Exponential weights.** $q_{t+1}=\mathrm{gq}(t+1,S_t)$ is the exponential-weights law, with $S_t=\sum_{s<t}\hat\theta_s$.
--   - **Relative entropy.** $D_{\mathrm{KL}}(q,\mu)=\int\log\frac{dq}{d\mu}\,dq$.
--   - **Prior cost.** For an atom $a$ of the reference measure $\mu$, $h_a=\log(1/\mu(\{a\}))$.
--   - **Mixability gap.** $D_t=\langle q_t,\hat f_t\rangle+\beta_t\log\langle q_t,e^{-\hat f_t/\beta_t}\rangle$, where $\hat f_t(x)=x^\top\hat\theta_t$.
--
--   **The four sums.** Write $\Delta(x)=(x-a^*)^\top\theta$ and $c^{\mathrm{vec}}_t=\theta_t-\theta$.
--   $$I_1=\beta_1h^*+\sum_{t=2}^T(\beta_t-\beta_{t-1})\,\mathbb E[h^*-D_{\mathrm{KL}}(q_t,\mu)],\qquad I_2=\sum_{t=1}^T\mathbb E[D_t],$$
--   $$I_3=\sum_{t=1}^T\mathbb E[\langle p_t-q_t,\Delta\rangle],\qquad I_4=\sum_{t=1}^T\mathbb E[\langle p_t-q_t,x^\top c^{\mathrm{vec}}_t\rangle].$$
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G.1.1, (G.3)–(G.5); Lemmas G.1, G.4, G.5, G.9

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL

/-!
# The four regret terms of GIA-FTRL in the corrupted analysis

Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits* (STOC submission version), Appendix G.1.1,
(G.3)–(G.5) and Lemmas G.1, G.4, G.5, G.9. Rounds of a run are `0`-based: the run's round `t`
is the paper's round `t + 1`, played with `β_{t+1}` and the exponential-weights law
`q_{t+1} = gq ℬ e (t + 1) (Σ_{s<t} θ̂_s)`.

* `GRun.qw`: the exponential-weights law `q_{t+1}`;
* `klDivR q μ = ∫ log (dq/dμ) dq`, the relative entropy `D_KL(q, μ)`;
* `hStar ℬ e a = log (1 / μ({a}))`, the prior cost of the atom `a`;
* `GRun.mixGap`: `D_t = ⟨q_t, f̂_t⟩ + β_t log ⟨q_t, e^{-f̂_t/β_t}⟩` with `f̂_t(x) = xᵀθ̂_t`;
* `penI1`, `stabI2`, `exploI3`, `corrI4`: the penalty, stability, exploration (under the fixed
  loss vector `θ`) and direct-corruption sums `I₁, I₂, I₃, I₄` of (G.3)–(G.5).
-/

open MeasureTheory

namespace IAFTRL

variable {d : ℕ}

/-- the exponential-weights law of run round `t` (paper round `t + 1`) -/
noncomputable def GRun.qw {Ω : Type*} (R : GRun d Ω) (ℬ : Set (Fin d → ℝ))
    (e : ℕ → Fin d → ℚ) (t : ℕ) (ω : Ω) : Measure (Fin d → ℝ) :=
  gq ℬ e (t + 1) (R.cumEst t ω)

/-- the relative entropy `D_KL(q, μ) = ∫ log (dq/dμ) dq` -/
noncomputable def klDivR (q μ : Measure (Fin d → ℝ)) : ℝ :=
  ∫ x, Real.log (q.rnDeriv μ x).toReal ∂q

/-- the prior cost `h_a = log (1 / μ({a}))` of an atom `a` of the reference measure -/
noncomputable def hStar (ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ) (a : Fin d → ℝ) : ℝ :=
  Real.log (1 / (refMu ℬ e {a}).toReal)

/-- the mixability gap `D_t = ⟨q_t, f̂_t⟩ + β_t log ⟨q_t, e^{-f̂_t/β_t}⟩` -/
noncomputable def GRun.mixGap {Ω : Type*} (R : GRun d Ω) (ℬ : Set (Fin d → ℝ))
    (e : ℕ → Fin d → ℚ) (t : ℕ) (ω : Ω) : ℝ :=
  ∫ x, x ⬝ᵥ R.thetaHat t ω ∂(R.qw ℬ e t ω) +
    gbeta d (t + 1) * Real.log
      (∫ x, Real.exp (-(x ⬝ᵥ R.thetaHat t ω) / gbeta d (t + 1)) ∂(R.qw ℬ e t ω))

/-- the penalty sum `I₁ = β₁ h* + Σ_{t=2}^T (β_t − β_{t−1}) E[h* − D_KL(q_t, μ)]` -/
noncomputable def penI1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ℬ : Set (Fin d → ℝ))
    (e : ℕ → Fin d → ℚ) (T : ℕ) (R : GRun d Ω) (astar : Fin d → ℝ) : ℝ :=
  gbeta d 1 * hStar ℬ e astar + ∑ t ∈ Finset.Ico 1 T, (gbeta d (t + 1) - gbeta d t) *
    ∫ ω, (hStar ℬ e astar - klDivR (R.qw ℬ e t ω) (refMu ℬ e)) ∂P

/-- the stability sum `I₂ = Σ_t E[D_t]` -/
noncomputable def stabI2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ℬ : Set (Fin d → ℝ))
    (e : ℕ → Fin d → ℚ) (T : ℕ) (R : GRun d Ω) : ℝ :=
  ∑ t ∈ Finset.range T, ∫ ω, R.mixGap ℬ e t ω ∂P

/-- the exploration sum `I₃ = Σ_t E[⟨p_t − q_t, Δ⟩]`, `Δ(x) = (x − a*)ᵀθ` -/
noncomputable def exploI3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ) (T : ℕ) (R : GRun d Ω) (θ astar : Fin d → ℝ) :
    ℝ :=
  ∑ t ∈ Finset.range T, ∫ ω, (∫ x, (x - astar) ⬝ᵥ θ ∂(R.p t ω) -
    ∫ x, (x - astar) ⬝ᵥ θ ∂(R.qw ℬ e t ω)) ∂P

/-- the direct-corruption sum `I₄ = Σ_t E[⟨p_t − q_t, xᵀc_t⟩]`, `c_t = θ_t − θ` -/
noncomputable def corrI4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ) (T : ℕ) (R : GRun d Ω) (θ : Fin d → ℝ) : ℝ :=
  ∑ t ∈ Finset.range T, ∫ ω, (∫ x, x ⬝ᵥ (R.θs t ω - θ) ∂(R.p t ω) -
    ∫ x, x ⬝ᵥ (R.θs t ω - θ) ∂(R.qw ℬ e t ω)) ∂P

end IAFTRL


