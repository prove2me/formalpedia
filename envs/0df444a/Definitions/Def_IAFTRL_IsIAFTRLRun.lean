-- Prove2me | Definitions.Def_IAFTRL_IsIAFTRLRun
-- name    : IAFTRL_IsIAFTRLRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:49:03.113379+00:00
-- url     : https://prove2.me/theorems/a85dedfe-715d-4227-8f1a-1de7d529d18c
-- title:
--   Execution of IA-FTRL against an adaptive environment
-- statement:
--   A run is an **execution of IA-FTRL for $T$ rounds** on a probability space $(\Omega,P)$ if for every round $t<T$:
--   1. $A_t$, $Y_t$, $\theta_t$ are random variables, $\mathcal G_t$ is a sub-σ-algebra containing the observation σ-algebra $\mathcal F_{t-1}$, $\theta_t$ is $\mathcal G_t$-measurable, $\mathcal G_t\subseteq\mathcal G_{t+1}$, and $A_t,Y_t$ are $\mathcal G_{t+1}$-measurable;
--   2. (selection) $p_t$ is $\mathcal F_{t-1}$-measurable and, on every outcome, solves the program (2.3) at round $t$ with the cumulative estimate $\sum_{s<t}\hat\theta_s$;
--   3. (action law) $P(A_t=b\mid\mathcal G_t)=p_{t,b}$ almost surely, for every action $b$;
--   4. (feedback) $|Y_t|\le1$ and $\mathbb E[Y_t\mid\mathcal G_t\vee\sigma(A_t)]=A_t^\top\theta_t$ almost surely;
--   5. (adversary) $\|\theta_t\|_{\mathcal A}\le1$.
--
--   This is Algorithm 1 (Information-Acquisition FTRL) run against an environment that may choose $\theta_t$ depending on the past and its own randomness. The learner uses only $\mathcal A$, the round and its observations.
--
--   **Formalization Note** Rounds are 0-based: Lean round $t$ is the paper's round $t+1$ and uses $\beta_{t+1}$, $\Gamma_{t+1}$, $\hat\Delta_{t+1}$. The σ-algebras $\mathcal G_t$ are the pre-action filtration of Appendix J.1: conditioning the action law on $\mathcal G_t$ says the learner's draw is independent of $\theta_t$ and of the environment's pre-action randomness given the past; the feedback identity is required given $\mathcal G_t$ and $A_t$. Every $\mathcal F_{t-1}$-measurable minimizer of (2.3) is allowed; the paper's rule (for instance the lexicographically smallest minimizer) is one of them. Only rounds $t<T$ are constrained.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Algorithm 1, p.18; Section 2.1, p.17; Section 1.1, pp.5–6; Appendix J.1, p.204

import Mathlib
import Definitions.Def_IAFTRL_actionNorm
import Definitions.Def_IAFTRL_IsMin2_3
import Definitions.Def_IAFTRL_Run_cumEst
import Definitions.Def_IAFTRL_Run_hist

namespace IAFTRL

open Matrix MeasureTheory

/-- **An execution of IA-FTRL for `T` rounds against an adaptive environment.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299,
Algorithm 1, p.18 ("Draw `A_t ∼ p_t`, play `A_t`, and observe `Y_t ∈ [−1, 1]`"), Section 2.1, p.17
("we simply choose `p_t` according to a fixed `F_{t−1}`-measurable rule"), Section 1.1, pp.5–6
("`E[Y_t | F_{t−1}, θ_t, A_t] = A_t^⊤θ_t` and `‖θ_t‖_𝒜 ≤ 1` … `|Y_t| ≤ 1` … the environment may choose
`θ_t` depending on `F_{t−1}` and its internal randomness"), Appendix J.1, p.204 ("Enlarging the
pre-action filtration to include an environment's fresh pre-action randomization does not reveal
it to the learner").

`IsIAFTRLRun P arms T R` says that for every (0-based) round `t < T`:
1. `A_t`, `Y_t`, `θ_t` are random variables; `G_t` is a sub-σ-algebra; `F_{t−1} ⊆ G_t`; `θ_t` is
   `G_t`-measurable; `G_t ⊆ G_{t+1}`; `A_t` and `Y_t` are `G_{t+1}`-measurable;
2. (selection, Algorithm 1 lines 3–5) `p_t` is `F_{t−1}`-measurable and, on every outcome, minimizes
   program (2.3) at paper round `t + 1` with the cumulative estimate `Σ_{s<t} θ̂_s`;
3. (action law, line 6) `P(A_t = b | G_t) = p_{t,b}` almost surely, for every action `b`;
4. (feedback) `|Y_t| ≤ 1` and `E[Y_t | G_t ∨ σ(A_t)] = A_t^⊤θ_t` almost surely;
5. (adversary) `‖θ_t‖_𝒜 ≤ 1`.

The learner's inputs are only `𝒜`, the round and its observations: the predicate mentions no
`θ`, `C`, `a*` or horizon-dependent tuning.

**Formalization Note.** Rounds are 0-based: Lean round `t` is the paper's round `t + 1` and uses
`β_{t+1}`, `Γ_{t+1}` and `Δ̂_{t+1}`. `R.hist t` is the paper's `F_t` (observations of the first `t`
rounds), and `G_t` is the paper's pre-action σ-algebra of p.204. The action law is conditional on
`G_t`, so the draw is independent of `θ_t` and of the environment's pre-action randomness given the
past; the feedback identity is conditional on `G_t ∨ σ(A_t)`. Any `F_{t−1}`-measurable minimizer is
allowed (the paper's rule is one such, e.g. the lexicographically smallest). Only rounds `t < T`
are constrained. -/
def IsIAFTRLRun {d K : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (arms : Fin K → Fin d → ℝ) (T : ℕ) (R : Run d K Ω) : Prop :=
  ∀ t < T,
    (Measurable (R.A t) ∧ Measurable (R.Y t) ∧ Measurable (R.θs t) ∧
      R.G t ≤ mΩ ∧ R.hist t ≤ R.G t ∧ Measurable[R.G t] (R.θs t) ∧ R.G t ≤ R.G (t + 1) ∧
      Measurable[R.G (t + 1)] (R.A t) ∧ Measurable[R.G (t + 1)] (R.Y t)) ∧
    (Measurable[R.hist t] (R.p t) ∧ ∀ ω, IsMin2_3 arms (t + 1) (R.cumEst arms t ω) (R.p t ω)) ∧
    (∀ b : Fin K, P[(R.A t ⁻¹' {b}).indicator (fun _ => (1 : ℝ)) | R.G t] =ᵐ[P]
      fun ω => R.p t ω b) ∧
    ((∀ ω, |R.Y t ω| ≤ 1) ∧
      P[R.Y t | R.G t ⊔ MeasurableSpace.comap (R.A t) inferInstance] =ᵐ[P]
        fun ω => arms (R.A t ω) ⬝ᵥ R.θs t ω) ∧
    (∀ ω, actionNorm arms (R.θs t ω) ≤ 1)

end IAFTRL


