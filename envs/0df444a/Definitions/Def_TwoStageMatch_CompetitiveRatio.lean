-- Prove2me | Definitions.Def_TwoStageMatch_CompetitiveRatio
-- name    : TwoStageMatch_CompetitiveRatio
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:32:31.719214+00:00
-- url     : https://prove2.me/theorems/a7650826-934f-474d-ac91-3cd3a2d9cd5f
-- title:
--   The competitive ratio $\Gamma_{\text{weighted-matching}}$ (Definition 2)
-- statement:
--   Definition 2 defines the competitive ratio of an algorithm against a benchmark $\mathsf{OPT}$ as
--   $$\Gamma_{\text{weighted-matching}}(\mathrm{ALG},\mathsf{OPT})=\min_{G,\{w_j\},\{\pi_i\}}\frac{\mathbb E\big[\sum_{j\in S}w_j\mathbb 1\{j\text{ is matched in }M_1\cup M_2\}\big]}{\mathsf{OPT}}.$$
--   Here the instances range over all finite instances, represented with demand sets $\{0,\dots,n_1-1\}$, $\{0,\dots,n_2-1\}$ and supply set $\{0,\dots,m-1\}$. Because Algorithm 1 leaves the optimal solution of $\mathscr P^g$ and the rounding unspecified, the algorithm is a **selection** $\sigma$ fixing one run of Algorithm 1 on every instance. For a benchmark $B\in\{\mathsf{OPT}_{\mathrm{offline}},\mathsf{OPT}_{\mathrm{online}}\}$,
--   $$\Gamma(\sigma,B)=\inf\Big\{\frac{\mathrm{ALG}_\sigma(I)}{B(I)} : I \text{ an instance with } B(I)>0\Big\}.$$
--
--   **Formalization Note** The ratio is undefined when $B(I)=0$, so such instances are excluded; the remaining set is nonempty and bounded below by $0$, so the real infimum is the infimum (a verification file shows nonemptiness).
-- source:
--   Y. Feng, R. Niazadeh, A. Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1 [cs.DS] (preprint, 21 Oct 2022), https://arxiv.org/abs/2210.11648v1, Definition 2, p.10

import Mathlib
import Definitions.Def_TwoStageMatch_Algorithm1

namespace TwoStageMatch

/-!
# The competitive ratio `Γ_weighted-matching` (Definition 2)

Feng, Niazadeh & Saberi, arXiv:2210.11648v1, Definition 2, p.10.

**Formalization Note.** The minimum over all graphs, weights and probabilities is taken over
the instances whose demand and supply sets are `Fin n₁`, `Fin n₂`, `Fin m` (every finite
instance is isomorphic to one of them). Algorithm 1 leaves the optimal `x*` and the rounding
unspecified, so the algorithm is a *selection* `σ` that fixes a run on every instance. The ratio
`ALG / OPT` is undefined when `OPT = 0`, so the minimum is read as the infimum of the ratios over
the instances with `OPT > 0`; that set is nonempty and bounded below by `0`, so the real `sInf`
is the infimum.
-/

/-- A finite instance with demand sets `Fin n₁`, `Fin n₂` and supply set `Fin m`. -/
structure FinInstance where
  n₁ : ℕ
  n₂ : ℕ
  m : ℕ
  inst : Instance (Fin n₁) (Fin n₂) (Fin m)

/-- A selection of runs of Algorithm 1 for `g`: one run on every finite instance. -/
def Selection (g : ℝ → ℝ) : Type :=
  ∀ I : FinInstance, Run I.inst g

/-- `OPT_offline` (1) on a finite instance. -/
noncomputable def FinInstance.optOffline (I : FinInstance) : ℝ :=
  TwoStageMatch.optOffline I.inst

/-- `OPT_online` (2) on a finite instance. -/
noncomputable def FinInstance.optOnline (I : FinInstance) : ℝ :=
  TwoStageMatch.optOnline I.inst

/-- `Γ_weighted-matching(ALG, OPT)` of Definition 2, p.10, for the algorithm given by the
selection `σ` and a benchmark `B` (`FinInstance.optOffline` or `FinInstance.optOnline`): the
infimum of `𝔼[Σ_j w_j 𝟙{j matched in M₁ ∪ M₂}] / OPT` over all finite instances with `OPT > 0`. -/
noncomputable def gamma {g : ℝ → ℝ} (σ : Selection g) (B : FinInstance → ℝ) : ℝ :=
  sInf {r : ℝ | ∃ I : FinInstance, 0 < B I ∧ r = (σ I).value / B I}

end TwoStageMatch


