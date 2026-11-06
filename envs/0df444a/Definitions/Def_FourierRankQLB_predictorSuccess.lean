-- Prove2me | Definitions.Def_FourierRankQLB_predictorSuccess
-- name    : FourierRankQLB_predictorSuccess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:43:04.712456+00:00
-- url     : https://prove2.me/theorems/92a8158b-be98-4167-a142-21dcc839307a
-- title:
--   The average success probability of the determinant predictor
-- statement:
--   Let a procedure return, given $Q$ and a sign vector $\sigma$, a real number with law $\kappa_\sigma(Q,\cdot)$. The predictor of §4.4
--
--   1. samples the random sign vector;
--   2. runs the procedure independently $125$ times with this vector;
--   3. takes the median $\hat Z$ of the outputs;
--   4. outputs $-1$ if $\hat Z>9/16$ and $+1$ otherwise.
--
--   This definition is its probability of outputting $\det Q$, averaged over $Q\sim\mu_d$, the sign vector and the runs:
--   $$
--   \int_{O(d)}\mathbb E_\sigma\,\kappa_\sigma(Q,\cdot)^{\otimes125}\{z:\text{output}(z)=\det Q\}\,d\mu_d(Q).
--   $$
--
--   **Formalization Note** The procedure is a Markov kernel for each sign vector, which makes the integrand measurable in $Q$.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, §4.4, steps (1)–(4), p.29

import Mathlib
import Definitions.Def_FourierRankQLB_predictorOutput
import Definitions.Def_FourierRankQLB_signAvg
import Definitions.Def_FourierRankQLB_haarO

open MeasureTheory ProbabilityTheory

namespace FourierRankQLB

/-- The success probability of the predictor of §4.4 built from a procedure, averaged over
`Q ∼ μ_d`, the random sign vector and the runs. The procedure is a Markov kernel `κ σ` for each sign
vector, giving the law of its real output at `Q`. The predictor samples `σ`, runs the procedure `125`
times independently with this `σ`, takes the median, and applies `predictorOutput`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, §4.4, steps (1)–(4), p. 29.

**Formalization Note.** Independence of the `125` runs is the product measure `(κ σ Q)^{⊗125}`. The
average over `σ` is `signAvg`. The event is that the output equals `det Q`. -/
noncomputable def predictorSuccess {d : ℕ} (κ : SignVec d → Kernel (Od d) ℝ) : ℝ :=
  ∫ Q, signAvg (fun σ => (Measure.pi fun _ : Fin 125 => κ σ Q).real
    {z | predictorOutput z = (Q : Matrix (Fin d) (Fin d) ℝ).det}) ∂haarO d

end FourierRankQLB


