-- Prove2me | Definitions.Def_UnderstandingML_PACBayes
-- name    : UnderstandingML_PACBayes
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T06:04:07.497234+00:00
-- url     : https://prove2.me/theorems/402284cb-8f5f-4573-9c1e-c7faf18c8696
-- title:
--   Chapter 31: the loss and risks of a posterior Q (Gibbs predictor) and the Kullback–Leibler divergence D(Q‖P)
-- statement:
--   Chapter 31 of Shalev-Shwartz and Ben-David. For a posterior distribution $Q$ over the class, read as the randomized rule that draws $h \sim Q$ and predicts $h(x)$: `gibbsLoss loss Q z` $= \ell(Q, z) = \mathbb{E}_{h \sim Q}[\ell(h, z)]$, `gibbsRisk loss D Q` $= L_D(Q) = \mathbb{E}_{h \sim Q}[L_D(h)]$ and `gibbsEmpRisk loss S Q` $= L_S(Q) = \mathbb{E}_{h \sim Q}[L_S(h)]$ (p. 415). `klDiv Q P` is the Kullback–Leibler divergence $D(Q\|P) = \mathbb{E}_{h \sim Q}[\ln(Q(h)/P(h))]$ (Theorem 31.1), with $Q(h)/P(h)$ the Radon–Nikodym derivative $dQ/dP$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §31.1 pp. 415-416 (ℓ(Q, z), L_D(Q), L_S(Q), D(Q‖P))

import Definitions.Def_UnderstandingML_Framework
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

/-!
# Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, Chapter 31: PAC-Bayes

Shalev-Shwartz and Ben-David, *Understanding Machine Learning: From Theory to Algorithms*,
Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §31.1.

**Priors, posteriors and Gibbs predictors (p. 415).** A prior distribution `P` over the class
`H` expresses prior knowledge; the learner outputs a posterior distribution `Q` over `H`, read
as the randomized rule that draws `h ∼ Q` and predicts `h(x)`. Its loss on `z` is
`ℓ(Q, z) = E_{h ∼ Q}[ℓ(h, z)]`, and by linearity of expectation `L_D(Q) = E_{h ∼ Q}[L_D(h)]` and
`L_S(Q) = E_{h ∼ Q}[L_S(h)]`. The **Kullback–Leibler divergence** is
`D(Q‖P) = E_{h ∼ Q}[ln(Q(h)/P(h))]` (Theorem 31.1).

**Conventions.** The class is a measurable space `Hyp`, priors and posteriors are probability
measures on it, and `Q(h)/P(h)` is the Radon–Nikodym derivative; the PAC-Bayes bound is stated
for posteriors `Q ≪ P` whose log-density is `Q`-integrable, the cases in which `D(Q‖P)` is a
real number (otherwise the bound is vacuous). Risks are those of Chapter 2, samples are
`Fin m`-indexed under `iidLaw`.
-/

open MeasureTheory

namespace UnderstandingML

section Gibbs

variable {Z Hyp : Type*} [MeasurableSpace Z] [MeasurableSpace Hyp]

/-- The loss of the posterior `Q` on the example `z`: `ℓ(Q, z) = E_{h ∼ Q}[ℓ(h, z)]` (p. 415). -/
noncomputable def gibbsLoss (loss : Hyp → Z → ℝ) (Q : Measure Hyp) (z : Z) : ℝ :=
  ∫ h, loss h z ∂Q

/-- The generalization loss of `Q`: `L_D(Q) = E_{h ∼ Q}[L_D(h)]` (p. 415). -/
noncomputable def gibbsRisk (loss : Hyp → Z → ℝ) (D : Measure Z) (Q : Measure Hyp) : ℝ :=
  ∫ h, risk loss D h ∂Q

/-- The training loss of `Q`: `L_S(Q) = E_{h ∼ Q}[L_S(h)]` (p. 415). -/
noncomputable def gibbsEmpRisk (loss : Hyp → Z → ℝ) {m : ℕ} (S : Fin m → Z) (Q : Measure Hyp) :
    ℝ :=
  ∫ h, empRisk loss S h ∂Q

/-- The **Kullback–Leibler divergence** `D(Q‖P) = E_{h ∼ Q}[ln(Q(h)/P(h))]` (Theorem 31.1), with
`Q(h)/P(h)` the Radon–Nikodym derivative `dQ/dP`. -/
noncomputable def klDiv (Q P : Measure Hyp) : ℝ :=
  ∫ h, Real.log (Q.rnDeriv P h).toReal ∂Q

end Gibbs

end UnderstandingML


