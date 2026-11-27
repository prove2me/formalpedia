-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel_law
-- name    : BauerleRiederMDP_LQ_Supplement_BayesModel_law
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:57:25.74266+00:00
-- url     : https://prove2.me/theorems/baa84805-d262-5752-b2f0-93a2b9bbad0e
-- title:
--   The joint law of the parameter, the history and the accumulated reward
-- statement:
--   **The joint law of the parameter, the history and the accumulated reward** in the Bayesian Model under a policy $\pi  \in  \tilde{\Pi}_N$ from $x_0 = x$ (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), p.150, PDF 163: $\mathbb P ^\pi _x(\cdot ) = \int  P^\pi _{x\theta }(\cdot ) Q_0(d\theta )$ built by Ionescu–Tulcea, in the disturbance form of p.154 and Example 5.2.4): $\theta  ~ Q_0$, and given $\theta $ and $\tilde{h}_k$ the action is $a_k = \pi _k(\tilde{h}_k)$, $z_{k+1} ~ Q^Z(\cdot |x_k, \theta , a_k)$, $x_{k+1} = T_X(x_k, a_k, z_{k+1})$. The third coordinate is $\sum _{j<k} \beta ^j r(x_j, \theta , a_j)$.
--
--   **Formalization Note.** Built forwards by `Measure.bind`; no value function enters. The reward is carried along so that the expected total reward is one integral.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.150, PDF 163: `ℙ^π_x(·) = ∫ P^π_{xθ}(·) Q_0(dθ)` built by Ionescu–Tulcea, in the disturbance form of p.154 and Example 5.2.4

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Htil
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Htil_state
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.LQ.Supplement

universe u

/-- **The joint law of the parameter, the history and the accumulated reward** in the Bayesian
Model under a policy `π ∈ Π̃_N` from `x_0 = x` (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), p.150, PDF 163: `ℙ^π_x(·) = ∫ P^π_{xθ}(·) Q_0(dθ)` built by
Ionescu–Tulcea, in the disturbance form of p.154 and Example 5.2.4): `θ ~ Q_0`, and given `θ` and
`h̃_k` the action is `a_k = π_k(h̃_k)`, `z_{k+1} ~ Q^Z(·|x_k, θ, a_k)`, `x_{k+1} = T_X(x_k, a_k, z_{k+1})`.
The third coordinate is `∑_{j<k} β^j r(x_j, θ, a_j)`.

**Formalization Note.** Built forwards by `Measure.bind`; no value function enters. The reward is
carried along so that the expected total reward is one integral. -/
noncomputable def BayesModel.law {EX A Z : Type u} {Θ : Type*} [MeasurableSpace EX] [MeasurableSpace A]
    [MeasurableSpace Z] [MeasurableSpace Θ] (M : BayesModel EX A Z Θ)
    (π : (k : ℕ) → Htil EX A Z k → A) (x : EX) : (k : ℕ) → Measure (Θ × Htil EX A Z k × ℝ)
  | 0 => M.Q0.map fun θ => (θ, x, 0)
  | k + 1 => (BayesModel.law M π x k).bind fun p =>
      (M.QZ (Htil.state k p.2.1, p.1, π k p.2.1)).map fun z =>
        (p.1, (p.2.1, π k p.2.1, z, M.TX (Htil.state k p.2.1, π k p.2.1, z)),
          p.2.2 + M.β ^ k * M.r (Htil.state k p.2.1, p.1, π k p.2.1))

end BauerleRiederMDP.LQ.Supplement


