-- Prove2me | Definitions.Def_BauerleRiederMDP_RegimeSwitching_stepKernel
-- name    : BauerleRiederMDP_RegimeSwitching_stepKernel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:01.20114+00:00
-- url     : https://prove2.me/theorems/1dd3e0c3-ab7a-408a-a546-f296b94c2fda
-- title:
--   Transition kernel $Q_k(\cdot\mid x,f_k(x))$ of the controlled state process
-- statement:
--   Given a Markov Decision Model with disturbances and a Markov policy $\pi=(f_k)$, the **one-step transition kernel at time $k$** sends a state $x$ to the law of
--
--   $$
--   T_k\big(x,f_k(x),Z_{k+1}\big),\qquad Z_{k+1}\sim Q^Z_k(\cdot\mid x,f_k(x)),
--   $$
--
--   that is, $Q_k(B\mid x,f_k(x))=Q^Z_k\big(\{z: T_k(x,f_k(x),z)\in B\}\mid x,f_k(x)\big)$. It is the transition law of the Markov Decision Process under $\pi$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 2.1.3, p.15 (PDF p.30); p.17 (PDF p.32)

import Mathlib
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_DisturbanceMDM
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_MarkovPolicy
open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.RegimeSwitching

/-- The one-step transition kernel at time `k` of the state process controlled by the Markov
policy `π`: from state `x` the next state is `T_k(x, f_k(x), Z_{k+1})` with
`Z_{k+1} ∼ Q^Z_k(· | x, f_k(x))`, i.e. `Q_k(B | x, f_k(x)) = Q^Z_k({z | T_k(x, f_k(x), z) ∈ B} |
x, f_k(x))` (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Theorem 2.1.3, p.15, PDF p.30, and condition (ii) of the
Ionescu–Tulcea construction, p.17, PDF p.32). -/
noncomputable def stepKernel {E A Z : Type*} [MeasurableSpace E] [MeasurableSpace A]
    [MeasurableSpace Z] (M : DisturbanceMDM E A Z) (π : MarkovPolicy E A) (k : ℕ) :
    Kernel E E :=
  (Kernel.deterministic id measurable_id ×ₖ
      (M.QZ k).comap (fun x => (x, π.f k x)) (measurable_id.prodMk (π.measurable_f k))).map
    (fun p => M.T k (p.1, π.f k p.1) p.2)

instance {E A Z : Type*} [MeasurableSpace E] [MeasurableSpace A] [MeasurableSpace Z]
    (M : DisturbanceMDM E A Z) (π : MarkovPolicy E A) (k : ℕ) :
    IsMarkovKernel (stepKernel M π k) := by
  have := M.isMarkovKernel_QZ k
  unfold stepKernel
  exact Kernel.IsMarkovKernel.map _
    ((M.measurable_T k).comp ((measurable_fst.prodMk ((π.measurable_f k).comp measurable_fst)).prodMk
      measurable_snd))

end BauerleRiederMDP.RegimeSwitching


