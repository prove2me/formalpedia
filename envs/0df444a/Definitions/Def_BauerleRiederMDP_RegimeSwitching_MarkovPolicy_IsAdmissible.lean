-- Prove2me | Definitions.Def_BauerleRiederMDP_RegimeSwitching_MarkovPolicy_IsAdmissible
-- name    : BauerleRiederMDP_RegimeSwitching_MarkovPolicy_IsAdmissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:56.078993+00:00
-- url     : https://prove2.me/theorems/9eb0ad7d-e9aa-4ee0-92a2-223bec3a26dc
-- title:
--   Admissible Markov policy from time $n$ to the horizon $N$
-- statement:
--   A Markov policy $\pi=(f_k)$ is **admissible from time $n$ to the horizon $N$** in a Markov Decision Model if
--
--   $$
--   f_k(x)\in D_k(x)\qquad\text{for all }x\in E\text{ and all }n\le k<N,
--   $$
--
--   that is, $f_n,\dots,f_{N-1}$ are decision rules. The value functions are suprema over these policies.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition 2.1.5, p.16 (PDF p.31)

import Mathlib
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_DisturbanceMDM
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_MarkovPolicy

namespace BauerleRiederMDP.RegimeSwitching

/-- The Markov policy `π` is **admissible from time `n` to the horizon `N`** in the model `M`:
for `n ≤ k < N` the map `f_k` is a decision rule, `f_k(x) ∈ D_k(x)` for every state `x ∈ E`
(Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Definition 2.1.5, p.16, PDF p.31). -/
def MarkovPolicy.IsAdmissible {E A Z : Type*} [MeasurableSpace E] [MeasurableSpace A]
    [MeasurableSpace Z] (M : DisturbanceMDM E A Z) (π : MarkovPolicy E A) (n N : ℕ) : Prop :=
  ∀ k, n ≤ k → k < N → ∀ x, π.f k x ∈ M.D k x

end BauerleRiederMDP.RegimeSwitching


