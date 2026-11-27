-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel_IsPolicy
-- name    : BauerleRiederMDP_LQ_Supplement_BayesModel_IsPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:56:59.332434+00:00
-- url     : https://prove2.me/theorems/3f82ac22-a9e7-4fd9-b23e-2dc41abdb56f
-- title:
--   The history-dependent policies $\tilde{\Pi}_N$
-- statement:
--   **The history-dependent policies $\tilde{\Pi}_N$** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), p.163, PDF 176): $\pi  = (f_0, \dots , f_{N-1})$ with measurable decision rules $f_k : \tilde{H}_k \to  A$, $f_k(\tilde{h}_k) \in  D(x_k)$, $k = 0, \dots , N - 1$.
--
--   **Formalization Note.** A policy is a family $\pi  k : \tilde{H}_k \to  A$ indexed by $k : \mathbb N $; only $k < N$ is constrained and only those rules enter the values.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.163, PDF 176

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Htil
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Htil_state
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel

namespace BauerleRiederMDP.LQ.Supplement

universe u

/-- **The history-dependent policies `Π̃_N`** (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), p.163, PDF 176): `π = (f_0, …, f_{N−1})` with measurable decision
rules `f_k : H̃_k → A`, `f_k(h̃_k) ∈ D(x_k)`, `k = 0, …, N − 1`.

**Formalization Note.** A policy is a family `π k : H̃_k → A` indexed by `k : ℕ`; only `k < N` is
constrained and only those rules enter the values. -/
def BayesModel.IsPolicy {EX A Z : Type u} {Θ : Type*} [MeasurableSpace EX] [MeasurableSpace A]
    [MeasurableSpace Z] [MeasurableSpace Θ] (M : BayesModel EX A Z Θ) (N : ℕ)
    (π : (k : ℕ) → Htil EX A Z k → A) : Prop :=
  ∀ k < N, Measurable (π k) ∧ ∀ h, (Htil.state k h, π k h) ∈ M.D

end BauerleRiederMDP.LQ.Supplement


