-- Prove2me | Definitions.Def_DeltaSLearning_leader
-- name    : DeltaSLearning_leader
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:06:35.41713+00:00
-- url     : https://prove2.me/theorems/9286e8bb-10aa-46a0-93d0-396ad5b1272f
-- title:
--   Leading index $j^n=\arg\max_{j\in\mathcal A^n}S^n_j$ (13)
-- statement:
--   Given the state at the beginning of an epoch, $j^n$ is an index of the active set with the highest target,
--   $$j^n := \arg\max_{j\in\mathcal A^n}S^n_j ,$$
--   the "information-maximizing" policy whose sales suffice to simulate every active policy.
--
--   **Formalization Note** The paper gives no tie-break; ties go to the smallest maximizing index. On an empty active set the value is a junk $0$; the active set is never empty when the confidence sizes are nonnegative.
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), eq. (13), p.13; Algorithm 1, p.15

import Mathlib
import Definitions.Def_DeltaSLearning_AlgState

namespace DeltaSLearning

/-- The index `jⁿ := argmax_{j ∈ 𝒜ⁿ} Sⁿ_j` of (13): the active policy with the highest target.
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), eq. (13), p.13, and Algorithm 1, p.15.

**Formalization Note** The paper gives no tie-break; ties go to the smallest maximizing index.
On an empty active set the value is the junk `sInf ∅ = 0`; the active set is never empty when the
confidence sizes are nonnegative. -/
noncomputable def leader (st : AlgState) : ℕ :=
  sInf {j : ℕ | j ∈ st.A ∧ ∀ i ∈ st.A, st.S i ≤ st.S j}

end DeltaSLearning


