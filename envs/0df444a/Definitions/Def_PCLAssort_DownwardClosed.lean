-- Prove2me | Definitions.Def_PCLAssort_DownwardClosed
-- name    : PCLAssort_DownwardClosed
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:33.412855+00:00
-- url     : https://prove2.me/theorems/cfc301cf-89d1-4e9a-9433-14afeefafa47
-- title:
--   Downward-closed family of feasible assortments
-- statement:
--   A family $\mathcal F$ of assortments is admissible if it contains $\emptyset$ and is downward closed: for any $A\in\mathcal F$ and $B\subseteq A$, also $B\in\mathcal F$. The paper assumes this throughout.
--
--   **Formalization Note** Nonemptiness of $\mathcal F$ is written as $\emptyset\in\mathcal F$; all the paper's constraint families contain $\emptyset$.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), §2, p.790 (PDF p.6)

import Mathlib

namespace PCLAssort

/-- A family `𝓕` of feasible assortments as assumed throughout the paper (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, §2, p.790):
`𝓕` is downward closed ("for any `A ∈ 𝓕` and `B ⊆ A`, we also have `B ∈ 𝓕`") and nonempty.

**Formalization Note.** Nonemptiness is stated as `∅ ∈ 𝓕` (equivalent, given downward closure);
every constraint family of the paper contains `∅`, and with `𝓕 = ∅` the value `z*` of (2) is
undefined. -/
def DownwardClosed {n : ℕ} (F : Set (Finset (Fin n))) : Prop :=
  ∅ ∈ F ∧ ∀ A ∈ F, ∀ B : Finset (Fin n), B ⊆ A → B ∈ F

end PCLAssort


