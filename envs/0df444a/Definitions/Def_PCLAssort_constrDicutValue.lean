-- Prove2me | Definitions.Def_PCLAssort_constrDicutValue
-- name    : PCLAssort_constrDicutValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:55.331738+00:00
-- url     : https://prove2.me/theorems/f85743dc-9351-4aba-bd92-e24f41492c58
-- title:
--   Constrained max-dicut value with the dummy vertex unselected
-- statement:
--   For a graph on the vertex set $[n+1]$ (dummy vertex $n+1$) with weights $w$ and a family $\mathcal F$ of subsets of $[n]$, the optimal max-dicut value subject to the constraints that the dummy vertex is not selected and that the set of chosen vertices lies in $\mathcal F$ is
--
--   $$
--   \max_{S\in\mathcal F}\ \sum_{(i,j)\in E:\ i\in S,\ j\notin S}w_{ij}.
--   $$
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), Lemmas 5 and 6, p.792 (PDF p.8)

import Mathlib
import Definitions.Def_PCLAssort_cutValue

namespace PCLAssort

/-- The optimal max-dicut value on a graph with vertex set `[n + 1]` subject to the constraints that the
dummy vertex `n + 1` is not selected and that the set of chosen vertices lies in `𝓕` (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, Lemmas 5
and 6, p.792): `max_{S ∈ 𝓕} ∑_{(i,j) ∈ E : i ∈ S, j ∉ S} w_ij`.

**Formalization Note.** Vertices are `Option (Fin n)` with `none` the dummy; a selection avoiding the
dummy is the image under `some` of an `S ⊆ [n]`. The supremum is over the finite set `𝓕`. -/
noncomputable def constrDicutValue {n : ℕ} (E : Finset (Option (Fin n) × Option (Fin n)))
    (w : Option (Fin n) × Option (Fin n) → ℝ) (F : Set (Finset (Fin n))) : ℝ :=
  ⨆ S : F, cutValue E w (S.1.image some)

end PCLAssort


