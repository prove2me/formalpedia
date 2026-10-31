-- Prove2me | Definitions.Def_PCLAssort_fValue
-- name    : PCLAssort_fValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:21:57.771994+00:00
-- url     : https://prove2.me/theorems/a3a6dc62-c8e9-43b6-916d-729649ed51fd
-- title:
--   The function $f(z)=\max_{x\in\mathcal F}h_z(x)$
-- statement:
--   For $z\in\mathbb R$,
--
--   $$
--   f(z)=\max_{x\in\mathcal F}h_z(x).
--   $$
--
--   The optimal revenue $z^*$ is the largest $z$ with $f(z)\ge v_0z$; the framework of Theorem 2 bounds $f$ from above by an LP value $g$.
--
--   **Formalization Note** A supremum over the finite family $\mathcal F$.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), equation (3), p.790 (PDF p.6)

import Mathlib
import Definitions.Def_PCLAssort_PCLInstance
import Definitions.Def_PCLAssort_hz

namespace PCLAssort

/-- The function `f(z) = max_{x ∈ 𝓕} h_z(x)` of equation (3) (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, p.790).

**Formalization Note.** A supremum over the finite set `𝓕`, attained when `𝓕` is nonempty. -/
noncomputable def fValue {n : ℕ} (I : PCLInstance n) (F : Set (Finset (Fin n))) (z : ℝ) : ℝ :=
  ⨆ S : F, hz I z S.1

end PCLAssort


