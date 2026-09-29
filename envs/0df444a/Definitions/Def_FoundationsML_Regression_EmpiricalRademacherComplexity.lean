-- Prove2me | Definitions.Def_FoundationsML_Regression_EmpiricalRademacherComplexity
-- name    : FoundationsML_Regression_EmpiricalRademacherComplexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:06:08.792213+00:00
-- url     : https://prove2.me/theorems/b387f74e-5cfb-44d6-8100-8b06770853ec
-- title:
--   Empirical Rademacher complexity (Definition 3.1)
-- statement:
--   **Definition 3.1, p. 30, PDF p. 47.** $\hat R_S(G) = \mathbb E_\sigma[\sup_{g\in G}
--   \frac1m\sum_i\sigma_i g(z_i)]$. Restated locally in this chunk's `Regression` namespace.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 30, Definition 3.1 (PDF p. 47)

import Mathlib

namespace FoundationsML.Regression

/-- The empirical Rademacher complexity of a family `G` of functions `Z → ℝ` with respect to
a fixed sample `S : Fin m → Z` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, Definition 3.1, p. 30, PDF p. 47, restated locally for
this chapter since drafts cannot import another chunk's draft module):
`R̂_S(G) = E_σ[sup_{g∈G} (1/m) ∑_{i=1}^m σ_i g(z_i)]`, where `σ_1,…,σ_m` are independent
uniform `{−1,+1}`-valued (Rademacher) random variables.

**Formalization Note.** `σ` ranges over `Fin m → Bool`; the expectation is the exact finite
uniform average over its `2^m` outcomes. -/
noncomputable def EmpiricalRademacherComplexity {Z : Type*} {m : ℕ}
    (G : Set (Z → ℝ)) (S : Fin m → Z) : ℝ :=
  (1 / (2 : ℝ) ^ m) * ∑ σ : Fin m → Bool,
    ⨆ g ∈ G, (1 / (m : ℝ)) * ∑ i : Fin m, (if σ i then (1 : ℝ) else -1) * g (S i)

end FoundationsML.Regression


