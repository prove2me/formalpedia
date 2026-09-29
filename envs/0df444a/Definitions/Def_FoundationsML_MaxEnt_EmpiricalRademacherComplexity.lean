-- Prove2me | Definitions.Def_FoundationsML_MaxEnt_EmpiricalRademacherComplexity
-- name    : FoundationsML_MaxEnt_EmpiricalRademacherComplexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:16:30.281923+00:00
-- url     : https://prove2.me/theorems/53ccce33-0bf6-4da2-b01d-a0ffdc77111b
-- title:
--   Empirical Rademacher complexity (Definition 3.1, restated)
-- statement:
--   **Definition 3.1, p. 30, PDF p. 47 (restated locally for this chapter).**
--   $\hat R_S(G) = \mathbb E_\sigma[\sup_{g\in G}\frac1m\sum_{i=1}^m\sigma_ig(z_i)]$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 30, Definition 3.1 (PDF p. 47)

import Mathlib

namespace FoundationsML.MaxEnt

/-- The empirical Rademacher complexity of a family `G` of functions `Z → ℝ` with respect to a
fixed sample `S : Fin m → Z` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, Definition 3.1, p. 30, PDF p. 47, restated locally for this
chapter since drafts cannot import another chunk's draft module):
`R̂_S(G) = E_σ[sup_{g∈G} (1/m) ∑_{i=1}^m σ_i g(z_i)]`. -/
noncomputable def EmpiricalRademacherComplexity {Z : Type*} {m : ℕ}
    (G : Set (Z → ℝ)) (S : Fin m → Z) : ℝ :=
  (1 / (2 : ℝ) ^ m) * ∑ σ : Fin m → Bool,
    ⨆ g ∈ G, (1 / (m : ℝ)) * ∑ i : Fin m, (if σ i then (1 : ℝ) else -1) * g (S i)

end FoundationsML.MaxEnt


