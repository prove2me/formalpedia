-- Prove2me | Definitions.Def_FoundationsML_RademacherVC_EmpiricalRademacherComplexity
-- name    : FoundationsML_RademacherVC_EmpiricalRademacherComplexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:10:53.218001+00:00
-- url     : https://prove2.me/theorems/2ab8cf70-1e1c-412f-8a90-bf3c17c7b0cd
-- title:
--   Empirical Rademacher complexity (Definition 3.1)
-- statement:
--   **Definition 3.1 (Empirical Rademacher complexity), p. 30, PDF p. 47.** Let $G$ be a
--   family of functions mapping from $Z$ to $[a,b]$ and $S=(z_1,\dots,z_m)$ a fixed sample.
--   The empirical Rademacher complexity of $G$ with respect to $S$ is
--   $$\hat R_S(G) = \mathbb E_\sigma\Big[\sup_{g\in G} \frac1m\sum_{i=1}^m \sigma_i g(z_i)\Big],$$
--   where $\sigma_1,\dots,\sigma_m$ are independent uniform $\{-1,+1\}$-valued (Rademacher)
--   random variables. It measures how well $G$ correlates with random noise on $S$.
--
--   **Formalization Note.** `σ` ranges over `Fin m → Bool` (`true` = `+1`, `false` = `-1`); the
--   expectation is the exact finite uniform average over its `2^m` outcomes (no measure theory
--   needed, since `σ`'s law is uniform on a finite set). `⨆ g ∈ G, …` is the supremum over `G`
--   (possibly infinite), matching the book's own standing measurability/well-definedness
--   assumption (footnote 3, p. 30).
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 30, Definition 3.1 (PDF p. 47)

import Mathlib

namespace FoundationsML.RademacherVC

/-- The empirical Rademacher complexity of a family `G` of functions `Z → ℝ` with respect to
a fixed sample `S : Fin m → Z` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, Definition 3.1, p. 30, PDF p. 47):
`R̂_S(G) = E_σ[sup_{g∈G} (1/m) ∑_{i=1}^m σ_i g(z_i)]`, where `σ_1,…,σ_m` are independent
uniform `{−1,+1}`-valued (Rademacher) random variables.

**Formalization Note.** Since `σ` ranges over the finite type `Fin m → Bool` (`true`
standing for `+1`, `false` for `−1`), the expectation over `σ` is the exact finite uniform
average over its `2^m` outcomes, avoiding any measure-theoretic integral; `true`/`false` is
mapped to `±1` via `if σ i then 1 else -1`. The supremum over `g ∈ G` is `⨆ g ∈ G, …`
(real supremum over the index set `G`), matching the book's own standing assumption
(footnote 3, p. 30) that this supremum is well-defined. -/
noncomputable def EmpiricalRademacherComplexity {Z : Type*} {m : ℕ}
    (G : Set (Z → ℝ)) (S : Fin m → Z) : ℝ :=
  (1 / (2 : ℝ) ^ m) * ∑ σ : Fin m → Bool,
    ⨆ g ∈ G, (1 / (m : ℝ)) * ∑ i : Fin m, (if σ i then (1 : ℝ) else -1) * g (S i)

end FoundationsML.RademacherVC


