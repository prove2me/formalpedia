-- Prove2me | Definitions.Def_SmoothedSimplex_Shadow_underPlaneMass
-- name    : SmoothedSimplex_Shadow_underPlaneMass
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T13:17:30.059804+00:00
-- url     : https://prove2.me/theorems/edd4c7fc-54a0-462a-b8e6-fd428d776a99
-- title:
--   §4 — the factor $\prod_{j>d}\int [\langle\omega|a_j\rangle\le s\langle\omega|q\rangle]\,\mu_j(a_j)\,da_j$
-- statement:
--   Let $\mu_{d+1},\dots,\mu_n$ be the Gaussian distributions of standard deviation $\sigma$ centered at $\bar a_{d+1},\dots,\bar a_n\in\mathbb R^d$. For vectors $\omega,q$ and a real $s$, this is
--
--   $$
--   \prod_{j>d}\int_{a_j}\big[\langle\omega|a_j\rangle\le s\langle\omega|q\rangle\big]\,\mu_j(a_j)\,da_j ,
--   $$
--
--   the probability that all of $a_{d+1},\dots,a_n$ lie in the halfspace below the hyperplane $\{x:\langle\omega|x\rangle=s\langle\omega|q\rangle\}$. It is the factor in the densities of Lemmas 4.1.1, 4.2.1, 4.2.2 and 4.2.3 that records the event that the simplex on $a_1,\dots,a_d$ is a facet with the other points underneath.
--
--   **Formalization Note** Indices are 0-based: the paper's $j\in\{d+1,\dots,n\}$ are the `j : Fin n` with $j\ge d$. Each factor is a probability, valued in $[0,\infty]$.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, densities of Lemmas 4.1.1 (p. 45), 4.2.1 (p. 52), 4.2.2 (p. 52), 4.2.3 (p. 54)

import Mathlib
import Definitions.Def_SmoothedSimplex_Shadow_gaussian

namespace SmoothedSimplex.Shadow

open scoped RealInnerProductSpace

/-- The factor `∏_{j>d} ∫_{a_j} [⟨ω|a_j⟩ ≤ s⟨ω|q⟩] µ_j(a_j) da_j` that appears in the densities of
Lemmas 4.1.1, 4.2.1, 4.2.2 and 4.2.3 (Spielman & Teng, arXiv:cs/0111050v7, printed pp. 44–54,
PDF pp. 44–54), where `µ_j` is the Gaussian of standard deviation `σ` centered at `ā_j`: the
product over `j > d` of the `µ_j`-measure of the halfspace `{a : ⟨ω|a⟩ ≤ s⟨ω|q⟩}`.

**Formalization Note.** Indices are 0-based: the paper's `j ∈ {d+1, …, n}` are the `j : Fin n`
with `d ≤ j`. Values are in `ℝ≥0∞` (each factor is a probability in `[0, 1]`). -/
noncomputable def underPlaneMass {d n : ℕ} (abar : Fin n → EuclideanSpace ℝ (Fin d)) (σ : ℝ)
    (ω q : EuclideanSpace ℝ (Fin d)) (s : ℝ) : ENNReal :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ j.val),
    gaussian (abar j) σ {a | ⟪ω, a⟫ ≤ s * ⟪ω, q⟫}

end SmoothedSimplex.Shadow


