-- Prove2me | Definitions.Def_RockafellianRelax_IsLimitExact
-- name    : RockafellianRelax_IsLimitExact
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:36:50.368087+00:00
-- url     : https://prove2.me/theorems/98e19cd8-2696-4560-8ff1-8d929ae3f1c0
-- title:
--   Limit-exact Rockafellians, supported by $\bar y$ (Definition 3.6)
-- statement:
--   Functions $f^\nu : \mathbb R^m \times \mathbb R^n \to \overline{\mathbb R}$, $\nu \in \mathbb N$, are **limit-exact Rockafellians** for the problem of minimizing $\varphi$, **supported by** $\bar y \in \mathbb R^m$, if they epi-converge to some Rockafellian $f$ for that problem which is exact, supported by $\bar y$.
--
--   Epi-convergence of $f^\nu$ to $f$ means: for every $z$ and every sequence $z^\nu \to z$, $\liminf_\nu f^\nu(z^\nu) \ge f(z)$ (3.8); and for every $z$ there is a sequence $z^\nu \to z$ with $\limsup_\nu f^\nu(z^\nu) \le f(z)$ (3.9).
--
--   **Formalization Note** Epi-convergence is the published `PerspEpi.SeqEpiConv` on the product topology of `(Fin m → ℝ) × (Fin n → ℝ)`; $\nu$ runs over Lean's $\mathbb N$ from $0$.
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, Definition 3.6 and (3.8)–(3.9), p.9

import Mathlib
import Definitions.Def_RockafellianRelax_IsExact
import Definitions.Def_PerspEpi_SeqEpiConv

namespace RockafellianRelax

/-- **Limit-exact Rockafellians, supported by `ȳ`** (Definition 3.6).
Royset, Chen & Eckstrand, arXiv:2204.04762v4, Definition 3.6, p.9: "For the problem (3.1), the
functions {fν : ℝᵐ × ℝⁿ → R̄, ν ∈ ℕ} are limit-exact Rockafellians if they epi-converge to an exact
Rockafellian f : ℝᵐ × ℝⁿ → R̄ of the problem. … The (strict) limiting exactness is said to be
supported by ȳ ∈ ℝᵐ when f is (strictly) exact, supported by ȳ."

**Formalization Note.** Epi-convergence is the sequential (3.8)–(3.9) of p.9, the published
`PerspEpi.SeqEpiConv` on the product topology of `(Fin m → ℝ) × (Fin n → ℝ)` (the same convergent
sequences as the Euclidean norm). The paper indexes by `ν ∈ ℕ = {1, 2, …}`; Lean's `ℕ` starts at
`0`, which changes no limit. -/
def IsLimitExact {m n : ℕ} (F : ℕ → (Fin m → ℝ) × (Fin n → ℝ) → EReal)
    (φ : (Fin n → ℝ) → EReal) (ybar : Fin m → ℝ) : Prop :=
  ∃ f : (Fin m → ℝ) × (Fin n → ℝ) → EReal, IsExact f φ ybar ∧ PerspEpi.SeqEpiConv F f

end RockafellianRelax


