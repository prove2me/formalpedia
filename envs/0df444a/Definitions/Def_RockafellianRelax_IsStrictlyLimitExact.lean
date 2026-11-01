-- Prove2me | Definitions.Def_RockafellianRelax_IsStrictlyLimitExact
-- name    : RockafellianRelax_IsStrictlyLimitExact
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:36:59.526013+00:00
-- url     : https://prove2.me/theorems/ddb5f22b-fd92-44fc-810c-b9727be1cfab
-- title:
--   Strictly limit-exact Rockafellians, supported by $\bar y$ (Definition 3.6)
-- statement:
--   Functions $f^\nu : \mathbb R^m \times \mathbb R^n \to \overline{\mathbb R}$, $\nu \in \mathbb N$, are **strictly limit-exact Rockafellians** for the problem of minimizing $\varphi$, **supported by** $\bar y \in \mathbb R^m$, if they epi-converge (in the sense of (3.8)–(3.9)) to some Rockafellian $f$ for that problem which is strictly exact, supported by $\bar y$.
--
--   **Formalization Note** Epi-convergence is the published `PerspEpi.SeqEpiConv`; $\nu$ runs over Lean's $\mathbb N$ from $0$.
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, Definition 3.6, p.9

import Mathlib
import Definitions.Def_RockafellianRelax_IsStrictlyExact
import Definitions.Def_PerspEpi_SeqEpiConv

namespace RockafellianRelax

/-- **Strictly limit-exact Rockafellians, supported by `ȳ`** (Definition 3.6).
Royset, Chen & Eckstrand, arXiv:2204.04762v4, Definition 3.6, p.9: "The functions {fν, ν ∈ ℕ} are
strictly limit-exact Rockafellians if f is strictly exact. The (strict) limiting exactness is said to
be supported by ȳ ∈ ℝᵐ when f is (strictly) exact, supported by ȳ."

**Formalization Note.** `f` is the epi-limit of the `fν` (sequential epi-convergence (3.8)–(3.9),
the published `PerspEpi.SeqEpiConv`, product topology). `ν` runs over Lean's `ℕ` from `0`. -/
def IsStrictlyLimitExact {m n : ℕ} (F : ℕ → (Fin m → ℝ) × (Fin n → ℝ) → EReal)
    (φ : (Fin n → ℝ) → EReal) (ybar : Fin m → ℝ) : Prop :=
  ∃ f : (Fin m → ℝ) × (Fin n → ℝ) → EReal, IsStrictlyExact f φ ybar ∧ PerspEpi.SeqEpiConv F f

end RockafellianRelax


