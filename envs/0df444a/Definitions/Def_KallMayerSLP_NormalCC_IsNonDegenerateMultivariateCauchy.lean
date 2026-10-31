-- Prove2me | Definitions.Def_KallMayerSLP_NormalCC_IsNonDegenerateMultivariateCauchy
-- name    : KallMayerSLP_NormalCC_IsNonDegenerateMultivariateCauchy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:11:37.37199+00:00
-- url     : https://prove2.me/theorems/15c8426a-e903-4e33-9c6a-f21656e98e73
-- title:
--   Non-degenerate multivariate Cauchy random vector (Definition 2.2)
-- statement:
--   An $r$-dimensional random vector $\zeta$ has a **non-degenerate multivariate Cauchy distribution** if there exist an $r\times s$ matrix $B$ with full row rank and with at least one nonzero entry in each of its columns, and $m\in\mathbb R^r$, such that
--   $$\zeta=B\tilde\zeta+m,$$
--   where $\tilde\zeta$ is an $s$-dimensional random vector with stochastically independent components, each having the standard Cauchy distribution.
--
--   This is the hypothesis of Theorem 2.7 (Marti), the Cauchy analogue of Kataoka's Theorem 2.5.
--
--   **Formalization Note** $\tilde\zeta$ lives on the same probability space as $\zeta$; the identity holds $\mathbb P$-almost surely. Full row rank is $\operatorname{rank}B=r$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, Definition 2.2, eq. (2.45), p.115 (PDF p.125)

import Mathlib
import Definitions.Def_KallMayerSLP_NormalCC_IsStandardCauchyVector

open MeasureTheory ProbabilityTheory

namespace KallMayerSLP.NormalCC

/-- **Non-degenerate multivariate Cauchy distribution** (Kall & Mayer 2005, Chapter 2,
Definition 2.2, (2.45), p.115, PDF p.125): "The `r`-dimensional random vector `ζ` has a
non-degenerate multivariate Cauchy distribution, if there exist an `(r × s)` matrix `B` with full
row rank and having at least one nonzero in each of its columns and `m ∈ ℝ^r`, such that
`ζ = B ζ̃ + m` holds, where `ζ̃` is an `s`-dimensional random vector with its components being
stochastically independent and `ζ̃_i` having a standard Cauchy distribution, `∀ i`."

**Formalization Note.** Full row rank is `B.rank = r`; "at least one nonzero in each column" is
`∀ j, ∃ i, B i j ≠ 0`. `ζ̃` lives on the same probability space as `ζ` (`IsStandardCauchyVector`),
and `ζ = B ζ̃ + m` is read as `P`-almost sure equality of random vectors. -/
def IsNonDegenerateMultivariateCauchy {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {r : ℕ}
    (ζ : Ω → Fin r → ℝ) : Prop :=
  ∃ (s : ℕ) (B : Matrix (Fin r) (Fin s) ℝ) (m : Fin r → ℝ) (ζt : Fin s → Ω → ℝ),
    B.rank = r ∧ (∀ j, ∃ i, B i j ≠ 0) ∧ IsStandardCauchyVector P ζt ∧
      ∀ᵐ ω ∂P, ζ ω = B.mulVec (fun j => ζt j ω) + m

end KallMayerSLP.NormalCC


