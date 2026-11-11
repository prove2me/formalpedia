-- Prove2me | Definitions.Def_RQCMoments_IsOrthonormalFamily
-- name    : RQCMoments_IsOrthonormalFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:08:09.690182+00:00
-- url     : https://prove2.me/theorems/6e6a24ac-5ca1-4d1b-aa1f-3f4e7348c186
-- title:
--   Orthonormal polynomials $q_0,q_1,\dots$ of a measure
-- statement:
--   Let $\nu$ be a measure on $\mathbb R$. A sequence of real polynomials $q_0,q_1,q_2,\dots$ is a family of **orthonormal polynomials** of $\nu$ if
--   $$
--   \deg q_n=n\quad\text{and}\quad \int q_n(t)\,q_m(t)\,d\nu(t)=\delta_{n,m}\qquad(n,m\ge 0).
--   $$
--
--   Under the assumptions of §2.4 such a family exists (Gram–Schmidt applied to $1,t,t^2,\dots$ in $L^2(\nu)$) and is unique up to the sign of each $q_n$; its zeros give the nodes of Gauss quadrature.
--
--   **Formalization Note** Each product $q_nq_m$ is required to be $\nu$-integrable, so the relations concern genuine integrals (Lean's Bochner integral of a non-integrable function is $0$). No sign normalization is imposed.
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), §2.4; (49), p.15 and p.21 (PDF pp.17, 23)

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

/-- A family of orthonormal polynomials of `ν` (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), §2.4, p.15; (49), p.21):
real polynomials `q₀, q₁, …` with `deg qₙ = n` and `∫ qₙ qₘ dν = δ_{n,m}`.

**Formalization Note** The products `qₙ qₘ` are required to be `ν`-integrable, so that the
orthonormality relations are about genuine integrals (a Bochner integral of a non-integrable
function is `0` in Lean). The family is not normalized by sign; under the §2.4 assumptions it
is unique up to the sign of each `qₙ`. -/
def IsOrthonormalFamily (ν : Measure ℝ) (q : ℕ → Polynomial ℝ) : Prop :=
  (∀ n, (q n).natDegree = n) ∧
    ∀ n m, Integrable (fun t => (q n).eval t * (q m).eval t) ν ∧
      ∫ t, (q n).eval t * (q m).eval t ∂ν = if n = m then 1 else 0

end RQCMoments


