-- Prove2me | Definitions.Def_RQCMoments_IsOPMeasure
-- name    : RQCMoments_IsOPMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:08:08.376769+00:00
-- url     : https://prove2.me/theorems/e4691c13-fcd0-4ad8-b783-042f18abe604
-- title:
--   Probability measure on $\mathbb R$ with finite moments and infinite support
-- statement:
--   A Borel measure $\nu$ on $\mathbb R$ satisfies the **standing assumption of §2.4** if
--   1. $\nu$ is a probability measure;
--   2. all moments are finite: $\int |t|^n\,d\nu(t)<\infty$ for every $n\ge 0$;
--   3. the support of $\nu$ is an infinite set.
--
--   Under these assumptions the orthonormal polynomials of $\nu$ exist for every degree, which is what Gauss quadrature and Christoffel functions need (§§2.4, 4.1).
--
--   **Formalization Note** Finite moments: every monomial $t\mapsto t^n$ is $\nu$-integrable. Infinite support: no finite set $s\subseteq\mathbb R$ carries all the mass, $\nu(\mathbb R\setminus s)\ne 0$; for a Borel measure on $\mathbb R$ this is equivalent to the support being infinite.
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), §2.4, p.15 (PDF p.17)

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

/-- The standing assumption of §2.4 (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), §2.4, p.15): `ν` is a probability measure on `ℝ`
with finite moments whose support is an infinite set.

**Formalization Note** "Finite moments" is integrability of every monomial `t ↦ tⁿ`. "Infinite
support" is encoded as: no finite set carries all of the mass, i.e. `ν(sᶜ) ≠ 0` for every finite
`s ⊆ ℝ`; for a Borel measure on `ℝ` this is equivalent to the support being infinite. -/
def IsOPMeasure (ν : Measure ℝ) : Prop :=
  IsProbabilityMeasure ν ∧ (∀ n : ℕ, Integrable (fun t : ℝ => t ^ n) ν) ∧
    ∀ s : Finset ℝ, ν ((s : Set ℝ)ᶜ) ≠ 0

end RQCMoments


