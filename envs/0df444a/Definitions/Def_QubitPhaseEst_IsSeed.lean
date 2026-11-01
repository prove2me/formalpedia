-- Prove2me | Definitions.Def_QubitPhaseEst_IsSeed
-- name    : QubitPhaseEst_IsSeed
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:18:20.056502+00:00
-- url     : https://prove2.me/theorems/5dac9c20-4e06-42ed-bd54-7295e32095fd
-- title:
--   Seed $\xi$ of a covariant phase POVM: $\xi\ge0$ and $\int_0^{2\pi}U_\phi\xi U_\phi^\dagger\,\frac{d\phi}{2\pi}=I$
-- statement:
--   A **covariant phase measurement** on $N$ qubits is a POVM of the form
--
--   $$
--   P(d\phi')=U_{\phi'}\,\xi\,U_{\phi'}^\dagger\,\frac{d\phi'}{2\pi},\qquad \phi'\in[0,2\pi),
--   $$
--
--   determined by one operator $\xi$, its **seed**. A $2^N\times2^N$ matrix $\xi$ is a seed when
--
--   1. $\xi$ is positive semidefinite, so that $P(d\phi)\ge0$, and
--   2. the POVM is normalized: $\displaystyle\int_0^{2\pi}U_\phi\,\xi\,U_\phi^\dagger\,\frac{d\phi}{2\pi}=I$.
--
--   These are the constraints (2) for the POVM (4). The estimation problem of the mission is to choose the best seed.
--
--   **Formalization Note** The integral of a matrix-valued function is taken entry by entry (complex interval integrals), since matrices carry no default norm. Every integrand is a trigonometric polynomial in $\phi$, so the integrals are genuine. The normalization is stated through the integral, not through the entries of $\xi$; their equivalence is a milestone.
-- source:
--   D'Ariano, Macchiavello, Perinotti, Optimal phase estimation for qubit mixed states, arXiv:quant-ph/0411133v3, Sec. II, Eqs. (2) and (4), p. 2

import Mathlib
import Definitions.Def_QubitPhaseEst_phaseShift

open scoped Matrix ComplexOrder

namespace QubitPhaseEst

/-- **Seed of a covariant phase POVM.** arXiv:quant-ph/0411133v3, Sec. II, Eqs. (2), (4), p. 2: the
covariant POVM `P(dφ′) = U_φ′ ξ U_φ′† dφ′/2π` has seed `ξ ≥ 0`, and the normalization of (2) is
`∫_0^{2π} U_φ ξ U_φ† dφ/2π = I`.

**Formalization Note.** The positivity `P(dφ) ≥ 0` of (2) is the positivity `ξ ≥ 0` of the seed.
Matrices have no default norm in Mathlib, so the normalization is stated entrywise with complex
interval integrals; every integrand is continuous in `φ`, so no junk value of the integral occurs.
The normalization is deliberately stated by the integral, not by the matrix entries of `ξ`: that
characterization is the theorem `QubitPhaseEst.isSeed_iff`. -/
def IsSeed {N : ℕ} (ξ : Matrix (Qb N) (Qb N) ℂ) : Prop :=
  ξ.PosSemidef ∧ ∀ x y : Qb N,
    (1 / (2 * (Real.pi : ℂ))) *
        ∫ φ in (0 : ℝ)..(2 * Real.pi), (phaseShift N φ * ξ * (phaseShift N φ)ᴴ) x y =
      (1 : Matrix (Qb N) (Qb N) ℂ) x y

end QubitPhaseEst


