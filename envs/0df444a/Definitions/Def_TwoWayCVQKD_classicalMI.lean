-- Prove2me | Definitions.Def_TwoWayCVQKD_classicalMI
-- name    : TwoWayCVQKD_classicalMI
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:45:36.924607+00:00
-- url     : https://prove2.me/theorems/e02b7e4c-8892-4d34-8484-9024d56da7d6
-- title:
--   Shannon mutual information $I(X_A:X_B)$ of Gaussian variables
-- statement:
--   The classical mutual information between Alice's and Bob's jointly Gaussian variables is
--   $$
--   I(X_A:X_B)=H(X_B)-H(X_B|X_A)=\tfrac12\log V(X_B)-\tfrac12\log V(X_B|X_A).
--   $$
--   Here $V(X_B)$ is the variance of $X_B$ when $X_B$ is a single real variable, and $V(X_B)=V(Q_B)V(P_B)$ when $X_B=\{Q_B,P_B\}$, and likewise for $V(X_B|X_A)$.
--
--   **Formalization Note** For a two-component variable the determinant of the covariance matrix is used; it equals the product above because $Q_B$ and $P_B$ are uncorrelated in the protocols of this mission. Logarithms are natural.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, below Eq. (7), p.6, and p.9 (above Eq. (73))

import Mathlib
import Definitions.Def_TwoWayCVQKD_crossCov
import Definitions.Def_TwoWayCVQKD_condCov

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, below Eq. (7), p.6, and p.9:
`I(X_A : X_B) := H(X_B) - H(X_B|X_A)` with `H(X_B) = (1/2) log V(X_B)` and
`H(X_B|X_A) = (1/2) log V(X_B|X_A)`.

**Formalization Note** For a two-component variable `V(X_B)` is the determinant of its covariance
matrix, which is `V(Q_B) V(P_B)` of p.9 because `Q_B` and `P_B` are uncorrelated in every protocol
here. Logarithms are natural; the additive constant of a differential entropy cancels. -/
noncomputable def classicalMI {S ι κ : Type*} [Fintype S] [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] (Sg : Matrix S S ℝ) (xA : κ → S → ℝ) (xB : ι → S → ℝ) : ℝ :=
  (1 / 2) * (Real.log (crossCov Sg xB xB).det - Real.log (condCov Sg xB xA).det)

end TwoWayCVQKD


