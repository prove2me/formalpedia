-- Prove2me | Definitions.Def_TwoWayCVQKD_gaussEntropy
-- name    : TwoWayCVQKD_gaussEntropy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:08.873636+00:00
-- url     : https://prove2.me/theorems/416b7776-2db3-4d95-8416-03fee62f2402
-- title:
--   Von Neumann entropy of a Gaussian state from its covariance matrix
-- statement:
--   A Gaussian state of $n$ modes with covariance matrix $\mathbf V$ and symplectic eigenvalues $\nu_1,\dots,\nu_n$ has the von Neumann entropy
--   $$
--   S(\rho)=\sum_{k=1}^n g(\nu_k),\qquad g(\nu)=\frac{\nu+1}{2}\log\frac{\nu+1}{2}-\frac{\nu-1}{2}\log\frac{\nu-1}{2}.
--   $$
--   The sum runs over the spectrum with multiplicity: for instance $W$ occurs twice in Eq. (57). All entropies of the paper are computed by this formula.
--
--   **Formalization Note** Logarithms are natural. The published `sympSpec` takes moduli of the eigenvalues of $\sigma\mathbf V$ and lists each symplectic eigenvalue once, and `symplecticEntropy` is the function $g$. That Eq. (2) gives the entropy of the actual density operator is the result [35] cited by the paper; it is not formalized here.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, Eqs. (2)–(3), p.6

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P49
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P19
import Definitions.Def_GaussianGLOCC_sympSpec
open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov)
open QAlgorithms.Papers.Independent.Information100.P49 (symplecticEntropy)
open GaussianGLOCC (sympSpec)

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, Eq. (2), p.6: the entropy
`S(ρ) = ∑ₖ g(νₖ)` of a Gaussian state with covariance matrix `V`, a sum over the symplectic
eigenvalues with multiplicity.

**Formalization Note** `sympSpec` is the published ordered symplectic spectrum (each symplectic
eigenvalue listed once per mode), and `symplecticEntropy` is the published function
`g(ν) = ((ν+1)/2) log((ν+1)/2) - ((ν-1)/2) log((ν-1)/2)` of Eq. (3), with `g(1) = 0`, in nats.
That Eq. (2) is the von Neumann entropy of the Gaussian density operator is the paper's cited
result [35]; this mission works at the covariance-matrix level, as the paper does. -/
noncomputable def gaussEntropy {n : ℕ} (V : Cov n) : ℝ :=
  ∑ k, symplecticEntropy (sympSpec V k)

end TwoWayCVQKD


