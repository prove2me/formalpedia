-- Prove2me | Definitions.Def_JencovaRenyi_IsPositiveTP
-- name    : JencovaRenyi_IsPositiveTP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:40:38.690369+00:00
-- url     : https://prove2.me/theorems/683d51f6-024d-4ed0-ab67-5b0621c86f62
-- title:
--   Positive linear trace-preserving map $\Phi : L_1(\mathcal M)\to L_1(\mathcal N)$
-- statement:
--   A complex-linear map $\Phi : \mathcal M_*\simeq L_1(\mathcal M) \to \mathcal N_*\simeq L_1(\mathcal N)$ is **positive and trace preserving** if it maps positive normal functionals to positive normal functionals and
--   $$
--   \operatorname{Tr}\Phi(h) = \operatorname{Tr} h, \qquad\text{i.e.}\qquad (\Phi\psi)(1) = \psi(1)\quad(\psi\in\mathcal M_*).
--   $$
--   Such a map sends normal states to normal states; its adjoint $\Phi^* : \mathcal N\to\mathcal M$ is normal, positive and unital. This is the class of maps for which the paper proves the data processing inequality.
--
--   **Formalization Note** No complete positivity, 2-positivity or continuity is assumed.
-- source:
--   Jenčová, Rényi relative entropies and noncommutative $L_p$-spaces, arXiv:1609.08462v4, §3.3, p.16

import Mathlib
import Definitions.Def_JencovaRenyi_Predual

namespace JencovaRenyi

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A positive linear trace-preserving map `Φ : L_1(M) → L_1(N)` (Jenčová, arXiv:1609.08462v4,
§3.3, p.16): `Φ` maps positive normal functionals to positive normal functionals, and
`Tr Φ(h) = Tr h`, i.e. `(Φψ)(1) = ψ(1)`.

**Formalization Note.** `Φ` is a complex-linear map between the preduals `M_* ≃ L_1(M)` and
`N_* ≃ L_1(N)`; no complete positivity, 2-positivity or continuity is assumed (a positive map
between preduals is automatically bounded). -/
def IsPositiveTP {A : StarSubalgebra ℂ (H →L[ℂ] H)} {B : StarSubalgebra ℂ (K →L[ℂ] K)}
    (Φ : Predual A →ₗ[ℂ] Predual B) : Prop :=
  (∀ k : Predual A, IsPositive k → IsPositive (Φ k)) ∧
    ∀ k : Predual A, (Φ k : B →L[ℂ] ℂ) 1 = (k : A →L[ℂ] ℂ) 1

end JencovaRenyi


