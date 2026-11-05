-- Prove2me | Definitions.Def_ShallowShadows_ShadowNorm_oTilde
-- name    : ShallowShadows_ShadowNorm_oTilde
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:34:01.840977+00:00
-- url     : https://prove2.me/theorems/e90d674e-d468-4be7-b1e8-a9dc8850edf9
-- title:
--   $\tilde O = \sum_{\lambda'\ne\lambda} P^\lambda P^{\lambda'} \beta_\lambda\beta_{\lambda'} \tau_{(\lambda,\lambda')}/(t_\lambda t_{\lambda'})$ (Eq. (21))
-- statement:
--   For a finite ensemble $\mathcal U$ and an operator $O = \sum_\lambda \beta_\lambda P^\lambda$,
--
--   $$
--   \tilde O = \sum_{\substack{\lambda',\lambda\in\{0,1\}^{2n}\\ \lambda'\neq\lambda}} P^\lambda P^{\lambda'}\,\beta_\lambda\beta_{\lambda'}\,\frac{\tau_{(\lambda,\lambda')}}{t_\lambda t_{\lambda'}}.
--   $$
--
--   It is the state dependent, off-diagonal part of the shadow norm in Theorem 7.
--
--   **Formalization Note** Lean's division by zero returns $0$; for the paper's ensembles every $t_\lambda$ is positive (Eq. (11), a milestone).
-- source:
--   Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, Shallow shadows: Expectation estimation using low-depth random Clifford circuits, arXiv:2209.12924v3, Theorem 7, Eq. (21), p. 7

import Mathlib
import Definitions.Def_ShallowShadows_ShadowNorm_tCoeff
import Definitions.Def_ShallowShadows_ShadowNorm_tauCoeff
import Definitions.Def_ShallowShadows_ShadowNorm_coeff

open ClassicalShadow.Linear

namespace ShallowShadows.ShadowNorm

/-- Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, *Shallow shadows: Expectation
estimation using low-depth random Clifford circuits*, arXiv:2209.12924v3, Theorem 7, Eq. (21),
p. 7: `Õ = Σ_{λ',λ ∈ {0,1}^{2n}, λ' ≠ λ} P^λ P^λ' β_λ β_λ' τ_{(λ,λ')} / (t_λ t_λ')`, for a finite
ensemble `𝒰` (the paper takes `𝒰 = 𝒰_d`), with `β` the Pauli coefficients of `O`.

**Formalization Note.** Lean's `x / 0 = 0`; for the paper's ensembles every `t_λ` is positive
(Eq. (11), a milestone), so no division by zero occurs there. -/
noncomputable def oTilde {n : ℕ} {ι : Type} [Fintype ι] (E : Primitive n ι) (O : Op n) : Op n :=
  ∑ lam, ∑ lam' ∈ Finset.univ.erase lam,
    (coeff O lam * coeff O lam' * (tauCoeff E lam lam' : ℂ) /
      ((tCoeff E lam : ℂ) * (tCoeff E lam' : ℂ))) • (pauli lam * pauli lam')

end ShallowShadows.ShadowNorm


