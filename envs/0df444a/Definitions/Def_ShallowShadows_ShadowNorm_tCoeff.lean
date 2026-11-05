-- Prove2me | Definitions.Def_ShallowShadows_ShadowNorm_tCoeff
-- name    : ShallowShadows_ShadowNorm_tCoeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:05.092212+00:00
-- url     : https://prove2.me/theorems/f6e96b5b-0859-41c3-8df6-a14427654261
-- title:
--   $t_{\lambda} = \Pr_{U\sim\mathcal U}(UP^\lambda U^\dagger \in \pm\mathcal Z)$ (Eq. (5))
-- statement:
--   For a finite ensemble $\mathcal U$ and $\lambda \in \{0,1\}^{2n}$,
--
--   $$
--   t_{\lambda} := \Pr_{U\sim\mathcal U}\big(UP^\lambda U^\dagger \in \pm\mathcal Z\big).
--   $$
--
--   For $\mathcal U = \mathcal U_d$ this is $t_{\lambda,d}$, the eigenvalue of the measurement channel $\mathcal M_d$ on $P^\lambda$ (Lemma 1).
--
--   **Formalization Note** $t$ is defined as this probability, never as the eigenvalue or as a second moment; those identities are milestones.
-- source:
--   Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, Shallow shadows: Expectation estimation using low-depth random Clifford circuits, arXiv:2209.12924v3, Lemma 1, Eq. (5), p. 4

import Mathlib
import Definitions.Def_ShallowShadows_ShadowNorm_prob
import Definitions.Def_ShallowShadows_ShadowNorm_InPmZ

open ClassicalShadow.Linear

namespace ShallowShadows.ShadowNorm

/-- Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, *Shallow shadows: Expectation
estimation using low-depth random Clifford circuits*, arXiv:2209.12924v3, Lemma 1, Eq. (5), p. 4:
`t_{λ} := Pr_{U∼𝒰}(U P^λ U† ∈ ±𝒵)`, for any finite ensemble `𝒰` (the paper takes `𝒰 = 𝒰_d`).

**Formalization Note.** `t` is defined as this probability, not as the second moment
`E[⟨0|U P^λ U†|0⟩²]` or as the eigenvalue of `M_d`; both identities are milestones. -/
noncomputable def tCoeff {n : ℕ} {ι : Type} [Fintype ι] (E : Primitive n ι)
    (lam : Bits n × Bits n) : ℝ :=
  prob E (fun U => InPmZ ((U : Op n) * pauli lam * star (U : Op n)))

end ShallowShadows.ShadowNorm


