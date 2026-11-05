-- Prove2me | Definitions.Def_ShallowShadows_ShadowNorm_tauCoeff
-- name    : ShallowShadows_ShadowNorm_tauCoeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:32:48.129889+00:00
-- url     : https://prove2.me/theorems/cb342e17-1ba7-461d-abc6-d3d2fc5723c5
-- title:
--   $\tau_{(\lambda,\lambda')} = \Pr_{U\sim\mathcal U}(UP^\lambda U^\dagger, UP^{\lambda'}U^\dagger \in \pm\mathcal Z)$ (Eq. (19))
-- statement:
--   For a finite ensemble $\mathcal U$ and $\lambda, \lambda' \in \{0,1\}^{2n}$,
--
--   $$
--   \tau_{(\lambda,\lambda')} := \Pr_{U\sim\mathcal U}\big(UP^\lambda U^\dagger \in \pm\mathcal Z \text{ and } UP^{\lambda'} U^\dagger \in \pm\mathcal Z\big),
--   $$
--
--   the probability that $U$ maps both Pauli strings to tensor products of $\mathbb I$ and $Z$ up to a sign. For $\mathcal U = \mathcal U_d$ this is $\tau_{(\lambda,\lambda'),d}$.
--
--   **Formalization Note** Defined as this probability, not as the third moment of Eq. (F6), which is a milestone.
-- source:
--   Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, Shallow shadows: Expectation estimation using low-depth random Clifford circuits, arXiv:2209.12924v3, Eq. (19), p. 7

import Mathlib
import Definitions.Def_ShallowShadows_ShadowNorm_prob
import Definitions.Def_ShallowShadows_ShadowNorm_InPmZ

open ClassicalShadow.Linear

namespace ShallowShadows.ShadowNorm

/-- Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, *Shallow shadows: Expectation
estimation using low-depth random Clifford circuits*, arXiv:2209.12924v3, Eq. (19), p. 7:
`τ_{(λ,λ')} := Pr_{U∼𝒰}(U P^λ U†, U P^λ' U† ∈ ±𝒵)`, "the probability that `U` sampled from the
ensemble … will map both Paulis `P^λ` and `P^λ'` to a tensor product of `𝕀` and `Z` operators up to
a factor `±1`", for any finite ensemble `𝒰` (the paper takes `𝒰 = 𝒰_d`).

**Formalization Note.** `τ` is defined as this probability, not as the third moment of Eq. (F6),
which is a milestone. -/
noncomputable def tauCoeff {n : ℕ} {ι : Type} [Fintype ι] (E : Primitive n ι)
    (lam lam' : Bits n × Bits n) : ℝ :=
  prob E (fun U => InPmZ ((U : Op n) * pauli lam * star (U : Op n)) ∧
    InPmZ ((U : Op n) * pauli lam' * star (U : Op n)))

end ShallowShadows.ShadowNorm


