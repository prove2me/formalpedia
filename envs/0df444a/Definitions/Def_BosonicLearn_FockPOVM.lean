-- Prove2me | Definitions.Def_BosonicLearn_FockPOVM
-- name    : BosonicLearn_FockPOVM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:15:30.519192+00:00
-- url     : https://prove2.me/theorems/c232480f-7244-4d06-9fa2-42d488b94b7f
-- title:
--   POVM with a measurable outcome space and its Born law
-- statement:
--   Let $I$ be a countable index set (an orthonormal basis of $\ell^2(I)$) and $\mathcal O$ a measurable space. A **POVM** on $\ell^2(I)$ with outcomes in $\mathcal O$ assigns to each measurable $B\subseteq\mathcal O$ an operator $E(B)$ such that
--
--   1. $0\le\langle z,E(B)z\rangle\le\langle z,z\rangle$ for every finitely supported vector $z$;
--   2. $E(\mathcal O)=I$;
--   3. for every density operator $\rho$, the map $B\mapsto \operatorname{Tr}(E(B)\rho)$ is a probability measure, the **Born law** $\mathbb P_\rho$ of the outcome.
--
--   The paper allows arbitrary POVMs, including non-Gaussian ones and ones with continuous outcomes such as heterodyne detection.
--
--   **Formalization Note** The Born law is carried as data with the identity $\mathbb P_\rho(B)=\operatorname{Re}\sum_i\sum_j E(B)_{ij}\rho_{ji}$ on measurable sets; countable additivity for every density gives weak σ-additivity of $E$, so this is the usual notion. Values on arrays that are not densities are unconstrained.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §1.1, p. 5; §5.4, pp. 34–35

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)

open MeasureTheory

namespace BosonicLearn

/-- **A POVM with a measurable outcome space, on a countable-basis Hilbert space.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §1.1, p. 5: "All of our theorems stated in Sec. 1.2 hold for general POVM measurements on n-mode
bosonic systems, which are allowed to be non-Gaussian"; outcomes may be continuous (heterodyne, p. 5;
`∫ dz_t |ϕ⟩⟨ϕ| = P_k`, §5.4, pp. 34–35).

A `FockPOVM I O` on `ℓ²(I)` with outcomes in the measurable space `O` consists of
1. effects `E(B)` (coefficient arrays) for measurable `B ⊆ O`, with `0 ≤ ⟨z, E(B) z⟩ ≤ ⟨z, z⟩` (real) for
   every finitely supported vector `z`, so each `E(B)` is a bounded operator between `0` and `I`;
2. `E(O) = I`;
3. the **Born law** `law ρ`, a measure on `O`, which for every density operator `ρ` is a probability measure
   with `law ρ (B) = Re Tr(E(B) ρ)` on measurable `B`.

Because `law ρ` is countably additive for every density `ρ` (in particular every rank-one `|z⟩⟨z|`), the
effects are weakly σ-additive: this is the usual definition of a POVM.

**Formalization Note.** The Born law is carried as data together with the identity tying it to the
effects; this avoids constructing a measure inside a definition and adds no condition. `Tr(E ρ)` is the
iterated series `∑ᵢ ∑ⱼ E_ij ρ_ji`, which converges absolutely for bounded `E` and trace-class `ρ`. Arrays
that are not densities are unconstrained. -/
structure FockPOVM (I O : Type) [DecidableEq I] [MeasurableSpace O] where
  /-- the effect `E(B)` of a measurable set of outcomes -/
  effect : Set O → Matrix I I ℂ
  /-- `0 ≤ ⟨z, E(B) z⟩ ≤ ⟨z, z⟩` for finitely supported `z` -/
  effect_form : ∀ B : Set O, MeasurableSet B → ∀ (s : Finset I) (z : I → ℂ),
    (∑ i ∈ s, ∑ j ∈ s, star (z i) * effect B i j * z j).im = 0 ∧
    0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * effect B i j * z j).re ∧
    (∑ i ∈ s, ∑ j ∈ s, star (z i) * effect B i j * z j).re ≤ ∑ i ∈ s, ‖z i‖ ^ 2
  /-- normalization `E(O) = I` -/
  effect_univ : effect Set.univ = 1
  /-- the outcome law of the measurement on the state `ρ` -/
  law : Matrix I I ℂ → Measure O
  /-- on densities the outcome law is a probability measure -/
  law_prob : ∀ ρ : Matrix I I ℂ, IsDensity ρ → IsProbabilityMeasure (law ρ)
  /-- Born rule `law ρ B = Tr(E(B) ρ)` -/
  law_born : ∀ ρ : Matrix I I ℂ, IsDensity ρ → ∀ B : Set O, MeasurableSet B →
    law ρ B = ENNReal.ofReal (∑' i, ∑' j, effect B i j * ρ j i).re

end BosonicLearn


