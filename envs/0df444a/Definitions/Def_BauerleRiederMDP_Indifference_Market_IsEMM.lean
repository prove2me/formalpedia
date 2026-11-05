-- Prove2me | Definitions.Def_BauerleRiederMDP_Indifference_Market_IsEMM
-- name    : BauerleRiederMDP_Indifference_Market_IsEMM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:27:56.769016+00:00
-- url     : https://prove2.me/theorems/943e79bf-5f88-4426-acad-759b0173aa6c
-- title:
--   Equivalent martingale measures of the one-period market
-- statement:
--   A measure $Q'$ on $\Omega$ is an equivalent martingale measure of the one-period market if it is a probability measure with the same null sets as $\mathbb P$ and satisfies condition (i) of Remark 4.9.3,
--   $$
--   \mathbb E_{Q'}S_1=S_0,
--   $$
--   where $S_0=s$ and $S_1=s\tilde R$. These are the measures among which $\mathbb Q$ minimizes the entropy.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Remark 4.9.3, p.137; Definition C.1.1, p.365

import Mathlib
import Definitions.Def_BauerleRiederMDP_Indifference_Market

open MeasureTheory

namespace BauerleRiederMDP.Indifference

namespace Market

/-- `Q'` is an equivalent martingale measure of the one-period market (Bäuerle & Rieder, Markov
Decision Processes with Applications to Finance (2011), Remark 4.9.3, p.137, PDF 151): a probability
measure on `Ω`, `ℙ`-equivalent, with condition (i) `𝔼_{Q'} S₁ = S₀`, where `S₀ = s` and
`S₁ = s R̃`.

**Formalization Note.** Equivalence is mutual absolute continuity (the same null sets, Definition
C.1.1 a)). -/
def IsEMM (M : Market) (Q' : Measure (Fin 4)) : Prop :=
  IsProbabilityMeasure Q' ∧ Q' ≪ M.P ∧ M.P ≪ Q' ∧ ∀ s : ℝ, ∫ ω, s * M.Rt ω ∂Q' = s

end Market

end BauerleRiederMDP.Indifference


