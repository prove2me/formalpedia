-- Prove2me | Definitions.Def_PrivLittlestone_coinMeasure
-- name    : PrivLittlestone_coinMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:31:16.461194+00:00
-- url     : https://prove2.me/theorems/55f14802-1a96-4ee5-88c6-a239913c3826
-- title:
--   Law of the coins of Algorithm 1
-- statement:
--   All coins of Algorithm 1 are independent: the $Km$ sampling coins are uniform on $[0,1]$, the $K$ threshold noises are $\xi_j \sim \mathrm{Lap}(2/\varepsilon_a)$ and the $T$ query noises are $\nu_t \sim \mathrm{Lap}(4/\varepsilon_a)$, where $\mathrm{Lap}(s)$ has density $e^{-|x|/s}/(2s)$.
--
--   **Formalization Note** $\mathrm{Lap}(s)$ is the published `PrivLearn.Generic.laplace s`.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Algorithm 1, lines 6, 8, 15, p.7

import Mathlib
import Definitions.Def_PrivLittlestone_Alg1Coins
import Definitions.Def_PrivLearn_Generic_Privacy

namespace PrivLittlestone

open MeasureTheory

instance laplace_sigmaFinite (s : ℝ) : SigmaFinite (PrivLearn.Generic.laplace s) := by
  unfold PrivLearn.Generic.laplace; infer_instance

/-- The **law of the coins of Algorithm 1** (He–He, *Private Online Learning of Littlestone
Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), Algorithm 1,
lines 6, 8, 15, p.7): all coordinates independent; the `K·m` sampling coins uniform on `[0,1]`,
the `K` threshold noises `ξ_j ∼ Lap(2/ε_a)`, the `T` query noises `ν_t ∼ Lap(4/ε_a)`.

**Formalization Note** `Lap(s)` is the published `PrivLearn.Generic.laplace s`, with density
`e^{−|x|/s}/(2s)`. -/
noncomputable def coinMeasure {X Z U : Type*} {D : ℕ} {B : ℝ} (P : Alg1Spec X Z U D B) :
    Measure (Alg1Coins P) :=
  (Measure.pi fun _ : Fin P.K => Measure.pi fun _ : Fin P.m =>
      (volume : Measure ℝ).restrict (Set.Icc 0 1)).prod
    ((Measure.pi fun _ : Fin P.K => PrivLearn.Generic.laplace (2 / P.εa)).prod
      (Measure.pi fun _ : Fin P.T => PrivLearn.Generic.laplace (4 / P.εa)))

end PrivLittlestone


