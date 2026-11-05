-- Prove2me | Definitions.Def_ShallowShadows_ShadowNorm_IsCliffordPrimitive
-- name    : ShallowShadows_ShadowNorm_IsCliffordPrimitive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:26.912753+00:00
-- url     : https://prove2.me/theorems/66a85bed-a56d-4c4b-90ea-ffdd1de82a38
-- title:
--   Ensemble of Clifford unitaries
-- statement:
--   A finite ensemble $\mathcal U = (\mathbb U, \mu)$ of unitaries is an **ensemble of Clifford gates** when every unitary drawn with positive probability is Clifford, $\mathbb U \subseteq \mathcal C_n$.
-- source:
--   Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, Shallow shadows: Expectation estimation using low-depth random Clifford circuits, arXiv:2209.12924v3, §III, p. 3

import Mathlib
import Definitions.Def_ShallowShadows_ShadowNorm_IsClifford

open ClassicalShadow.Linear

namespace ShallowShadows.ShadowNorm

/-- Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, *Shallow shadows: Expectation
estimation using low-depth random Clifford circuits*, arXiv:2209.12924v3, §III, p. 3: "a unitary
`U` is independently chosen from a subset `𝕌 ⊆ 𝒞_n` of Clifford unitaries with probability
`μ(U)`. This defines an ensemble of `n`-qubits Clifford gates `𝒰 = (𝕌, μ)`." A finite ensemble is
a Clifford ensemble when every unitary drawn with positive probability is Clifford. -/
def IsCliffordPrimitive {n : ℕ} {ι : Type} [Fintype ι] (E : Primitive n ι) : Prop :=
  ∀ i, 0 < E.w.prob i → IsClifford (E.U i)

end ShallowShadows.ShadowNorm


