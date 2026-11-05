-- Prove2me | Definitions.Def_ShallowShadows_ShadowNorm_globalClifford
-- name    : ShallowShadows_ShadowNorm_globalClifford
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:34:24.786958+00:00
-- url     : https://prove2.me/theorems/357ebf06-ff0d-41d8-a999-77d7f6fe365b
-- title:
--   The global Clifford ensemble $\mathcal U_\infty$
-- statement:
--   The ensemble $\mathcal U_\infty$ draws a uniformly random $n$-qubit Clifford unitary. It is the $d = \infty$ member of the family $\mathcal U_d$ and the second scheme of Huang, Kueng and Preskill.
--
--   **Formalization Note** Uniform over $n$-qubit Cliffords modulo global phase, with the representative unitary of each class.
-- source:
--   Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, Shallow shadows: Expectation estimation using low-depth random Clifford circuits, arXiv:2209.12924v3, §III, p. 3; §V, p. 4

import Mathlib
import Definitions.Def_ShallowShadows_ShadowNorm_CliffordLabel
import Definitions.Def_ShallowShadows_ShadowNorm_uniformDist

open ClassicalShadow.Linear

namespace ShallowShadows.ShadowNorm

/-- Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, *Shallow shadows: Expectation
estimation using low-depth random Clifford circuits*, arXiv:2209.12924v3, §III, p. 3 and §V,
p. 4: the ensemble `𝒰_∞ = (𝕌_∞, μ_∞)`, where "`𝕌_∞` consists of all `n`-qubit Clifford unitaries"
and `μ_∞` is "the uniform distribution over" it; it is the `d = ∞` member of the family `𝒰_d`.

**Formalization Note.** Uniform over Cliffords means uniform over Cliffords modulo global phase
(`CliffordLabel n`, finiteness as an instance argument); the unitary of a label is its
representative. The ensemble is a reused HKP measurement primitive, so `M_∞` is
`ClassicalShadow.Linear.measChannel (globalClifford n)`. -/
noncomputable def globalClifford (n : ℕ) [Fintype (CliffordLabel n)] :
    Primitive n (CliffordLabel n) where
  w := uniformDist _
  U c := c.rep

end ShallowShadows.ShadowNorm


