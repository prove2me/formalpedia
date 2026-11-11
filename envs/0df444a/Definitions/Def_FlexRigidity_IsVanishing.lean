-- Prove2me | Definitions.Def_FlexRigidity_IsVanishing
-- name    : FlexRigidity_IsVanishing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:57.56007+00:00
-- url     : https://prove2.me/theorems/4efa95fd-12da-426f-ad90-ff77a93ae0c0
-- title:
--   Vanishing functions
-- statement:
--   A function $v:[0,a]\to\mathbb R$ is **vanishing** if it is nonnegative and nondecreasing, $v(0)=0$, and $\lim_{\delta\to0^+}v(\delta)=0$.
--
--   **Formalization Note** $v$ is a function on $\mathbb R$; only its values on $[0,a]$ are constrained, and the limit is taken within $(0,a]$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Definition 2.2, p. 17

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Vanishing function** (Arqand–Kundu–Tan, *Flexible rigidity*, arXiv:2610.00444, artifact
sha256 8c67699d…, Definition 2.2, p. 17): a nonnegative, nondecreasing `v : [0, a] → ℝ` with
`v(0) = 0` and `lim_{δ→0⁺} v(δ) = 0`.

**Formalization Note** `v` is a function on `ℝ`; only its values on `[0, a]` are constrained, and
the limit is taken within `(0, a]`, so for `a = 0` it is vacuous, as in the paper. -/
def IsVanishing (v : ℝ → ℝ) (a : ℝ) : Prop :=
  (∀ δ ∈ Set.Icc 0 a, 0 ≤ v δ) ∧ MonotoneOn v (Set.Icc 0 a) ∧ v 0 = 0 ∧
    Tendsto v (𝓝[Set.Ioc 0 a] 0) (𝓝 0)

end FlexRigidity


