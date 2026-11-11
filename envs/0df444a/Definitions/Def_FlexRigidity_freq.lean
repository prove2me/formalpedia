-- Prove2me | Definitions.Def_FlexRigidity_freq
-- name    : FlexRigidity_freq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:15:04.20399+00:00
-- url     : https://prove2.me/theorems/c8407244-3855-417b-84a8-44b72dabb022
-- title:
--   Frequency distribution $\mathrm{freq}_z$
-- statement:
--   For a string $z=(z_1,\dots,z_n)\in\mathcal Z^n$, $\mathrm{freq}_z(y)=|\{i:z_i=y\}|/n$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Definition 2.1, p. 17

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

/-- **Frequency distribution** (Arqand–Kundu–Tan, *Flexible rigidity*, arXiv:2610.00444, artifact
sha256 8c67699d…, Definition 2.1, p. 17): for `z = (z_1, …, z_n) ∈ Z^n`,
`freq_z(y) = |{i : z_i = y}|/n`. -/
def freq {Z : Type} [DecidableEq Z] {n : ℕ} (z : Fin n → Z) : Z → ℝ :=
  fun y => ((Finset.univ.filter fun i => z i = y).card : ℝ) / n

end FlexRigidity


