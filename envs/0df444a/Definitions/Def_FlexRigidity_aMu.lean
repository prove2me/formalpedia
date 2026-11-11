-- Prove2me | Definitions.Def_FlexRigidity_aMu
-- name    : FlexRigidity_aMu
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:16:25.480411+00:00
-- url     : https://prove2.me/theorems/e794a104-1f07-4f03-9cf6-60008e8c6073
-- title:
--   The constant $a_\mu=1-\mu+\mu/|S|$
-- statement:
--   $a_\mu=1-\mu+\mu/|S|$, the eigenvalue of $(1-\mu)|\phi\rangle\langle\phi|+\mu I/|S|$ on $|\phi\rangle$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Lemma 4.5, p. 35; (53), p. 47

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

/-- **The constant `a_µ = 1 − µ + µ/|S|`** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, Lemma 4.5, p. 35, and (53), p. 47): the eigenvalue of
the depolarized pure state `(1−µ)|ϕ⟩⟨ϕ| + µ I/|S|` on `|ϕ⟩`; `s` is the dimension `|S|`. -/
def aMu (μ s : ℝ) : ℝ :=
  1 - μ + μ / s

end FlexRigidity


