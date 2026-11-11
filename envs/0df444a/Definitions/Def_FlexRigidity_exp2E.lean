-- Prove2me | Definitions.Def_FlexRigidity_exp2E
-- name    : FlexRigidity_exp2E
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:57.640203+00:00
-- url     : https://prove2.me/theorems/4709b863-3936-4b33-86b5-a4a97d7ee23d
-- title:
--   $2^x$ on the extended reals
-- statement:
--   $2^{+\infty}=+\infty$, $2^{-\infty}=0$, and $2^x$ for real $x$. It expresses $2^{(\alpha-1)D_\alpha}$ in Lemma 4.3.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Lemma 4.3, p. 30

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

/-- **`2^x` on the extended reals**: `2^{+∞} = +∞`, `2^{−∞} = 0`, and `2^x` for real `x`
(Arqand–Kundu–Tan, *Flexible rigidity*, arXiv:2610.00444, artifact sha256 8c67699d…, Lemma 4.3,
p. 30, where `2^{(α−1) D_α}` appears). -/
def exp2E (x : EReal) : ℝ≥0∞ :=
  if x = ⊤ then ⊤ else if x = ⊥ then 0 else ENNReal.ofReal ((2 : ℝ) ^ x.toReal)

end FlexRigidity


