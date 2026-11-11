-- Prove2me | Definitions.Def_FlexRigidity_SAcc
-- name    : FlexRigidity_SAcc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:20:29.031864+00:00
-- url     : https://prove2.me/theorems/31861e11-4141-4335-bcfa-719f8c14c362
-- title:
--   The accepting set $S_{\mathrm{Acc}_{\varepsilon_{\mathrm{tol}}}}$, eq. (42)
-- statement:
--   $S_{\mathrm{Acc}_{\varepsilon_{\mathrm{tol}}}}=\{Q_C:\|Q_C-P_C\|_{\mathrm{tr}}\le\varepsilon_{\mathrm{tol}}\}$, $Q_C$ ranging over distributions on $C=\{\mathrm{gen},0,1\}$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), eq. (42), p. 40

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_PC
import Definitions.Def_HybridXorLift_tvDist
import Definitions.Def_FlexRigidity_IsDistribution
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **The accepting set `S_{Acc_εtol}`, eq. (42)** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, p. 40):
`S_{Acc_εtol} = {Q_C : ‖Q_C − P_C‖_tr ≤ εtol}`, `Q_C` ranging over distributions on
`C = {gen, 0, 1}`; `ω` is `ω*`. -/
def SAcc (γ ω ε : ℝ) : Set (Option Bool → ℝ) :=
  {Q | IsDistribution Q ∧ HybridXorLift.tvDist Q (PC γ ω) ≤ ε}

end FlexRigidity


