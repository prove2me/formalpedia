-- Prove2me | Definitions.Def_FlexRigidity_diSeqData
-- name    : FlexRigidity_diSeqData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:32:26.22855+00:00
-- url     : https://prove2.me/theorems/eee2d5b3-465b-42b9-92ae-c287c5908fe3
-- title:
--   The §5.3 channel pairs (48)–(52)
-- statement:
--   The sequential data of Postulate Set 4.1 for the DI protocol: records $C=\{\mathrm{gen},0,1\}$, $O_i=U_iX_iY_iA_iB_i$, $M_i=M^{\mathrm A}_iM^{\mathrm B}_i$, $Z_i=U_iX_iC_i$, $S_i=A_iS^{\mathrm A}_iS^{\mathrm B}_i$, $J_i$; $\mathcal G_i$ of (48), $\mathcal T_i$ of (49), and the controlled replacer $\mathcal P_i$ of (51), which is the identity on test triples and replaces $S_i$ by $\omega^{\mu,x}_{S_i}=(1-\mu)\omega^x_{S_i}+\mu I/|S_i|$ on generation triples. Then $\mathcal E_i=\mathcal T_i\circ\mathcal G_i$ and $\mathcal F^\mu_i=\mathcal T_i\circ\mathcal P_i\circ\mathcal G_i$ (52).
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), §5.3, eqs. (48)–(52), pp. 45–47

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_roundG
import Definitions.Def_FlexRigidity_roundT
import Definitions.Def_FlexRigidity_omegaX
import Definitions.Def_FlexRigidity_depol
import Definitions.Def_FlexRigidity_SeqData
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **The §5.3 channel pairs** (Arqand–Kundu–Tan, *Flexible rigidity*, arXiv:2610.00444, artifact
sha256 8c67699d…, §5.3, eqs. (48)–(52), pp. 45–47): the sequential data of Postulate Set 4.1 with
records `C = {gen, 0, 1}`, `O_i = U_i X_i Y_i A_i B_i`, `M_i = M^A_i M^B_i`, `Z_i = U_i X_i C_i`,
`S_i = A_i S^A_i S^B_i`, `J_i` as in `RoundJ`, `G_i` of (48), `T_i` of (49), and the controlled
replacer `P_i` of (51): the identity on test triples (`Z* = {(test, x, c)}`) and, on generation
triples `(gen, x, c)`, the replacer with `ω^{µ,x}_{S_i} = (1−µ) ω^x_{S_i} + µ I_{S_i}/|S_i|`. Then
`E_i = T_i ∘ G_i` and `F^µ_i = T_i ∘ P_i ∘ G_i` (52). -/
def diSeqData {X Y A B SA SB : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype SA]
    [Fintype SB] [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] [DecidableEq SA]
    [DecidableEq SB] (G : Game X Y A B) (Rz : Realization X Y A B SA SB) (γ μ : ℝ)
    {I : StoredImpl X Y A B} (Ex : Extraction X Y A B SA SB I) :
    SeqData (Option Bool) (fun _ => RoundO X Y A B) (fun k => Fin (I.dA k) × Fin (I.dB k))
      (fun _ => Bool × X × Option Bool) (fun _ => A × SA × SB)
      (fun k => RoundJ Y B (Ex.qA k) (Ex.qB k) (I.dA (k + 1)) (I.dB (k + 1))) where
  cOf := fun _ z => z.2.2
  G := fun k => roundG G Rz γ Ex k
  Zs := fun _ => Finset.univ.filter fun z => z.1 = true
  ω := fun _ z => depol μ (omegaX Rz z.2.1)
  T := fun k => roundT Ex k

end FlexRigidity


