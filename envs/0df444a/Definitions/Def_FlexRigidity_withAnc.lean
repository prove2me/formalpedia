-- Prove2me | Definitions.Def_FlexRigidity_withAnc
-- name    : FlexRigidity_withAnc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:20:49.861545+00:00
-- url     : https://prove2.me/theorems/e67becde-5a87-49f3-a3e6-60e8fe443cc7
-- title:
--   Appending the ancillas $|00\rangle_{M'^{\mathrm A}_iM'^{\mathrm B}_i}$
-- statement:
--   The vector $|\rho\rangle_{RM^{\mathrm A}_iM^{\mathrm B}_i}\otimes|00\rangle_{M'^{\mathrm A}_iM'^{\mathrm B}_i}$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), §5.4, p. 47

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_StoredImpl
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Appending the ancillas `|00⟩_{M′^A_i M′^B_i}`** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, §5.4, p. 47): the vector `|ρ⟩_{R M^A_i M^B_i} ⊗ |00⟩`
on `R (M^A_i M′^A_i)(M^B_i M′^B_i)`. -/
def withAnc {X Y A B R : Type} (I : StoredImpl X Y A B) (i : ℕ)
    (ρ : R × (Fin (I.dA i) × Fin (I.dB i)) → ℂ) :
    R × ((Fin (I.dA i) × Fin (I.kA i + 1)) × (Fin (I.dB i) × Fin (I.kB i + 1))) → ℂ :=
  fun p => if p.2.1.2 = 0 ∧ p.2.2.2 = 0 then ρ (p.1, (p.2.1.1, p.2.2.1)) else 0

end FlexRigidity


