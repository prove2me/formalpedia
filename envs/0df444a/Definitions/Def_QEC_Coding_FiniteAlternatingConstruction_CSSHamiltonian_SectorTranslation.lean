-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T05:31:41.547024+00:00
-- url     : https://prove2.me/theorems/99d9d96a-1051-4b1b-9fa1-4253f1e49e5f
-- title:
--   Sector Translation
-- statement:
--   Definitions and structural lemmas for Sector Translation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/SectorTranslation.lean

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26SectorTranslation
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26CSSDaviesLocality BDL26TwoSectorBadProjector
open scoped BigOperators
variable (S : OddScale) (n : Nat)
local instance _p2m_local_instance_8726da3c88_19 : Fintype (XImage S n) := Fintype.ofFinite _
local instance _p2m_local_instance_8726da3c88_20 : Fintype (ZImage S n) := Fintype.ofFinite _
abbrev basisError (q : Physical S n) : Word (ZMod 2) (Physical S n) := Pi.single q 1
def epsilonX (q : Physical S n) : XImage S n :=
  ⟨zSyndrome S n (basisError S n q), ⟨basisError S n q, rfl⟩⟩
def epsilonZ (q : Physical S n) : ZImage S n :=
  ⟨xSyndrome S n (basisError S n q), ⟨basisError S n q, rfl⟩⟩
def translation (q : Physical S n) (a : CSSDaviesLocality.Axis) : JointImage S n ≃ JointImage S n :=
  CSSGibbs.jointTranslation (zSyndrome S n) (xSyndrome S n) (CSSDaviesLocality.singlePauli q a)
def translated (q : Physical S n) (a : CSSDaviesLocality.Axis) (A : Finset (JointImage S n)) :
    Finset (JointImage S n) := A.map (translation S n q a).toEmbedding
def translatedX (q : Physical S n) (a : CSSDaviesLocality.Axis) (A : Finset (XImage S n)) :=
  A.map (CSSGibbs.rangeShiftEquiv (zSyndrome S n) (CSSDaviesLocality.singlePauli q a).vector.xPart).toEmbedding
def translatedZ (q : Physical S n) (a : CSSDaviesLocality.Axis) (B : Finset (ZImage S n)) :=
  B.map (CSSGibbs.rangeShiftEquiv (xSyndrome S n) (CSSDaviesLocality.singlePauli q a).vector.zPart).toEmbedding
end QEC.Coding.BDL26SectorTranslation


