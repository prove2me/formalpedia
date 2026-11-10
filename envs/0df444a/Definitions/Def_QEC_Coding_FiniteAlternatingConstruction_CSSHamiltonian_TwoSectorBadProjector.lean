-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T01:58:16.474117+00:00
-- url     : https://prove2.me/theorems/ff8e02e4-9044-412c-a85e-077ca8822c3a
-- title:
--   Two Sector Bad Projector
-- statement:
--   Definitions and structural lemmas for Two Sector Bad Projector, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/TwoSectorBadProjector.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26TwoSectorBadProjector
open Classical Semantics BDL26FiniteTannerSquare BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (n : Nat)
abbrev XImage := LinearMap.range (zSyndrome S n)
abbrev ZImage := LinearMap.range (xSyndrome S n)
local instance _p2m_local_instance_06cc962c0b_24 : Fintype (XImage S n) := Fintype.ofFinite _
local instance _p2m_local_instance_06cc962c0b_25 : Fintype (ZImage S n) := Fintype.ofFinite _
abbrev JointImage := XImage S n × ZImage S n
abbrev selected (A : Finset (JointImage S n)) : Operator (Qubit.QubitRegister (Physical S n)) :=
  CSSGibbs.selectedProjector (zSyndrome S n) (xSyndrome S n) (row_orthogonal S n) A
def goodX (BX : Finset (XImage S n)) : Finset (JointImage S n) := BXᶜ ×ˢ Finset.univ
def goodZ (BZ : Finset (ZImage S n)) : Finset (JointImage S n) := Finset.univ ×ˢ BZᶜ
def goodJoint (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n)) :
    Finset (JointImage S n) := BXᶜ ×ˢ BZᶜ
def PX (BX : Finset (XImage S n)) := selected S n (goodX S n BX)
def PZ (BZ : Finset (ZImage S n)) := selected S n (goodZ S n BZ)
def Pjoint (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n)) :=
  selected S n (goodJoint S n BX BZ)
def badUnionWords (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n)) :
    Finset (Word (ZMod 2) (Sum (ZLabel S n) (XLabel S n))) :=
  ((goodJoint S n BX BZ)ᶜ).map (CSSGibbs.realizableEmbedding (zSyndrome S n) (xSyndrome S n))
def pX (β : ℝ) (BX : Finset (XImage S n)) : ℝ :=
  ∑ u ∈ BX, CSSGibbs.rowProbability (zSyndrome S n) (2*β) u
def pZ (β : ℝ) (BZ : Finset (ZImage S n)) : ℝ :=
  ∑ v ∈ BZ, CSSGibbs.rowProbability (xSyndrome S n) (2*β) v
end QEC.Coding.BDL26TwoSectorBadProjector


