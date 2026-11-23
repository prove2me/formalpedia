-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaRecognitionLabelsAgreeOfIso
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaRecognitionLabelsAgreeOfIso
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:49.763799+00:00
-- url     : https://prove2.me/theorems/d2b891f1-6fa1-4035-a7ea-7e34945adcf3
-- title:
--   Theta Recognition Labels Agree Of Iso
-- statement:
--   Definitions and structural lemmas for Theta Recognition Labels Agree Of Iso, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ThetaRecognitionLabelsAgreeOfIso.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaConstantTermRepresentativeDependence
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTermStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomTransportStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SymmPairingEqOneOfOddOfDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisUniqueMinPairSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
namespace GlobalTheory.LabelsAgree
section Transport
variable {O : Type} [CommRing O] {N N' : NumD O} (J : NumD.Iso N N')
def toHom : NumD.Hom (RingHom.id O) N N' where
  φ := J.φ.toMonoidHom
  h := J.h
  h_one := J.h_one
  θ_eq := J.θ_eq
  σ_eq := J.σ_eq
  lam := J.lam
  th_eq := J.th_eq
  e := J.e
  c_eq := J.c_eq
  ψ_eq := J.ψ_eq
def TR {k : ℕ} (p : N.QT k) (p' : N'.QT k) : Prop :=
  p'.1.1.toAdd = J.e p.1.1.toAdd ∧ J.Rel p.1.2 p'.1.2
end Transport
section Level
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ} (μ : Match N N' n) (J : NumD.Iso N N')
def Defect (k : ℕ) (x : N.X) (d : N'.QT k) : Prop :=
  d.1.1 = 1 ∧ d.1.2.b = 1 ∧ ∀ p a, p.1.1.toAdd = x → TR J p a → μ.r k p (a * d)
end Level
end GlobalTheory.LabelsAgree


