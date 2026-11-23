-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLatticePointsIntegralIdelesEquiv
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLatticePointsIntegralIdelesEquiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:57.767423+00:00
-- url     : https://prove2.me/theorems/5b3d1d18-dcf0-451d-99b4-68b43cb9048e
-- title:
--   Exists Lattice Points Integral Ideles Equiv
-- statement:
--   Definitions and structural lemmas for Exists Lattice Points Integral Ideles Equiv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLatticePointsIntegralIdelesEquiv.lean

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdelicRingClassLatticeOneEqOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmRingClassOrderUnitsEqMaxRealSubfieldUnitsStatement
import Theorems.Thm_GlobalTheory_CMVal_out_mem_lattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
namespace GlobalTheory.CMVal.LatBij
variable {E : Type} [Field E] [NumberField E]
def diag : Eˣ →* (Af E)ˣ := Units.map (algebraMap E (Af E)).toMonoidHom
def rep {c : Ideal (OF E)} {y : (Af E)ˣ} (a : modUnits (lattice c y)) : Eˣ := Units.mk0 a.1.out (out_mem_lattice a).2
def toIdele (c : Ideal (OF E)) (p : Σ q : PicO c, modUnits (lattice c q.out)) :
    {z : (Af E)ˣ ⧸ hatOUnits c // ∃ y : (Af E)ˣ, (QuotientGroup.mk y : (Af E)ˣ ⧸ hatOUnits c) = z ∧ (y : Af E) ∈ hatO c} :=
  ⟨QuotientGroup.mk (diag (rep p.2) * p.1.out⁻¹), _, rfl, (out_mem_lattice p.2).1⟩
end GlobalTheory.CMVal.LatBij


