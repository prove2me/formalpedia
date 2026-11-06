-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
-- name    : QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:17:25.137207+00:00
-- url     : https://prove2.me/theorems/3b8b87e3-1412-4bd0-ade3-9d6aabc333a0
-- title:
--   Differential Local
-- statement:
--   Definitions and structural lemmas for Differential Local, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DifferentialLocal.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_Differential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuation_uniformizer

set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped WithZero
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
namespace Differential
noncomputable def localParameter (P : GlobalPlace k F) : F :=
  P.uniformizer
theorem localParameter_valuation (P : GlobalPlace k F) :
    P.valuation (localParameter P) = WithZero.exp (-1 : ℤ) :=
  P.valuation_uniformizer
theorem localParameter_ne_zero (P : GlobalPlace k F) : localParameter P ≠ 0 := by
  intro hzero
  have hvaluation := localParameter_valuation P
  rw [hzero, (P.valuation).map_zero] at hvaluation
  exact WithZero.exp_ne_zero hvaluation.symm
noncomputable def localParameterUnit (P : GlobalPlace k F) : Fˣ :=
  Units.mk0 (localParameter P) (localParameter_ne_zero P)
noncomputable def localDifferentialLattice (P : GlobalPlace k F) :
    Submodule P.valuationRing (Differential k F) :=
  Submodule.span P.valuationRing
    (Set.range fun f : P.valuationRing => differential k F (f : F))
noncomputable def localParameterPower (P : GlobalPlace k F) (n : ℤ) : F :=
  ((localParameterUnit P) ^ n : Fˣ)
def OrderAtLeast (P : GlobalPlace k F) (n : ℤ) (omega : Differential k F) : Prop :=
  localParameterPower P (-n) • omega ∈ localDifferentialLattice P
def ResidueCongruent (P : GlobalPlace k F) (omega eta : Differential k F) : Prop :=
  OrderAtLeast P 0 (omega - eta)
end Differential
namespace GlobalPlace
noncomputable def uniformizerInValuationRing (P : GlobalPlace k F) :
    P.valuationRing :=
  ⟨P.uniformizer, (P.mem_valuationRing_iff _).mpr (by
    rw [P.valuation_uniformizer, ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by omega))⟩
end GlobalPlace
namespace Differential
noncomputable def simplePoleDifferentialLattice (P : GlobalPlace k F) :
    Submodule P.valuationRing (Differential k F) :=
  (localDifferentialLattice P).comap
    (LinearMap.lsmul P.valuationRing (Differential k F)
      P.uniformizerInValuationRing)
noncomputable def regularDifferentialSubmoduleOfSimplePole (P : GlobalPlace k F) :
    Submodule P.valuationRing (simplePoleDifferentialLattice P) :=
  (localDifferentialLattice P).comap (simplePoleDifferentialLattice P).subtype
noncomputable abbrev localResidueLine (P : GlobalPlace k F) :=
  simplePoleDifferentialLattice P ⧸ regularDifferentialSubmoduleOfSimplePole P
end Differential
end QEC.Coding.AlgebraicGeometry


