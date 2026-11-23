-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxC
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:47:37.509812+00:00
-- url     : https://prove2.me/theorems/a662c556-9ca4-43a7-8635-fb3d7cc43f95
-- title:
--   Loc Dens Idx C
-- statement:
--   Definitions and structural lemmas for Loc Dens Idx C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensIdxC.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  IsLocalRing
namespace IdxHW
section Main
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (b : Module.Basis (Fin 2) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ)
def Cmat : Matrix (Fin 2) (Fin 2) F := fun k l => b.repr (σ (b l)) k
def cr (y : Fv F v ⊗[F] E) (k : Fin 2) : Fv F v := (Algebra.TensorProduct.basis (Fv F v) b).repr y k
def psi (k0 : Fin 2) : hermO b v σ a →+ (Fin a × Fin a → v.adicCompletionIntegers F) where
  toFun S q := if q.1 < q.2 then ⟨crdS b v σ a S q.1 q.2 0, (mem_hermO_iff b v σ a S).1 S.2 _ _ _⟩
    else if q.2 < q.1 then ⟨crdS b v σ a S q.2 q.1 1, (mem_hermO_iff b v σ a S).1 S.2 _ _ _⟩
    else ⟨crdS b v σ a S q.1 q.1 k0, (mem_hermO_iff b v σ a S).1 S.2 _ _ _⟩
  map_zero' := by
    funext q
    split_ifs <;> ext <;> simp [crdS]
  map_add' S T := by
    funext q
    simp only [Pi.add_apply]
    by_cases h1 : q.1 < q.2
    · simp only [if_pos h1]
      ext
      simp [crdS_add]
    · by_cases h2 : q.2 < q.1
      · simp only [if_neg h1, if_pos h2]
        ext
        simp [crdS_add]
      · simp only [if_neg h1, if_neg h2]
        ext
        simp [crdS_add]
end Main
end IdxHW
end PI.VolStabW


