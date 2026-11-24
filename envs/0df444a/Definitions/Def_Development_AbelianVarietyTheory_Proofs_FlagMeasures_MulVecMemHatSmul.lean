-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MulVecMemHatSmul
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_MulVecMemHatSmul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:05.848306+00:00
-- url     : https://prove2.me/theorems/ccf1f34c-c8dd-47d2-8953-13eb3da3a59a
-- title:
--   Mul Vec Mem Hat Smul
-- statement:
--   Definitions and structural lemmas for Mul Vec Mem Hat Smul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MulVecMemHatSmul.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelWeilLocal_HermitianPerpSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelWeilLocal_ColumnDimensionRational
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped TensorProduct ENNReal Pointwise
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IndefiniteRowSideFullHecke
namespace GlobalTheory.ColCmp
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {n r k : ℕ}
def zPerp (σ : E →+* E) {m : ℕ} (Jb : Matrix (Fin m) (Fin m) E) (z : Fin m → E) :
    Submodule (𝓞 E) (Fin m → E) where
  carrier := {x | form σ Jb x z = 0}
  zero_mem' := by simp [form]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, form, Matrix.mulVec_add, dotProduct_add] at *
    rw [ha, hb, add_zero]
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq, form] at *
    rw [Matrix.mulVec_smul, dotProduct_smul, ha, smul_zero]
def levelJoin (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E)
    (f : Matrix (Fin n) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin n → E)) (g₁ g₂ : ℕ)
    (w : HeightOneSpectrum (𝓞 F) → HeightOneSpectrum (𝓞 E))
    (ε : HeightOneSpectrum (𝓞 F) → Fin k → Fin n → E) : Subgroup (HA (Af F) σ J) :=
  (ParabolicSubgroups.Np (Af F) σ J P ⊓ ParabolicSubgroups.Kmax σ J Λ) ⊔
    (ParabolicSubgroups.Hp (Af F) σ J P f ⊓ ParabolicSubgroups.Kmax σ J Λ ⊓
      ⨅ p ∈ ParabolicSubgroups.Typed F g₁ g₂, ParabolicSubgroups.uniAt σ J Λ (w p).asIdeal (ε p)) ⊔
    FlagUnipotentStabilizers.Kprin σ J Λ (g₁ * g₂)
end GlobalTheory.ColCmp


