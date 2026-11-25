-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleVanishingOnFixingSubgroupDeterminedByGene
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleVanishingOnFixingSubgroupDeterminedByGene
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T05:04:10.324961+00:00
-- url     : https://prove2.me/theorems/21df68ed-b5c5-4f78-a4a1-bfb6774de58f
-- title:
--   Cocycle Vanishing On Fixing Subgroup Determined By Gene
-- statement:
--   Definitions and structural lemmas for Cocycle Vanishing On Fixing Subgroup Determined By Gene, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CocycleVanishingOnFixingSubgroupDeterminedByGene.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousOrbitPadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceAlmostOntoOfLevels
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Filter Topology
namespace GlobalTheory.Cyc.Procyclic
section Abstract
variable {Γ X : Type} [Group Γ] [NormedAddCommGroup X]
def psum (A : Γ → X →+ X) (g : Γ) (w : X) (n : ℕ) : X := (fun x => w + A g x)^[n] 0
variable {G : Subgroup Γ} {A : Γ → X →+ X} {g : Γ} {w : X}
variable [IsUltrametricDist X]
variable [TopologicalSpace Γ]
end Abstract
variable {l : ℕ} [Fact l.Prime]
def intSub (F : IntermediateField ℚ_[l] (Om l)) : Subring (PadicComplex l) where
  carrier := intC F
  mul_mem' := by
    rintro _ _ ⟨⟨x, hx, rfl⟩, hx1⟩ ⟨⟨y, hy, rfl⟩, hy1⟩
    refine ⟨⟨x * y, F.mul_mem hx hy, UniformSpace.Completion.coe_mul _ _⟩, ?_⟩
    rw [norm_mul]; exact mul_le_one₀ hx1 (norm_nonneg _) hy1
  one_mem' := ⟨⟨1, F.one_mem, UniformSpace.Completion.coe_one _⟩, norm_one.le⟩
  add_mem' := by
    rintro _ _ ⟨⟨x, hx, rfl⟩, hx1⟩ ⟨⟨y, hy, rfl⟩, hy1⟩
    exact ⟨⟨x + y, F.add_mem hx hy, UniformSpace.Completion.coe_add _ _⟩,
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx1 hy1)⟩
  zero_mem' := ⟨⟨0, F.zero_mem, UniformSpace.Completion.coe_zero⟩, by simp⟩
  neg_mem' := by
    rintro _ ⟨⟨x, hx, rfl⟩, hx1⟩
    exact ⟨⟨-x, F.neg_mem hx, UniformSpace.Completion.coe_neg _⟩, by rwa [norm_neg]⟩
def ohatSub (K : FinExt l) : Subring (PadicComplex l) := (intSub (Kinf K)).topologicalClosure
variable {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ}
def twHom (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) {r : ℕ}
    (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (σ : GQ l) :
    (Fin r → PadicComplex l) →+ (Fin r → PadicComplex l) :=
  AddMonoidHom.mk' (twAct act χ i U σ) fun x y => by
    ext a
    simp [twAct, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
variable {K : FinExt l} {m r : ℕ} {U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)} {g : GQ l}
end GlobalTheory.Cyc.Procyclic


