-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSplitEtaleHermitianPairIsometry
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSplitEtaleHermitianPairIsometry
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:10.381326+00:00
-- url     : https://prove2.me/theorems/ec691949-6669-4993-801a-51fe9618667d
-- title:
--   Exists Split Etale Hermitian Pair Isometry
-- statement:
--   Definitions and structural lemmas for Exists Split Etale Hermitian Pair Isometry, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSplitEtaleHermitianPairIsometry.lean

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
namespace GlobalTheory.JR.SplitEt
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E]
def piCoord {ι : Type} [Fintype ι] (b : Module.Basis ι F E) (r : ℕ) :
    (Fin r → E) ≃ₗ[Fin r → F] (ι → (Fin r → F)) where
  toFun y k i := b.repr (y i) k
  invFun c i := ∑ k, c k i • b k
  map_add' y y' := by ext k i; simp
  map_smul' x y := by ext k i; simp
  left_inv y := by funext i; simp [b.sum_repr]
  right_inv c := by classical ext k i; simp [Finsupp.single_apply]
end GlobalTheory.JR.SplitEt
namespace GlobalTheory.JR.SplitEt
variable (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E]
theorem push_pi (r : ℕ) : Algebra.IsPushout F E (Fin r → F) (Fin r → E) := by
  refine ⟨?_⟩
  have h := IsBaseChange.finitePow (Fin r) (IsBaseChange.linearMap F E)
  have e : (IsScalarTower.toAlgHom F (Fin r → F) (Fin r → E)).toLinearMap = (Algebra.linearMap F E).compLeft (Fin r) :=
    LinearMap.ext fun _ => rfl
  rw [e]
  exact h
abbrev splitEt (r : ℕ) : Et F E :=
  haveI : LocallyCompactSpace F := Unram.lcF E
  letI : MeasurableSpace (Fin r → F) := borel (Fin r → F)
  haveI : BorelSpace (Fin r → F) := ⟨rfl⟩
  letI tL : TopologicalSpace (Fin r → E) := moduleTopology F (Fin r → E)
  letI : MeasurableSpace (Fin r → E) := borel (Fin r → E)
  haveI : BorelSpace (Fin r → E) := ⟨rfl⟩
  haveI : IsModuleTopology F (Fin r → E) := ⟨rfl⟩
  { K := Fin r → F
    L := Fin r → E
    push := push_pi F E r
    star_K := fun x => by funext i; exact Unram.star_fix (E := E) (x i)
    star_E := fun y => rfl }
end GlobalTheory.JR.SplitEt


