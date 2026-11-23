-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:38:44.429706+00:00
-- url     : https://prove2.me/theorems/ada57928-d067-4940-834c-86ee2718c83f
-- title:
--   Exact And Ker Base Change Of Forall Residue Field
-- statement:
--   Definitions and structural lemmas for Exact And Ker Base Change Of Forall Residue Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndKerBaseChangeOfForallResidueField.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Function
namespace GlobalTheory
section LinearAlgebra
variable {R : Type*} [CommRing R] {A B C : Type*}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
end LinearAlgebra
section Comparison
open CategoryTheory Category Limits
set_option backward.isDefEq.respectTransparency false
variable {C D : Type*} [Category* C] [Category* D]
section ShortComplex
variable [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D) [F.PreservesZeroMorphisms]
noncomputable def shortCyclesComparison (S : ShortComplex C) [S.HasHomology]
    [(S.map F).HasHomology] : F.obj S.cycles ⟶ (S.map F).cycles :=
  (S.map F).liftCycles (F.map S.iCycles) (by
    rw [ShortComplex.map_g, ← F.map_comp, S.iCycles_g, F.map_zero])
@[reassoc (attr := simp)]
theorem shortCyclesComparison_iCycles (S : ShortComplex C) [S.HasHomology]
    [(S.map F).HasHomology] :
    shortCyclesComparison F S ≫ (S.map F).iCycles = F.map S.iCycles :=
  ShortComplex.liftCycles_i _ _ _
@[reassoc (attr := simp)]
theorem map_toCycles_shortCyclesComparison (S : ShortComplex C) [S.HasHomology]
    [(S.map F).HasHomology] :
    F.map S.toCycles ≫ shortCyclesComparison F S = (S.map F).toCycles := by
  rw [← cancel_mono (S.map F).iCycles, assoc, shortCyclesComparison_iCycles, ← F.map_comp,
    S.toCycles_i, (S.map F).toCycles_i, ShortComplex.map_f]
variable [PreservesColimitsOfShape WalkingParallelPair F]
noncomputable def shortHomologyComparison (S : ShortComplex C) [S.HasHomology]
    [(S.map F).HasHomology] : F.obj S.homology ⟶ (S.map F).homology :=
  (CokernelCofork.mapIsColimit _ S.homologyIsCokernel F).desc
    (CokernelCofork.ofπ (shortCyclesComparison F S ≫ (S.map F).homologyπ) (by
      rw [map_toCycles_shortCyclesComparison_assoc, ShortComplex.toCycles_comp_homologyπ]))
@[reassoc (attr := simp)]
theorem map_homologyπ_shortHomologyComparison (S : ShortComplex C) [S.HasHomology]
    [(S.map F).HasHomology] :
    F.map S.homologyπ ≫ shortHomologyComparison F S =
      shortCyclesComparison F S ≫ (S.map F).homologyπ :=
  Cofork.IsColimit.π_desc (CokernelCofork.mapIsColimit _ S.homologyIsCokernel F)
end ShortComplex
section Complex
variable [HasZeroMorphisms C] [HasZeroMorphisms D] [CategoryWithHomology C]
  [CategoryWithHomology D] (F : C ⥤ D) [F.PreservesZeroMorphisms] {ι : Type*} {c : ComplexShape ι}
noncomputable def cyclesComparison (K : HomologicalComplex C c) (p : ι) :
    F.obj (K.cycles p) ⟶ ((F.mapHomologicalComplex c).obj K).cycles p :=
  shortCyclesComparison F (K.sc p)
@[reassoc (attr := simp)]
theorem cyclesComparison_iCycles (K : HomologicalComplex C c) (p : ι) :
    cyclesComparison F K p ≫ ((F.mapHomologicalComplex c).obj K).iCycles p =
      F.map (K.iCycles p) :=
  shortCyclesComparison_iCycles F (K.sc p)
variable [PreservesColimitsOfShape WalkingParallelPair F]
noncomputable def homologyComparison (K : HomologicalComplex C c) (p : ι) :
    F.obj (K.homology p) ⟶ ((F.mapHomologicalComplex c).obj K).homology p :=
  shortHomologyComparison F (K.sc p)
@[reassoc (attr := simp)]
theorem map_homologyπ_homologyComparison (K : HomologicalComplex C c) (p : ι) :
    F.map (K.homologyπ p) ≫ homologyComparison F K p =
      cyclesComparison F K p ≫ ((F.mapHomologicalComplex c).obj K).homologyπ p :=
  map_homologyπ_shortHomologyComparison F (K.sc p)
end Complex
end Comparison
section Homotopy
open CategoryTheory Category Limits
set_option backward.isDefEq.respectTransparency false
variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [CategoryWithHomology C] [CategoryWithHomology D] {ι : Type*} {c : ComplexShape ι}
end Homotopy
section Modules
open CategoryTheory Category Limits
universe u w
variable {R : Type u} [CommRing R] {ι : Type*} {c : ComplexShape ι}
end Modules
section Explicit
open CategoryTheory Category Limits ChangeOfRings
universe u
variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
  {ι : Type*} {c : ComplexShape ι}
set_option backward.isDefEq.respectTransparency false in

noncomputable def tensorEquivExtendScalars (M : ModuleCat.{u} R) :
    S ⊗[R] M ≃ₗ[S] (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).obj M :=
  let e : S ≃ₗ[R] (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) :=
    { toFun := fun s => s
      invFun := fun s => s
      map_add' := fun _ _ => rfl
      map_smul' := fun r s => Algebra.smul_def r s
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  { (TensorProduct.congr e (LinearEquiv.refl R M)).toAddEquiv with
    map_smul' := fun s x => by
      change TensorProduct.congr e (LinearEquiv.refl R M) (s • x) =
        s • TensorProduct.congr e (LinearEquiv.refl R M) x
      induction x with
      | zero => simp
      | tmul a m => rfl
      | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add] }
noncomputable def homologyBaseChange (K : HomologicalComplex (ModuleCat.{u} R) c) (p : ι) :
    S ⊗[R] (K.homology p : ModuleCat R) →ₗ[S]
      ((((ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).mapHomologicalComplex c).obj
        K).homology p : ModuleCat S) :=
  (homologyComparison (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)) K p).hom ∘ₗ
    (tensorEquivExtendScalars S (K.homology p)).toLinearMap
end Explicit
section Main
open CategoryTheory Category Limits
universe u
variable {R : Type u} [CommRing R]
end Main
end GlobalTheory


