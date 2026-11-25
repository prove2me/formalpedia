-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteOfIsClosedSplitTorusOfPowEqOne
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteOfIsClosedSplitTorusOfPowEqOne
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T23:53:19.909797+00:00
-- url     : https://prove2.me/theorems/45997f68-1715-4780-9ff8-d4dd5982c3f0
-- title:
--   Finite Of Is Closed Split Torus Of Pow Eq One
-- statement:
--   Definitions and structural lemmas for Finite Of Is Closed Split Torus Of Pow Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FiniteOfIsClosedSplitTorusOfPowEqOne.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne
import Theorems.Thm_GlobalTheory_laurentEval_single
import Theorems.Thm_GlobalTheory_torusCoord_apply
import Theorems.Thm_GlobalTheory_torusEval_bijective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_ringHom_ext_ZU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_torusIso_hom_fst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.laurentEval_single
attribute [local simp] GlobalTheory.torusCoord_apply


set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
namespace GlobalTheory
theorem adjunction_homEquiv_symm_mul {C D : Type*} [Category C] [Category D]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) [R.Monoidal] {Y : C} {M : D} [MonObj M] (a b : Y ⟶ R.obj M) :
    (adj.homEquiv Y M).symm (a * b) = (adj.homEquiv Y M).symm a * (adj.homEquiv Y M).symm b := by
  rw [Hom.mul_def, Hom.mul_def, Functor.obj.μ_def, ← Category.assoc,
    adj.homEquiv_naturality_right_symm]
  congr 1
  ext
  · rw [← adj.homEquiv_naturality_right_symm]; simp
  · rw [← adj.homEquiv_naturality_right_symm]; simp
variable {k : Type} [Field k] {X : Type} [AddCommGroup X]
attribute [local instance] zuAlgebra
open scoped AlgebraMonoidAlgebra
noncomputable def splitTorusPoint (t : Multiplicative X →* kˣ) :
    𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X :=
  Over.homMk (Spec.map (CommRingCat.ofHom (torusEval t).toRingHom) ≫ (torusIso k X).hom) (by
    erw [Category.assoc, torusIso_hom_hom, ← Spec.map_comp]
    rw [← CommRingCat.ofHom_comp]
    have : (torusEval t).toRingHom.comp (algebraMap k (AddMonoidAlgebra k X)) = RingHom.id k :=
      (torusEval t).comp_algebraMap
    rw [this]
    exact Spec.map_id _)
theorem splitTorusPoint_left (t : Multiplicative X →* kˣ) :
    (splitTorusPoint t).left =
      Spec.map (CommRingCat.ofHom (torusEval t).toRingHom) ≫ (torusIso k X).hom := rfl
theorem splitTorusPoint_bijective :
    Function.Bijective (splitTorusPoint : (Multiplicative X →* kˣ) → _) := by
  constructor
  · intro s t h
    have h1 := congrArg (·.left) h
    simp only [splitTorusPoint_left] at h1
    have h2 := Spec.map_injective ((cancel_mono _).1 h1)
    exact torusEval_bijective.1 (AlgHom.coe_ringHom_injective (congrArg (·.hom) h2))
  · intro x
    let g : Spec (.of k) ⟶ Spec (.of (AddMonoidAlgebra k X)) := x.left ≫ (torusIso k X).inv
    have hg : CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k X)) ≫ Spec.preimage g = 𝟙 _ := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, ← torusIso_hom_hom, Spec.map_id]
      simp only [g]
      erw [Category.assoc, Iso.inv_hom_id_assoc]
      exact Over.w x
    obtain ⟨t, ht⟩ := torusEval_bijective.2 ⟨(Spec.preimage g).hom, fun r => congr($hg r)⟩
    refine ⟨t, Over.OverMorphism.ext ?_⟩
    rw [splitTorusPoint_left, ht]
    change Spec.map (Spec.preimage g) ≫ _ = _
    rw [Spec.map_preimage]
    simp only [g]
    erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
noncomputable def splitTorusDown (x : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) :
    (Spec (.of k)).asOver (Spec ZU) ⟶ splitTorusAff ZU X :=
  (Over.homMk (𝟙 (Sp k)) (specULiftZIsTerminal.hom_ext _ _) :
    (Spec (.of k)).asOver (Spec ZU) ⟶ (Over.map (toZ (Sp k))).obj (𝟙_ (Over (Sp k)))) ≫
    ((Over.mapPullbackAdj (toZ (Sp k))).homEquiv _ _).symm x
theorem splitTorusDown_left (x : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) :
    (splitTorusDown x).left = x.left ≫ torusFst (Sp k) X := by
  simp [splitTorusDown, Adjunction.homEquiv_symm_apply, torusFst]
  rfl
theorem splitTorusDown_mul (x y : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) :
    splitTorusDown (x * y) = splitTorusDown x * splitTorusDown y := by
  unfold splitTorusDown
  rw [← comp_mul]
  exact congrArg _ (adjunction_homEquiv_symm_mul (Over.mapPullbackAdj _) x y)
theorem splitTorusDown_injective :
    Function.Injective (splitTorusDown : (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) → _) := by
  intro x y h
  have h1 := congrArg (·.left) h
  simp only [splitTorusDown_left] at h1
  exact Over.OverMorphism.ext (pullback.hom_ext h1 ((Over.w x).trans (Over.w y).symm))
noncomputable def torusEvalInt (t : Multiplicative X →* kˣ) :
    AddMonoidAlgebra ZU.{0} X →ₐ[ZU.{0}] k :=
  AddMonoidAlgebra.lift _ k X ((Units.coeHom k).comp t)
theorem splitTorusDown_point (t : Multiplicative X →* kˣ) :
    splitTorusDown (splitTorusPoint t) = Spec.mapMulEquiv (WithConv.toConv (torusEvalInt t)) := by
  refine Over.OverMorphism.ext ?_
  rw [splitTorusDown_left, splitTorusPoint_left]
  erw [Category.assoc, torusIso_hom_fst, ← Spec.map_comp]
  change _ = Spec.map (CommRingCat.ofHom (torusEvalInt t).toRingHom)
  rw [← CommRingCat.ofHom_comp]
  congr 2
  refine ringHom_ext_ZU fun y => ?_
  simp [torusEvalInt]
theorem torusEvalInt_mul (s t : Multiplicative X →* kˣ) :
    WithConv.toConv (torusEvalInt (s * t)) =
      WithConv.toConv (torusEvalInt s) * WithConv.toConv (torusEvalInt t) := by
  apply WithConv.ofConv_injective
  apply AlgHom.coe_ringHom_injective
  refine ringHom_ext_ZU fun y => ?_
  simp [torusEvalInt, AlgHom.convMul_def]
theorem splitTorusPoint_mul (s t : Multiplicative X →* kˣ) :
    splitTorusPoint (s * t) = splitTorusPoint s * splitTorusPoint t := by
  apply splitTorusDown_injective
  rw [splitTorusDown_mul, splitTorusDown_point, splitTorusDown_point, splitTorusDown_point,
    torusEvalInt_mul, map_mul]
variable (k X) in

noncomputable def splitTorusPointEquiv :
    (Multiplicative X →* kˣ) ≃* (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) :=
  { Equiv.ofBijective _ splitTorusPoint_bijective with map_mul' := splitTorusPoint_mul }
end GlobalTheory


