-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveSpMapFst
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveSpMapFst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:36.527841+00:00
-- url     : https://prove2.me/theorems/e2425fe7-b1b3-4b01-be69-9ebfe6fd91cb
-- title:
--   Surjective Sp Map Fst
-- statement:
--   Definitions and structural lemmas for Surjective Sp Map Fst, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SurjectiveSpMapFst.lean

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DenseInterior_23def473f6482931
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualNumberSectionsUniqueDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
noncomputable section
namespace GlobalTheory.InvFieldRing
attribute [local instance] Over.cartesianMonoidalCategory
section Val
variable {A : Type} [CommRing A] {Y : Scheme.{0}}
end Val
section Geo
theorem spMap_fst_comp (R : Type) [CommRing R] :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
end Geo
section Group
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  (U : X.affineOpens) (u : Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)
def tanPt (hu : IsTanAtG t (chart U) u) : tEpsG (chart U) ⟶ t.G := Over.homMk u hu.1
def transl (hu : IsTanAtG t (chart U) u) : tEpsG (chart U) ⊗ t.G ⟶ t.G :=
  snd _ t.G * (fst _ t.G ≫ tanPt t U u hu)
def redPt : Over.mk (chart U) ⟶ tEpsG (chart U) :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom Γ(X, U.1) Γ(X, U.1) Γ(X, U.1)).toRingHom) (by
    change _ ≫ spMap _ ≫ chart U = chart U
    rw [← Category.assoc, spMap_fst_comp, Category.id_comp])
end Group
section Group2
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  (U : X.affineOpens) (u : Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)
end Group2
end GlobalTheory.InvFieldRing


