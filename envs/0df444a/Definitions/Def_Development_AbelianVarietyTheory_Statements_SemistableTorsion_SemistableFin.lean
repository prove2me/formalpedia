-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
-- name    : Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:59:29.7669+00:00
-- url     : https://prove2.me/theorems/44765fe1-a8f8-447b-b236-a4a30a743c01
-- title:
--   Semistable Fin
-- statement:
--   Definitions and structural lemmas for Semistable Fin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Statements/SemistableTorsion/SemistableFin.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.SS
def IsModel {K W L : Type} [Field K] [CommRing W] [Field L] [Algebra K L] [Algebra W L]
    (A : Over (Sp K)) [GrpObj A] (G : Over (Sp W)) [GrpObj G] : Prop :=
  ∃ e : (Over.pullback (spMap (algebraMap W L))).obj G ≅ (Over.pullback (spMap (algebraMap K L))).obj A, IsMonHom e.hom
noncomputable abbrev spFibre {W : Type} [CommRing W] [IsLocalRing W] (G : Over (Sp W)) : Over (Sp (IsLocalRing.ResidueField W)) :=
  (Over.pullback (spMap (IsLocalRing.residue W))).obj G
def PotModel (V K : Type) [CommRing V] [Field K] [Algebra V K] (A : Over (Sp K)) [GrpObj A]
    (Q : ∀ (W : Type) [CommRing W] [IsLocalRing W] (G : Over (Sp W)) [GrpObj G], Prop) : Prop :=
  ∃ (W L : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Field L) (_ : Algebra V W)
    (_ : Algebra W L) (_ : Algebra K L) (_ : IsFractionRing W L),
    (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) ∧ Module.Finite V W ∧
    IsLocalHom (algebraMap V W) ∧ IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧
    ∃ (G : Over (Sp W)) (_ : GrpObj G), IsModel (L := L) A G ∧ Q W G
def SSRedFor (C : ∀ (k : Type) [Field k], Prop)
    (Q : ∀ (W : Type) [CommRing W] [IsLocalRing W] (G : Over (Sp W)) [GrpObj G], Prop) : Prop :=
  ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], C (IsLocalRing.ResidueField V) →
    ∀ (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → PotModel V K A Q
def SplitSemi (W : Type) [CommRing W] [IsLocalRing W] (G : Over (Sp W)) [GrpObj G] : Prop :=
  IsSemiAbelian G ∧ ∃ E : SplitExt (Sp (IsLocalRing.ResidueField W)), E.IsGt (spFibre G)
def SemistableAll : Prop := SSRedFor (fun _ _ => True) SplitSemi
def SemistableFin : Prop := SSRedFor (fun k _ => Finite k) SplitSemi
def SemistablePol : Prop :=
  ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Finite (IsLocalRing.ResidueField V) →
    ∀ A : Out.PolAV (Sp K), PotModel V K A.A SplitSemi
end GlobalTheory.SS


