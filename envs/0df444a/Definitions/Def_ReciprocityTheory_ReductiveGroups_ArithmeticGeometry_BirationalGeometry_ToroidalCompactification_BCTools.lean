-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:31:51.085657+00:00
-- url     : https://prove2.me/theorems/c2732e01-8c89-4143-9ba3-7b0a78344774
-- title:
--   BCTools
-- statement:
--   Definitions and structural lemmas for BCTools, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/BCTools.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_OLinBaseChangeSt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
def QkPullExistsSt : Prop :=
  ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : Out.DegPre R)
    (D' : Out.DegPre R') (hD : Out.IsPullDeg φ D D') (F : Type) [Field F] [Algebra (FractionRing R) F]
    [Algebra (FractionRing R') F],
    (∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
      algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (φ r))) →
    ∀ (k : ℕ) (p' : Out.QkPt D' F k), ∃ p : Out.QkPt D F k, p'.y = hD.xe.symm p.y ∧ Out.IsPullGtF φ hD F p.g p'.g
def PolOActPullSt : Prop :=
  ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (P : Out.PolAV S) (P' : Out.PolAV S') (g : P'.A.left ⟶ P.A.left),
    IsGrpPullback P'.A P.A f g → LBIso (P.L.pull g) P'.L →
    ∀ (O : Type) [CommRing O] [StarRing O] (o : P.OAct O), ∃ o' : P'.OAct O,
      ∀ a, (o'.act a).left ≫ g = g ≫ (o.act a).left
section Grp
variable {S S' : Scheme.{0}}
end Grp
section Iso
variable {X Y Y' : Scheme.{0}}
def chartPullSame (L : LB X) {K : Type} [Fintype K] (φ' : K → (Y' ⟶ X)) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y)
    (hc : ∀ k, φ' k = h ≫ φ k) : ChartPull (LB.LinComb L φ' ε) (LB.LinComb L φ ε) h :=
  have le : ∀ j : K → L.ι, LB.wchart L φ' j ≤ h ⁻¹ᵁ LB.wchart L φ j := fun j y hy => Set.mem_iInter.2 fun k => by
    have : φ' k y ∈ L.U (j k) := Set.mem_iInter.1 hy k
    rw [hc] at this; exact this
  { idx := fun j => j
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L φ' ε (𝟙 Y') y j j' hj hj').trans (Eq.trans (Finset.prod_congr rfl fun k _ => ?_)
        (gm_linComb L φ ε h y _ _ (le j hj) (le j' hj')).symm)
      rw [Category.id_comp, hc] }
def chartPullId (L : LB X) : ChartPull L L (𝟙 X) := ⟨fun i => i, fun _ _ h => h, fun _ _ _ _ _ => rfl⟩
def chartPullUnpull (L : LB X) (F : X ⟶ X) (e : F = 𝟙 X) : ChartPull L (L.pull F) (𝟙 X) where
  idx i := fun _ => i
  le i y hy := by subst e; exact mem_pull.2 hy
  g y i j hi hj := by
    subst e
    exact ((gm_pull_g L (𝟙 X) (𝟙 X) y (fun _ => i) (fun _ => j) (mem_pull.2 hi) (mem_pull.2 hj)).trans
      (by rw [Category.id_comp])).symm
end Iso
section Field
variable {F : Type} [Field F] {X : Scheme.{0}}
def toStk (z : Sp F) : F →+* (Sp F).presheaf.stalk z :=
  ((Sp F).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
variable {B B' B₀ : Scheme.{0}} {M : LB B} {M' : LB B'} {M₀ : LB B₀} {K : Type} [Fintype K] {ε : K → ℤ}
end Field
end ReciprocityTheory.ChartRestriction.G.Geo.Tor


