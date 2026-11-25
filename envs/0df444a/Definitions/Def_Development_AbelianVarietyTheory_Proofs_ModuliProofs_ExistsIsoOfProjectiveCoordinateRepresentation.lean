-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsoOfProjectiveCoordinateRepresentation
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsoOfProjectiveCoordinateRepresentation
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T03:09:29.0344+00:00
-- url     : https://prove2.me/theorems/54754fc9-1d09-400d-9cce-874e0c5b77d6
-- title:
--   Exists Iso Of Projective Coordinate Representation
-- statement:
--   Definitions and structural lemmas for Exists Iso Of Projective Coordinate Representation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsoOfProjectiveCoordinateRepresentation.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_mul
import Theorems.Thm_GlobalTheory_ProjSpace_resG_appLE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM
noncomputable section
namespace GlobalTheory.RepUniq
open TopologicalSpace GlobalTheory.Cartier GlobalTheory.ProjSpace
variable {σ : Type} {T T' X X' X'' : Scheme.{0}}
def NoZero {W : T.Opens} (f : σ → Γ(T, W)) : Prop :=
  ∀ t (ht : t ∈ W), ∃ i, IsUnit ((T.presheaf.germ W t ht).hom (f i))
theorem NoZero.res {W W' : T.Opens} {f : σ → Γ(T, W)} (hf : NoZero f) (h : W' ≤ W) :
    NoZero fun i => resG T h (f i) := fun t ht =>
  (hf t (h ht)).imp fun i hi => by rwa [germ_resG]
theorem appLE_compat {M : LB X} (a : M.Sec) (x : T ⟶ X) {W : T.Opens} (j k : M.ι) (hj : W ≤ x ⁻¹ᵁ M.U j)
    (hk : W ≤ x ⁻¹ᵁ M.U k) :
    (x.appLE _ W hj).hom (a.f j) =
      (x.appLE (M.U j ⊓ M.U k) W (le_inf hj hk)).hom (M.g j k).val * (x.appLE _ W hk).hom (a.f k) := by
  have h : W ≤ x ⁻¹ᵁ (M.U j ⊓ M.U k) := le_inf hj hk
  have := congrArg (x.appLE (M.U j ⊓ M.U k) W h).hom (a.compat j k)
  rw [map_mul] at this
  exact (appLE_resG x inf_le_left h _).symm.trans
    (this.trans (congrArg (_ * ·) (appLE_resG x inf_le_right h _)))
def Frame (M : LB X) (th : σ → M.Sec) (x : T ⟶ X) (W : T.Opens) (f : σ → Γ(T, W)) : Prop :=
  ∃ (j : M.ι) (h : W ≤ x ⁻¹ᵁ M.U j) (u : Γ(T, W)), IsUnit u ∧ ∀ i, (x.appLE _ W h).hom ((th i).f j) = u * f i
variable {M : LB X} {th : σ → M.Sec} {M' : LB X'} {th' : σ → M'.Sec} {M'' : LB X''} {th'' : σ → M''.Sec}
  {x : T ⟶ X} {x' : T ⟶ X'} {x'' : T ⟶ X''}
theorem Frame.res {W W' : T.Opens} {f : σ → Γ(T, W)} (H : Frame M th x W f) (h : W' ≤ W) :
    Frame M th x W' fun i => resG T h (f i) := by
  obtain ⟨j, hj, u, hu, e⟩ := H
  exact ⟨j, h.trans hj, resG T h u, hu.map _, fun i => by rw [← map_mul, ← e, resG_appLE]⟩
theorem Frame.mul {W : T.Opens} {f f' : σ → Γ(T, W)} (H : Frame M th x W f') {c : Γ(T, W)} (hc : IsUnit c)
    (h : ∀ i, f' i = c * f i) : Frame M th x W f := by
  obtain ⟨j, hj, u, hu, e⟩ := H
  exact ⟨j, hj, u * c, hu.mul hc, fun i => by rw [e, h, mul_assoc]⟩
theorem Frame.ratio {W : T.Opens} {f f' : σ → Γ(T, W)} (H : Frame M th x W f) (H' : Frame M th x W f') :
    ∃ c : Γ(T, W), IsUnit c ∧ ∀ i, f' i = c * f i := by
  obtain ⟨j, hj, u, hu, e⟩ := H
  obtain ⟨k, hk, u', hu', e'⟩ := H'
  obtain ⟨u', rfl⟩ := hu'
  refine ⟨u'⁻¹.val * (x.appLE (M.U k ⊓ M.U j) W (le_inf hk hj)).hom (M.g k j).val * u,
    ((Units.isUnit _).mul ((Units.isUnit _).map _)).mul hu, fun i => ?_⟩
  rw [mul_assoc, ← e, mul_assoc, ← appLE_compat _ x k j hk hj, e', Units.inv_mul_cancel_left]
def Same (M : LB X) (th : σ → M.Sec) (x : T ⟶ X) (M' : LB X') (th' : σ → M'.Sec) (x' : T ⟶ X') : Prop :=
  ∀ t : T, ∃ W : T.Opens, t ∈ W ∧ ∃ f, Frame M th x W f ∧ Frame M' th' x' W f
theorem Same.trans (H : Same M th x M' th' x') (H' : Same M' th' x' M'' th'' x'') :
    Same M th x M'' th'' x'' := fun t => by
  obtain ⟨W, hW, f, h₁, h₂⟩ := H t
  obtain ⟨V, hV, f', h₃, h₄⟩ := H' t
  obtain ⟨c, hc, e⟩ := (h₂.res (inf_le_left : W ⊓ V ≤ W)).ratio (h₃.res inf_le_right)
  exact ⟨W ⊓ V, ⟨hW, hV⟩, _, h₁.res inf_le_left, (h₄.res inf_le_right).mul hc e⟩
def LocCoord (M : LB X) (th : σ → M.Sec) (x : T ⟶ X) (v : σ → Γ(T, ⊤)) : Prop :=
  ∀ t : T, ∃ W : T.Opens, t ∈ W ∧ Frame M th x W fun i => resG T le_top (v i)
section Ring
variable {A : Type} [CommRing A]
abbrev fn (v : σ → A) : σ → Γ(Sp A, ⊤) := fun i => (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (v i)
end Ring
section Top
variable {A : Type} [CommRing A]
end Top
section Rep
variable {R : Type} [CommRing R] {I I' : Ideal (MvPolynomial σ R)} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R}
end Rep
end GlobalTheory.RepUniq


