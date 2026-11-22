-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:25:26.992167+00:00
-- url     : https://prove2.me/theorems/e7355426-7892-4eb3-b265-c7eb45240c7e
-- title:
--   Sab Pull
-- statement:
--   Definitions and structural lemmas for Sab Pull, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/SabPull.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pt_eq

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
section Chart
variable {X X' Y Y' : Scheme.{0}}
structure ChartPull (A' : LB Y') (A : LB Y) (h : Y' ⟶ Y) where
  idx : A'.ι → A.ι
  le : ∀ i, A'.U i ≤ h ⁻¹ᵁ A.U (idx i)
  g : ∀ (y : Y') i j, y ∈ A'.U i → y ∈ A'.U j →
    gm (𝟙 Y') y (A'.U i ⊓ A'.U j) (A'.g i j) = gm h y (A.U (idx i) ⊓ A.U (idx j)) (A.g (idx i) (idx j))
theorem gm_linComb {Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z)
    (j j' : K → L.ι) (hj : r z ∈ LB.wchart L φ j) (hj' : r z ∈ LB.wchart L φ j') :
    gm r z (LB.wchart L φ j ⊓ LB.wchart L φ j') ((LB.LinComb L φ ε).g j j') =
      ∏ k, gm (r ≫ φ k) z (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)) ^ ε k := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  exact (gm_res r z _ (show r z ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' from ⟨hj, hj'⟩) _).trans
    (gm_pull r (φ k) z (L.U (j k) ⊓ L.U (j' k)) ⟨Set.mem_iInter.1 hj k, Set.mem_iInter.1 hj' k⟩ _)
theorem gm_pull_g {Z : Scheme.{0}} (L : LB X) (F : X' ⟶ X) (r : Z ⟶ X') (z : Z) (J J' : PUnit → L.ι)
    (hj : r z ∈ (L.pull F).U J) (hj' : r z ∈ (L.pull F).U J') :
    gm r z ((L.pull F).U J ⊓ (L.pull F).U J') ((L.pull F).g J J') =
      gm (r ≫ F) z _ (L.g (J PUnit.unit) (J' PUnit.unit)) :=
  (gm_linComb L (fun _ : PUnit => F) (fun _ => 1) r z J J' hj hj').trans (by rw [Fintype.prod_unique, zpow_one])
def chartPullPull (L : LB X) (F h : X' ⟶ X) (e : h = F) : ChartPull (L.pull F) L h where
  idx J := J PUnit.unit
  le J y hy := by subst e; exact mem_pull.1 hy
  g y J J' hj hj' := by subst e; exact (gm_pull_g L h (𝟙 _) y J J' hj hj').trans (by rw [Category.id_comp])
def chartPullLinComb (L : LB X) (F : X' ⟶ X) {K : Type} [Fintype K] (φ' : K → (Y' ⟶ X')) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (h : Y' ⟶ Y) (hc : ∀ k, φ' k ≫ F = h ≫ φ k) : ChartPull (LB.LinComb (L.pull F) φ' ε) (LB.LinComb L φ ε) h :=
  have le : ∀ j : K → PUnit → L.ι, LB.wchart (L.pull F) φ' j ≤ h ⁻¹ᵁ LB.wchart L φ (fun k => j k PUnit.unit) :=
    fun j y hy => Set.mem_iInter.2 fun k => by
      have := mem_pull.1 (Set.mem_iInter.1 hy k)
      show φ k (h y) ∈ L.U (j k PUnit.unit)
      rw [pt_eq hc]; exact this
  { idx := fun j k => j k PUnit.unit
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb (L.pull F) φ' ε (𝟙 Y') y j j' hj hj').trans
        (Eq.trans (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_)
          (gm_linComb L φ ε h y _ _ (le j hj) (le j' hj')).symm)
      refine (gm_pull_g L F (𝟙 Y' ≫ φ' k) y (j k) (j' k) (Set.mem_iInter.1 hj k) (Set.mem_iInter.1 hj' k)).trans ?_
      rw [Category.id_comp, hc] }
end Chart
section Grp
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
theorem psum_hom {T : Over S} {T' : Over S'} (ρ : (T' ⟶ G') →* (T ⟶ G)) {n : ℕ} (x : Fin n → (T' ⟶ G'))
    (I : Finset (Fin n)) : ρ (psum G' x I) = psum G (fun i => ρ (x i)) I := by
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => exact map_one ρ
  | cons k l ih => exact (map_mul ρ _ _).trans (congrArg (ρ (x k) * ·) ih)
omit [IsCommMonObj G] [IsCommMonObj G'] in

def pushHom (h : IsGrpPullback G' G f φ) (T : Over S') : (T ⟶ G') →* (Over.mk (T.hom ≫ f) ⟶ G) :=
  MonoidHom.mk' (pushPt h.1.w) fun x y => Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm
omit [IsCommMonObj G] in

def preHom {T T' : Over S} (U : T' ⟶ T) : (T ⟶ G) →* (T' ⟶ G) :=
  MonoidHom.mk' (U ≫ ·) fun x y => MonObj.comp_mul U x y
theorem psum_push (h : IsGrpPullback G' G f φ) {T' : Over S'} {T : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ G'))
    (x : Fin n → (T ⟶ G)) (U : Over.mk (T'.hom ≫ f) ⟶ T) (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i)
    (I : Finset (Fin n)) : (psum G' x' I).left ≫ φ = U.left ≫ (psum G x I).left := by
  have e : pushPt h.1.w (psum G' x' I) = U ≫ psum G x I :=
    (psum_hom (pushHom h T') x' I).trans ((congrArg (fun z => psum G z I) (funext hx)).trans
      (psum_hom (preHom U) x I).symm)
  exact congrArg (fun z => z.left) e
def cubeMapOf (h : IsGrpPullback G' G f φ) : CubeMap G' G where
  F := φ
  F3 := (lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2)))).left
  e := f
  e_comm := by
    have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
    have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
    rw [e₁] at e
    refine e.trans ?_
    show (toUnit _ ≫ η[G]).left = _
    simp [eSec]
  psum_comm I := psum_push h _ _ _ (fun i => by fin_cases i <;> simp [x3]) I
end Grp
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
end ReciprocityTheory.ChartRestriction.G.Geo.Tor


