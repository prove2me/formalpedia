-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:25:22.712571+00:00
-- url     : https://prove2.me/theorems/9d0d1789-5457-4bb9-bbad-4e655ffab3ee
-- title:
--   Lin Comb Triv G
-- statement:
--   Definitions and structural lemmas for Lin Comb Triv G, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/LinCombTrivG.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Out.Inh
open Semi
instance geomConn_id (S : Scheme.{0}) : GeometricallyConnected (𝟙 S) := by
  rw [geometricallyConnected_iff]
  intro K _ y Z fst snd h
  have h' : IsPullback y (𝟙 _) (𝟙 S) y := IsPullback.of_vert_isIso ⟨by simp⟩
  let e : Z ≅ Spec (CommRingCat.of K) := h.isoIsPullback _ _ h'
  exact (Scheme.homeoOfIso e.symm).surjective.connectedSpace (Scheme.homeoOfIso e.symm).continuous
def trivLB (X : Scheme.{0}) : LB X := ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩
theorem trivLB_isLB (X : Scheme.{0}) : (trivLB X).IsLB where
  cover := by simp [trivLB]
  g_self := fun _ => map_one _
  cocycle := fun _ _ _ => by
    erw [map_one]; (try erw [map_one]); (try erw [map_one]); exact _root_.one_mul _
theorem linComb_triv_g {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (j j' : (LB.LinComb (trivLB X) φ ε).ι) : (LB.LinComb (trivLB X) φ ε).g j j' = 1 := by
  have hg : ∀ a b, (trivLB X).g a b = 1 := fun _ _ => rfl
  apply Finset.prod_eq_one
  intro k _
  rw [hg, map_one]
  first
    | exact (congrArg (· ^ ε k) (map_one _)).trans (one_zpow _)
    | (erw [map_one, one_zpow])
theorem powOver_triv_g {S : Scheme.{0}} (A : Over S) (U : S.Opens) (N : ℕ)
    (j j' : (powOver A (trivLB A.left) U N).ι) : (powOver A (trivLB A.left) U N).g j j' = 1 :=
  linComb_triv_g _ _ j j'
theorem surj_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (D : X.Opens) (hD : D = ⊤)
    (e : D ≤ f ⁻¹ᵁ ⊤) : Function.Surjective (f.appLE ⊤ D e).hom := by
  subst hD
  have h1 : IsIso (homOfLE e) := ⟨⟨homOfLE le_top, rfl, rfl⟩⟩
  have h2 : IsIso (f.appLE ⊤ ⊤ e) := by
    first
      | (rw [Scheme.Hom.appLE]; infer_instance)
      | (show IsIso (f.app ⊤ ≫ X.presheaf.map (homOfLE e).op); infer_instance)
  first
    | exact (ConcreteCategory.bijective_of_isIso (f.appLE ⊤ ⊤ e)).2
    | exact (asIso (f.appLE ⊤ ⊤ e)).commRingCatIsoToRingEquiv.surjective
variable (S : Scheme.{0})
def zeroPolAV : PolAV S where
  A := 𝟙_ (Over S)
  isAb :=
    { comm := inferInstance
      smooth := by show Smooth (𝟙 S); infer_instance
      proper := by show IsProper (𝟙 S); infer_instance
      geomConnected := by show GeometricallyConnected (𝟙 S); infer_instance }
  g := 0
  smoothDim := by show SmoothOfRelativeDimension 0 (𝟙 S); infer_instance
  L := trivLB _
  isLB := trivLB_isLB _
  rigid := ⟨⟨fun _ => 1⟩, by
    intro i j; rw [linComb_triv_g, _root_.one_mul]; dsimp only; repeat erw [map_one]
    all_goals rfl⟩
  sym := fun _ => ⟨⊤, trivial, ⟨fun _ => 1⟩, by
    intro i j; rw [linComb_triv_g, _root_.one_mul]; dsimp only; repeat erw [map_one]
    all_goals rfl⟩
  ample := by
    intro U hU
    haveI : IsIso (𝟙_ (Over S)).hom := by show IsIso (𝟙 S); infer_instance
    let Y := ((𝟙_ (Over S)).hom ⁻¹ᵁ U).toScheme
    let s0 : LB.Sec (powOver (𝟙_ (Over S)) (trivLB _) U 1) :=
      ⟨fun _ => 1, by
        intro i j; rw [powOver_triv_g, Units.val_one, _root_.one_mul]; repeat erw [map_one]
        all_goals rfl⟩
    have hD : nonzeroLocus s0 = ⊤ := by
      apply top_unique
      intro x _
      simp only [nonzeroLocus, s0, Scheme.basicOpen_one]
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => PUnit.unit, by
        simp only [powOver, LB.LinComb, LB.wchart, trivLB]
        exact Set.mem_iInter.2 fun _ => trivial⟩
    refine ⟨1, le_rfl, 0, fun _ => s0, by simp only [iSup_const]; exact hD,
      fun _ => ⟨?_, fun _ => 1, ?_, ?_⟩⟩
    · rw [hD]
      have : IsAffine Y := hU
      exact isAffineOpen_top Y
    · intro j k
      erw [map_one]; (try erw [map_one]); (try erw [map_one]); exact (_root_.mul_one _).symm
    · intro p
      obtain ⟨a, rfl⟩ := surj_appLE ((𝟙_ (Over S)).hom ∣_ U) _ hD le_top p
      exact ⟨MvPolynomial.C a, MvPolynomial.eval₂Hom_C _ _ _⟩
  ktriv := fun _ _ _ x _ => toUnit_unique x _
end ReciprocityTheory.ChartRestriction.G.Out.Inh


