-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_TorusGraphMaps
-- name    : Development_AbelianVarietyTheory_BlockTheory_CMModuli_TorusGraphMaps
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:36.466374+00:00
-- url     : https://prove2.me/theorems/955da291-a7a1-4697-8c34-e80c3f85fa43
-- title:
--   Torus Graph Maps
-- statement:
--   Definitions and structural lemmas for Torus Graph Maps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/TorusGraphMaps.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtPtBridgeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
section Prim
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]
def graphφ (f : A ⟶ A) : Fin 5 → (A.left ⟶ A.left) :=
  ![(padd A (𝟙 A) f).left, 𝟙 A.left, f.left, (toUnit A ≫ η[A]).left, 𝟙 A.left]
def graphε : Fin 5 → ℤ := ![1, -1, -1, 1, -1]
end Prim
variable {R : Type} [CommRing R] [IsDomain R]
section Data
variable {O : Type} [Ring O] [StarRing O] {D : DegPre R} [Module O D.X]
def IsRigGraphIso (D : DegPre R) (f : D.P.A ⟶ D.P.A)
    (v : LB.Gen (LB.LinComb D.P.L (graphφ D.P.A f) graphε)) : Prop :=
  v.IsGen ∧ LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ v (eSec D.P.A))
    (LB.invGen D.P.L _ _ D.rig)
def PsiThrough (ac : D.OAct O) (w : O) : Prop :=
  ∃ v : LB.Gen (LB.LinComb D.P.L (graphφ D.P.A (ac.onB.act w)) graphε),
    IsRigGraphIso D (ac.onB.act w) v ∧
    ∀ y : D.X, LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (D.tau y (w • y)) (LB.pullGen D.P.L _ _ v (D.xK y)))
      (D.psi y)
end Data
def PsiGenOn (D : DegPre R) (χ : D.X) (U : Set (Spec (CommRingCat.of R))) : Prop :=
  ∀ x ∈ U, ∃ (j : PUnit → D.P.L.ι) (V : (Spec (CommRingCat.of R)).Opens), x ∈ V ∧
    V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit) ∧
    ∃ (h : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j)
      (r : Γ(Spec (CommRingCat.of R), V)ˣ), pullU (jK R) V r = res h ((D.psi χ).s j)
section Points
variable {O : Type} [Ring O] [StarRing O] {D : DegPre R} [Module O D.X]
variable {F : Type} [Field F] [Algebra (FractionRing R) F]
def IsRigAdjIso (D : DegPre R) (f g : D.P.A ⟶ D.P.A)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)) : Prop :=
  u.IsGen ∧ LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L)
def GtSmul (ac : D.OAct O) (a : O) (g g' : GtPtF D F) : Prop :=
  g'.b = g.b ≫ ac.onB.act a ∧
    ∃ u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (ac.onB.act a) (ac.onB.act (star a))) rosatiε),
      IsRigAdjIso D (ac.onB.act a) (ac.onB.act (star a)) u ∧
      ∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _
        (LB.mulGen D.P.L _ _ _ _ (g'.s χ)
          (LB.pullGen D.P.L _ _ u (lift g.b (DegPre.cF D F χ)).left))
        (g.s (star a • χ))
def QkAdd {k : ℕ} (p p' p'' : QkPt D F k) : Prop :=
  ∃ q : QkPt D F k, q.y = p.y + p'.y ∧ GtPtF.IsAdd p.g p'.g q.g ∧ QkPt.Equiv D F q p''
def QkSmul (ac : D.OAct O) (a : O) {k : ℕ} (p p' : QkPt D F k) : Prop :=
  ∃ q : QkPt D F k, q.y = a • p.y ∧ GtSmul ac a p.g q.g ∧ QkPt.Equiv D F q p'
variable {F' : Type} [Field F'] [Algebra (FractionRing R) F']
abbrev specExt (σ : F →ₐ[FractionRing R] F') : (TF (R := R) F').left ⟶ (TF (R := R) F).left :=
  Spec.map (CommRingCat.ofHom (σ : F →+* F'))
def GtMap (σ : F →ₐ[FractionRing R] F') (g : GtPtF D F) (g' : GtPtF D F') : Prop :=
  g'.b.left = specExt σ ≫ g.b.left ∧
    ∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _ (g'.s χ) (LB.pullGen D.P.L _ _ (g.s χ) (specExt σ))
def QkMap (σ : F →ₐ[FractionRing R] F') {k : ℕ} (p : QkPt D F k) (p' : QkPt D F' k) : Prop :=
  ∃ q : QkPt D F' k, q.y = p.y ∧ GtMap σ p.g q.g ∧ QkPt.Equiv D F' q p'
end Points
section Host
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
lemma bar_bar (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply Subtype.ext
  have h1 := H.bar_eq (H.bar a)
  rw [H.bar_eq a, IsCMField.complexConj_apply_apply] at h1
  exact h1
@[reducible] def hostStar (H : Host E) : StarRing (𝓞 E) where
  star := H.bar
  star_involutive := bar_bar H
  star_mul := fun a b => by
    change H.bar (a * b) = H.bar b * H.bar a
    rw [map_mul, _root_.mul_comm]
  star_add := fun a b => map_add H.bar a b
def PsiThroughHost (H : Host E) {D : DegPre R} [Module (𝓞 E) D.X]
    (ac : letI := hostStar H; D.OAct (𝓞 E)) : Prop :=
  letI := hostStar H; PsiThrough ac H.w0
end Host
end GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps


