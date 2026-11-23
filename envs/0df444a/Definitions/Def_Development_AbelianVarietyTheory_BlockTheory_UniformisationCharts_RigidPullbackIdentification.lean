-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_RigidPullbackIdentification
-- name    : Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_RigidPullbackIdentification
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:29.435811+00:00
-- url     : https://prove2.me/theorems/688a9db3-82d2-48b5-b082-09e39e72c302
-- title:
--   Rigid Pullback Identification
-- statement:
--   Definitions and structural lemmas for Rigid Pullback Identification, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/RigidPullbackIdentification.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
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
namespace GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
section Carries
variable {X X' Y : Scheme.{0}} (L : LB X) (L' : LB X') (F : X' ⟶ X)
lemma chart_le_target (p' : Y ⟶ X') (p : Y ⟶ X) (hp : p' ≫ F = p) (j : L.ι) (j' : L'.ι) :
    p' ⁻¹ᵁ (LB.div (L.pull F) L').U (fun _ => j, j') ≤
      LB.wchart L (fun _ : PUnit => p) (fun _ => j) := by
  intro y hy
  refine Set.mem_iInter.2 fun _ => ?_
  have h1 : p'.base y ∈ LB.wchart L (fun _ : PUnit => F) (fun _ => j) := hy.1
  have h2 : F.base (p'.base y) ∈ L.U j := Set.mem_iInter.1 h1 PUnit.unit
  subst hp
  exact h2
lemma chart_le_source (p' : Y ⟶ X') (j : L.ι) (j' : L'.ι) :
    p' ⁻¹ᵁ (LB.div (L.pull F) L').U (fun _ => j, j') ≤
      LB.wchart L' (fun _ : PUnit => p') (fun _ => j') :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy.2
def CarriesAt (w : LB.Iso L' (L.pull F)) (p' : Y ⟶ X') (p : Y ⟶ X) (hp : p' ≫ F = p) (n : ℤ)
    (a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p') (fun _ => n)))
    (b : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))) : Prop :=
  ∀ (j : L.ι) (j' : L'.ι),
    res (chart_le_target L L' F p' p hp j j') (b.s (fun _ => j)) =
      (pullU p' _ (w.s (fun _ => j, j'))) ^ n *
        res (chart_le_source L L' F p' j j') (a.s (fun _ => j'))
end Carries
section Pull
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
abbrev specOf (φ : R →+* R') : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom φ)
lemma ptK_comp (φ : R →+* R') {B : Over (Spec (CommRingCat.of R))}
    {B' : Over (Spec (CommRingCat.of R'))} (F : B'.left ⟶ B.left)
    (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ B) (x' : 𝟙_ (Over (Spec (CommRingCat.of R'))) ⟶ B')
    (hx : x'.left ≫ F = specOf φ ≫ x.left) (W : (Spec (CommRingCat.of R)).Opens)
    (g : (TK R').left ⟶ (TW W).left) (hg : g ≫ W.ι = jK R' ≫ specOf φ) :
    ptK x' ≫ F = g ≫ (toUnit (TW W) ≫ x).left := by
  have h1 : ptK x' = jK R' ≫ x'.left := rfl
  have h2 : (toUnit (TW W) ≫ x).left = W.ι ≫ x.left := rfl
  rw [h1, h2]
  calc (jK R' ≫ x'.left) ≫ F = jK R' ≫ (x'.left ≫ F) := Category.assoc _ _ _
    _ = jK R' ≫ (specOf φ ≫ x.left) := by rw [hx]
    _ = (jK R' ≫ specOf φ) ≫ x.left := (Category.assoc _ _ _).symm
    _ = (g ≫ W.ι) ≫ x.left := by rw [hg]
    _ = g ≫ W.ι ≫ x.left := Category.assoc _ _ _
structure PullIdent (φ : R →+* R') (D : DegPre R) (D' : DegPre R') where
  F : D'.P.A.left ⟶ D.P.A.left
  cart : IsPullback F D'.P.A.hom D.P.A.hom (specOf φ)
  F_one : eSec D'.P.A ≫ F = specOf φ ≫ eSec D.P.A
  F_mul : (μ[D'.P.A]).left ≫ F =
    pullback.map D'.P.A.hom D'.P.A.hom D.P.A.hom D.P.A.hom F F (specOf φ) cart.w.symm cart.w.symm ≫
      (μ[D.P.A]).left
  w : LB.Iso D'.P.L (D.P.L.pull F)
  w_gen : w.IsGen
  w_rig : CarriesAt D.P.L D'.P.L F w (eSec D'.P.A) (specOf φ ≫ eSec D.P.A) F_one 1 D'.rig
    (LB.pullGen D.P.L _ _ D.rig (specOf φ))
  xe : D'.X ≃+ D.X
  c_eq : ∀ χ : D'.X, (D'.c χ).left ≫ F = specOf φ ≫ (D.c (xe χ)).left
  w_psi : ∃ (W : (Spec (CommRingCat.of R)).Opens) (ψW : PsiOn D W)
    (g : (TK R').left ⟶ (TW W).left) (hg : g ≫ W.ι = jK R' ≫ specOf φ),
    ∀ χ : D'.X, CarriesAt D.P.L D'.P.L F w (D'.xK χ) (g ≫ (toUnit (TW W) ≫ D.c (xe χ)).left)
      (ptK_comp φ F (D.c (xe χ)) (D'.c χ) (c_eq χ) W g hg) (-1) (D'.psi χ)
      (LB.pullGen D.P.L _ _ (ψW.psi (xe χ)) g)
example (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (h : PullIdent φ D D') :
    D'.rank = D.rank :=
  h.xe.toIntLinearEquiv.finrank_eq
example (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (h : PullIdent φ D D') :
    ∃ W : (Spec (CommRingCat.of R)).Opens, Nonempty (PsiOn D W) ∧ Nonempty W.toScheme := by
  obtain ⟨W, ψW, g, -, -⟩ := h.w_psi
  have p : (Spec (CommRingCat.of (FractionRing R'))) := (⊥ : PrimeSpectrum (FractionRing R'))
  exact ⟨W, ⟨ψW⟩, ⟨g.base p⟩⟩
end Pull
end GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification


