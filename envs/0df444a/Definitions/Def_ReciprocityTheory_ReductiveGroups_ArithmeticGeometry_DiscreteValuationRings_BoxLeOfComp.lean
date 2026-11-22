-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_BoxLeOfComp
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_BoxLeOfComp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:50:33.151524+00:00
-- url     : https://prove2.me/theorems/f4c50c58-b422-40a2-9484-af755f673a9b
-- title:
--   Box Le Of Comp
-- statement:
--   Definitions and structural lemmas for Box Le Of Comp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/BoxLeOfComp.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
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
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
section BoxSec
variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
abbrev prK (pG : IsPowGrp G' G j) (i : Fin j) : pullback G'.hom (jK R) ⟶ pullback G.hom (jK R) :=
  ((Over.pullback (jK R)).map (pG.pr i)).left
lemma prK_fst (pG : IsPowGrp G' G j) (i : Fin j) :
    prK pG i ≫ pullback.fst G.hom (jK R) = pullback.fst G'.hom (jK R) ≫ (pG.pr i).left := by
  simp only [prK, Over.pullback_map_left]
  exact pullback.lift_fst _ _ _
variable {LG : LB G.left} {LG' : LB G'.left}
lemma boxSec_le_a (pG : IsPowGrp G' G j) (jN : Fin j → LG.ι) (jL : LG'.ι) :
    pullback.fst G'.hom (jK R) ⁻¹ᵁ (LB.div (boxLB LG pG.pr) LG').U (jN, jL) ≤
      LB.wchart LG' (fun _ : Fin 1 => pullback.fst G'.hom (jK R)) (fun _ => jL) :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy.2
lemma boxSec_le_b (pG : IsPowGrp G' G j) (jN : Fin j → LG.ι) (jL : LG'.ι) (i : Fin j) :
    pullback.fst G'.hom (jK R) ⁻¹ᵁ (LB.div (boxLB LG pG.pr) LG').U (jN, jL) ≤
      prK pG i ⁻¹ᵁ LB.wchart LG (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => jN i) := by
  intro y hy
  have h := Set.mem_iInter.1 hy.1 i
  refine Set.mem_iInter.2 fun _ => ?_
  show (pullback.fst G.hom (jK R)).base ((prK pG i).base y) ∈ (LG.U (jN i) : Set G.left)
  rw [← Scheme.Hom.comp_apply, prK_fst, Scheme.Hom.comp_apply]
  exact h
def IsBoxSecK (pG : IsPowGrp G' G j) (w : LB.Iso LG' (boxLB LG pG.pr)) (k : ℕ)
    (s' : LB.Sec (LB.LinComb LG' (K := Fin 1) (fun _ => pullback.fst G'.hom (jK R))
      (fun _ => (k : ℤ))))
    (s : Fin j → LB.Sec (LB.LinComb LG (K := Fin 1) (fun _ => pullback.fst G.hom (jK R))
      (fun _ => (k : ℤ)))) : Prop :=
  ∀ (jN : Fin j → LG.ι) (jL : LG'.ι),
    ((pullU (Y := pullback G'.hom (jK R)) (pullback.fst G'.hom (jK R)) _ (w.s (jN, jL))) ^ k).val *
      ((pullback G'.hom (jK R)).presheaf.map (homOfLE (boxSec_le_a pG jN jL)).op).hom
        (s'.f (fun _ => jL)) =
    ∏ i, ((pullback G'.hom (jK R)).presheaf.map (homOfLE (boxSec_le_b pG jN jL i)).op).hom
      (((prK pG i).app _).hom ((s i).f (fun _ => jN i)))
end BoxSec
section BoxFam
lemma box_le_of_comp {X X' Y Y' : Scheme.{0}} (L : LB X) {j : ℕ} {Kx : Type} [Fintype Kx]
    (pr : Fin j → (X' ⟶ X)) (φ' : Kx → (Y' ⟶ X')) (φ : Kx → (Y ⟶ X)) (p : Y' ⟶ Y) (i : Fin j)
    (hφ : ∀ a, φ' a ≫ pr i = p ≫ φ a) (jN : Kx → Fin j → L.ι) :
    LB.wchart (LB.LinComb L pr (fun _ => 1)) φ' jN ≤ p ⁻¹ᵁ LB.wchart L φ (fun a => jN a i) := by
  intro y hy
  refine Set.mem_iInter.2 fun a => ?_
  have h1 := Set.mem_iInter.1 hy a
  have h2 := Set.mem_iInter.1 h1 i
  show (φ a).base (p.base y) ∈ (L.U (jN a i) : Set X)
  rw [← Scheme.Hom.comp_apply, ← hφ a, Scheme.Hom.comp_apply]
  exact h2
variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ}
abbrev prB {D' D : DegPre R} (pD : IsPowDeg D' D j) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (i : Fin j) :
    (DegPre.BF D' F).left ⟶ (DegPre.BF D F).left :=
  (TF (R := R) F ◁ pD.pw.pr i).left
def IsBoxFam {D' D : DegPre R} (pD : IsPowDeg D' D j) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (F' : Fam D' F k) (Fs : Fin j → Fam D F k) : Prop :=
  ∀ α' : D'.X, ∃ hφ : ∀ (i : Fin j) (a : Fin 4),
      DegPre.famφ D' F α' a ≫ (pD.pw.pr i).left = prB pD F i ≫ DegPre.famφ D F (pD.xe α' i) a,
    ∀ (jN : Fin 4 → Fin j → D.P.L.ι) (jM : Fin 4 → D'.P.L.ι),
      (@id (Γ((DegPre.BF D' F).left, LB.wchart (boxLB D.P.L pD.pw.pr) (DegPre.famφ D' F α') jN ⊓
          LB.wchart D'.P.L (DegPre.famφ D' F α') jM)ˣ)
        ((LB.linCombIso pD.w (DegPre.famφ D' F α') (DegPre.famε k)).s (jN, jM))).val *
        ((DegPre.BF D' F).left.presheaf.map (homOfLE (inf_le_right :
          LB.wchart (boxLB D.P.L pD.pw.pr) (DegPre.famφ D' F α') jN ⊓
            LB.wchart D'.P.L (DegPre.famφ D' F α') jM ≤
          LB.wchart D'.P.L (DegPre.famφ D' F α') jM)).op).hom ((F'.s α').f jM) =
      ∏ i, ((DegPre.BF D' F).left.presheaf.map (homOfLE (inf_le_left.trans
          (box_le_of_comp D.P.L (fun i => (pD.pw.pr i).left) (DegPre.famφ D' F α')
            (DegPre.famφ D F (pD.xe α' i)) (prB pD F i) i (hφ i) jN) :
          LB.wchart (boxLB D.P.L pD.pw.pr) (DegPre.famφ D' F α') jN ⊓
            LB.wchart D'.P.L (DegPre.famφ D' F α') jM ≤
          prB pD F i ⁻¹ᵁ LB.wchart D.P.L (DegPre.famφ D F (pD.xe α' i)) (fun a => jN a i))).op).hom
        (((prB pD F i).app _).hom (((Fs i).s (pD.xe α' i)).f (fun a => jN a i)))
end BoxFam
section Prod
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {j : ℕ} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {pD : IsPowDeg D'.toPre D.toPre j} {pA : IsPowPolAV A' A j} {pG : IsPowGrp G' G j}
  {U' : Unif I D' A' G'} {U : Unif I D A G}
end Prod
section BoxQ
variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ}
def IsBoxGtF {D' D : DegPre R} (pD : IsPowDeg D' D j) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (g' : GtPtF D' F) (g : Fin j → GtPtF D F) : Prop :=
  (∀ i, g'.b ≫ pD.pw.pr i = (g i).b) ∧
    ∀ χ' : D'.X, ∃ hψ : ∀ (i : Fin j) (a : Fin 4),
        DegPre.gtφ D' F g'.b χ' a ≫ (pD.pw.pr i).left =
          𝟙 _ ≫ DegPre.gtφ D F (g i).b (pD.xe χ' i) a,
      LB.Gen.Maps (LB.linCombIso pD.w _ DegPre.gtε) (g'.s χ')
        (GeneratorPullback.boxGen D.P.L (fun i => (pD.pw.pr i).left) _ DegPre.gtε (fun i =>
          GeneratorPullback.pullAlong D.P.L (pD.pw.pr i).left (𝟙 _) _ DegPre.gtε _ (hψ i)
            ((g i).s (pD.xe χ' i))))
def IsBoxQk {D' D : DegPre R} (pD : IsPowDeg D' D j) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (p' : QkPt D' F k) (p : Fin j → QkPt D F k) : Prop :=
  pD.xe p'.y = (fun i => (p i).y) ∧ IsBoxGtF pD F p'.g (fun i => (p i).g)
end BoxQ
section ProdMap
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {j : ℕ} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {pD : IsPowDeg D'.toPre D.toPre j} {pA : IsPowPolAV A' A j} {pG : IsPowGrp G' G j}
  {U' : Unif I D' A' G'} {U : Unif I D A G}
end ProdMap
end ReciprocityTheory.ChartRestriction.G.DVR


