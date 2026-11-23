-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExp
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:45:31.736122+00:00
-- url     : https://prove2.me/theorems/ac355d1e-44f2-48a9-b90f-edf4f8416658
-- title:
--   Prod Exp
-- statement:
--   Definitions and structural lemmas for Prod Exp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ProdExp.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_BoxLeOfComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
section BoxG
variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {LG : LB G.left} {LG' : LB G'.left}
lemma boxG_le_b (pG : IsPowGrp G' G j) (jN : Fin j → LG.ι) (jL : LG'.ι) :
    (LB.div (boxLB LG pG.pr) LG').U (jN, jL) ≤ LB.wchart LG' (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL) := by
  unfold LB.div boxLB
  refine le_trans inf_le_right ?_
  intro x hx
  first
    | exact Set.mem_iInter.2 fun _ => hx
    | simpa [LB.wchart] using hx
lemma boxG_le_c (pG : IsPowGrp G' G j) (jN : Fin j → LG.ι) (jL : LG'.ι) (i : Fin j) :
    (LB.div (boxLB LG pG.pr) LG').U (jN, jL) ≤
      (pG.pr i).left ⁻¹ᵁ LB.wchart LG (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jN i) := by
  unfold LB.div boxLB
  refine le_trans inf_le_left (le_trans (LB.wchart_le LG _ jN i) ?_)
  intro x hx
  first
    | exact Set.mem_iInter.2 fun _ => hx
    | simpa [LB.wchart] using hx
def IsBoxSecG (pG : IsPowGrp G' G j) (w : LB.Iso LG' (boxLB LG pG.pr)) (k : ℕ) (σ' : H0 LG' k)
    (σ : Fin j → H0 LG k) : Prop :=
  ∀ (jN : Fin j → LG.ι) (jL : LG'.ι),
    ((w.s (jN, jL)) ^ k).val * rs (boxG_le_b pG jN jL) (σ'.f (fun _ => jL)) =
      ∏ i, rs (boxG_le_c pG jN jL i) (((pG.pr i).left.app _).hom ((σ i).f (fun _ => jN i)))
end BoxG
section BoxB
variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ}
def IsBoxFamB {D' D : DegPre R} (pD : IsPowDeg D' D j) (k : ℕ) (f' : ∀ α' : D'.X, D'.SecB k α')
    (f : Fin j → ∀ α : D.X, D.SecB k α) : Prop :=
  ∀ α' : D'.X, ∃ hφ : ∀ (i : Fin j) (a : Fin 4),
      D'.famφB α' a ≫ (pD.pw.pr i).left = (pD.pw.pr i).left ≫ D.famφB (pD.xe α' i) a,
    ∀ (jN : Fin 4 → Fin j → D.P.L.ι) (jM : Fin 4 → D'.P.L.ι),
      (@id (Γ(D'.P.A.left, LB.wchart (boxLB D.P.L pD.pw.pr) (D'.famφB α') jN ⊓
          LB.wchart D'.P.L (D'.famφB α') jM)ˣ)
        ((LB.linCombIso pD.w (D'.famφB α') (DegPre.famε k)).s (jN, jM))).val *
        rs (inf_le_right : LB.wchart (boxLB D.P.L pD.pw.pr) (D'.famφB α') jN ⊓
            LB.wchart D'.P.L (D'.famφB α') jM ≤ LB.wchart D'.P.L (D'.famφB α') jM) ((f' α').f jM) =
      ∏ i, rs (inf_le_left.trans (box_le_of_comp D.P.L (fun i => (pD.pw.pr i).left) (D'.famφB α')
            (D.famφB (pD.xe α' i)) (pD.pw.pr i).left i (hφ i) jN))
        (((pD.pw.pr i).left.app _).hom (((f i) (pD.xe α' i)).f (fun a => jN a i)))
end BoxB
section Exp
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {j : ℕ} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {pD : IsPowDeg D'.toPre D.toPre j} {pA : IsPowPolAV A' A j} {pG : IsPowGrp G' G j}
  {U' : Unif I D' A' G'} {U : Unif I D A G}
end Exp
end ReciprocityTheory.ChartRestriction.G.DVR


