-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsRosatiGen
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsRosatiGen
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-27T06:19:09.272498+00:00
-- url     : https://prove2.me/theorems/ef7805c2-2807-496b-868f-37fa99d67ff6
-- title:
--   Exists Rosati Gen
-- statement:
--   Definitions and structural lemmas for Exists Rosati Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExistsRosatiGen.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_genHasVal_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_genHasVal_invGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_genHasVal_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_genHasVal_mulGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_genHasVal_pullGen_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_genHasVal_unique

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
namespace ReciprocityTheory.ChartRestriction.G.DVR.QForm
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  (D : DegData V (maximalIdeal V))
variable {Q : D.toPre.X → ℤ}
instance (P : PolAV (Spec (CommRingCat.of V))) : IsSeparated P.A.hom := by
  have : IsProper P.A.hom := P.isAb.proper
  infer_instance
lemma over_sec {Y B : Over (Spec (CommRingCat.of V))} (q : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ Y) (f : Y ⟶ B) :
    (q.left ≫ f.left) ≫ B.hom = 𝟙 _ := by
  rw [Category.assoc, Over.w f]
  first
  | simpa using Over.w q
  | exact Over.w q
lemma sumElim_sec {Y : Scheme.{0}} {Ix Ix' : Type} {f : Ix → (Spec (CommRingCat.of V) ⟶ Y)}
    {g : Ix' → (Spec (CommRingCat.of V) ⟶ Y)} {s : Y ⟶ Spec (CommRingCat.of V)}
    (hf : ∀ k, f k ≫ s = 𝟙 _) (hg : ∀ k, g k ≫ s = 𝟙 _) : ∀ k, Sum.elim f g k ≫ s = 𝟙 _ := by
  rintro (k | k) <;> simp [hf, hg]
theorem rigK_val : GenHasVal ϖ D.toPre.P.L (fun _ : PUnit => 𝟙 _ ≫ eSec D.toPre.P.A)
    (fun _ => (toUnit (TK V)).left ≫ eSec D.toPre.P.A) (fun _ => by rw [Category.id_comp]; rfl) (fun _ => 1)
    D.toPre.rigK 0 :=
  genHasVal_pullGen_of (ϖ := ϖ) D.toPre.P.L _ _ D.toPre.rig D.toPre.rig_gen (𝟙 _) (toUnit (TK V)).left
    (by rw [Category.comp_id]; rfl)
include hϖ in

theorem tau_val (hQ : IsQ D.toPre ϖ Q) (a b : D.toPre.X) :
    ∃ (φ : _) (hφ : _), (∀ k, φ k ≫ D.toPre.P.A.hom = 𝟙 _) ∧
      GenHasVal ϖ D.toPre.P.L φ _ hφ _ (D.toPre.tau a b) (bOf D.toPre Q a b) := by
  have hL := D.toPre.P.isLB
  have h1 := genHasVal_mulGen hϖ D.toPre.P.L hL _ _ _ _ _ _ _ _ _ _ (hQ (a + b))
    (genHasVal_invGen D.toPre.P.L hL _ _ _ _ _ (hQ a))
  have h2 := genHasVal_mulGen hϖ D.toPre.P.L hL _ _ _ _ _ _ _ _ _ _ h1
    (genHasVal_invGen D.toPre.P.L hL _ _ _ _ _ (hQ b))
  have h3 := genHasVal_mulGen hϖ D.toPre.P.L hL _ _ _ _ _ _ _ _ _ _ h2
    (genHasVal_invGen D.toPre.P.L hL _ _ _ _ _ (rigK_val D))
  have h4 : Q (a + b) + -Q a + -Q b + -0 = bOf D.toPre Q a b := by simp only [bOf]; ring
  rw [h4] at h3
  exact ⟨_, _, by (simp [Sum.forall, Fin.forall_fin_succ, Over.w, Over.w_assoc, eSec, Matrix.cons_val_zero, Matrix.cons_val_succ]), h3⟩
include hϖ in

theorem bOf_add_left (hQ : IsQ D.toPre ϖ Q) (a a' b : D.toPre.X) :
    bOf D.toPre Q (a + a') b = bOf D.toPre Q a b + bOf D.toPre Q a' b := by
  have hL := D.toPre.P.isLB
  obtain ⟨_, _, hsA, hA⟩ := tau_val hϖ D hQ (a + a') b
  obtain ⟨_, _, hsB, hB⟩ := tau_val hϖ D hQ a b
  obtain ⟨_, _, hsC, hC⟩ := tau_val hϖ D hQ a' b
  have hcub := genHasVal_pullGen_of (ϖ := ϖ) D.toPre.P.L _ _ D.toPre.cub.t D.toPre.cub.isGen
    (lift (D.toPre.c a) (lift (D.toPre.c a') (D.toPre.c b))).left (D.toPre.pt3 a a' b)
    (by simp [DegPre.pt3, ← CartesianMonoidalCategory.comp_lift])
  have h1 := genHasVal_mulGen hϖ D.toPre.P.L hL _ _ _ _ _ _ _ _ _ _ hA hcub
  have h2 := genHasVal_mulGen hϖ D.toPre.P.L hL _ _ _ _ _ _ _ _ _ _ hB hC
  have := genHasVal_unique hϖ D.toPre.P.L hL _ _ _ _ _
    (genHasVal_corr hϖ D.toPre.P.L hL D.toPre.P.A.hom _ _ _ _ _ _ _ _
      (sumElim_sec hsA (fun _ => over_sec _ _)) (sumElim_sec hsB hsC) _ _
      (genHasVal_isGen D.toPre.P.L _ _ _ _ _ h2) (D.tau_bimult a a' b) h1) h2
  linarith
theorem bOf_comm (χ χ' : D.toPre.X) : bOf D.toPre Q χ χ' = bOf D.toPre Q χ' χ := by
  unfold bOf
  rw [add_comm χ χ']
  ring
include hϖ in

def bHom (hQ : IsQ D.toPre ϖ Q) : D.toPre.X →+ D.toPre.X →+ ℤ :=
  AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun b => bOf D.toPre Q a b) (fun b b' => by
      rw [bOf_comm D (Q := Q) a (b + b'), bOf_add_left hϖ D hQ, bOf_comm D (Q := Q) b a,
        bOf_comm D (Q := Q) b' a]))
    (fun a a' => by ext b; simp [bOf_add_left hϖ D hQ])
end ReciprocityTheory.ChartRestriction.G.DVR.QForm


