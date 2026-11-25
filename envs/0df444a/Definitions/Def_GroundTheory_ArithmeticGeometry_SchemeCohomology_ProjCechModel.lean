-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjCechModel
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjCechModel
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:06:40.42585+00:00
-- url     : https://prove2.me/theorems/73b3c7e9-d682-4bc7-82ca-0150e33a50bb
-- title:
--   Proj Cech Model
-- statement:
--   Definitions and structural lemmas for Proj Cech Model, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjCechModel.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjLaurent
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_X_mem
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_awayToLaurent_injective
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_inter_stdOpen
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_mem_LDeg_iff
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_xprod_mem
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_xprod_succ
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_ext
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_toSection_bijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite MvPolynomial
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
namespace ProjSpace
variable {A : Type u} [CommRing A] {n : ℕ}
variable (A n) in

abbrev twistAb (k : ℤ) : (Opens (projectiveSpace A n).toTopCat)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (modulesAb (twistingSheaf (grading A n) k)).obj
def awayDegEquiv {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) (k : ℤ) :
    ProjTwist.awayDeg (grading A n) (xprod_mem i) (Nat.succ_pos p) k ≃+ LDeg A (Set.range i) k :=
  AddEquiv.ofBijective
    ({ toFun z := ⟨awayToLaurent i z.1, (mem_LDeg_iff i k _).2 ⟨z.1, z.2, rfl⟩⟩
       map_zero' := Subtype.ext (map_zero _)
       map_add' _ _ := Subtype.ext (map_add _ _ _) } :
      ProjTwist.awayDeg (grading A n) (xprod_mem i) (Nat.succ_pos p) k →+ LDeg A (Set.range i) k)
    ⟨fun z z' h => Subtype.ext (awayToLaurent_injective i (congrArg Subtype.val h)),
      fun ℓ => by
        obtain ⟨z, hz, h⟩ := (mem_LDeg_iff i k ℓ.1).1 ℓ.2
        exact ⟨⟨z, hz⟩, Subtype.ext h⟩⟩
def sectionEquiv {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) (k : ℤ) :
    ProjTwist.awayDeg (grading A n) (xprod_mem i) (Nat.succ_pos p) k ≃+
      Γ(twistingSheaf (grading A n) k, Proj.basicOpen (grading A n) (xprod i)) :=
  AddEquiv.ofBijective _ (ProjTwist.toSection_bijective (X_mem (i 0))
    (xprod_mem (i ∘ Fin.succ)) (xprod_succ i) (xprod_mem i) k)
def resEquiv {X : TopCat.{u}} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) {V W : Opens X} (h : V = W) :
    P.obj (op W) ≃+ P.obj (op V) where
  toFun := res P h.le
  invFun := res P h.ge
  left_inv x := by rw [res_res, res_refl]
  right_inv x := by rw [res_res, res_refl]
  map_add' := map_add _
variable (A n) in

abbrev cover : Fin (n + 1) → Opens (projectiveSpace A n).toTopCat := stdOpen A n
def theta {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) (k : ℤ) :
    LDeg A (Set.range i) k ≃+ (twistAb A n k).obj (op (inter (cover A n) i)) :=
  ((awayDegEquiv i k).symm.trans (sectionEquiv i k)).trans
    (resEquiv (twistAb A n k) (inter_stdOpen i))
lemma nmem_of_mem_inter {p : ℕ} {i : Fin (p + 1) → Fin (n + 1)}
    (x : inter (cover A n) i) : xprod (A := A) i ∉ x.1.asHomogeneousIdeal := by
  have hx : x.1 ∈ Proj.basicOpen (grading A n) (xprod i) := by
    rw [← inter_stdOpen]
    exact x.2
  exact hx
def lval {k : ℤ} {p : ℕ} (σ : Cochain (twistAb A n k) (cover A n) p) (i : Fin (p + 1) → Fin (n + 1)) :
    Laurent A n :=
  ((theta i k).symm (σ i)).1
lemma lval_mem {k : ℤ} {p : ℕ} (σ : Cochain (twistAb A n k) (cover A n) p)
    (i : Fin (p + 1) → Fin (n + 1)) : lval σ i ∈ LDeg A (Set.range i) k :=
  ((theta i k).symm (σ i)).2
def ofL {k : ℤ} {p : ℕ} (f : ∀ i : Fin (p + 1) → Fin (n + 1), LDeg A (Set.range i) k) :
    Cochain (twistAb A n k) (cover A n) p :=
  fun i => theta i k (f i)
end ProjSpace
end
end GroundTheory.Arith.SchemeCoh


