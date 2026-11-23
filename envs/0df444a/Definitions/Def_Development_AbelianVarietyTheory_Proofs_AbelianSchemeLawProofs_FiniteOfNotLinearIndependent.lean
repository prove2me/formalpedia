-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteOfNotLinearIndependent
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteOfNotLinearIndependent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:47:08.154148+00:00
-- url     : https://prove2.me/theorems/c1baa90f-db42-425b-8d30-8f7e8f07c08a
-- title:
--   Finite Of Not Linear Independent
-- statement:
--   Definitions and structural lemmas for Finite Of Not Linear Independent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteOfNotLinearIndependent.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIndepSections
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_lcg_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_lcg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_res

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
namespace GlobalTheory.SecGrowth
section Poly
variable {σ R A : Type} [CommRing R] [CommRing A]
theorem eval₂Hom_mul_of_isHomogeneous (c : R →+* A) (u : A) (x : σ → A) {F : MvPolynomial σ R} {t : ℕ}
    (hF : F.IsHomogeneous t) :
    MvPolynomial.eval₂Hom c (fun j => u * x j) F = u ^ t * MvPolynomial.eval₂Hom c x F := by
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [hF.degree_eq_sum_deg_support hd]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring
end Poly
section Sections
variable {X : Scheme.{0}}
theorem rs_eval₂Hom {R σ : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) {U V : X.Opens} (h : V ≤ U)
    (x : σ → Γ(X, U)) (F : MvPolynomial σ R) :
    rs X h (MvPolynomial.eval₂Hom (cst f U) x F) = MvPolynomial.eval₂Hom (cst f V) (fun j => rs X h (x j)) F := by
  rw [MvPolynomial.map_eval₂Hom]
  congr 2
  exact RingHom.ext fun r => rs_cst f h r
def polySec {R σ : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) {H : LB X} (s : σ → LB.Sec H)
    {t : ℕ} {F : MvPolynomial σ R} (hF : F.IsHomogeneous t) : LB.Sec (pw H t) where
  f := fun k => MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k) F
  compat := fun k l => by
    have h₁ := rs_eval₂Hom f (inf_le_left : H.U k ⊓ H.U l ≤ H.U k) (fun j => (s j).f k) F
    have h₂ := rs_eval₂Hom f (inf_le_right : H.U k ⊓ H.U l ≤ H.U l) (fun j => (s j).f l) F
    have h₃ : (fun j => rs X (inf_le_left : H.U k ⊓ H.U l ≤ H.U k) ((s j).f k)) =
        fun j => (H.g k l).val * rs X (inf_le_right : H.U k ⊓ H.U l ≤ H.U l) ((s j).f l) :=
      funext fun j => (s j).compat k l
    rw [h₃, eval₂Hom_mul_of_isHomogeneous _ _ _ hF, ← h₂] at h₁
    refine h₁.trans (congrArg₂ (· * ·) ?_ rfl)
    change _ = ((H.g k l) ^ (t : ℤ)).val
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
def transSec {M M' : LB X} (a : M'.ι → M.ι) (ha : ∀ j, M'.U j ≤ M.U (a j))
    (hg : ∀ j j', M'.g j j' = res (inf_le_inf (ha j) (ha j')) (M.g (a j) (a j'))) (σ : LB.Sec M) : LB.Sec M' where
  f := fun j => rs X (ha j) (σ.f (a j))
  compat := fun j j' => by
    have h := congrArg (rs X (inf_le_inf (ha j) (ha j'))) (σ.compat (a j) (a j'))
    rw [map_mul] at h
    rw [hg]
    exact (rs_rs _ _ _).trans (((rs_rs _ _ _).symm.trans h).trans
      (congrArg₂ (· * ·) rfl ((rs_rs _ _ _).trans (rs_rs _ _ _).symm)))
end Sections
section Growth
end Growth
section Modules
end Modules
section Abelian
variable {X Y : Scheme.{0}} (L : LB X) (π : Y ⟶ X)
theorem wchart_le_one (j : PUnit → L.ι) :
    LB.wchart L (fun _ : PUnit => π) j ≤ LB.wchart L (fun _ : Fin 1 => π) (fun _ => j PUnit.unit) :=
  fun _ hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy PUnit.unit
theorem wchart_le_unit (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => π) j ≤ LB.wchart L (fun _ : PUnit => π) (fun _ => j 0) :=
  fun _ hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0
theorem lcg_pow_pow (N t : ℕ) (j j' : PUnit → L.ι) :
    (LB.lcg L (K := PUnit) (fun _ => π) (fun _ => 1) j j' ^ (N : ℤ)) ^ (t : ℤ) =
      res (inf_le_inf (wchart_le_one L π j) (wchart_le_one L π j'))
        (LB.lcg L (K := Fin 1) (fun _ => π) (fun _ => ((N * t : ℕ) : ℤ)) _ _) := by
  rw [LB.res_lcg, LB.lcg_pull, Fintype.prod_unique, ← zpow_mul, Nat.cast_mul]
theorem lcg_mul (N t : ℕ) (j j' : Fin 1 → L.ι) :
    LB.lcg L (K := Fin 1) (fun _ => π) (fun _ => ((N * t : ℕ) : ℤ)) j j' =
      res (inf_le_inf (wchart_le_unit L π j) (wchart_le_unit L π j'))
        ((LB.lcg L (K := PUnit) (fun _ => π) (fun _ => 1) _ _ ^ (N : ℤ)) ^ (t : ℤ)) := by
  rw [map_zpow, map_zpow, LB.lcg_pull, LB.res_res, LB.lcg, Fintype.prod_unique, ← zpow_mul, Nat.cast_mul]
  rfl
def toPw (N t : ℕ) (σ : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => ((N * t : ℕ) : ℤ)))) :
    LB.Sec (pw (pw (L.pull π) N) t) :=
  transSec (M := LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => ((N * t : ℕ) : ℤ)))
    (M' := pw (pw (L.pull π) N) t) (fun j _ => j PUnit.unit) (wchart_le_one L π) (lcg_pow_pow L π N t) σ
def ofPw (N t : ℕ) (σ : LB.Sec (pw (pw (L.pull π) N) t)) :
    LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => ((N * t : ℕ) : ℤ))) :=
  transSec (M := pw (pw (L.pull π) N) t)
    (M' := LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => ((N * t : ℕ) : ℤ)))
    (fun j _ => j 0) (wchart_le_unit L π) (lcg_mul L π N t) σ
end Abelian
end GlobalTheory.SecGrowth


