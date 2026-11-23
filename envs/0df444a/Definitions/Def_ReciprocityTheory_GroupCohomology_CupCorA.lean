-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorA
-- name    : ReciprocityTheory_GroupCohomology_CupCorA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:26.449676+00:00
-- url     : https://prove2.me/theorems/9f7ff0f1-4d5a-4d7e-b8ad-51aea4c12cd2
-- title:
--   Cup Cor A
-- statement:
--   Definitions and structural lemmas for Cup Cor A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CupCorA.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_ContinuousContractNth
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Coh.CCA
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
section HomLemmas
variable {R : Type u} [CommRing R] {A B C : Cx R}
end HomLemmas
section Retr
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)
theorem mkR_eq {a b : G} :
    Quotient.mk (QuotientGroup.rightRel U) a = Quotient.mk _ b ↔ b * a⁻¹ ∈ U :=
  Quotient.eq.trans QuotientGroup.rightRel_apply
theorem retr_spec (g : G) : (retr U g : G) = g * (rep U g)⁻¹ := rfl
instance finite_rightRel [U.FiniteIndex] : Finite (Quotient (QuotientGroup.rightRel U)) :=
  Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel U).symm
def cosetMul (g : G) (c : Quotient (QuotientGroup.rightRel U)) : Quotient (QuotientGroup.rightRel U) :=
  Quotient.mk _ (c.out * g)
theorem cosetMul_bij (g : G) : Bijective (cosetMul U g) := by
  have key : ∀ h : G, ∀ c, cosetMul U h⁻¹ (cosetMul U h c) = c := by
    intro h c
    unfold cosetMul
    conv_rhs => rw [← Quotient.out_eq c]
    rw [mkR_eq]
    have hw : (c.out * h) * (Quotient.mk (QuotientGroup.rightRel U) (c.out * h)).out⁻¹ ∈ U :=
      QuotientGroup.rightRel_apply.mp (Quotient.mk_out (c.out * h))
    simpa [mul_inv_rev, mul_assoc] using hw
  exact ⟨Function.LeftInverse.injective (key g), Function.RightInverse.surjective (fun c => by
    simpa using key g⁻¹ c)⟩
theorem out_mul (g : G) (c : Quotient (QuotientGroup.rightRel U)) :
    c.out * g = (retr U (c.out * g) : G) * (cosetMul U g c).out := by
  rw [retr_spec]
  simp [rep, cosetMul]
end Retr
section Norm
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : TRep R G) (U : Subgroup G) [U.FiniteIndex]
def normF (n : ℕ) (F : (Fin (n + 1) → G) → M.V) (x : Fin (n + 1) → G) : M.V :=
  ∑ᶠ c : Quotient (QuotientGroup.rightRel U), M.rho c.out⁻¹ (F fun i => c.out * x i)
theorem normF_eq [Fintype (Quotient (QuotientGroup.rightRel U))] (n : ℕ) (F : (Fin (n + 1) → G) → M.V)
    (x : Fin (n + 1) → G) :
    normF M U n F x = ∑ c : Quotient (QuotientGroup.rightRel U), M.rho c.out⁻¹ (F fun i => c.out * x i) :=
  finsum_eq_sum_of_fintype _
theorem continuous_rho (s : G) : Continuous (M.rho s) :=
  M.cont.comp (continuous_const.prodMk continuous_id)
theorem normF_mem (n : ℕ) (F : (Fin (n + 1) → G) → M.V) (hF : F ∈ hcoch (M.resSub U) G n) :
    normF M U n F ∈ hcoch M G n := by
  classical
  haveI : Fintype (Quotient (QuotientGroup.rightRel U)) := Fintype.ofFinite _
  refine ⟨?_, fun g x => ?_⟩
  · have : normF M U n F = fun x => ∑ c : Quotient (QuotientGroup.rightRel U),
        M.rho c.out⁻¹ (F fun i => c.out * x i) := funext (normF_eq M U n F)
    rw [this]
    refine continuous_finset_sum _ fun c _ => (continuous_rho M _).comp (hF.1.comp ?_)
    exact continuous_pi fun i => continuous_const.mul (continuous_apply i)
  · rw [normF_eq, normF_eq, map_sum]
    have key : ∀ c : Quotient (QuotientGroup.rightRel U),
        M.rho c.out⁻¹ (F fun i => c.out * (g • x i)) =
        M.rho g (M.rho (cosetMul U g c).out⁻¹ (F fun i => (cosetMul U g c).out * x i)) := by
      intro c
      have e := out_mul U g c
      have h1 : (fun i => c.out * (g • x i)) =
          fun i => retr U (c.out * g) • ((cosetMul U g c).out * x i) := by
        funext i
        show c.out * (g * x i) = (retr U (c.out * g) : G) * ((cosetMul U g c).out * x i)
        rw [← mul_assoc, ← mul_assoc, ← e]
      rw [h1, hF.2]
      show M.rho c.out⁻¹ (M.rho (retr U (c.out * g) : G) _) = _
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      rw [show (retr U (c.out * g) : G) = c.out * g * ((cosetMul U g c).out)⁻¹ by
        rw [eq_mul_inv_iff_mul_eq]; exact e.symm]
      group
    simp only [key]
    exact Fintype.sum_bijective _ (cosetMul_bij U g) _ _ fun _ => rfl
theorem normF_hd (n : ℕ) (F : (Fin (n + 1) → G) → M.V) :
    normF M U (n + 1) (hd n F) = hd n (normF M U n F) := by
  classical
  haveI : Fintype (Quotient (QuotientGroup.rightRel U)) := Fintype.ofFinite _
  funext x
  simp only [normF_eq, hd, map_sum, map_zsmul, Finset.smul_sum]
  exact Finset.sum_comm
theorem normF_add (n : ℕ) (F F' : (Fin (n + 1) → G) → M.V) :
    normF M U n (F + F') = normF M U n F + normF M U n F' := by
  classical
  haveI : Fintype (Quotient (QuotientGroup.rightRel U)) := Fintype.ofFinite _
  funext x
  simp only [Pi.add_apply, normF_eq, map_add, Finset.sum_add_distrib]
theorem normF_smul (n : ℕ) (r : R) (F : (Fin (n + 1) → G) → M.V) :
    normF M U n (r • F) = r • normF M U n F := by
  classical
  haveI : Fintype (Quotient (QuotientGroup.rightRel U)) := Fintype.ofFinite _
  funext x
  simp only [Pi.smul_apply, normF_eq, map_smul, Finset.smul_sum]
def normL (n : ℕ) : hcoch (M.resSub U) G n →ₗ[R] hcoch M G n where
  toFun F := ⟨normF M U n F.1, normF_mem M U n F.1 F.2⟩
  map_add' F F' := by
    classical
    haveI : Fintype (Quotient (QuotientGroup.rightRel U)) := Fintype.ofFinite _
    refine Subtype.ext (funext fun x => ?_)
    exact congrFun (normF_add M U n F.1 F'.1) x
  map_smul' r F := by
    classical
    haveI : Fintype (Quotient (QuotientGroup.rightRel U)) := Fintype.ofFinite _
    refine Subtype.ext (funext fun x => ?_)
    exact congrFun (normF_smul M U n r F.1) x
variable {M U}
def normCx (A : Cx R) (eA : ∀ n, A.X n ≃ₗ[R] hcoch (M.resSub U) G n) (hA : IsHomog (M.resSub U) G A eA)
    (eG : ∀ n, M.coch.X n ≃ₗ[R] hcoch M G n) (hG : IsHomog M G M.coch eG) : Hom A M.coch where
  f n := ((eG n).symm.toLinearMap.comp (normL M U n)).comp (eA n).toLinearMap
  comm n F := by
    apply (eG (n + 1)).injective
    apply Subtype.ext
    rw [hG]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    show normF M U (n + 1) (eA (n + 1) (A.d n F)).1 = hd n (normF M U n (eA n F).1)
    rw [hA]; exact normF_hd M U n _
end Norm
end
end ReciprocityTheory.Coh.CCA


