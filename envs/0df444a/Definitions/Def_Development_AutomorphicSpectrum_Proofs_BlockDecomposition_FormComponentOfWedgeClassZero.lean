-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FormComponentOfWedgeClassZero
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FormComponentOfWedgeClassZero
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T03:07:01.541299+00:00
-- url     : https://prove2.me/theorems/9efd69e3-8e67-41fe-9fa3-502b6688458d
-- title:
--   Form Component Of Wedge Class Zero
-- statement:
--   Definitions and structural lemmas for Form Component Of Wedge Class Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FormComponentOfWedgeClassZero.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential
namespace GlobalTheory.CompanionTheory.HypWedge
section Alt
variable {R M N V W : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
def alt2 (B : M →ₗ[R] M →ₗ[R] N) (h : ∀ x, B x x = 0) : M [⋀^Fin 2]→ₗ[R] N where
  toFun v := B (v 0) (v 1)
  map_update_add' := by
    intro _ v i x y
    fin_cases i <;> simp
  map_update_smul' := by
    intro _ v i c x
    fin_cases i <;> simp
  map_eq_zero_of_eq' := by
    intro v i j hv hij
    have hv' : v 0 = v 1 := by
      fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | exact hv | exact hv.symm
    simp only [hv', h]
def ext2 (B : M →ₗ[R] M →ₗ[R] N) (h : ∀ x, B x x = 0) : ⋀[R]^2 M →ₗ[R] N :=
  exteriorPower.alternatingMapLinearEquiv (alt2 B h)
variable (R M) in

def wB : M →ₗ[R] M →ₗ[R] ⋀[R]^2 M :=
  LinearMap.mk₂ R (fun a b ↦ exteriorPower.ιMulti R 2 ![a, b])
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply, add_mul]))
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply]))
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply, mul_add]))
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply]))
def mix (σ : V →ₗ[R] M) (k : W →ₗ[R] M) : V ⊗[R] W →ₗ[R] ⋀[R]^2 M :=
  TensorProduct.lift ((wB R M).compl₁₂ σ k)
end Alt
section Coh
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}
variable (F) in

def fn2 : cechDeRhamTotalCocyclesTwo F →ₗ[R] Z2 F where
  toFun c := ⟨c.1.1, (mem_cechDeRhamTotalCocyclesTwo_iff.1 c.2).1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
variable (F) in

def rho : Hyp2 F →ₗ[R] H2 F :=
  Submodule.mapQ _ _ (fn2 F) (by rintro _ ⟨g, rfl⟩; exact ⟨g.1, rfl⟩)
def cl (hcl : Closed1 F = ⊤) : Glob1 F →ₗ[R] cechDeRhamTotalCocyclesOne F :=
  formZZ F ∘ₗ LinearMap.codRestrict (Closed1 F) LinearMap.id (fun w ↦ by rw [hcl]; trivial)
theorem cl_coe (hcl : Closed1 F = ⊤) (w : Glob1 F) : (cl hcl w).1 = (0, w.1) := rfl
def Lc (hcl : Closed1 F = ⊤) (τ : H1 F →ₗ[R] cechDeRhamTotalCocyclesOne F) : H1 F ⊗[R] Glob1 F →ₗ[R] cechDeRhamTotalCocyclesTwo F :=
  TensorProduct.lift ((cupZZ F).compl₁₂ τ (cl hcl))
theorem cup_cl_self (hcl : Closed1 F = ⊤) (w : Glob1 F) : cupZZ F (cl hcl w) (cl hcl w) = 0 := by
  refine Subtype.ext (Tot2.ext (fun T T' T'' φ ψ ↦ ?_) (fun T T' φ ↦ ?_) fun T ↦ ?_)
  · simp [coe_cupZZ, cupTot_apply, cl_coe]
  · simp [coe_cupZZ, cupTot_a, cl_coe]
  · simp [coe_cupZZ, cupTot_η, cl_coe]
def Nc (hcl : Closed1 F = ⊤) : ⋀[R]^2 (Glob1 F) →ₗ[R] cechDeRhamTotalCocyclesTwo F :=
  ext2 ((cupZZ F).compl₁₂ (cl hcl) (cl hcl)) (cup_cl_self hcl)
abbrev sR (τ : H1 F →ₗ[R] cechDeRhamTotalCocyclesOne F) : H1 F ⊗[R] Glob1 F →ₗ[R] Z1 F ⊗[R] Glob1 F :=
  LinearMap.rTensor (Glob1 F) (cechDeRhamTotalCocyclesOne.fn F ∘ₗ τ)
end Coh
section Main
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}
end Main
end GlobalTheory.CompanionTheory.HypWedge


