-- Prove2me | solution 1 for AutomorphicForm.isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/5cda3558-90b2-53f0-ad17-e8d51e439a95

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution
import Theorems.Thm_AutomorphicForm_archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
import Theorems.Thm_AutomorphicForm_rightConv_mem_archCutSubmodule_of_isArchBiFinite
import Theorems.Thm_AutomorphicForm_IsFactorizableTestFn_isArchSmoothAt_and_archDerivAt_eq_tensor
import Theorems.Thm_AutomorphicForm_leftCasimir_eq_archCasimirAt_of_isArchSmoothAt
import Theorems.Thm_AutomorphicForm_archCasimirAt_rightTranslate_archRealGLAt
import Theorems.Thm_AutomorphicForm_archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne
import Theorems.Thm_AutomorphicForm_apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

noncomputable section

namespace Ws23
namespace CAS88

open MeasureTheory

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K} (hw : w.IsReal)

def Ld (d : ArchDir) (γ : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  fun y => deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * y)) 0

def leftCasimir (α : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  fun y => -((1 / 4 : ℂ) * Ld hw .H (Ld hw .H α) y - (1 / 2 : ℂ) * Ld hw .H α y + Ld hw .E (Ld hw .Fm α) y)

theorem isFactorizableTestFn_Ld {γ : AdelicGL2 (𝓞 K) K → ℂ} (hγ : IsFactorizableTestFn K γ) (d : ArchDir) :
    IsFactorizableTestFn K (Ld hw d γ) := by
  obtain ⟨fa, ff, hfa, hff, hγeq⟩ := hγ
  obtain ⟨fa', hfa', heq⟩ :=
    (AutomorphicForm.archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn K hw d).2.1 fa ff hfa
  refine ⟨fa', ff, hfa', hff, fun y => ?_⟩
  have hfun : (fun t : ℝ => γ (archFlowAt hw d (-t) * y)) =
      fun t : ℝ => fa (glArch (𝓞 K) K (archFlowAt hw d (-t) * y)) * ff (glFin (𝓞 K) K (archFlowAt hw d (-t) * y)) := by
    funext t; exact hγeq _
  show deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * y)) 0 = _
  rw [hfun]
  exact congrFun heq y

theorem Ld_left_inv {γ : AdelicGL2 (𝓞 K) K → ℂ} {k : AdelicGL2 (𝓞 K) K} (hk : glArch (𝓞 K) K k = 1)
    (h : ∀ y, γ (k * y) = γ y) (d : ArchDir) (y : AdelicGL2 (𝓞 K) K) : Ld hw d γ (k * y) = Ld hw d γ y := by
  show deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * (k * y))) 0 = deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * y)) 0
  congr 1
  funext t
  rw [← mul_assoc, archFlowAt_mul_comm_of_glArch_eq_one hw d (-t) hk, mul_assoc, h]

theorem leftCasimir_left_inv (N : Ideal (𝓞 K)) (α : AdelicGL2 (𝓞 K) K → ℂ)
    (hαU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K),
      α (k * g) = α g ∧ α (g * k) = α g) :
    ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), ∀ y : AdelicGL2 (𝓞 K) K,
      leftCasimir hw α (k * y) = leftCasimir hw α y := by
  intro k hk y
  have hk1 : glArch (𝓞 K) K k = 1 := (mem_finiteAdelicGL2Subgroup_iff K k).mp (Subgroup.mem_inf.mp hk).2
  have hα' : ∀ y, α (k * y) = α y := fun y => (hαU y k hk).1
  have e1 : ∀ y, Ld hw .H α (k * y) = Ld hw .H α y := fun y => Ld_left_inv hw hk1 hα' .H y
  have e2 : ∀ y, Ld hw .H (Ld hw .H α) (k * y) = Ld hw .H (Ld hw .H α) y := fun y => Ld_left_inv hw hk1 e1 .H y
  have e3 : ∀ y, Ld hw .Fm α (k * y) = Ld hw .Fm α y := fun y => Ld_left_inv hw hk1 hα' .Fm y
  have e4 : ∀ y, Ld hw .E (Ld hw .Fm α) (k * y) = Ld hw .E (Ld hw .Fm α) y := fun y => Ld_left_inv hw hk1 e3 .E y
  show -((1 / 4 : ℂ) * Ld hw .H (Ld hw .H α) (k * y) - (1 / 2 : ℂ) * Ld hw .H α (k * y) + Ld hw .E (Ld hw .Fm α) (k * y)) =
    -((1 / 4 : ℂ) * Ld hw .H (Ld hw .H α) y - (1 / 2 : ℂ) * Ld hw .H α y + Ld hw .E (Ld hw .Fm α) y)
  rw [e1, e2, e4]

theorem rightConv_leftCasimir_eq (α : AdelicGL2 (𝓞 K) K → ℂ) (hαf : IsFactorizableTestFn K α) :
    ∀ x' : AdelicGL2 (𝓞 K) K → ℂ, Continuous x' →
      rightConv K x' (leftCasimir hw α) = fun g => -((1 / 4 : ℂ) * rightConv K x' (Ld hw .H (Ld hw .H α)) g
        - (1 / 2 : ℂ) * rightConv K x' (Ld hw .H α) g + rightConv K x' (Ld hw .E (Ld hw .Fm α)) g) := by
  intro x' hx'
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  have hfac1 : IsFactorizableTestFn K (Ld hw .H α) := isFactorizableTestFn_Ld hw hαf .H
  have hfac2 : IsFactorizableTestFn K (Ld hw .H (Ld hw .H α)) := isFactorizableTestFn_Ld hw hfac1 .H
  have hfac4 : IsFactorizableTestFn K (Ld hw .E (Ld hw .Fm α)) :=
    isFactorizableTestFn_Ld hw (isFactorizableTestFn_Ld hw hαf .Fm) .E
  have hint : ∀ {γ : AdelicGL2 (𝓞 K) K → ℂ}, IsFactorizableTestFn K γ → ∀ g : AdelicGL2 (𝓞 K) K,
      Integrable (fun y => x' (g * y) * γ y) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro γ hγ g
    obtain ⟨hγc, hγs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K γ hγ
    exact ((hx'.comp (continuous_const.mul continuous_id)).mul hγc).integrable_of_hasCompactSupport hγs.mul_left
  funext g
  rw [rightConv_apply, rightConv_apply, rightConv_apply, rightConv_apply]
  have hfun : (fun y => x' (g * y) * leftCasimir hw α y) = fun y => -((1 / 4 : ℂ) * (x' (g * y) * Ld hw .H (Ld hw .H α) y) -
      (1 / 2 : ℂ) * (x' (g * y) * Ld hw .H α y) + x' (g * y) * Ld hw .E (Ld hw .Fm α) y) := by
    funext y
    show x' (g * y) * -((1 / 4 : ℂ) * Ld hw .H (Ld hw .H α) y - (1 / 2 : ℂ) * Ld hw .H α y + Ld hw .E (Ld hw .Fm α) y) = _
    ring
  have hA : Integrable (fun y => (1 / 4 : ℂ) * (x' (g * y) * Ld hw .H (Ld hw .H α) y)) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) :=
    (hint hfac2 g).const_mul _
  have hB : Integrable (fun y => (1 / 2 : ℂ) * (x' (g * y) * Ld hw .H α y)) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) :=
    (hint hfac1 g).const_mul _
  have hAB : Integrable (fun y => (1 / 4 : ℂ) * (x' (g * y) * Ld hw .H (Ld hw .H α) y) - (1 / 2 : ℂ) * (x' (g * y) * Ld hw .H α y))
      (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := hA.sub hB
  rw [hfun, integral_neg, integral_add hAB (hint hfac4 g), integral_sub hA hB, integral_const_mul, integral_const_mul]

theorem rightConv_mem_levelInvariantSubmodule_of_left_inv (D : Set (AdelicGL2 (𝓞 K) K)) (N : Ideal (𝓞 K))
    (β : AdelicGL2 (𝓞 K) K → ℂ)
    (hβU : ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), ∀ y : AdelicGL2 (𝓞 K) K, β (k * y) = β y)
    (x' : AdelicGL2 (𝓞 K) K → ℂ) :
    rightConv K x' β ∈ levelInvariantSubmodule K (productionPinsOf K D
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N := by
  intro g u hu
  rw [AutomorphicForm.rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply]
  have hfun : (fun y => β (u⁻¹ * y)) = β := funext fun y => hβU u⁻¹ (Subgroup.inv_mem _ hu) y
  rw [hfun]

theorem rightConv_mem_archCutSubmodule (tys : ArchTypeFamily K) (β : AdelicGL2 (𝓞 K) K → ℂ)
    (hβf : IsFactorizableTestFn K β) (hβb : IsArchBiFinite K tys β)
    (x' : AdelicGL2 (𝓞 K) K → ℂ) (hx' : Continuous x') :
    rightConv K x' β ∈ archCutSubmodule K tys :=
  AutomorphicForm.rightConv_mem_archCutSubmodule_of_isArchBiFinite K tys x' hx' β hβf hβb

theorem rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule (D : Set (AdelicGL2 (𝓞 K) K)) (N : Ideal (𝓞 K))
    (tys : ArchTypeFamily K) (β : AdelicGL2 (𝓞 K) K → ℂ)
    (hβf : IsFactorizableTestFn K β) (hβb : IsArchBiFinite K tys β)
    (hβU : ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), ∀ y : AdelicGL2 (𝓞 K) K, β (k * y) = β y) :
    ∀ x' : AdelicGL2 (𝓞 K) K → ℂ, Continuous x' →
      x' ∈ levelInvariantSubmodule K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N → x' ∈ archCutSubmodule K tys →
      rightConv K x' β ∈ levelInvariantSubmodule K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N ⊓
        archCutSubmodule K tys :=
  fun x' hx' _ _ => Submodule.mem_inf.mpr
    ⟨rightConv_mem_levelInvariantSubmodule_of_left_inv D N β hβU x', rightConv_mem_archCutSubmodule tys β hβf hβb x' hx'⟩

theorem rightConv_leftCasimir_mem (D : Set (AdelicGL2 (𝓞 K) K)) (N : Ideal (𝓞 K)) (tys : ArchTypeFamily K)
    (α : AdelicGL2 (𝓞 K) K → ℂ)
    (hαU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K),
      α (k * g) = α g ∧ α (g * k) = α g)
    (hβf : IsFactorizableTestFn K (leftCasimir hw α)) (hβb : IsArchBiFinite K tys (leftCasimir hw α)) :
    ∀ x' : AdelicGL2 (𝓞 K) K → ℂ, Continuous x' →
      x' ∈ levelInvariantSubmodule K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N → x' ∈ archCutSubmodule K tys →
      rightConv K x' (leftCasimir hw α) ∈ levelInvariantSubmodule K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N ⊓
        archCutSubmodule K tys :=
  rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule D N tys (leftCasimir hw α) hβf hβb
    (leftCasimir_left_inv hw N α hαU)

def Tens (ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ) (γ : AdelicGL2 (𝓞 K) K → ℂ) : Prop :=
  ∃ fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ, IsArchTestFactor K fa ∧ ∀ y, γ y = fa (glArch (𝓞 K) K y) * ff (glFin (𝓞 K) K y)

theorem tens_Ld {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ} {γ : AdelicGL2 (𝓞 K) K → ℂ}
    (hγ : Tens ff γ) (d : ArchDir) : Tens ff (Ld hw d γ) := by
  obtain ⟨fa, hfa, hγeq⟩ := hγ
  obtain ⟨fa', hfa', heq⟩ :=
    (AutomorphicForm.archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn K hw d).2.1 fa ff hfa
  refine ⟨fa', hfa', fun y => ?_⟩
  have hfun : (fun t : ℝ => γ (archFlowAt hw d (-t) * y)) =
      fun t : ℝ => fa (glArch (𝓞 K) K (archFlowAt hw d (-t) * y)) * ff (glFin (𝓞 K) K (archFlowAt hw d (-t) * y)) := by
    funext t; exact hγeq _
  show deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * y)) 0 = _
  rw [hfun]
  exact congrFun heq y

theorem isFactorizableTestFn_leftCasimir (α : AdelicGL2 (𝓞 K) K → ℂ) (hαf : IsFactorizableTestFn K α) :
    IsFactorizableTestFn K (leftCasimir hw α) := by
  classical
  obtain ⟨fa, ff, hfa, hff, hαeq⟩ := hαf
  have hT0 : Tens ff α := ⟨fa, hfa, hαeq⟩
  obtain ⟨fa1, ⟨⟨Φ1, hΦ1, hfa1⟩, hs1⟩, h1⟩ := tens_Ld hw hT0 .H
  obtain ⟨fa2, ⟨⟨Φ2, hΦ2, hfa2⟩, hs2⟩, h2⟩ := tens_Ld hw (tens_Ld hw hT0 .H) .H
  obtain ⟨fa4, ⟨⟨Φ4, hΦ4, hfa4⟩, hs4⟩, h4⟩ := tens_Ld hw (tens_Ld hw hT0 .Fm) .E
  have hβeq : ∀ y, leftCasimir hw α y = (fun z => (-(1 / 4 : ℂ)) * fa2 z + (1 / 2 : ℂ) * fa1 z + (-1 : ℂ) * fa4 z)
      (glArch (𝓞 K) K y) * ff (glFin (𝓞 K) K y) := by
    intro y
    show -((1 / 4 : ℂ) * Ld hw .H (Ld hw .H α) y - (1 / 2 : ℂ) * Ld hw .H α y + Ld hw .E (Ld hw .Fm α) y) = _
    rw [h1, h2, h4]
    ring
  refine ⟨fun z => (-(1 / 4 : ℂ)) * fa2 z + (1 / 2 : ℂ) * fa1 z + (-1 : ℂ) * fa4 z, ff, ⟨⟨fun m => (-(1 / 4 : ℂ)) * Φ2 m +
    (1 / 2 : ℂ) * Φ1 m + (-1 : ℂ) * Φ4 m, ?_, fun z => ?_⟩, ?_⟩, hff, hβeq⟩
  · exact ((contDiff_const.mul hΦ2).add (contDiff_const.mul hΦ1)).add (contDiff_const.mul hΦ4)
  · show (-(1 / 4 : ℂ)) * fa2 z + (1 / 2 : ℂ) * fa1 z + (-1 : ℂ) * fa4 z = _
    rw [hfa2, hfa1, hfa4]
  · exact (hs2.mul_left.add hs1.mul_left).add hs4.mul_left

theorem leftCasimir_eq_archCasimirAt (α : AdelicGL2 (𝓞 K) K → ℂ) (hαf : IsFactorizableTestFn K α) :
    leftCasimir hw α = archCasimirAt hw α :=
  funext (AutomorphicForm.leftCasimir_eq_archCasimirAt_of_isArchSmoothAt K w hw α
    (AutomorphicForm.IsFactorizableTestFn.isArchSmoothAt_and_archDerivAt_eq_tensor K w hw α hαf).1)

end Ws23.CAS88

end

open AutomorphicForm

namespace Ws23
namespace H1

variable {H G : Type*} [Group H] [Group G]

def rT (ι : H →* G) (k : H) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun u x := u (x * ι k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] theorem rT_apply (ι : H →* G) (k : H) (u : G → ℂ) (x : G) : rT ι k u x = u (x * ι k) := rfl

theorem rT_mul (ι : H →* G) (h k : H) (u : G → ℂ) : rT ι h (rT ι k u) = rT ι (h * k) u := by
  funext x; simp [mul_assoc]

theorem equivariant_mem_iSup_typeSubmodule {m : ℕ} {W : Fin m → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ι : H →* G) (hι : Function.Injective ι)
    (ρ : ∀ i : Fin m, Representation ℂ H (W i))
    (V : Submodule ℂ (G → ℂ)) (hV : ∀ k : H, ∀ u ∈ V, rT ι k u ∈ V)
    (hVle : V ≤ ⨆ i, typeSubmodule ι (ρ i))
    (Ψ : V →ₗ[ℂ] (G → ℂ))
    (hΨ : ∀ (k : H) (u : V), Ψ ⟨rT ι k u, hV k u u.2⟩ = rT ι k (Ψ u)) (u : V) :
    Ψ u ∈ ⨆ i, typeSubmodule ι (ρ i) := by
  have h := AutomorphicForm.apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective ι ι hι V
    (fun k u hu => hV k u hu) Ψ (fun k u x => congrFun (hΨ k u) x) ρ (u : G → ℂ) u.2 (hVle u.2)
  simpa only [Subtype.coe_eta] using h

end Ws23.H1
p2m_reactivate "P2MW.S_AutomorphicForm_isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite.Ws23 P2MW.S_AutomorphicForm_isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite.Ws23.H1"
p2m_reactivate "P2MW.S_AutomorphicForm_isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite.Ws23"

namespace Ws23
namespace CAS88

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent Ws23.H1

variable {K : Type} [Field K] [NumberField K]

theorem rowIsometryInclAt₀_injective (v : InfinitePlace K) : Function.Injective (rowIsometryInclAt₀ K v) := by
  intro a b h
  apply Subtype.ext
  have h1 := congrArg (fun x => archComponent K v (glArch (𝓞 K) K x)) h
  simpa only [rowIsometryInclAt₀_apply, adelicArchGLInclAt, MonoidHom.comp_apply, glArch_adelicArchGLIncl,
    archComponent_archGLIncl_self] using h1

theorem rT_mem_iSup_typeSubmodule {H G : Type*} [Group H] [Group G] {m : ℕ} {W : Fin m → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] (ι : H →* G)
    (ρ : ∀ i : Fin m, Representation ℂ H (W i)) {u : G → ℂ}
    (hu : u ∈ ⨆ i, typeSubmodule ι (ρ i)) (k : H) : rT ι k u ∈ ⨆ i, typeSubmodule ι (ρ i) := by
  have hle : (⨆ i, typeSubmodule ι (ρ i)).map (rT ι k) ≤ ⨆ i, typeSubmodule ι (ρ i) := by
    rw [Submodule.map_iSup]
    refine iSup_mono fun i => ?_
    rintro _ ⟨f, hf, rfl⟩
    exact comp_mul_mem_typeSubmodule hf k
  exact hle (Submodule.mem_map_of_mem hu)

theorem rT_mem_span_range_rT {H G : Type*} [Group H] [Group G] (ι : H →* G) (f : G → ℂ) (k : H) {u : G → ℂ}
    (hu : u ∈ Submodule.span ℂ (Set.range fun k : H => rT ι k f)) :
    rT ι k u ∈ Submodule.span ℂ (Set.range fun k : H => rT ι k f) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
  · rintro _ ⟨k', rfl⟩
    rw [rT_mul]
    exact Submodule.subset_span ⟨k * k', rfl⟩
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro u v _ _ hu hv; rw [map_add]; exact Submodule.add_mem _ hu hv
  · intro c u _ hu; rw [map_smul]; exact Submodule.smul_mem _ c hu

theorem comp_inv_archCasimirAt_mem_archCutSubmodule {w : InfinitePlace K} (hw : w.IsReal) (tys : ArchTypeFamily K)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hαs : IsArchSmoothAt hw α) (hα : (fun x => α x⁻¹) ∈ archCutSubmodule K tys) :
    (fun x => archCasimirAt hw α x⁻¹) ∈ archCutSubmodule K tys := by
  rw [mem_archCutSubmodule_iff] at hα ⊢
  intro v
  have hαv : (fun x => α x⁻¹) ∈ ⨆ i, typeSubmodule (rowIsometryInclAt₀ K v) (tys.rep v i).ρ := hα v
  set ι := rowIsometryInclAt₀ K v with hι
  set αc : AdelicGL2 (𝓞 K) K → ℂ := fun x => α x⁻¹ with hαc
  set V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) :=
    Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ v.Completion => rT ι k αc) with hVdef
  have hVstab : ∀ k : rowIsometrySubgroup₀ v.Completion, ∀ u ∈ V, rT ι k u ∈ V :=
    fun k u hu => rT_mem_span_range_rT ι αc k hu
  have hVle : V ≤ ⨆ i, typeSubmodule ι (tys.rep v i).ρ :=
    Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact rT_mem_iSup_typeSubmodule ι _ hαv k)
  have hSm : ∀ u ∈ V, IsArchSmoothAt hw (fun y => u y⁻¹) := by
    intro u hu
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨k, rfl⟩
      have e : (fun y => (rT ι k αc) y⁻¹) = fun y => α ((ι k)⁻¹ * y) := by
        funext y
        simp only [rT_apply, hαc, _root_.mul_inv_rev, inv_inv]
      rw [e]
      exact hαs.comp_mul_left _
    · exact isArchSmoothAt_const hw 0
    · intro u u' _ _ hu hu'
      exact hu.add hu'
    · intro c u _ hu
      exact hu.smul c
  let Ψ : V →ₗ[ℂ] (AdelicGL2 (𝓞 K) K → ℂ) :=
    { toFun := fun u x => archCasimirAt hw (fun y => (u : AdelicGL2 (𝓞 K) K → ℂ) y⁻¹) x⁻¹
      map_add' := fun u u' => by
        funext x
        show archCasimirAt hw (fun y => ((u : AdelicGL2 (𝓞 K) K → ℂ) + (u' : AdelicGL2 (𝓞 K) K → ℂ)) y⁻¹) x⁻¹ =
          archCasimirAt hw (fun y => (u : AdelicGL2 (𝓞 K) K → ℂ) y⁻¹) x⁻¹ +
            archCasimirAt hw (fun y => (u' : AdelicGL2 (𝓞 K) K → ℂ) y⁻¹) x⁻¹
        have e : (fun y => ((u : AdelicGL2 (𝓞 K) K → ℂ) + (u' : AdelicGL2 (𝓞 K) K → ℂ)) y⁻¹) =
            (fun y => (u : AdelicGL2 (𝓞 K) K → ℂ) y⁻¹) + fun y => (u' : AdelicGL2 (𝓞 K) K → ℂ) y⁻¹ := rfl
        rw [e, archCasimirAt_add (hSm _ u.2) (hSm _ u'.2)]
        rfl
      map_smul' := fun c u => by
        funext x
        show archCasimirAt hw (fun y => (c • (u : AdelicGL2 (𝓞 K) K → ℂ)) y⁻¹) x⁻¹ =
          c • archCasimirAt hw (fun y => (u : AdelicGL2 (𝓞 K) K → ℂ) y⁻¹) x⁻¹
        have e : (fun y => (c • (u : AdelicGL2 (𝓞 K) K → ℂ)) y⁻¹) = c • fun y => (u : AdelicGL2 (𝓞 K) K → ℂ) y⁻¹ := rfl
        rw [e, archCasimirAt_smul]
        rfl }
  have hΨ : ∀ (k : rowIsometrySubgroup₀ v.Completion) (u : V), Ψ ⟨rT ι k u, hVstab k u u.2⟩ = rT ι k (Ψ u) := by
    intro k u
    funext x
    show archCasimirAt hw (fun y => (rT ι k (u : AdelicGL2 (𝓞 K) K → ℂ)) y⁻¹) x⁻¹ =
      archCasimirAt hw (fun y => (u : AdelicGL2 (𝓞 K) K → ℂ) y⁻¹) (x * ι k)⁻¹
    have e : (fun y => (rT ι k (u : AdelicGL2 (𝓞 K) K → ℂ)) y⁻¹) =
        fun y => (fun z => (u : AdelicGL2 (𝓞 K) K → ℂ) z⁻¹) ((ι k)⁻¹ * y) := by
      funext y
      simp only [rT_apply, _root_.mul_inv_rev, inv_inv]
    rw [e, _root_.mul_inv_rev]
    exact congrFun (archCasimirAt_comp_mul_left hw (fun z => (u : AdelicGL2 (𝓞 K) K → ℂ) z⁻¹) (ι k)⁻¹) x⁻¹
  have hαcV : αc ∈ V := by
    have e : rT ι 1 αc = αc := by funext y; simp only [rT_apply, map_one, mul_one]
    rw [← e]
    exact Submodule.subset_span ⟨1, rfl⟩
  have key := equivariant_mem_iSup_typeSubmodule ι (rowIsometryInclAt₀_injective v) (fun i => (tys.rep v i).ρ)
    V hVstab hVle Ψ hΨ ⟨αc, hαcV⟩
  have e2 : (Ψ ⟨αc, hαcV⟩ : AdelicGL2 (𝓞 K) K → ℂ) = fun x => archCasimirAt hw α x⁻¹ := by
    funext x
    show archCasimirAt hw (fun y => αc y⁻¹) x⁻¹ = _
    have e : (fun y => αc y⁻¹) = α := funext fun y => by simp only [hαc, inv_inv]
    rw [e]
  rw [e2] at key
  exact key

def Reg {w : InfinitePlace K} (hw : w.IsReal) (u : AdelicGL2 (𝓞 K) K → ℂ) : Prop :=
  Continuous u ∧ IsArchSmoothAt hw u ∧ (∀ d : ArchDir, Continuous (archDerivAt hw d u)) ∧
    ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' u))

theorem Reg.add {w : InfinitePlace K} {hw : w.IsReal} {u v : AdelicGL2 (𝓞 K) K → ℂ} (hu : Reg hw u) (hv : Reg hw v) :
    Reg hw (u + v) := by
  refine ⟨hu.1.add hv.1, hu.2.1.add hv.2.1, fun d => ?_, fun d d' => ?_⟩
  · rw [archDerivAt_add hu.2.1 hv.2.1]
    exact (hu.2.2.1 d).add (hv.2.2.1 d)
  · rw [archDerivAt_add hu.2.1 hv.2.1, archDerivAt_add (hu.2.1.archDerivAt d') (hv.2.1.archDerivAt d')]
    exact (hu.2.2.2 d d').add (hv.2.2.2 d d')

theorem Reg.smul {w : InfinitePlace K} {hw : w.IsReal} {u : AdelicGL2 (𝓞 K) K → ℂ} (hu : Reg hw u) (c : ℂ) :
    Reg hw (c • u) := by
  refine ⟨hu.1.const_smul c, hu.2.1.smul c, fun d => ?_, fun d d' => ?_⟩
  · rw [archDerivAt_smul]
    exact (hu.2.2.1 d).const_smul c
  · rw [archDerivAt_smul, archDerivAt_smul]
    exact (hu.2.2.2 d d').const_smul c

theorem reg_of_isFactorizableTestFn {w : InfinitePlace K} (hw : w.IsReal) {α : AdelicGL2 (𝓞 K) K → ℂ}
    (hα : IsFactorizableTestFn K α) : Reg hw α := by
  have hT := AutomorphicForm.IsFactorizableTestFn.isArchSmoothAt_and_archDerivAt_eq_tensor K w hw α hα
  obtain ⟨hαs, fa, ff, hfa, hff, hαeq, hder⟩ := hT
  have hD : ∀ d : ArchDir, IsFactorizableTestFn K (archDerivAt hw d α) := by
    intro d
    obtain ⟨fa', hfa', h⟩ := hder d
    exact ⟨fa', ff, hfa', hff, h⟩
  refine ⟨(AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K α hα).1, hαs,
    fun d => (AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K _ (hD d)).1, fun d d' => ?_⟩
  have hT' := AutomorphicForm.IsFactorizableTestFn.isArchSmoothAt_and_archDerivAt_eq_tensor K w hw _ (hD d')
  obtain ⟨_, fa1, ff1, hfa1, hff1, h1eq, hder1⟩ := hT'
  obtain ⟨fa'', hfa'', h⟩ := hder1 d
  exact (AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K _ ⟨fa'', ff1, hfa'', hff1, h⟩).1

theorem rowIsometryInclAt₀_eq_archRealGLAt {w : InfinitePlace K} (hw : w.IsReal) (k : rowIsometrySubgroup₀ w.Completion) :
    rowIsometryInclAt₀ K w k =
      archRealGLAt hw ((glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm).symm (k : GL (Fin 2) w.Completion)) := by
  rw [rowIsometryInclAt₀_apply]
  show adelicArchGLInclAt K w (k : GL (Fin 2) w.Completion) =
    adelicArchGLInclAt K w ((glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm).toMonoidHom
      ((glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm).symm (k : GL (Fin 2) w.Completion)))
  rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]

theorem reg_rT_and_archCasimirAt_rT {w : InfinitePlace K} (hw : w.IsReal) (v : InfinitePlace K)
    (k : rowIsometrySubgroup₀ v.Completion) {u : AdelicGL2 (𝓞 K) K → ℂ} (hu : Reg hw u) :
    Reg hw (rT (rowIsometryInclAt₀ K v) k u) ∧
      archCasimirAt hw (rT (rowIsometryInclAt₀ K v) k u) = rT (rowIsometryInclAt₀ K v) k (archCasimirAt hw u) := by
  obtain ⟨huc, hus, hD1, hD2⟩ := hu
  have hcont : Continuous (rT (rowIsometryInclAt₀ K v) k u) := huc.comp (continuous_mul_const _)
  by_cases hvw : v = w
  · subst hvw
    have h := AutomorphicForm.archCasimirAt_rightTranslate_archRealGLAt K v hw u huc hus hD1 hD2
      ((glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm).symm (k : GL (Fin 2) v.Completion))
    rw [← rowIsometryInclAt₀_eq_archRealGLAt hw k] at h
    exact ⟨⟨hcont, h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩
  · have h := AutomorphicForm.archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne K w hw u huc hus hD1 hD2 v hvw k
    exact ⟨⟨hcont, h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩

theorem archCasimirAt_mem_archDualCutSubmodule {w : InfinitePlace K} (hw : w.IsReal) (tys : ArchTypeFamily K)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hαr : Reg hw α) (hα : α ∈ archDualCutSubmodule K tys) :
    archCasimirAt hw α ∈ archDualCutSubmodule K tys := by
  rw [mem_archDualCutSubmodule_iff] at hα ⊢
  intro v
  have hαv : α ∈ ⨆ i, typeSubmodule (rowIsometryInclAt₀ K v) (tys.rep v i).ρ.dual := hα v
  set ι := rowIsometryInclAt₀ K v with hι
  set V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) :=
    Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ v.Completion => rT ι k α) with hVdef
  have hVstab : ∀ k : rowIsometrySubgroup₀ v.Completion, ∀ u ∈ V, rT ι k u ∈ V :=
    fun k u hu => rT_mem_span_range_rT ι α k hu
  have hVle : V ≤ ⨆ i, typeSubmodule ι (tys.rep v i).ρ.dual :=
    Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact rT_mem_iSup_typeSubmodule ι _ hαv k)
  have hReg : ∀ u ∈ V, Reg hw u := by
    intro u hu
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨k, rfl⟩
      exact (reg_rT_and_archCasimirAt_rT hw v k hαr).1
    · have e : (0 : AdelicGL2 (𝓞 K) K → ℂ) = (0 : ℂ) • α := by simp
      rw [e]
      exact hαr.smul 0
    · intro u u' _ _ hu hu'
      exact hu.add hu'
    · intro c u _ hu
      exact hu.smul c
  let Ψ : V →ₗ[ℂ] (AdelicGL2 (𝓞 K) K → ℂ) :=
    { toFun := fun u => archCasimirAt hw (u : AdelicGL2 (𝓞 K) K → ℂ)
      map_add' := fun u u' => by rw [Submodule.coe_add]; exact archCasimirAt_add (hReg _ u.2).2.1 (hReg _ u'.2).2.1
      map_smul' := fun c u => by rw [RingHom.id_apply, Submodule.coe_smul, archCasimirAt_smul] }
  have hΨ : ∀ (k : rowIsometrySubgroup₀ v.Completion) (u : V), Ψ ⟨rT ι k u, hVstab k u u.2⟩ = rT ι k (Ψ u) := by
    intro k u
    exact (reg_rT_and_archCasimirAt_rT hw v k (hReg _ u.2)).2
  have hαV : α ∈ V := by
    have e : rT ι 1 α = α := by funext y; simp only [rT_apply, map_one, mul_one]
    rw [← e]
    exact Submodule.subset_span ⟨1, rfl⟩
  exact equivariant_mem_iSup_typeSubmodule ι (rowIsometryInclAt₀_injective v) (fun i => (tys.rep v i).ρ.dual)
    V hVstab hVle Ψ hΨ ⟨α, hαV⟩

theorem isArchBiFinite_archCasimirAt {w : InfinitePlace K} (hw : w.IsReal) (tys : ArchTypeFamily K)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hαf : IsFactorizableTestFn K α) (hαb : IsArchBiFinite K tys α) :
    IsArchBiFinite K tys (archCasimirAt hw α) :=
  ⟨comp_inv_archCasimirAt_mem_archCutSubmodule hw tys α (reg_of_isFactorizableTestFn hw hαf).2.1 hαb.1,
    archCasimirAt_mem_archDualCutSubmodule hw tys α (reg_of_isFactorizableTestFn hw hαf) hαb.2⟩

end Ws23.CAS88
p2m_reactivate "P2MW.S_AutomorphicForm_isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite.Ws23 P2MW.S_AutomorphicForm_isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite.Ws23.H1"
p2m_reactivate "P2MW.S_AutomorphicForm_isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite.Ws23 P2MW.S_AutomorphicForm_isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite.Ws23.H1"

theorem solution
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsReal)
    (N : Ideal (𝓞 K)) (tys : AutomorphicForm.ArchTypeFamily K)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hαf : IsFactorizableTestFn K α) (hαb : IsArchBiFinite K tys α)
    (hαU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), α (k * g) = α g ∧ α (g * k) = α g) :
    let L : ArchDir → (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun d γ y => deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * y)) 0
    let β : AdelicGL2 (𝓞 K) K → ℂ :=
      fun y => -((1 / 4 : ℂ) * L .H (L .H α) y - (1 / 2 : ℂ) * L .H α y + L .E (L .Fm α) y)
    (IsFactorizableTestFn K β ∧ IsArchBiFinite K tys β) ∧
    (∀ x' : AdelicGL2 (𝓞 K) K → ℂ, Continuous x' →
      rightConv K x' β = fun g => -((1 / 4 : ℂ) * rightConv K x' (L .H (L .H α)) g
        - (1 / 2 : ℂ) * rightConv K x' (L .H α) g + rightConv K x' (L .E (L .Fm α)) g)) ∧
    (∀ x' : AdelicGL2 (𝓞 K) K → ℂ, Continuous x' →
      x' ∈ levelInvariantSubmodule K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N → x' ∈ archCutSubmodule K tys →
      rightConv K x' β ∈ levelInvariantSubmodule K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N ⊓ archCutSubmodule K tys) := by
  intro L β
  have hβf : IsFactorizableTestFn K β := Ws23.CAS88.isFactorizableTestFn_leftCasimir hw α hαf
  have hβb : IsArchBiFinite K tys β := by
    show IsArchBiFinite K tys (Ws23.CAS88.leftCasimir hw α)
    rw [Ws23.CAS88.leftCasimir_eq_archCasimirAt hw α hαf]
    exact Ws23.CAS88.isArchBiFinite_archCasimirAt hw tys α hαf hαb
  exact ⟨⟨hβf, hβb⟩, Ws23.CAS88.rightConv_leftCasimir_eq hw α hαf,
    Ws23.CAS88.rightConv_leftCasimir_mem hw D N tys α hαU hβf hβb⟩

end S_AutomorphicForm_isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite
end P2MW
export P2MW.S_AutomorphicForm_isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite (solution)
