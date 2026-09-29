-- Prove2me | solution 1 for AutomorphicForm.setIntegral_centralEllipticPart_fold_eq_zero_of_forall_apply_mul_centralScalar_eq_of_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/33087554-e1c6-5d39-95da-87847c9e9689

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_NumberField_AdelicHeight
import Theorems.Thm_NumberField_setIntegral_ideleClassChar_mul_eq_zero_of_isFundamentalDomain_of_forall_mul_eq_of_apply_ne_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_centralEllipticPart_fold_eq_zero_of_forall_apply_mul_centralScalar_eq_of_ne_one

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open Matrix Polynomial

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace AutomorphicForm
p2m_export "AutomorphicForm" "AdelicGL2 globalPoints centralScalar centralCell hyperbolicCell ellipticCell mem_centralCell_iff mem_hyperbolicCell_iff mem_ellipticCell_iff adelicKernelCentralPart adelicKernelEllipticPart"
p2m_open "AutomorphicForm"

section Cells

variable {k : Type*} [Field k]

theorem val_mul_scalar' (γ : GL (Fin 2) k) (u : kˣ) :
    ((γ * Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      (u : k) • (γ : Matrix (Fin 2) (Fin 2) k) := by
  rw [Units.val_mul]
  change (γ : Matrix (Fin 2) (Fin 2) k) * Matrix.scalar (Fin 2) (u : k) = _
  rw [Matrix.scalar_apply, ← smul_eq_mul_diagonal]

theorem charpoly_eq_mul_iff' (M : Matrix (Fin 2) (Fin 2) k) (a b : k) :
    M.charpoly = (X - C a) * (X - C b) ↔ M.trace = a + b ∧ M.det = a * b := by
  have e2 : ((X - C a) * (X - C b) : k[X]) = X ^ 2 - C (a + b) * X + C (a * b) := by
    simp only [map_add, map_mul]; ring
  rw [Matrix.charpoly_fin_two, e2]
  constructor
  · intro e
    have h0 := congrArg (fun p : k[X] => p.coeff 0) e
    have h1 := congrArg (fun p : k[X] => p.coeff 1) e
    simp [coeff_C] at h0 h1
    exact ⟨by linear_combination (-1 : k) * h1, h0⟩
  · rintro ⟨ht, hd⟩
    rw [ht, hd]

theorem mul_scalar_mem_hyperbolicCell' {γ : GL (Fin 2) k} (hγ : γ ∈ hyperbolicCell k) (u : kˣ) :
    γ * Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ hyperbolicCell k := by
  rw [mem_hyperbolicCell_iff] at hγ ⊢
  rw [val_mul_scalar']
  obtain ⟨a, b, hab, hch⟩ := hγ
  have hu : (u : k) ≠ 0 := u.ne_zero
  refine ⟨(u : k) * a, (u : k) * b, fun h => hab (mul_left_cancel₀ hu h), ?_⟩
  rw [charpoly_eq_mul_iff'] at hch ⊢
  rw [Matrix.trace_smul, Matrix.det_smul, hch.1, hch.2, Fintype.card_fin]
  simp only [smul_eq_mul]
  constructor <;> ring

theorem bijOn_mul_scalar' (S : Set (GL (Fin 2) k))
    (hS : ∀ γ ∈ S, ∀ u : kˣ, γ * Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ S) (u : kˣ) :
    Set.BijOn (fun γ : GL (Fin 2) k => γ * Matrix.GeneralLinearGroup.scalar (Fin 2) u) S S := by
  refine ⟨fun γ hγ => hS γ hγ u, fun a _ b _ h => mul_right_cancel h, fun γ hγ => ?_⟩
  refine ⟨γ * Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹, hS γ hγ u⁻¹, ?_⟩
  show γ * Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u = γ
  rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]

end Cells

section Central

variable (K : Type) [Field K] [NumberField K]

theorem mul_centralScalar_comm' (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    g * centralScalar (𝓞 K) K z = centralScalar (𝓞 K) K z * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  change (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) * Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 K) K) =
    Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 K) K) * (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
  exact ((Matrix.scalar_commute (z : AdeleRing (𝓞 K) K) (fun r' => mul_comm _ r') _).eq).symm

theorem centralScalar_units_map_algebraMap' (u : Kˣ) :
    centralScalar (𝓞 K) K (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) =
      globalPoints (𝓞 K) K (Matrix.GeneralLinearGroup.scalar (Fin 2) u) := by
  apply Units.ext
  ext i j
  change (Matrix.scalar (Fin 2) (algebraMap K (AdeleRing (𝓞 K) K) (u : K))) i j =
    algebraMap K (AdeleRing (𝓞 K) K) ((Matrix.scalar (Fin 2) (u : K)) i j)
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs
  · rfl
  · exact (map_zero _).symm

theorem finsum_mem_globalPoints_scalar_mul' {M : Type*} [AddCommMonoid M]
    (S : Set (GL (Fin 2) K)) (hS : ∀ γ ∈ S, ∀ u : Kˣ, γ * Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ S)
    (F : AdelicGL2 (𝓞 K) K → M) (x y : AdelicGL2 (𝓞 K) K) (u : Kˣ) :
    ∑ᶠ γ ∈ S, F (x⁻¹ * globalPoints (𝓞 K) K γ *
        (globalPoints (𝓞 K) K (Matrix.GeneralLinearGroup.scalar (Fin 2) u) * y)) =
      ∑ᶠ γ ∈ S, F (x⁻¹ * globalPoints (𝓞 K) K γ * y) := by
  refine finsum_mem_eq_of_bijOn (fun γ : GL (Fin 2) K => γ * Matrix.GeneralLinearGroup.scalar (Fin 2) u)
    (bijOn_mul_scalar' S hS u) (fun γ _ => ?_)
  simp only [map_mul, mul_assoc]

theorem finsum_mem_mul_right' {M : Type*} [AddCommMonoid M]
    (S : Set (GL (Fin 2) K)) (F : AdelicGL2 (𝓞 K) K → M) (c : AdelicGL2 (𝓞 K) K)
    (hF : ∀ g, F (g * c) = F g) (x y : AdelicGL2 (𝓞 K) K) :
    ∑ᶠ γ ∈ S, F (x⁻¹ * globalPoints (𝓞 K) K γ * (y * c)) = ∑ᶠ γ ∈ S, F (x⁻¹ * globalPoints (𝓞 K) K γ * y) := by
  refine finsum_mem_congr rfl (fun γ _ => ?_)
  rw [← mul_assoc, hF]

end Central

section CellsCE

variable {k : Type*} [Field k]

theorem mul_scalar_mem_centralCell' {γ : GL (Fin 2) k} (hγ : γ ∈ centralCell k) (u : kˣ) :
    γ * Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ centralCell k := by
  rw [mem_centralCell_iff] at hγ ⊢
  obtain ⟨c, hc⟩ := hγ
  refine ⟨(u : k) * c, ?_⟩
  rw [val_mul_scalar', hc, smul_smul]

theorem mul_scalar_mem_ellipticCell' {γ : GL (Fin 2) k} (hγ : γ ∈ ellipticCell k) (u : kˣ) :
    γ * Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ ellipticCell k := by
  rw [mem_ellipticCell_iff] at hγ ⊢
  intro a ha
  apply hγ ((u : k)⁻¹ * a)
  have hu : (u : k) ≠ 0 := u.ne_zero
  rw [Polynomial.IsRoot, Matrix.charpoly_fin_two] at ha ⊢
  rw [val_mul_scalar', Matrix.trace_smul, Matrix.det_smul, Fintype.card_fin] at ha
  simp only [smul_eq_mul, eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C] at ha ⊢
  have key : ((u : k)⁻¹ * a) ^ 2 - (γ : Matrix (Fin 2) (Fin 2) k).trace * ((u : k)⁻¹ * a) + (γ : Matrix (Fin 2) (Fin 2) k).det =
      (u : k)⁻¹ ^ 2 * (a ^ 2 - (u : k) * (γ : Matrix (Fin 2) (Fin 2) k).trace * a + (u : k) ^ 2 * (γ : Matrix (Fin 2) (Fin 2) k).det) := by
    field_simp
  rw [key, ha, mul_zero]

end CellsCE

open scoped TensorProduct.RightActions in
theorem _root_.P2MW.S_AutomorphicForm_setIntegral_centralEllipticPart_fold_eq_zero_of_forall_apply_mul_centralScalar_eq_of_ne_one.solution
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (φK : AdelicGL2 (𝓞 K) K → ℂ)
    (z₀ : (AdeleRing (𝓞 K) K)ˣ) (hz₀ : ξ ⟨z₀, Subgroup.mem_top z₀⟩ ≠ 1)
    (hφ : ∀ g : AdelicGL2 (𝓞 K) K, φK (g * AutomorphicForm.centralScalar (𝓞 K) K z₀) = φK g)
    (x : AdelicGL2 (𝓞 K) K) :
    (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      (AutomorphicForm.adelicKernelCentralPart K φK x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
        AutomorphicForm.adelicKernelEllipticPart K φK x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK) = 0 := by
  classical
  have hC : ∀ γ ∈ centralCell K, ∀ u : Kˣ, γ * Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ centralCell K :=
    fun γ hγ u => mul_scalar_mem_centralCell' hγ u
  have hE : ∀ γ ∈ ellipticCell K, ∀ u : Kˣ, γ * Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ ellipticCell K :=
    fun γ hγ u => mul_scalar_mem_ellipticCell' hγ u
  refine NumberField.setIntegral_ideleClassChar_mul_eq_zero_of_isFundamentalDomain_of_forall_mul_eq_of_apply_ne_one
    K νZK ΩK hΩK ξ hξt z₀ hz₀
    (fun z : (AdeleRing (𝓞 K) K)ˣ =>
      AutomorphicForm.adelicKernelCentralPart K φK x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
        AutomorphicForm.adelicKernelEllipticPart K φK x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ?_ ?_
  ·
    intro γ₀ hγ₀ z
    obtain ⟨u, rfl⟩ := hγ₀
    beta_reduce
    rw [map_mul, mul_assoc]
    unfold adelicKernelCentralPart adelicKernelEllipticPart
    rw [centralScalar_units_map_algebraMap', finsum_mem_globalPoints_scalar_mul' K (centralCell K) hC φK x _ u,
      finsum_mem_globalPoints_scalar_mul' K (ellipticCell K) hE φK x _ u]
  ·
    intro z
    beta_reduce
    have hc : AutomorphicForm.centralScalar (𝓞 K) K (z * z₀) * x =
        AutomorphicForm.centralScalar (𝓞 K) K z * x * AutomorphicForm.centralScalar (𝓞 K) K z₀ := by
      rw [map_mul, mul_assoc, mul_assoc, mul_centralScalar_comm' K z₀ x]
    rw [hc]
    unfold adelicKernelCentralPart adelicKernelEllipticPart
    rw [finsum_mem_mul_right' K (centralCell K) φK _ hφ x, finsum_mem_mul_right' K (ellipticCell K) φK _ hφ x]

end AutomorphicForm

end S_AutomorphicForm_setIntegral_centralEllipticPart_fold_eq_zero_of_forall_apply_mul_centralScalar_eq_of_ne_one
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_centralEllipticPart_fold_eq_zero_of_forall_apply_mul_centralScalar_eq_of_ne_one (solution)
