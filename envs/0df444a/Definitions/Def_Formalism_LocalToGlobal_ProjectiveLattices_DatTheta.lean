-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DatTheta
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_DatTheta
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:03:03.54626+00:00
-- url     : https://prove2.me/theorems/a2d3b8da-20a4-4fc6-8018-0aa569f7d56b
-- title:
--   Dat Theta
-- statement:
--   Definitions and structural lemmas for Dat Theta, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DatTheta.lean

import Mathlib
import Definitions.Def_Lemmata_FirstBlockLemmaH_Imports
import Definitions.Def_Lemmata_GeneralBFactThirdVariant_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj.DatLin
open NumberField TensorProduct
open scoped nonZeroDivisors ComplexConjugate
variable {E : Type} [Field E] [NumberField E]
section Scalar
variable (Ψ : Finset (E →+* ℂ))
def embO : 𝓞 E →+ (Ψ → ℂ) where
  toFun e τ := (τ : E →+* ℂ) (e : E)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp
def phi1 : ℝ ⊗[ℤ] 𝓞 E →ₗ[ℝ] (Ψ → ℂ) := LinearMap.liftBaseChange ℝ (embO Ψ).toIntLinearMap
variable {Ψ}
end Scalar
section General
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (b : Module.Basis ι E V) (Ψ : Finset (E →+* ℂ)) (M : Submodule (𝓞 E) V)
def coordO : M →+ (Ψ → ι → ℂ) where
  toFun v τ i := (τ : E →+* ℂ) (b.repr v i)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp
def theta : ℝ ⊗[ℤ] M →ₗ[ℝ] (Ψ → ι → ℂ) :=
  LinearMap.liftBaseChange ℝ (coordO b Ψ M).toIntLinearMap
def embI : (ι → 𝓞 E) →+ (Ψ → ι → ℂ) where
  toFun n τ i := (τ : E →+* ℂ) (n i : E)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp
def phiI : ℝ ⊗[ℤ] (ι → 𝓞 E) →ₗ[ℝ] (Ψ → ι → ℂ) :=
  LinearMap.liftBaseChange ℝ (embI (ι := ι) Ψ).toIntLinearMap
variable {Ψ}
variable {b M}
variable (b M)
def kapF (s : 𝓞 E) (hs : ∀ v ∈ M, ∀ i,
      algebraMap (𝓞 E) E s * b.repr v i ∈ (algebraMap (𝓞 E) E).range) (v : M) (i : ι) : 𝓞 E :=
  (hs v v.2 i).choose
theorem kapF_spec (s : 𝓞 E) (hs) (v : M) (i : ι) :
    algebraMap (𝓞 E) E (kapF b M s hs v i) = algebraMap (𝓞 E) E s * b.repr v i :=
  (hs v v.2 i).choose_spec
def kap (s : 𝓞 E) (hs : ∀ v ∈ M, ∀ i,
      algebraMap (𝓞 E) E s * b.repr v i ∈ (algebraMap (𝓞 E) E).range) : M →+ (ι → 𝓞 E) where
  toFun v i := kapF b M s hs v i
  map_zero' := by
    funext i
    apply IsFractionRing.injective (𝓞 E) E
    rw [kapF_spec]
    simp
  map_add' x y := by
    funext i
    apply IsFractionRing.injective (𝓞 E) E
    simp only [Pi.add_apply, map_add]
    rw [kapF_spec, kapF_spec, kapF_spec]
    simp [mul_add]
def iota1 (s' : 𝓞 E) (hs' : ∀ i, s' • b i ∈ M) : (ι → 𝓞 E) →+ M where
  toFun n := ⟨∑ i, n i • s' • b i, Submodule.sum_mem _ fun i _ => M.smul_mem _ (hs' i)⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [add_smul, Finset.sum_add_distrib]
end General
end Formalism.L2.Pj.DatLin


