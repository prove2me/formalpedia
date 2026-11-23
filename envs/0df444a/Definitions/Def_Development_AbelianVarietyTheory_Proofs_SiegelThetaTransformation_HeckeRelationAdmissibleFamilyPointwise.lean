-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:46.171287+00:00
-- url     : https://prove2.me/theorems/53397ea4-55ba-4f6d-893d-d3dab2798037
-- title:
--   Hecke Relation Admissible Family Pointwise
-- statement:
--   Definitions and structural lemmas for Hecke Relation Admissible Family Pointwise, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HeckeRelationAdmissibleFamilyPointwise.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
import Theorems.Thm_GlobalTheory_SW_Base_herm_one
import Theorems.Thm_P2M_GlobalTheory_SW_Nbr_Int__symm_b5c59deb8a7e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open scoped TensorProduct LinearAlgebra.Projectivization
namespace GlobalTheory.SW.HeckeId
section Abstract
variable {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
def Hyp (P : Ideal O) (M : Type) [AddCommGroup M] [Module O M] : Set (Submodule O M) :=
  {N | ∃ f : M →ₗ[O] O ⧸ P, f ≠ 0 ∧ LinearMap.ker f = N}
attribute [local instance] Ideal.Quotient.field
end Abstract
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
open Nbr
noncomputable def eT (w : E) : ℂ := cexp (2 * Real.pi * I * ((Algebra.trace ℚ E w : ℚ) : ℂ))
omit [IsCMField E] in
theorem eT_add (w w' : E) : eT (w + w') = eT w * eT w' := by
  simp [eT, mul_add, Complex.exp_add]
omit [IsCMField E] in
theorem eT_eq_one_iff (w : E) : eT w = 1 ↔ ∃ k : ℤ, Algebra.trace ℚ E w = k := by
  rw [eT, Complex.exp_eq_one_iff]
  refine exists_congr fun k => ?_
  rw [mul_comm, mul_left_inj' Complex.two_pi_I_ne_zero]
  exact_mod_cast Iff.rfl
omit [IsCMField E] in
theorem eT_int {w : E} (h : IsIntegral ℤ w) : eT w = 1 := by
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (Algebra.isIntegral_trace (L := ℚ) (F := E) h)
  exact (eT_eq_one_iff w).2 ⟨k, hk.symm⟩
noncomputable def sym (a b : Fin N → E) : Matrix (Fin N) (Fin N) E :=
  vecMulVec a (fun i => cc (b i)) + vecMulVec b fun i => cc (a i)
theorem herm_ar (x y y' : Fin n → E) : herm 1 x (y + y') = herm 1 x y + herm 1 x y' := by
  simp [Nbr.herm_one, cc, mul_add, Finset.sum_add_distrib]
def perp (Λ : Lt E n) (y : Fin n → E) : Submodule (𝓞 E) Λ :=
  Submodule.comap Λ.subtype
    { carrier := {x : Fin n → E | Int' x y}
      add_mem' := fun ha hb => Int'.add ha hb
      zero_mem' := int_zero y
      smul_mem' := fun c _ hx => Int'.smul c hx }
variable {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
noncomputable def pairChar (u : X →ₗ[𝓞 E] (Fin n → E)) (b : 𝓞 E) (η : X) : AddChar X ℂ where
  toFun := fun ξ => eT (herm 1 (u η) (u (b • ξ)))
  map_zero_eq_one' := eT_int (Int'.symm (by rw [smul_zero, map_zero]; exact int_zero _))
  map_add_eq_mul' := fun ξ ξ' => by rw [smul_add, map_add, herm_ar, eT_add]
end GlobalTheory.SW.HeckeId


