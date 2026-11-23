-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionInterSubspace
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionInterSubspace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:13:10.746998+00:00
-- url     : https://prove2.me/theorems/4c823dd3-4c9d-4b5b-8c55-21bb2fef3823
-- title:
--   Extension Inter Subspace
-- statement:
--   Definitions and structural lemmas for Extension Inter Subspace, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/ExtensionInterSubspace.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Nat
namespace Formalism.L2.Th1.H
section ExpSeries
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
def powForm (l : V →L[ℂ] ℂ) (n : ℕ) : ContinuousMultilinearMap ℂ (fun _ : Fin n => V) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compContinuousLinearMap (fun _ => l)
def expTerm {X : Type*} (c : X → ℂ) (l : X → V →L[ℂ] ℂ) (n : ℕ) (x : X) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => V) ℂ :=
  (c x / (n ! : ℂ)) • powForm (l x) n
def expFPS {X : Type*} (c : X → ℂ) (l : X → V →L[ℂ] ℂ) : FormalMultilinearSeries ℂ V ℂ :=
  fun n => ∑' x, expTerm c l n x
end ExpSeries
section KerP
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
def flipR (H : Sesq V) : V →ₗ[ℝ] (V →L[ℂ] ℂ) where
  toFun u := LinearMap.toContinuousLinearMap (H.flip u)
  map_add' := by intro a b; ext z; simp
  map_smul' := by
    intro r u
    ext z
    show H z (r • u) = r • H z u
    rw [← Complex.coe_smul r u, map_smulₛₗ, Complex.conj_ofReal, smul_eq_mul, Complex.real_smul]
def kC (H : Sesq V) (α : V → ℂ) (w x : V) : ℂ :=
  α x * Complex.exp ((Real.pi : ℂ) * H x w - (Real.pi : ℂ) * H x x / 2)
def kL (H : Sesq V) (w x : V) : V →L[ℂ] ℂ :=
  (Real.pi : ℂ) • LinearMap.toContinuousLinearMap (H.flip (w - x))
end KerP
end Formalism.L2.Th1.H


