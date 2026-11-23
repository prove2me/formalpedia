-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit
-- name    : Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:13:22.714996+00:00
-- url     : https://prove2.me/theorems/f15f9354-a2a3-4f35-aa8c-eb0c1b0ab801
-- title:
--   Block Minor Absolute Of Explicit
-- statement:
--   Definitions and structural lemmas for Block Minor Absolute Of Explicit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorAbsoluteOfExplicit.lean

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gk_herm_add_left
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gk_herm_add_right
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gk_herm_smul_left
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gk_herm_smul_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open scoped ComplexConjugate TensorProduct
namespace Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.QuantumDeterminants
noncomputable def tensorBasisCoordinates {W V : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (xi : Module.Basis (Fin n) ℂ V) : (W ⊗[ℂ] V) →ₗ[ℂ] (Fin n → W) :=
  (TensorProduct.piScalarRight ℂ ℂ W (Fin n)).toLinearMap ∘ₗ LinearMap.lTensor W xi.equivFun.toLinearMap
noncomputable def hermitianSesquilinearForm {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => herm H x y)
    (fun u v w => gk_herm_add_left H u v w) (fun c u w => gk_herm_smul_left H c u w)
    (fun u v w => gk_herm_add_right H u v w) (fun c u w => gk_herm_smul_right H c u w)
section ext
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
noncomputable def gramCoordinateMap (H : Matrix ι ι ℂ) (v : σ → ι → ℂ) : (ι → ℂ) →ₗ[ℂ] (σ → ℂ) :=
  ((Matrix.of fun i j => herm H (v j) (v i))⁻¹).mulVecLin ∘ₗ LinearMap.pi fun j => (hermitianSesquilinearForm H).flip (v j)
end ext
def reflectFlagCoordinates (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  fun i => if r ≤ i.val ∧ i.val ≤ r + k then x i else 0
end Formalism.HermitianLatticeCounting.P


