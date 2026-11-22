-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsOrthonormalFrameComplement
-- name    : Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsOrthonormalFrameComplement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:46:05.176378+00:00
-- url     : https://prove2.me/theorems/1ae7713c-8f58-431b-88c1-f3614d8600e4
-- title:
--   Exists Orthonormal Frame Complement
-- statement:
--   Definitions and structural lemmas for Exists Orthonormal Frame Complement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsOrthonormalFrameComplement.lean

import Definitions.Def_Formalism_SizeWindowBrackets_MatrixFamilyBoundsOfCardEqCeil
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module NumberField
open scoped ComplexOrder
namespace Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
noncomputable section
section Fam
variable {ι : Type} [Fintype ι] {D D' : ℕ} {d : ι → ℕ}
end Fam
section Inv
variable {n : ℕ}
end Inv
section Frame
variable {Dall D D1 : ℕ}
end Frame
namespace Model
def J0 : Matrix (Fin 2) (Fin 1) ℂ := !![1; 0]
def modelEmbedding : Matrix (Fin 2) (Fin 1) ℂ := !![0; 1]
def c0 : Fin 20 → ℂ := fun _ => 2 * Complex.I
def P0 : ∀ _u : Fin 20, Matrix (Fin 2) (Fin 2) ℂ := fun _ => 1
def r0 : Fin 20 → ℕ := fun u => if u = 0 then 1 else 2
def En (n : ℕ) : Matrix (Fin 2) (Fin n) ℂ := fun i j => if i.val = j.val then 1 else 0
def V0 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def U0 : ∀ u : Fin 20, Matrix (Fin (r0 u)) (Fin (r0 u)) ℂ := fun _ => Complex.I • 1
def A0 : ∀ u, Matrix (Fin 1) (Fin (r0 u)) ℂ :=
  fun u => c0 u • (J0ᴴ * (V0 * Bram (d := fun _ => 2) (r := r0) P0 (fun u => En (r0 u)) u * U0 u))
end Model
namespace Model
section Lat
variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
def bW : Basis (Fin 1) K K := Basis.singleton (Fin 1) K
def bV (i : Fin 20) : Basis (Fin (r0 i)) K (Fin (r0 i) → K) := Pi.basisFun K (Fin (r0 i))
def Lc : Submodule (𝓞 K) K := Submodule.span (𝓞 K) {(1 : K)}
def LN (i : Fin 20) : Submodule (𝓞 K) (Fin (r0 i) → K) :=
  Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin (r0 i))))
def MB (i : Fin 20) : Matrix (Fin 1) (Fin (r0 i)) K := fun _ j => if j.val = 1 then -2 else 0
def BB (i : Fin 20) : (Fin (r0 i) → K) →ₗ[K] K := Matrix.toLin (bV K i) (bW K) (MB K i)
end Lat
end Model
end
end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance


