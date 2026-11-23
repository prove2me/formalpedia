-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_TangentPairingStatement
-- name    : ReciprocityTheory_DualLattices_TangentPairingStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:02.153065+00:00
-- url     : https://prove2.me/theorems/4f5b45a9-3f85-451f-ac73-70b7b1113041
-- title:
--   Tangent Pairing Statement
-- statement:
--   Definitions and structural lemmas for Tangent Pairing Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/TangentPairingStatement.lean

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Theorems.Thm_ReciprocityTheory_PGsh_LHom_sqZero_of_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
namespace ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
namespace BX
variable (B : BX R₀)
def evK {R' R : LAlg R₀} (π : LHom R' R) (h : B.gg →ₗ[R₀] R') (V : B.gg ⊗[R₀] π.ker) : R' :=
  LinearMap.mul' R₀ R' (TensorProduct.map h π.ker.subtype V)
end BX
def TangentPairingStatement (B : BX R₀) : Prop :=
  ∀ (R' R : LAlg R₀) (π : LHom R' R) (ξ : (R' : Type u)) (Dp : DualPair R) (N : ℕ)
    (hsurj : Function.Surjective π.1) (hker : RingHom.ker π.1 = Ideal.span {ξ}) (hsq : ξ * ξ = 0),
    (∀ a, a * ξ = 0 → a ∈ Ideal.span {ξ}) → (N : (R' : Type u)) = 0 →
    ∀ (sh th : B.G R') (Vs Vt : B.gg ⊗[R₀] π.ker) (hs ht : B.gg →ₗ[R₀] R')
      (zh : (R' : Type u)ˣ) (z : (R : Type u)ˣ),
      N • sh = B.tg π (π.sqZero_of_span ξ hsurj hker hsq) Vs → N • th = B.tg π (π.sqZero_of_span ξ hsurj hker hsq) Vt →
      B.IsHeight Dp N (B.map π sh) (π.1.toLinearMap ∘ₗ hs) →
      B.IsHeight Dp N (B.map π th) (π.1.toLinearMap ∘ₗ ht) →
      B.IsPairing N (B.map π sh) (B.map π th) z → Units.map (π.1 : R' →* R) zh = z →
      (zh : (R' : Type u)) ^ N = 1 + (B.evK π ht Vs - B.evK π hs Vt)
end ReciprocityTheory.PGsh


