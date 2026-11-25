-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDA
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDA
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:16:11.571185+00:00
-- url     : https://prove2.me/theorems/fdf44e02-2019-47f7-b915-58310eaaa760
-- title:
--   Tie LDA
-- statement:
--   Definitions and structural lemmas for Tie LDA, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/TieLDA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.L2.Pj.QAt.TieLDA
open TensorProduct Module
def tm (K K₁ : Type*) [Field K] [Field K₁] [Algebra K K₁] {U : Type*} [AddCommGroup U]
    [Module K U] (u : U) : K₁ ⊗[K] U :=
  (1 : K₁) ⊗ₜ[K] u
section Base
variable {K K₁ : Type*} [Field K] [Field K₁] [Algebra K K₁]
abbrev modT (T : Subring K₁) (U : Type*) [AddCommGroup U] [Module K U] :
    Module T (K₁ ⊗[K] U) :=
  Module.compHom _ T.subtype
attribute [local instance] modT
abbrev modR (R : Type*) [CommRing R] [Algebra R K] (U : Type*) [AddCommGroup U] [Module K U] :
    Module R (K₁ ⊗[K] U) :=
  Module.compHom _ (algebraMap R K)
attribute [local instance] modR
variable {U : Type*} [AddCommGroup U] [Module K U]
theorem smulT_def (T : Subring K₁) (t : T) (l : K₁ ⊗[K] U) : t • l = (t : K₁) • l := rfl
instance scalarT (T : Subring K₁) : IsScalarTower T K₁ (K₁ ⊗[K] U) :=
  ⟨fun t k l => by rw [smulT_def, Subring.smul_def, smul_eq_mul, mul_smul]⟩
theorem smulK_eq (k : K) (l : K₁ ⊗[K] U) : k • l = algebraMap K K₁ k • l := by
  induction l using TensorProduct.induction_on with
  | zero => simp
  | tmul a u =>
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', Algebra.smul_def]
    rfl
  | add x y hx hy => rw [smul_add, smul_add, hx, hy]
section R
variable {R : Type*} [CommRing R] [Algebra R K] [Module R U] [IsScalarTower R K U]
def tmR : U →ₗ[R] K₁ ⊗[K] U where
  toFun u := tm K K₁ u
  map_add' x y := tmul_add _ _ _
  map_smul' r u := by
    change (1 : K₁) ⊗ₜ[K] (r • u) = algebraMap R K r • ((1 : K₁) ⊗ₜ[K] u)
    rw [← algebraMap_smul K r u, tmul_smul]
variable (T : Subring K₁) [Algebra R T]
  (hRT : ∀ r : R, ((algebraMap R T r : T) : K₁) = algebraMap K K₁ (algebraMap R K r))
include hRT in
theorem tower : IsScalarTower R T (K₁ ⊗[K] U) := by
  constructor
  intro r t l
  show ((r • t : T) : K₁) • l = algebraMap R K r • ((t : K₁) • l)
  rw [smulK_eq, smul_smul, Algebra.smul_def r t, Subring.coe_mul, hRT]
noncomputable def Phi (X : Submodule R U) : T ⊗[R] X →ₗ[T] K₁ ⊗[K] U :=
  @LinearMap.liftBaseChange R X (K₁ ⊗[K] U) T _ _ _ _ _ _ _ _ (tower (U := U) T hRT)
    ((tmR (K₁ := K₁) (K := K) (U := U)).comp X.subtype)
variable [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K]
end R
end Base
section DVR
end DVR
end Formalism.L2.Pj.QAt.TieLDA


