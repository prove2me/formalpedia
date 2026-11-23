-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_SopNegComm
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_SopNegComm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:32:19.345804+00:00
-- url     : https://prove2.me/theorems/153ea3a3-f171-4e10-91ec-d286c3001914
-- title:
--   Sop Neg Comm
-- statement:
--   Definitions and structural lemmas for Sop Neg Comm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/SopNegComm.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix WithLp
namespace ReciprocityTheory.ChartRestriction.DS
namespace USum
variable {n : ℕ}
section Ops
variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
def sop (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂) : WithLp 2 (H₁ × H₂) →L[ℂ] WithLp 2 (H₁ × H₂) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H₁ H₂).symm.toContinuousLinearMap ∘L
    ((A.prodMap B) ∘L (WithLp.prodContinuousLinearEquiv 2 ℂ H₁ H₂).toContinuousLinearMap)
def sD (D₁ : Submodule ℂ H₁) (D₂ : Submodule ℂ H₂) : Submodule ℂ (WithLp 2 (H₁ × H₂)) :=
  (D₁.prod D₂).comap (WithLp.linearEquiv 2 ℂ (H₁ × H₂)).toLinearMap
variable {D₁ : Submodule ℂ H₁} {D₂ : Submodule ℂ H₂}
def toP : sD D₁ D₂ →ₗ[ℂ] D₁ × D₂ where
  toFun x := (⟨(ofLp (x : WithLp 2 (H₁ × H₂))).1, x.2.1⟩, ⟨(ofLp (x : WithLp 2 (H₁ × H₂))).2, x.2.2⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def ofP : D₁ × D₂ →ₗ[ℂ] sD D₁ D₂ where
  toFun p := ⟨toLp 2 ((p.1 : H₁), (p.2 : H₂)), p.1.2, p.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def lift (F₁ : Module.End ℂ D₁) (F₂ : Module.End ℂ D₂) : Module.End ℂ (sD D₁ D₂) :=
  ofP ∘ₗ (F₁.prodMap F₂) ∘ₗ toP
def liftL : (Module.End ℂ D₁ × Module.End ℂ D₂) →ₗ[ℂ] Module.End ℂ (sD D₁ D₂) where
  toFun p := lift p.1 p.2
  map_add' _ _ := LinearMap.ext fun _ => rfl
  map_smul' _ _ := LinearMap.ext fun _ => rfl
def sE (E₁ : Fin n → Fin n → Module.End ℂ D₁) (E₂ : Fin n → Fin n → Module.End ℂ D₂) :
    Fin n → Fin n → Module.End ℂ (sD D₁ D₂) :=
  fun a b => lift (E₁ a b) (E₂ a b)
section Rep
variable {ε : Fin n → Bool}
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}
def sσ (σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)) (σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)) :
    Matrix (Fin n) (Fin n) ℂ → (WithLp 2 (H₁ × H₂) →L[ℂ] WithLp 2 (H₁ × H₂)) :=
  fun g => sop (σ₁ g) (σ₂ g)
end Rep
end Ops
end USum
end ReciprocityTheory.ChartRestriction.DS


