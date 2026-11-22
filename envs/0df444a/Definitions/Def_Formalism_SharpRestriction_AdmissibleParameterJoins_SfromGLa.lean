-- Prove2me | Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_SfromGLa
-- name    : Formalism_SharpRestriction_AdmissibleParameterJoins_SfromGLa
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:20:55.504992+00:00
-- url     : https://prove2.me/theorems/62e9052e-e05b-4c2f-8358-e6d53b2d781e
-- title:
--   Sfrom GLa
-- statement:
--   Definitions and structural lemmas for Sfrom GLa, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLa.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.J
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
section Transport
variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
def latMap (φ : V ≃ₗ[K] V') (M : Submodule (𝓞 K) V) : Submodule (𝓞 K) V' :=
  M.map ((φ : V →ₗ[K] V').restrictScalars (𝓞 K))
theorem mem_tr (φ : V ≃ₗ[K] V') (M : Submodule (𝓞 K) V) (y : V') : y ∈ latMap φ M ↔ φ.symm y ∈ M := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨φ.symm y, h, by simp⟩
theorem tr_symm_tr (φ : V ≃ₗ[K] V') (M : Submodule (𝓞 K) V) : latMap φ.symm (latMap φ M) = M := by
  ext x; simp [mem_tr]
theorem tr_injective (φ : V ≃ₗ[K] V') : Function.Injective (latMap (K := K) φ) := fun a b h => by
  rw [← tr_symm_tr φ a, h, tr_symm_tr]
def cj (φ : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) : V' ≃ₗ[K] V' := (φ.symm.trans g).trans φ
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
end Transport
end Formalism.MainNotions.J
end


