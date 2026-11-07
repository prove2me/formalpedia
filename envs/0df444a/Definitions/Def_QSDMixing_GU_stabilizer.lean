-- Prove2me | Definitions.Def_QSDMixing_GU_stabilizer
-- name    : QSDMixing_GU_stabilizer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:50:40.69245+00:00
-- url     : https://prove2.me/theorems/3d933da4-3d07-4f91-80c0-0ab7f7532d60
-- title:
--   The stabilizer subgroup $H$ of the generator state
-- statement:
--   For a unitary representation $U$ of a group $G$ on a Hilbert space and a vector $\psi$, the stabilizer is
--
--   $$
--   H=\{h\in G:\ U_h\psi=\psi\}.
--   $$
--
--   **Formalization Note** This is the vector stabilizer: an element acting on $\psi$ by a nontrivial phase does not belong to it.
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), §3, p.17

import Mathlib
import Definitions.Def_GaussTesting_Ell2

set_option autoImplicit false
open GaussTesting (Ell2)

namespace QSDMixing.GU

/-- The stabilizer subgroup `H = {h ∈ G : U_h |ψ⟩ = |ψ⟩}` of the generator state.

Zhou, Leditzky, *A mixing time method for estimating the sample complexity of quantum state discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), §3, p.17.

**Formalization Note.** This is the vector stabilizer. An element acting on `ψ` by a nontrivial phase is
not in it. -/
def stabilizer {G ι : Type} [Group G] (U : G →* unitary (Ell2 ι →L[ℂ] Ell2 ι)) (ψ : Ell2 ι) :
    Subgroup G where
  carrier := {h | (U h : Ell2 ι →L[ℂ] Ell2 ι) ψ = ψ}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_mul, Submonoid.coe_mul, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    have h1 : (U (a⁻¹ * a) : Ell2 ι →L[ℂ] Ell2 ι) ψ = ψ := by simp
    rw [map_mul, Submonoid.coe_mul, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, ha] at h1
    exact h1

end QSDMixing.GU


