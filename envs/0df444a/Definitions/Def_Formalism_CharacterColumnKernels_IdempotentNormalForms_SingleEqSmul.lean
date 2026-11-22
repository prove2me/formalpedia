-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SingleEqSmul
-- name    : Formalism_CharacterColumnKernels_IdempotentNormalForms_SingleEqSmul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:15:54.725743+00:00
-- url     : https://prove2.me/theorems/b4ab58c8-b5de-4615-a086-d9e56f0acb69
-- title:
--   Single Eq Smul
-- statement:
--   Definitions and structural lemmas for Single Eq Smul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/SingleEqSmul.lean

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.NG
section HomAux
variable {R O M : Type*} [Ring R] [CommRing O] [AddCommGroup M] [Module R M] [Module O M]
  [SMulCommClass R O M] {m g : Type} [Fintype m] [Fintype g] [DecidableEq g]
theorem relMap_apply' (Θ : Matrix m g R) (v : g → M) (i : m) :
    relMap O M Θ v i = ∑ j, Θ i j • v j := rfl
def combo (v : g → M) : (g → R) →ₗ[R] M where
  toFun w := ∑ j, w j • v j
  map_add' w w' := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r w := by simp [mul_smul, Finset.smul_sum]
theorem combo_apply (v : g → M) (w : g → R) : combo v w = ∑ j, w j • v j := rfl
theorem combo_single (v : g → M) (j : g) (x : R) : combo v (Pi.single j x) = x • v j := by
  rw [combo_apply]
  simp [Pi.single_apply, ite_smul]
theorem single_eq_smul (j : g) (x : R) : (Pi.single j x : g → R) = x • Pi.single j 1 := by
  ext i
  by_cases h : i = j
  · subst h; simp
  · simp [h]
theorem sum_row (Θ : Matrix m g R) (i : m) :
    ∑ j, Θ i j • (Pi.single j (1 : R) : g → R) = Θ i := by
  ext k
  simp [Finset.sum_apply, Pi.single_apply]
def toVec (Θ : Matrix m g R) (φ : Coker Θ →ₗ[R] M) : g → M :=
  fun j => φ ((relSpan Θ).mkQ (Pi.single j (1 : R)))
theorem toVec_mem (Θ : Matrix m g R) (φ : Coker Θ →ₗ[R] M) :
    toVec Θ φ ∈ LinearMap.ker (relMap O M Θ) := by
  rw [LinearMap.mem_ker]
  funext i
  rw [relMap_apply', Pi.zero_apply]
  simp only [toVec]
  have h : ∑ j, Θ i j • φ ((relSpan Θ).mkQ (Pi.single j (1 : R))) =
      φ ((relSpan Θ).mkQ (∑ j, Θ i j • (Pi.single j (1 : R) : g → R))) := by
    simp [map_sum, map_smul]
  rw [h, sum_row]
  have hmem : Θ i ∈ relSpan Θ := Submodule.subset_span ⟨i, rfl⟩
  rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr hmem, map_zero]
def ofVec (Θ : Matrix m g R) (v : LinearMap.ker (relMap O M Θ)) : Coker Θ →ₗ[R] M :=
  (relSpan Θ).liftQ (combo (v : g → M)) (by
    rw [relSpan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, combo_apply]
    have h := congrFun (LinearMap.mem_ker.mp v.2) i
    rw [relMap_apply'] at h
    exact h)
theorem ofVec_mk (Θ : Matrix m g R) (v : LinearMap.ker (relMap O M Θ)) (w : g → R) :
    ofVec Θ v (Submodule.Quotient.mk w) = combo (v : g → M) w := rfl
def homEquiv (Θ : Matrix m g R) : (Coker Θ →ₗ[R] M) ≃ₗ[O] LinearMap.ker (relMap O M Θ) where
  toFun φ := ⟨toVec Θ φ, toVec_mem Θ φ⟩
  invFun v := ofVec Θ v
  map_add' φ ψ := by
    apply Subtype.ext; funext j; simp [toVec]
  map_smul' c φ := by
    apply Subtype.ext; funext j; simp [toVec]
  left_inv φ := by
    apply Submodule.linearMap_qext
    apply LinearMap.pi_ext
    intro j x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply, ofVec_mk, combo_single,
      single_eq_smul j x, Submodule.Quotient.mk_smul, map_smul]
    rfl
  right_inv v := by
    apply Subtype.ext; funext j
    show ofVec Θ v (Submodule.Quotient.mk (Pi.single j (1 : R))) = (v : g → M) j
    rw [ofVec_mk, combo_single, one_smul]
end HomAux
end Formalism.NG


