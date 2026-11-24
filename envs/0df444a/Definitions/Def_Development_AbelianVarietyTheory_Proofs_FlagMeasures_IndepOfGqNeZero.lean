-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndepOfGqNeZero
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndepOfGqNeZero
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T21:47:02.138296+00:00
-- url     : https://prove2.me/theorems/49530eaa-085d-437c-ba81-02381c33b0ce
-- title:
--   Indep Of Gq Ne Zero
-- statement:
--   Definitions and structural lemmas for Indep Of Gq Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IndepOfGqNeZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_DiagMemCongruencePairs
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_gq_zero
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_mem_genConf_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
namespace GlobalTheory.SgGlob.Iota
variable {E : Type} [Field E] [NumberField E]
variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}
def formL (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (w : Fin n → E) : (Fin n → E) →ₗ[E] E where
  toFun v := form σ J v w
  map_add' a b := by simp [form, Matrix.mulVec_add]
  map_smul' a b := by simp [form, Matrix.mulVec_smul]
section Pair
variable {g : ℕ} {Λ : Submodule (𝓞 E) (Fin n → E)} {P P' : Matrix (Fin n) (Fin (r + 1)) E}
end Pair
section Gram
end Gram
example (σ : E →+* E) {g : ℕ} (hg : g ≠ 0) :
    IsHermU σ (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) E) ∧
      Gq (r := 0) σ 1 (1 + 2 * g) !![-1 - (g : E)] ≠ 0 ∧
      (GenConf (r := 0) σ !![1, 0; 0, -1] 1 (1 + 2 * g) g !![-1 - (g : E)]).Nonempty :=
  ⟨⟨by ext i j; fin_cases i <;> fin_cases j <;> simp [cT], by simp [Matrix.det_fin_two]⟩,
    by rw [Inhab.gq_zero]; exact pow_ne_zero _ (Nat.cast_ne_zero.2 hg), _, Inhab.mem_genConf_zero σ hg⟩
end GlobalTheory.SgGlob.Iota


