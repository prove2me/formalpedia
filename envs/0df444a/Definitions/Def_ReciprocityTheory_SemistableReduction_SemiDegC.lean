-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegC
-- name    : ReciprocityTheory_SemistableReduction_SemiDegC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:11.363846+00:00
-- url     : https://prove2.me/theorems/47d34432-32a9-4859-aad1-86352630c085
-- title:
--   Semi Deg C
-- statement:
--   Definitions and structural lemmas for Semi Deg C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegC.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_succ
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_hermForm_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_succ
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_zero


set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
open NumberField Matrix
open scoped nonZeroDivisors
def coordForm {K : Type} [Field K] [NumberField K] {r k : ℕ} (S : HermForm K r)
    (b : Fin k → Fin r → K) : HermForm K k where
  c := S.c
  c_invol := S.c_invol
  c_emb := S.c_emb
  G := hGram S b
  G_herm i j := hermForm_conj S (b i) (b j)
def combMap {K : Type} [Field K] {r k : ℕ} (b : Fin k → Fin r → K) :
    (Fin k → K) →ₗ[K] (Fin r → K) where
  toFun t := ∑ i, t i • b i
  map_add' s t := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a t := by simp [Finset.smul_sum, smul_smul]
def coordLat {K : Type} [Field K] [NumberField K] {r k : ℕ} (B : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) : Submodule (𝓞 K) (Fin k → K) := B.comap ((combMap b).restrictScalars (𝓞 K))
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
namespace ReciprocityTheory.MultiplicativeHeights
open SemiDegIdx
end ReciprocityTheory.MultiplicativeHeights


