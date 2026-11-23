-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphB
-- name    : ReciprocityTheory_SemistableReduction_ApproxGraphB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:13.65833+00:00
-- url     : https://prove2.me/theorems/ca77ed23-53f1-492f-8ddb-70a3e05c224e
-- title:
--   Approx Graph B
-- statement:
--   Definitions and structural lemmas for Approx Graph B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxGraphB.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_negPart_add
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_negPart_smul
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_posPart_add
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_posPart_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
open ComplexConjugate
def graphMap (p : ℕ) {r : ℕ} (X : Fin r → Fin r → ℂ) : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) where
  toFun w := posPart p (∑ j, posPart p w j • X j) + negPart p w
  map_add' u v := by
    simp only [posPart_add, negPart_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]; abel
  map_smul' c u := by
    have h : ∀ j, posPart p (c • u) j • X j = c • (posPart p u j • X j) := fun j => by
      rw [posPart_smul, Pi.smul_apply, smul_eq_mul, mul_smul]
    rw [Finset.sum_congr rfl (fun j _ => h j)]
    simp only [← Finset.smul_sum, posPart_smul, negPart_smul, RingHom.id_apply, smul_add]
end ReciprocityTheory.MultiplicativeHeights.ApproximationGraph


