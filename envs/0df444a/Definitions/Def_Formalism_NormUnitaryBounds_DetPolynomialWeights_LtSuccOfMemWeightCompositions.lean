-- Prove2me | Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_LtSuccOfMemWeightCompositions
-- name    : Formalism_NormUnitaryBounds_DetPolynomialWeights_LtSuccOfMemWeightCompositions
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T12:24:02.419796+00:00
-- url     : https://prove2.me/theorems/b912ce53-d50a-4196-a744-9dc1a9f62e4b
-- title:
--   Lt Succ Of Mem Weight Compositions
-- statement:
--   Definitions and structural lemmas for Lt Succ Of Mem Weight Compositions, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/LtSuccOfMemWeightCompositions.lean

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearCoefficients
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_weight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
universe u
namespace Formalism.NormUnitaryCountingLemmas
namespace WeightCompositions
variable {N n : ℕ}
lemma sum_blockWt (d : (Fin N × Fin n) →₀ ℕ) :
    ∑ j, Finsupp.weight (blockWt N n) d j = ∑ p, d p := by
  simp only [Finsupp.weight_eq_sum, Finset.sum_apply, blockWt, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [Pi.single_apply]
lemma weight_one (d : (Fin N × Fin n) →₀ ℕ) :
    Finsupp.weight (fun _ : Fin N × Fin n => (1 : ℕ)) d = ∑ p, d p := by
  simp [Finsupp.weight_eq_sum]
variable {K : Type u} [Field K] (ν : Fin N → ℕ)
lemma mem_block {F : MvPolynomial (Fin N × Fin n) K} (hF : F ∈ H K ν) :
    F ∈ weightedHomogeneousSubmodule K (blockWt N n) ν := by
  unfold H at hF
  exact (Submodule.mem_inf.mp hF).1
lemma H_le_total :
    H K (n := n) ν ≤
      weightedHomogeneousSubmodule K (fun _ : Fin N × Fin n => (1 : ℕ)) (∑ j, ν j) := by
  intro F hF
  have hb := mem_block ν hF
  rw [mem_weightedHomogeneousSubmodule] at hb ⊢
  intro d hd
  rw [weight_one, ← sum_blockWt, hb hd]
instance finiteDimensional_H : FiniteDimensional K (H K (n := n) ν) := by
  have : FiniteDimensional K
      (weightedHomogeneousSubmodule K (fun _ : Fin N × Fin n => (1 : ℕ)) (∑ j, ν j)) :=
    Module.Finite.iff_fg.mpr
      (weightedHomogeneousSubmodule_fg K _ (fun _ => one_ne_zero) _)
  exact Submodule.finiteDimensional_of_le (H_le_total ν)
def S0 (n s : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.range (s + 1)).filter (fun w => ∑ k, w k = s)
def Dw (K : Type u) [Field K] (ν : Fin N → ℕ) (w : Fin n → ℕ) : ℕ :=
  Module.finrank K ↥(H K ν ⊓ weightedHomogeneousSubmodule K (coordWt N n) w)
end WeightCompositions
end Formalism.NormUnitaryCountingLemmas


