-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_SamplingScale
-- name    : ConsistentSubmodular_Deterministic_Reduction_SamplingScale
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:11:27.358832+00:00
-- url     : https://prove2.me/theorems/2fd45ce7-c02e-4acf-810d-8cc0b0689558
-- title:
--   Contraction of an objective onto a ground set with a fixed buffer baseline
-- statement:
--   Let $f$ be a nonnegative monotone submodular objective on $[n]$ (`Objective n`, with value $f(\emptyset)$ possibly nonzero).
--
--   - `Objective.contractOn f U B`: for a set $U\subseteq[n]$ of old elements and a fixed buffer $B\subseteq[n]$, the objective
--   $$f_{U,B}(S)\;=\;f\bigl(B\cup (S\cap U)\bigr)-f(B).$$
--   It restricts the dependence on $S$ to the old ground set $U$ and subtracts the baseline value of the buffer. The structure fields are discharged inside the definition: $f_{U,B}$ is nonnegative (by monotonicity of $f$), monotone, and submodular (the union and intersection of two sets $B\cup(S\cap U)$ and $B\cup(T\cap U)$ are $B\cup((S\cup T)\cap U)$ and $B\cup((S\cap T)\cap U)$).
--
--   The file also proves that the contracted objective vanishes on the empty set, $f_{U,B}(\emptyset)=0$.
--
--   This contraction is the normalization used in the sampling and rounding step of the reduction for deterministic algorithms (Appendix B): the marginal value of old elements on top of the buffer of recently arrived elements is again a monotone submodular objective with value zero at the empty set.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/SamplingScale.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_SharedThreshold
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Model
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_PhysicalSampling

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Objective

variable {n : ℕ} (f : Objective n)

/-- Restrict to the old ground set and subtract the fixed buffer baseline. -/
def contractOn (U B : Finset (Fin n)) : Objective n where
  value S := f.value (B ∪ (S ∩ U)) - f.value B
  nonnegative S := sub_nonneg.mpr (f.monotone _ _ Finset.subset_union_left)
  monotone S T h := sub_le_sub_right (f.monotone _ _
    (Finset.union_subset_union_right (Finset.inter_subset_inter h (Finset.Subset.refl U)))) _
  submodular S T := by
    have h := f.submodular (B ∪ (S ∩ U)) (B ∪ (T ∩ U))
    have hu : (B ∪ (S ∩ U)) ∪ (B ∪ (T ∩ U)) = B ∪ ((S ∪ T) ∩ U) := by
      ext e; simp; tauto
    have hi : (B ∪ (S ∩ U)) ∩ (B ∪ (T ∩ U)) = B ∪ ((S ∩ T) ∩ U) := by
      ext e; simp; tauto
    rw [hu, hi] at h
    linarith

@[simp] theorem contractOn_empty (U B : Finset (Fin n)) : (f.contractOn U B).value ∅ = 0 := by
  simp [contractOn]

end ConsistentSubmodular.Objective

end


