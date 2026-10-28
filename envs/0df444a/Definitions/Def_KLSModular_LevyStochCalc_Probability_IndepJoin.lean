-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Probability_IndepJoin
-- name    : KLSModular_LevyStochCalc_Probability_IndepJoin
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:39:28.819104+00:00
-- url     : https://prove2.me/theorems/15fc6375-12e2-4c9f-a8c1-138171ac0589
-- title:
--   Intersection sets for joins of sigma-algebras
-- statement:
--   Vendored from LevyStochCalc (https://github.com/cgarryZA/LevyStochCalc). `interSets m₁ m₂` is the set of measurable intersections $A\textrm{ intersect }B$ with $A$ measurable for $m_1$ and $B$ measurable for $m_2$. It is the elementary pi-system used by downstream independence-of-joins results; the declarations in this bundle only define this family.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Probability.Independence.Basic
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def interSets (m₁ m₂ : MeasurableSpace Ω) : Set (Set Ω) :=
--     {s | ∃ A B, MeasurableSet[m₁] A ∧ MeasurableSet[m₂] B ∧ s = A ∩ B}
--   ```
--
--   **Module navigation**
--
--   Theorems in source order:
--
--   - [`indep_sup_left_of_indep`](https://prove2.me/theorems/c2c528da-fe2a-4d38-a81e-84fdbfe1a3dc)
--   - [`indep_iSup_of_finset`](https://prove2.me/theorems/203c9447-e491-43d7-8d96-6b87e13fa487)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Probability/IndepJoin.lean) · `LevyStochCalc.Probability.IndepJoin` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/IndepJoin.lean#L26-L28 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.IndepJoin`, definition bundle `KLSModular_LevyStochCalc_Probability_IndepJoin`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.Probability.Independence.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/IndepJoin.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
namespace LevyStochCalc
namespace Probability
variable {Ω : Type*} {m₁ m₂ m₃ mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
/-- The π-system of intersections `A ∩ B` with `A ∈ m₁` and `B ∈ m₂`. -/
def interSets (m₁ m₂ : MeasurableSpace Ω) : Set (Set Ω) :=
  {s | ∃ A B, MeasurableSet[m₁] A ∧ MeasurableSet[m₂] B ∧ s = A ∩ B}
end Probability
end LevyStochCalc


