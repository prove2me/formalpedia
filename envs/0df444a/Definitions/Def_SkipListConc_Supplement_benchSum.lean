-- Prove2me | Definitions.Def_SkipListConc_Supplement_benchSum
-- name    : SkipListConc_Supplement_benchSum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:47:58.332889+00:00
-- url     : https://prove2.me/theorems/2b15ae14-a2b6-4ab4-9919-e7bb66b37d32
-- title:
--   Benchmark sum $A(\sigma)=\sum_t a_t$
-- statement:
--   For an operation sequence $\sigma$ of length $F$, the **benchmark sum** is
--   $$
--   A(\sigma)=\sum_{t=1}^{F}a_t ,
--   $$
--   the sum of the benchmark costs of all charges. The paper shows $A(\sigma)\le C_p\,\mathrm{Ent}(\sigma)$ (Lemma 4.4); Theorem B is stated in terms of both.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §1.2, p.7

import Mathlib
import Definitions.Def_SkipListConc_Supplement_chargeBench

namespace SkipListConc.Supplement

/-- The benchmark sum `A(σ) = ∑_t a_t` of an operation sequence (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), §1.2, p.7). -/
noncomputable def benchSum {α : Type*} [DecidableEq α] (p : ℝ) (σ : List α) : ℝ :=
  ∑ t : Fin σ.length, chargeBench p σ t

end SkipListConc.Supplement


