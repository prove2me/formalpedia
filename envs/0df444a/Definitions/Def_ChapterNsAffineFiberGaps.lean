-- Prove2me | Definitions.Def_ChapterNsAffineFiberGaps
-- name    : ChapterNsAffineFiberGaps
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-20T23:12:36.909724+00:00
-- url     : https://prove2.me/theorems/7fe2281d-b033-4522-8756-8f7b633e2bba
-- title:
--   Navier–Stokes affine-fiber leaf-gap carrier
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.NsAffineFiberGaps`, source chapter `BookProof/ChapterNsAffineFiberGaps.lean`): Navier–Stokes affine-fiber leaf-gap carrier
--
--   The published copy of `Def_ChapterNavierStokesAffineFiberEsa` was leaf-dropped: four `rfl` lemmas that the source chapter declares are absent from it, so every bundle or solution that cites them dies server-side with `Unknown identifier` (§2.59 leaf-selection gaps). Published bundles are immutable, so the fix is this auxiliary bundle, which re-carries exactly the dropped cluster in its original namespaces:
--
--   * `PairShift.fst_shift` / `PairShift.snd_shift` — `P.fst.shift = P.shift₁` and `P.snd.shift = P.shift₂` (the component shifts of a pair shift). * `affData_shift₁` / `affData_shift₂` — the affine fiber field adds exactly `n ↦ n + 2` (constant part) and `n ↦ n + 1` (linear part) to the Hermite level.
--
--   Consumers add a single `import Definitions.Def_ChapterNsAffineFiberGaps`. The workspace copy of `Def_ChapterNavierStokesAffineFiberEsa` has these four declarations stripped, so the name is declared exactly once in every environment (platform, published mirror, candidate mirror).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesAffineFiberEsa.lean

import Mathlib
import Definitions.Def_ChapterNavierStokesAffineFiberEsa

/-! # Navier–Stokes affine-fiber leaf-gap carrier

The published copy of `Def_ChapterNavierStokesAffineFiberEsa` was leaf-dropped:
four `rfl` lemmas that the source chapter declares are absent from it, so every
bundle or solution that cites them dies server-side with `Unknown identifier`
(§2.59 leaf-selection gaps).  Published bundles are immutable, so the fix is
this auxiliary bundle, which re-carries exactly the dropped cluster in its
original namespaces:

* `PairShift.fst_shift` / `PairShift.snd_shift` — `P.fst.shift = P.shift₁`
  and `P.snd.shift = P.shift₂` (the component shifts of a pair shift).
* `affData_shift₁` / `affData_shift₂` — the affine fiber field adds exactly
  `n ↦ n + 2` (constant part) and `n ↦ n + 1` (linear part) to the Hermite
  level.

Consumers add a single `import Definitions.Def_ChapterNsAffineFiberGaps`.
The workspace copy of `Def_ChapterNavierStokesAffineFiberEsa` has these four
declarations stripped, so the name is declared exactly once in every
environment (platform, published mirror, candidate mirror).
-/

open scoped ENNReal

namespace BookProof.NavierStokesFlow

namespace AffineFiber

variable {ι : Type*}

namespace PairShift

variable (P : PairShift ι)

@[simp] theorem fst_shift : P.fst.shift = P.shift₁ := rfl

@[simp] theorem snd_shift : P.snd.shift = P.shift₂ := rfl

end PairShift

@[simp] theorem affData_shift₁ {κ c : ℝ} (hκ : 0 ≤ κ) (hc : 0 ≤ c) :
    (affData hκ hc).shift₁ = fun n : ℕ => n + 2 := rfl

@[simp] theorem affData_shift₂ {κ c : ℝ} (hκ : 0 ≤ κ) (hc : 0 ≤ c) :
    (affData hκ hc).shift₂ = fun n : ℕ => n + 1 := rfl

end AffineFiber

end BookProof.NavierStokesFlow


