-- Prove2me | Definitions.Def_ChapterSirkEndToEnd
-- name    : ChapterSirkEndToEnd
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:10:33.318083+00:00
-- url     : https://prove2.me/theorems/f5daaff8-0d98-4b19-883f-eafeacf2711c
-- title:
--   `CONSOLIDATED_PLAN.md` §12.2 **Gap 1** records that the four stages of the SIRK/Hashimoto pipeline exist as separate mod ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.SirkEndToEnd`, source chapter `BookProof/ChapterSirkEndToEnd.lean`).
--
--   `CONSOLIDATED_PLAN.md` §12.2 **Gap 1** records that the four stages of the SIRK/Hashimoto pipeline exist as separate modules but that *no theorem composes them* into a single flow-approximation statement
--
--   `‖e^{−itH} v − V_m e^{−itB_m} V_m∗ v‖ ≤ bound(m, shifts, t, spectral geometry)`,
--
--   and §12.3 names this "the highest-value, lowest-risk step: it does not touch any physics". This chapter is that assembly, on the generic machinery, with the constants `C`, `Dmin`, `h` abstract.
--
--   * `sirk_error_bound_at` **weakens** the compression-transfer hypothesis of `ChapterH4.sirk_error_bound` from "for every vector" to "at the one seed vector `v`". That is what makes the composition possible at all: the rational transfer `r(X) v = V r(B) V∗ v` of `ChapterH4.compress_rational_transfer` is only available **on the range of `V`**, which is exactly where the Krylov seed lives. * `sirk_end_to_end` therefore has **no `hrt` hypothesis left**: the transfer is discharged from the isometry, the Krylov invariance of the range and the invertibility of the rational denominator. What remains conditional is only the pair of Crouzeix bounds and the `e^{−hm}` deformation — the two inputs the project has always carried as *named hypotheses with citation*, never axioms. * `crouzeix_domain_transfer` shows that **one** Crouzeix domain serves both bounds: if `Σ` is convex and contains the numerical range of `X`, it contains the convex hull of the numerical range of every compression `B = V∗XV` (`ChapterH9.numRange_compress_subset`). So `hcx1` and `hcx2` may be taken with the *same* `C` and the *same* `D = ‖ψ − r‖_{∞,Σ}`, which is what the informal argument silently uses. * `sirk_flow_error_tendsto_zero` and `sirk_flow_error_uniform_in_time` are the convergence conclusions: the reduced flows converge to the exact one as the Krylov dimension grows, and — when the constants do not depend on the time — the convergence is **uniform in `t`** (the bound half of §12.2 Gap 3). * `sirkApprox_id`, `sirkReconstruction_isIdempotent`, `sirkReconstruction_isSelfAdjoint`: the reconstruction step `V ∘ V∗` *is* the orthogonal projection onto the retained subspace (§12.2 Gap 4a).
--
--   Nothing here proves Crouzeix's inequality or the `e^{−hm}` deformation; they enter as named hypotheses exactly as in `ChapterH4`. Nothing here instantiates the constants for a particular Hamiltonian (§12.2 Gap 2), and nothing is claimed about floating-point arithmetic (§12.2 Gap 6). What is proved is the *composition*: from the two named inputs, the isometry and the Krylov invariance, the end-to-end bound and its convergence follow.
--
--   Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkEndToEnd.lean

import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterH7
import Definitions.Def_ChapterH8
import Definitions.Def_ChapterH9
import Mathlib

import Mathlib

/-!
# Chapter SirkEndToEnd — the end-to-end SIRK reliability statement (assembly)

`CONSOLIDATED_PLAN.md` §12.2 **Gap 1** records that the four stages of the
SIRK/Hashimoto pipeline exist as separate modules but that *no theorem composes
them* into a single flow-approximation statement

  `‖e^{−itH} v − V_m e^{−itB_m} V_m∗ v‖ ≤ bound(m, shifts, t, spectral geometry)`,

and §12.3 names this "the highest-value, lowest-risk step: it does not touch any
physics".  This chapter is that assembly, on the generic machinery, with the
constants `C`, `Dmin`, `h` abstract.

## What is new here (as opposed to restated)

* `sirk_error_bound_at` **weakens** the compression-transfer hypothesis of
  `ChapterH4.sirk_error_bound` from "for every vector" to "at the one seed
  vector `v`".  That is what makes the composition possible at all: the rational
  transfer `r(X) v = V r(B) V∗ v` of `ChapterH4.compress_rational_transfer` is
  only available **on the range of `V`**, which is exactly where the Krylov seed
  lives.
* `sirk_end_to_end` therefore has **no `hrt` hypothesis left**: the transfer is
  discharged from the isometry, the Krylov invariance of the range and the
  invertibility of the rational denominator.  What remains conditional is only
  the pair of Crouzeix bounds and the `e^{−hm}` deformation — the two inputs the
  project has always carried as *named hypotheses with citation*, never axioms.
* `crouzeix_domain_transfer` shows that **one** Crouzeix domain serves both
  bounds: if `Σ` is convex and contains the numerical range of `X`, it contains
  the convex hull of the numerical range of every compression `B = V∗XV`
  (`ChapterH9.numRange_compress_subset`).  So `hcx1` and `hcx2` may be taken with
  the *same* `C` and the *same* `D = ‖ψ − r‖_{∞,Σ}`, which is what the informal
  argument silently uses.
* `sirk_flow_error_tendsto_zero` and `sirk_flow_error_uniform_in_time` are the
  convergence conclusions: the reduced flows converge to the exact one as the
  Krylov dimension grows, and — when the constants do not depend on the time —
  the convergence is **uniform in `t`** (the bound half of §12.2 Gap 3).
* `sirkApprox_id`, `sirkReconstruction_isIdempotent`,
  `sirkReconstruction_isSelfAdjoint`: the reconstruction step `V ∘ V∗` *is* the
  orthogonal projection onto the retained subspace (§12.2 Gap 4a).

## Honest boundary

Nothing here proves Crouzeix's inequality or the `e^{−hm}` deformation; they
enter as named hypotheses exactly as in `ChapterH4`.  Nothing here instantiates
the constants for a particular Hamiltonian (§12.2 Gap 2), and nothing is claimed
about floating-point arithmetic (§12.2 Gap 6).  What is proved is the
*composition*: from the two named inputs, the isometry and the Krylov
invariance, the end-to-end bound and its convergence follow.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

noncomputable section

open Filter Topology

namespace BookProof.ChapterSirkEndToEnd

open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH8 BookProof.ChapterH9

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-! ## 1. The SIRK approximant and the reconstruction projection -/

/-- The **SIRK approximant** `V ψ(B) V∗`: reduce with `V∗`, propagate with the
`m × m` reduced operator `ψ(B)`, reconstruct with `V`. -/
def sirkApprox (V : F →L[ℂ] E) (psiB : F →L[ℂ] F) : E →L[ℂ] E :=
  V.comp (psiB.comp V.adjoint)



/-- The **reconstruction operator** `V ∘ V∗`. -/
def sirkReconstruction (V : F →L[ℂ] E) : E →L[ℂ] E := V.comp V.adjoint











/-! ## 2. The pointwise Crouzeix core -/



/-! ## 3. One Crouzeix domain for both bounds -/





/-! ## 4. The end-to-end bound -/



/-! ## 5. Convergence in the reduction order, and uniformity in time -/







/-! ## 6. Non-vacuity -/



end BookProof.ChapterSirkEndToEnd


