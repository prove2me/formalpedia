-- Prove2me | Definitions.Def_ChapterBrstUnboundedLeakage
-- name    : ChapterBrstUnboundedLeakage
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-03T18:42:09.256565+00:00
-- url     : https://prove2.me/theorems/745b4ede-decc-4a97-9843-6d88c3d41fc0
-- title:
--   Chapter BrstUnboundedLeakage
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterBrstUnboundedLeakage.lean`): generated def bundle for ChapterBrstUnboundedLeakage. See BookProof/ChapterBrstUnboundedLeakage.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBrstUnboundedLeakage.lean

import Definitions.Def_ChapterBrstTruncationLeakage
import Definitions.Def_ChapterStoneGenerator
import Mathlib


/-!
# BRST leakage of the truncated dynamics for an **unbounded** Hamiltonian

`CONSOLIDATED_PLAN.md` §12.2 **Gap 5** asks for a bound on the physical-subspace (BRST)
leakage `‖Ω ψ(t)‖` of the *truncated* dynamics in terms of the truncation.
`BookProof/ChapterBrstTruncationLeakage.lean` closes it for **bounded** generators and
records the unbounded field-theoretic Hamiltonian as the remaining boundary.  This module
removes that restriction: the exact generator is an arbitrary unbounded self-adjoint
operator `T` (the bundled `UnboundedSelfAdjoint` of `BookProof.ChapterStoneResolvent`,
whose flow `e^{-itT} = T.stoneU t` is the one Stone's theorem produces), and the truncated
generator is the compression `P T P` to a **finite-dimensional** retained subspace — which
is exactly the finite-`m` object the SIRK/Hashimoto solver integrates.

## What is proved

* **Duhamel against an unbounded exact generator.**
  `hasDerivAt_duhamel_stone` differentiates `u ↦ e^{-i(t-u)T} e^{-iuB} x` when the truncated
  orbit stays in the domain of `T`; the derivative is `e^{-i(t-u)T}(-i)(B - T)` applied to
  the orbit, so only the *defect* `T - B` along the orbit enters.  The step that replaces
  the bounded-generator product rule is `hasDerivAt_isometry_apply`, an elementary
  strong-continuity lemma: an isometric, strongly continuous family `U h` applied to a
  differentiable curve vanishing at `0` is differentiable, with derivative `U 0` of the
  curve's derivative.
* **The flow error.**  `norm_flow_sub_stoneU_le` — `‖e^{-itB}x - e^{-itT}x‖ ≤ K t` whenever
  `‖T y - B y‖ ≤ K` along the truncated orbit `y = e^{-isB}x`, `s ∈ [0, t]`.  No
  boundedness, no relative bound, no analytic-vector hypothesis: unitarity of both groups
  is what keeps the rate linear in `t`.
* **The leakage bound.**  `leakage_le` — for a bounded observable `Ω` commuting with the
  exact group, `‖Ω(e^{-itB}x)‖ ≤ ‖Ωx‖ + ‖Ω‖ K t`, and `leakage_le_of_physical` for a
  physical initial state `Ωx = 0`.  The exact dynamics does not leak
  (`norm_omega_stoneU_eq`): all of the leakage comes from the truncation.
* **The truncation instance.**  For a finite-dimensional subspace `V ≤ T.domain` with
  orthogonal projection `P`, the compression `truncGen = P T P` is a *bounded* self-adjoint
  operator (`truncGen_isSelfAdjoint`) — finite-dimensionality is what makes `T P` bounded —
  its flow keeps a retained state retained (`flow_truncGen_mem`, by ODE uniqueness), and the
  defect along the orbit is exactly the discarded off-diagonal block `(1 - P) T P`
  (`truncDefect`).  Hence
  * **`norm_flow_truncGen_sub_stoneU_le`** — `‖e^{-itPTP}x - e^{-itT}x‖ ≤ ‖(1-P)TP‖ ‖x‖ t`,
    the finite-`m` flow error for an unbounded Hamiltonian, and
  * **`truncation_leakage_le`** — `‖Ω(e^{-itPTP}x)‖ ≤ ‖Ωx‖ + ‖Ω‖ ‖(1-P)TP‖ ‖x‖ t`,
    with `truncation_leakage_le_of_physical` for a physical retained state.

  Both vanish with the discarded block, so a retained subspace that is nearly invariant
  under the unbounded Hamiltonian leaks nearly nothing.
* **Restarts.**  `restartGen` is the sequence of compressions the restarted cycle uses — a
  fresh retained subspace each cycle — and **`restart_leakage_le`** accumulates the bound
  linearly in the number of cycles:
  `‖Ω (leakageIter (restartGen …) τ x n)‖ ≤ ‖Ωx‖ + n ‖Ω‖ D ‖x‖ τ` whenever every discarded
  block satisfies `‖(1 - Pᵢ)TPᵢ‖ ≤ D` and the restarted state is retained in the new
  subspace at each restart (which is what re-seeding the Krylov cycle provides).

## Honest boundary

`Ω` is a bounded observable and is assumed to commute with the *group* `e^{-itT}` (the
correct unbounded form of "commutes with `H`"); nilpotency `Ω² = 0` is not needed.  The
retained subspace is finite-dimensional and inside the domain — the finite-`m` Krylov
subspace of the numerics.  All the bounds are stated for `t ≥ 0` (unlike the bounded-
generator module, which reflects the generators to reach negative times; reflecting an
unbounded generator would require rebuilding its group).  Nothing about floating-point
arithmetic (§12.2 Gap 6) is claimed.
-/

open NormedSpace Filter Topology
open scoped InnerProductSpace

namespace BookProof.BrstUnboundedLeakage

open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## A strong-continuity product rule -/



/-! ## The flow of a bounded generator -/





/-! ## Duhamel against the unbounded group -/

variable (T : UnboundedSelfAdjoint H)





/-! ## The leakage bound -/







/-! ## The finite-dimensional truncation -/

section Truncation

variable (V : Submodule ℂ H) [FiniteDimensional ℂ V] (hV : V ≤ T.domain)

/-- The orthogonal projection onto the retained subspace, as an operator on `H`. -/
noncomputable def projOp : H →L[ℂ] H := V.starProjection

/-- `T P`: the unbounded operator applied to the retained part.  Bounded because the
retained subspace is finite-dimensional. -/
noncomputable def opProj : H →L[ℂ] H :=
  (LinearMap.toContinuousLinearMap (T.op.comp (Submodule.inclusion hV))) ∘L
    (V.orthogonalProjection)

/-- The truncated (compressed) generator `P T P` — a *bounded* self-adjoint operator. -/
noncomputable def truncGen : H →L[ℂ] H := projOp V ∘L opProj T V hV

/-- The discarded off-diagonal block `(1 - P) T P`. -/
noncomputable def truncDefect : H →L[ℂ] H := (1 - projOp V) ∘L opProj T V hV

































end Truncation

/-! ## Restarts -/

section Restart

variable (Vs : ℕ → Submodule ℂ H) [∀ i, FiniteDimensional ℂ (Vs i)] (hVs : ∀ i, Vs i ≤ T.domain)

/-- The restarted truncated generators: cycle `i` is integrated with the compression of `T`
to the `i`-th retained subspace. -/
noncomputable def restartGen (i : ℕ) : H →L[ℂ] H := truncGen T (Vs i) (hVs i)







end Restart

end BookProof.BrstUnboundedLeakage


