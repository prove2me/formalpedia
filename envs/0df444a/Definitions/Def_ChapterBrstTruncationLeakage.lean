-- Prove2me | Definitions.Def_ChapterBrstTruncationLeakage
-- name    : ChapterBrstTruncationLeakage
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:29:03.361993+00:00
-- url     : https://prove2.me/theorems/bb956e31-1cb8-4c48-b079-92afb3d1addf
-- title:
--   Chapter BrstTruncationLeakage
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterBrstTruncationLeakage.lean`): generated def bundle for ChapterBrstTruncationLeakage. See BookProof/ChapterBrstTruncationLeakage.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBrstTruncationLeakage.lean

import Definitions.Def_ChapterSirkRestart
import Mathlib


/-!
# BRST leakage under Krylov truncation: a quantitative bound

`CONSOLIDATED_PLAN.md` §12.2 **Gap 5** ("the physical-subspace (BRST) leakage") records
what is missing: the truncated dynamics the SIRK/Hashimoto solver actually integrates does
*not* preserve the physical subspace — the numerics document growth of the BRST-charge
content `‖Ω ψ(t)‖` under aggressive truncation, which is why the solver rides a BRST
projector along — and no formal bound on that leakage in terms of the truncation exists.
`BookProof.ChapterBRSTNilpotent` supplies the algebraic side (`Ω² = 0`, `[H, Ω] = 0`); this
module supplies the analytic side.

## What is new here

`BookProof.ChapterSirkRestart.brst_leakage_bound` already bounds the leakage of `n` cycles of
a truncated *propagator* `S` by `‖Ω‖ n ε ‖v‖` — but with the per-cycle closeness `ε` of `S`
to the exact propagator as a *hypothesis*, so nothing there ties the leakage to the
truncation itself.  This module works one level down, at the generators the algorithm
actually truncates, and produces `ε` rather than assuming it: the leakage rate is the norm
of the block of the Hamiltonian that the truncation discards.  The bridge back is
`brst_leakage_bound_of_generator`.

## The statement

Everything is at the level of *bounded* generators — the finite-`m` reduced generators the
algorithm exponentiates, and any bounded model Hamiltonian — on a complex Hilbert space `E`.
For a self-adjoint `A` the flow is `flow A t = exp (t • (-i A))`, a unitary group
(`flow_mem_unitary`, `norm_flow_apply`).

* **Exact dynamics does not leak.**  If `Ω` commutes with `H` then `Ω` is carried along the
  flow, `omega_flow_apply`, so `‖Ω (flow H t x)‖ = ‖Ω x‖` (`norm_omega_flow_eq`) and the
  physical subspace `ker Ω` is invariant (`flow_mem_ker_omega`).
* **The Duhamel estimate.**  `norm_flow_sub_flow_apply_le`: if `‖(A − B)(flow B s x)‖ ≤ K`
  along the `B`-orbit for `s ∈ [0, t]`, then `‖flow B t x − flow A t x‖ ≤ K t`.  The proof
  is the derivative of `s ↦ flow A (t − s) (flow B s x)` (`hasDerivAt_duhamel`) together
  with the mean-value inequality; unitarity of the two groups is what makes the derivative
  bound `K` and not `K e^{c t}`.
* **The sharp transfer rate.**  `norm_flow_sub_flow_le`: in operator norm,
  `‖e^{-itA} − e^{-itB}‖ ≤ ‖A − B‖ t` for self-adjoint bounded generators — the rate that
  `BookProof.ChapterSirkGroupTransfer` records as not claimed there, its telescoping
  estimate carrying an extra factor `e^{|t| M}` (which it needs, being valid for arbitrary
  bounded generators).
* **The leakage bound.**  `leakage_le`: for the truncated flow `ψ(t) = flow B t x`,

  `‖Ω ψ(t)‖ ≤ ‖Ω x‖ + ‖Ω‖ K t`,

  and `leakage_le_of_physical` for a physical initial state (`Ω x = 0`): the leakage grows
  at most linearly in `t`, with slope `‖Ω‖ K`.
* **The truncation instance.**  For an orthogonal projection `P` (idempotent and
  self-adjoint) the truncated generator is `truncGen P H = P H P`; the flow of the truncated
  generator keeps a state inside the retained subspace (`flow_truncGen_mem`, proved by an ODE
  uniqueness argument, not by a series manipulation), so the constant `K` is the
  *off-diagonal block* `‖(1 − P) H P‖ ‖x‖` and not the crude `‖H − P H P‖ ‖x‖`:
  **`truncation_leakage_le`**

  `‖Ω (flow (P H P) t x)‖ ≤ ‖Ω x‖ + ‖Ω‖ ‖(1 − P) H P‖ ‖x‖ t`   (`P x = x`).

  In particular a state that is physical and retained leaks at most
  `‖Ω‖ ‖(1 − P) H P‖ ‖x‖ t` (`truncation_leakage_le_of_physical`): the leakage is controlled
  by the part of the Hamiltonian that the truncation discards, and vanishes with it.
* **Both time directions.**  The bounds above are stated for `t ≥ 0`; when the defect is
  bounded along the whole orbit they hold for every real `t` with `t` replaced by `|t|`
  (`norm_flow_sub_flow_apply_le_abs`, `leakage_le_abs`, `truncation_leakage_le_abs`), by
  reflecting the generators.
* **Restarts.**  The numerics restarts the Krylov cycle, with a *new* truncation each cycle
  (§12.2 Gap 4a).  `leakageIter` is the restarted state after `n` cycles of length `τ` with
  truncated generators `B 0, B 1, …`, and **`leakage_iterate_le`** accumulates the bound
  linearly in the number of cycles:

  `‖Ω (leakageIter B τ x n)‖ ≤ ‖Ω x‖ + n ‖Ω‖ K τ ‖x‖`  whenever `‖H − B i‖ ≤ K`.

## Honest boundary

The generators here are bounded operators: this is the finite-`m` reduced problem and any
bounded model, not the unbounded field-theoretic Hamiltonian, for which the same estimate
needs the Duhamel argument in the strong-resolvent form of `ChapterSirkTrotterKato`.  `Ω` is
an arbitrary bounded operator commuting with `H`; nilpotency `Ω² = 0` — the BRST content of
`ChapterBRSTNilpotent` — is not needed for the leakage bound and is therefore not assumed.
No floating-point analysis (§12.2 Gap 6) is claimed.
-/

open NormedSpace

namespace BookProof.BrstLeakage

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## The unitary group of a bounded self-adjoint generator -/

/-- The flow `e^{-i t A}` of a bounded generator `A`. -/
noncomputable def flow (A : E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E := exp (t • ((-Complex.I) • A))











/-! ## Exact dynamics carries a commuting observable along -/







/-! ## The Duhamel estimate -/













/-! ## The leakage bound -/







/-! ## The truncation instance -/

/-- The truncated generator `P H P` of an orthogonal projection `P`. -/
def truncGen (P H : E →L[ℂ] E) : E →L[ℂ] E := P * H * P











/-! ## Restarts -/

/-- The restarted state: `n` cycles of length `τ`, the `i`-th integrated with the truncated
generator `B i`. -/
noncomputable def leakageIter (B : ℕ → E →L[ℂ] E) (τ : ℝ) (x : E) : ℕ → E
  | 0 => x
  | n + 1 => flow (B n) τ (leakageIter B τ x n)









/-! ## The bridge to the discrete restart estimate

`BookProof.ChapterSirkRestart.brst_leakage_bound` bounds the leakage of `n` cycles of a
truncated *propagator* `S` by `‖Ω‖ n ε ‖v‖`, with the per-cycle closeness `ε` of `S` to the
exact propagator `U` as a hypothesis.  For propagators generated by bounded generators the
Duhamel estimate discharges that hypothesis, with `ε = ‖H − B‖ τ`. -/





end BookProof.BrstLeakage


