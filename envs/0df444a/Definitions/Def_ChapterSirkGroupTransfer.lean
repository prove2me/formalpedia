-- Prove2me | Definitions.Def_ChapterSirkGroupTransfer
-- name    : ChapterSirkGroupTransfer
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-08T01:40:59.1605+00:00
-- url     : https://prove2.me/theorems/422adb03-7eaa-429a-be1d-a62cc1f0a961
-- title:
--   One-parameter group transfer
-- statement:
--   Formal definitions for the One-parameter group transfer of the timepiece Lean 4 formalization (module `BookProof.SirkGroupTransfer`, source chapter `BookProof/ChapterSirkGroupTransfer.lean`).
--
--   `CONSOLIDATED_PLAN.md` §12.2 **Gap 3** asks for the transfer of generator convergence to the *unitary group*: `e^{−itA_m} → e^{−itA}` strongly, locally uniformly in `t`. For an unbounded selected extension this is the Trotter–Kato theorem and is still open in this development. For **bounded** generators — which is the case the numerics actually run in, since the reduced generator `B_m` is an `m × m` matrix and the operator the algorithm iterates is the *bounded* shift-invert — the transfer holds with an explicit rate, and that is what this chapter proves.
--
--   * `norm_pow_sub_pow_le` — the telescoping estimate `‖Aⁿ − Bⁿ‖ ≤ n M^{n−1} ‖A − B‖` for two elements of a Banach algebra of norm at most `M`. * `norm_exp_sub_exp_le` — summing it against the exponential series: `‖exp A − exp B‖ ≤ ‖A − B‖ · e^{M}`. So the exponential is Lipschitz on balls, with the expected constant. * `groupFlow`, `norm_groupFlow_sub_le` — the Schrödinger propagator `U_A(t) = e^{−itA}` of a bounded generator, and the transfer rate `‖U_A(t) − U_B(t)‖ ≤ |t| ‖A − B‖ e^{|t| M}`. * `groupFlow_transfer_uniform_on_interval` — the **locally uniform in `t`** statement: on any time interval `[−T, T]` the two propagators differ by at most `T ‖A − B‖ e^{T M}`, uniformly, so generator convergence in norm implies convergence of the flows uniformly on compact time intervals. * `groupFlow_zero` — the sanity check `U_a(0) = 1`.
--
--   This is the **bounded** half of §12.2 Gap 3. Nothing here proves Trotter–Kato: the unbounded case — strong *resolvent* convergence of the selected extensions implying strong convergence of their unitary groups — needs the spectral calculus of unbounded self-adjoint operators and remains open. The rate proved here degrades exponentially in `|t| M`, as it must for arbitrary bounded generators; for *self-adjoint* generators the sharp rate `|t| ‖A − B‖` is proved in `BookProof.ChapterBrstTruncationLeakage` (`BrstLeakage.norm_flow_sub_flow_le`), by a Duhamel argument that uses unitarity of the two groups.
--
--   Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkGroupTransfer.lean

import Mathlib

/-!
# Chapter SirkGroupTransfer — the unitary-group transfer for bounded generators

`CONSOLIDATED_PLAN.md` §12.2 **Gap 3** asks for the transfer of generator
convergence to the *unitary group*: `e^{−itA_m} → e^{−itA}` strongly, locally
uniformly in `t`.  For an unbounded selected extension this is the Trotter–Kato
theorem and is still open in this development.  For **bounded** generators —
which is the case the numerics actually run in, since the reduced generator
`B_m` is an `m × m` matrix and the operator the algorithm iterates is the
*bounded* shift-invert — the transfer holds with an explicit rate, and that is
what this chapter proves.

* `norm_pow_sub_pow_le` — the telescoping estimate `‖Aⁿ − Bⁿ‖ ≤ n M^{n−1} ‖A − B‖`
  for two elements of a Banach algebra of norm at most `M`.
* `norm_exp_sub_exp_le` — summing it against the exponential series:
  `‖exp A − exp B‖ ≤ ‖A − B‖ · e^{M}`.  So the exponential is Lipschitz on balls,
  with the expected constant.
* `groupFlow`, `norm_groupFlow_sub_le` — the Schrödinger propagator
  `U_A(t) = e^{−itA}` of a bounded generator, and the transfer rate
  `‖U_A(t) − U_B(t)‖ ≤ |t| ‖A − B‖ e^{|t| M}`.
* `groupFlow_transfer_uniform_on_interval` — the **locally uniform in `t`**
  statement: on any time interval `[−T, T]` the two propagators differ by at most
  `T ‖A − B‖ e^{T M}`, uniformly, so generator convergence in norm implies
  convergence of the flows uniformly on compact time intervals.
* `groupFlow_zero` — the sanity check `U_a(0) = 1`.

## Honest boundary

This is the **bounded** half of §12.2 Gap 3.  Nothing here proves Trotter–Kato:
the unbounded case — strong *resolvent* convergence of the selected extensions
implying strong convergence of their unitary groups — needs the spectral calculus
of unbounded self-adjoint operators and remains open.  The rate proved here
degrades exponentially in `|t| M`, as it must for arbitrary bounded generators; for
*self-adjoint* generators the sharp rate `|t| ‖A − B‖` is proved in
`BookProof.ChapterBrstTruncationLeakage` (`BrstLeakage.norm_flow_sub_flow_le`), by a
Duhamel argument that uses unitarity of the two groups.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

noncomputable section

namespace BookProof.ChapterSirkGroupTransfer

open NormedSpace

variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-! ## 1. The telescoping estimate for powers -/





/-! ## 2. The exponential is Lipschitz on balls -/



/-! ## 3. The Schrödinger propagator of a bounded generator -/

/-- The propagator `U_a(t) = e^{−ita}` of a bounded generator. -/
def groupFlow (a : A) (t : ℝ) : A := exp ((-(t : ℂ) * Complex.I) • a)







end BookProof.ChapterSirkGroupTransfer


