-- Prove2me | Definitions.Def_RennerKoenig_rankOp
-- name    : RennerKoenig_rankOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:00.172446+00:00
-- url     : https://prove2.me/theorems/01f5739b-0d85-4781-b4ac-ef45c768d985
-- title:
--   Rank of an operator
-- statement:
--   The rank of an operator $T$ on a Hilbert space is the dimension of its range.
--
--   **Formalization Note** Lean's `Module.finrank` returns $0$ on an infinite-dimensional range, so every statement of the mission that uses a rank assumes the range finite-dimensional.
-- source:
--   Renner–König, Universally Composable Privacy Amplification Against Quantum Adversaries, arXiv:quant-ph/0403133v2, §2.2, p.3 and §2.4, p.6

import Mathlib

namespace RennerKoenig

/-- **Rank of an operator**: the dimension of its range. Renner–König, *Universally Composable Privacy Amplification Against Quantum Adversaries*,
arXiv:quant-ph/0403133v2, §2.2, p.3 and §2.4, p.6.

**Formalization Note** `Module.finrank` is `0` on an infinite-dimensional range, so every statement
using `rankOp T` carries the hypothesis that the range of `T` is finite-dimensional. -/
noncomputable def rankOp {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (T : K →L[ℂ] K) : ℕ :=
  Module.finrank ℂ (LinearMap.range (T : K →ₗ[ℂ] K))

end RennerKoenig


