-- Prove2me | Definitions.Def_KernelRankLean_ExpPoly
-- name    : KernelRankLean_ExpPoly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T01:47:52.004408+00:00
-- url     : https://prove2.me/theorems/f13ef478-616a-41e2-a56d-bb545c003ff3
-- title:
--   Exp Poly
-- statement:
--   Definitions and structural lemmas for Exp Poly, from Olli Niemitalo's pinned Finite separable rank of radial kernels development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ExpPoly.lean

import Mathlib
set_option autoImplicit true
open Complex Polynomial
namespace KernelRank
noncomputable def expPoly (P : ℂ[X]) (μ : ℂ) (u : ℝ) : ℂ :=
  P.eval (u : ℂ) * exp (μ * u)
noncomputable def shiftDeriv (a μ : ℂ) (P : ℂ[X]) : ℂ[X] :=
  derivative P + C (μ - a) * P
end KernelRank


