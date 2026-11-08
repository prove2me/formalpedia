-- Prove2me | Definitions.Def_MaxCompForest_condLoss
-- name    : MaxCompForest_condLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:34:01.976844+00:00
-- url     : https://prove2.me/theorems/06663789-838c-4d2a-b6e5-8d46d365eae9
-- title:
--   Conditional loss $\ell_j(S)=K_{jS}K_S^{-1}K_{Sj}$
-- statement:
--   For a symmetric matrix $K$ indexed by a finite set, a subset $S$ with $K_S$ invertible, and an index $j$,
--   $$
--   \ell_j(S)=K_{jS}K_S^{-1}K_{Sj}.
--   $$
--   It is the amount by which conditioning on $S$ decreases the diagonal entry $K_{jj}$.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Lemma 4.1, p.25

import Mathlib
import Definitions.Def_MaxCompForest_onLabels

namespace MaxCompForest

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The conditional loss** `ℓ_j(S) = K_{jS} K_S⁻¹ K_{Sj}`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Lemma 4.1, p.25.

**Formalization Note.** `Matrix.inv` is junk on a singular block; every use has `K_S` positive definite. -/
noncomputable def condLoss (K : Matrix ι ι ℝ) (S : Finset ι) (j : ι) : ℝ :=
  dotProduct (fun i : S => K j i) ((onLabels K S)⁻¹.mulVec fun i : S => K i j)

end MaxCompForest


