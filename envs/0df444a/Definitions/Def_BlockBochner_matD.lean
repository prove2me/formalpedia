-- Prove2me | Definitions.Def_BlockBochner_matD
-- name    : BlockBochner_matD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:36:55.26605+00:00
-- url     : https://prove2.me/theorems/7cc478bc-1cdf-4182-a8ed-eeddaf7cb405
-- title:
--   $D=\mathrm{blockdiag}(C_{T_1},\dots,C_{T_m})$
-- statement:
--   $D$ is the block-diagonal part of $C$ with respect to the blocks $T_1,\dots,T_m$: $D_{ij}=C_{ij}$ when $i,j$ lie in a common block and $D_{ij}=0$ otherwise.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Theorem 3, p.4

import Mathlib
import Definitions.Def_BlockBochner_matC

namespace BlockBochner

/-- **`D = blockdiag(C_{T₁}, …, C_{T_m})`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Theorem 3, p.4.

**Formalization Note** The `(i, j)` entry is `C_{ij}` when `i` and `j` lie in a common block and `0`
otherwise; for pairwise disjoint blocks this is the block-diagonal part of `C`. -/
noncomputable def matD {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ} (A : Matrix V V ℝ)
    (T : Fin m → Finset V) : Matrix (blockUnion T) (blockUnion T) ℝ :=
  fun i j => if ∃ a, i.1 ∈ T a ∧ j.1 ∈ T a then matC A T i j else 0

end BlockBochner


