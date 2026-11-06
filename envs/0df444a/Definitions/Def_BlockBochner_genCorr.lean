-- Prove2me | Definitions.Def_BlockBochner_genCorr
-- name    : BlockBochner_genCorr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:42.11497+00:00
-- url     : https://prove2.me/theorems/db7677a4-052b-4384-b5a1-f6c6cac1da21
-- title:
--   Generalized correlation $c_\nu$
-- statement:
--   For a link $\nu$ on $k=|R|$ sites,
--   $$c_\nu=\sup\Bigl\{\frac{\sum_{i\ne j}\langle g_i,g_j\rangle_\nu}{(k-1)\sum_i\|g_i\|_2^2}\ :\ g_i\in U^\nu_i,\ \sum_i\|g_i\|_2^2>0\Bigr\}.$$
--   For $k=2$ it is the HGR maximal correlation.
--
--   **Formalization Note** A real supremum. The ratios are at most $1$, and the set is nonempty for a nontrivial link.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Sec. 2.2, p.16

import Mathlib
import Definitions.Def_BlockBochner_Uspace

open MeasureTheory

namespace BlockBochner

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- **Generalized correlation `c_ν`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 2.2, p.16:
`c_ν = sup Σ_{i≠j} ⟨g_i, g_j⟩_ν / ((k − 1) Σ_i ‖g_i‖²₂)` over `g_i ∈ U^ν_i` with `Σ_i ‖g_i‖² > 0`, where
`k = |R|`.

**Formalization Note** A real supremum. The ratios are at most `1` (Cauchy–Schwarz), so the set is
bounded above; it is nonempty when some `U^ν_i ≠ 0`, which holds for a nontrivial link. -/
noncomputable def genCorr (ν : Measure (∀ i, X i)) : ℝ :=
  sSup {r | ∃ g : ι → Lp ℝ 2 ν, (∀ i, g i ∈ Uspace ν i) ∧ 0 < ∑ i, ‖g i‖ ^ 2 ∧
    r = (∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (g i) (g j)) /
      (((Fintype.card ι : ℝ) - 1) * ∑ i, ‖g i‖ ^ 2)}

end BlockBochner


