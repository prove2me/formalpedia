-- Prove2me | Definitions.Def_BosonicLearn_traceDist
-- name    : BosonicLearn_traceDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:15:11.6196+00:00
-- url     : https://prove2.me/theorems/78dd70f5-6096-45b8-b0f0-3309f1d5690d
-- title:
--   Trace distance $D_{\mathrm{tr}}(A,B)=\tfrac12\|A-B\|_1$
-- statement:
--   For two operators $A,B$ on a Hilbert space with a countable orthonormal basis, the **trace distance** is
--
--   $$D_{\mathrm{tr}}(A,B)=\tfrac12\,\|A-B\|_1 ,$$
--
--   where $\|\cdot\|_1$ is the trace norm. It is the error measure of every learning statement in the paper: a state $\rho$ is learned to precision $\varepsilon$ when the output $\hat\rho$ has $D_{\mathrm{tr}}(\hat\rho,\rho)\le\varepsilon$.
--
--   **Formalization Note** The trace norm is the published nuclear norm `traceSize` of `Dependency50.P33` (an infimum over nuclear expansions, $+\infty$ for an array that is not trace class), so the value is an extended nonnegative real. On two density operators it is finite and at most $1$.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, footnote 1, p. 3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)

open scoped ENNReal

namespace BosonicLearn

/-- **Trace distance** `D_tr(A, B) = ½‖A − B‖₁` of two coefficient arrays.
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, footnote 1, p. 3 ("trace distance … ½‖ρ − σ‖₁"), used in every theorem of the paper.

The trace norm is `traceSize` of `Dependency50.P33`, the infimum over nuclear expansions (`∞` when the
array is not trace class), so the value lies in `ℝ≥0∞`.

**Formalization Note.** On two density operators the difference is trace class and the value is finite
and at most `1`; the paper only applies it to densities. -/
noncomputable def traceDist {I : Type} (A B : Matrix I I ℂ) : ℝ≥0∞ :=
  traceSize (A - B) / 2

end BosonicLearn


