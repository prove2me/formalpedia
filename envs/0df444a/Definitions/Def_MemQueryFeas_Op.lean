-- Prove2me | Definitions.Def_MemQueryFeas_Op
-- name    : MemQueryFeas_Op
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:33:24.598557+00:00
-- url     : https://prove2.me/theorems/7f3c4d1c-9a1e-45b9-9ff4-cff4d6930e2f
-- title:
--   Linear maps of $\mathbb R^d$
-- statement:
--   Linear maps $T:\mathbb R^d\to\mathbb R^d$, such as the stretches $T_{F,\alpha}$ and the phase transformations $T_v$, and the orthogonal projections $P_E$ onto subspaces $E\subseteq\mathbb R^d$ are elements of the space of linear maps of $\mathbb R^d$, normed by the operator norm $\|T\|_{op}$.
--
--   **Formalization Note** Continuous linear maps `Vec d →L[ℝ] Vec d` (all linear maps of a finite-dimensional space are continuous), with the Borel σ-algebra of the operator-norm topology, which is standard Borel. Subspaces are represented by their orthogonal projections.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Notations, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_MemQueryFeas_Vec

namespace MemQueryFeas

/-- **Linear maps of `ℝ^d`.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Notations, p.7 (PDF p.8): linear maps `T : ℝ^d → ℝ^d` and the
orthogonal projections `P_E` onto subspaces `E ∈ Gr(k,d)`.

**Formalization Note.** A linear map of `ℝ^d` is a continuous linear map `Vec d →L[ℝ] Vec d`
(every linear map of a finite-dimensional space is continuous). Subspaces are represented by their
orthogonal projections, which are elements of this type; it carries the Borel σ-algebra of its
operator-norm topology and is standard Borel. -/
abbrev Op (d : ℕ) : Type := Vec d →L[ℝ] Vec d

end MemQueryFeas


