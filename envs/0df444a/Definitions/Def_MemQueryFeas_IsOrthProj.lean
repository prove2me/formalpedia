-- Prove2me | Definitions.Def_MemQueryFeas_IsOrthProj
-- name    : MemQueryFeas_IsOrthProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:34:14.136933+00:00
-- url     : https://prove2.me/theorems/a0777628-4dfd-42dd-965b-3f6da4c64cdf
-- title:
--   Orthogonal projection onto a $k$-dimensional subspace
-- statement:
--   A linear map $p$ of $\mathbb R^d$ is the **orthogonal projection onto a $k$-dimensional subspace** if it is idempotent ($p^2=p$), self-adjoint, and its range has dimension $k$. Then $p=P_E$ for $E=\operatorname{range}p\in\mathrm{Gr}(k,d)$, the set of $k$-dimensional subspaces of $\mathbb R^d$.
--
--   **Formalization Note** Throughout the mission a subspace $E$ is represented by $P_E$.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Notations, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_MemQueryFeas_Op

namespace MemQueryFeas

/-- **Orthogonal projection onto a `k`-dimensional subspace.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Notations, p.7 (PDF p.8): "We
denote by `Gr(k, d)` the collection of `k`-dimensional subspaces of `ℝ^d`. For `E ∈ Gr(k, d)`, we
denote by `P_E` the orthogonal projection onto `E`."

`IsOrthProj k p`: `p` is idempotent and self-adjoint with a `k`-dimensional range, i.e. `p = P_E` for
`E = range p ∈ Gr(k, d)`.

**Formalization Note.** A subspace `E` is represented by its projection `P_E`; `E ↦ P_E` is a
bijection from `Gr(k,d)` onto these operators. -/
def IsOrthProj {d : ℕ} (k : ℕ) (p : Op d) : Prop :=
  IsIdempotentElem p ∧ IsSelfAdjoint p ∧
    Module.finrank ℝ (LinearMap.range (p : Vec d →ₗ[ℝ] Vec d)) = k

end MemQueryFeas


