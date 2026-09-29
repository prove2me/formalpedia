-- Prove2me | Definitions.Def_HighDimStat_SparseLinear_ConeSet
-- name    : HighDimStat_SparseLinear_ConeSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:05:49.462962+00:00
-- url     : https://prove2.me/theorems/c6409d64-5461-4535-bdb6-ed756347111e
-- title:
--   The cone C_alpha(S) of Wainwright Eq. (7.21)
-- statement:
--   This is the **cone** $C_\alpha(S)$ of Wainwright's Eq. (7.21), the set of error directions
--   whose mass off a support set $S$ is controlled by a multiple of their mass on $S$. It is
--   the geometric object both the restricted nullspace property (special case $\alpha=1$,
--   p. 201) and the restricted eigenvalue condition (Eq. (7.22)) are stated over.
--
--   For $S \subseteq \{1,\dots,d\}$, $\alpha \ge 1$, and $\Delta \in \mathbb R^d$,
--
--   $$
--   \Delta \in C_\alpha(S) \;:\Longleftrightarrow\; \|\Delta_{S^c}\|_1 \;\le\; \alpha \|\Delta_S\|_1,
--   $$
--
--   where $\Delta_S$ and $\Delta_{S^c}$ denote $\Delta$ restricted to $S$ and its complement.
--
--   **Formalization Note** Realized directly with the two `Finset` sums $\sum_{j\in S^c}
--   |\Delta_j|$ and $\sum_{j\in S}|\Delta_j|$ rather than a "restricted vector" operation, so
--   it is stated for arbitrary real $\alpha$ (the book only ever instantiates $\alpha=1$ or
--   $\alpha=3$, both $\ge 1$, but the definition itself carries no lower bound on $\alpha$,
--   matching how the book introduces it before restricting attention to $\alpha \ge 1$).
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 207 (PDF p. 227), Eq. (7.21)

import Mathlib

namespace HighDimStat.SparseLinear

/-- The cone `C_α(S) := {Δ ∈ ℝ^d | ‖Δ_{Sᶜ}‖₁ ≤ α‖Δ_S‖₁}` of Wainwright, *High-Dimensional
Statistics* (2019), Eq. (7.21), for a subset `S ⊆ {1,...,d}` and a constant `α ≥ 1`. The special
case `α = 1` is the set `C(S)` used to define the restricted nullspace property (p. 201). -/
def ConeSet {d : ℕ} (S : Finset (Fin d)) (α : ℝ) (Δ : Fin d → ℝ) : Prop :=
  (∑ j ∈ Sᶜ, |Δ j|) ≤ α * ∑ j ∈ S, |Δ j|

end HighDimStat.SparseLinear


