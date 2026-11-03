-- Prove2me | Definitions.Def_RankRobustAssort_errNorm
-- name    : RankRobustAssort_errNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:56.836723+00:00
-- url     : https://prove2.me/theorems/ad3cbbb0-fa67-4f76-b9e7-075c44f432d5
-- title:
--   Norm $\|\epsilon\|$ of the estimation error vector
-- statement:
--   Let $S_1,\dots,S_M\subseteq\mathcal N_0=\{0,\dots,n\}$ be the past assortments. An **error vector** $\epsilon=(\epsilon_{m,i})_{m\in\mathcal M,\ i\in S_m}$ has one coordinate for each past assortment $m$ and each product $i$ offered in it. Its norm is
--
--   $$
--   \|\epsilon\|_1=\sum_{m\in\mathcal M}\sum_{i\in S_m}|\epsilon_{m,i}|\qquad\text{or}\qquad \|\epsilon\|_\infty=\max_{m\in\mathcal M,\ i\in S_m}|\epsilon_{m,i}|,
--   $$
--
--   according to the chosen norm.
--
--   This is the norm bounding the gap between predicted and observed purchase frequencies in the consistent set $\mathcal U$.
--
--   **Formalization Note.** The error vector is stored as a function on all pairs $(m,i)$, but only the coordinates with $i\in S_m$ are read; the others play no role anywhere. The maximum over an empty index set is $0$.
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Notation p.6 and §2, p.8

import Mathlib
import Definitions.Def_RankRobustAssort_NormChoice

namespace RankRobustAssort

/-- The norm `‖ϵ‖` of an error vector `ϵ = (ϵ_{m,i})_{m ∈ ℳ, i ∈ S_m}`, for the past assortments
`S : Fin M → Finset (Fin (n+1))`: `∑_m ∑_{i ∈ S_m} |ϵ_{m,i}|` for `ℓ₁`, and
`max_{m, i ∈ S_m} |ϵ_{m,i}|` for `ℓ∞`.

Sturt, arXiv:2112.05010v4, p.6 (the norm is `ℓ₁` or `ℓ∞`) and p.8 (definition of `𝒰`, where `ϵ`
has one coordinate `ϵ_{m,i}` for each `m ∈ ℳ` and `i ∈ S_m`).

Formalization Note: `ϵ` is stored as a full function `Fin M → Fin (n+1) → ℝ`, but the norm reads
only the coordinates `(m, i)` with `i ∈ S_m`; the other coordinates are ignored (and are not
constrained anywhere), so this is the paper's norm on `ℝ^{∑_m |S_m|}`. The `ℓ∞` maximum is a
`Finset.sup` in `ℝ≥0`, which is `0` when there is no coordinate at all (the norm of the empty
vector). -/
noncomputable def errNorm {n M : ℕ} (c : NormChoice) (S : Fin M → Finset (Fin (n + 1)))
    (ε : Fin M → Fin (n + 1) → ℝ) : ℝ :=
  match c with
  | .l1 => ∑ m, ∑ i ∈ S m, |ε m i|
  | .linf => (((Finset.univ : Finset (Fin M)).sup fun m => (S m).sup fun i => ‖ε m i‖₊ : NNReal) : ℝ)

end RankRobustAssort


