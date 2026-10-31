-- Prove2me | Definitions.Def_PandoraComb_Discretize
-- name    : PandoraComb_Discretize
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:08:59.838986+00:00
-- url     : https://prove2.me/theorems/30d19adf-0163-49a3-b7f6-271324d17fb1
-- title:
--   Transformation $T^\epsilon$: the cap $\kappa_\epsilon$ and the discretized laws $D_i^\epsilon$
-- statement:
--   Let $\epsilon>0$ and let $D_1,\dots,D_n$ be the laws of an instance.
--
--   1. The **cap** is
--   $$\kappa_\epsilon=\min\Big\{\kappa\ge0\ \Big|\ \sum_{i=1}^n\mathbb E\big[(V_i-\kappa)^+\big]\le\epsilon\Big\}.$$
--   2. $D_i^\epsilon$ is the law of $\bar V_i=\epsilon\cdot\big\lfloor\min(V_i,\kappa_\epsilon)/\epsilon\big\rfloor$, and $T^\epsilon(D_1,\dots,D_n,c)=(D_1^\epsilon,\dots,D_n^\epsilon,c)$: the cost is unchanged.
--
--   $T^\epsilon$ turns an instance into one with finitely supported laws, losing at most $2\epsilon$ in the optimal utility (Proposition 4.1).
--
--   **Formalization Note** $\kappa_\epsilon$ is written as an infimum over the reals. For laws with finite expectations and $\epsilon>0$ the set is nonempty (Lemma F.1), bounded below by $0$ and closed, so the infimum is the minimum. $D_i^\epsilon$ is the push-forward of $D_i$ under $x\mapsto\epsilon\lfloor\min(x,\kappa_\epsilon)/\epsilon\rfloor$.
-- source:
--   Berger, Ezra, Feldman & Fusco, Pandora’s Problem with Combinatorial Cost, arXiv:2303.01078v1, §4, p.18, Transformation 1

import Mathlib

open MeasureTheory

noncomputable section

namespace PandoraComb

/-- **The capping constant** `κ_ϵ := min{κ ≥ 0 | Σ_{i=1}^n E[(V_i − κ)^+] ≤ ϵ}` of
Transformation 1 (arXiv:2303.01078v1, §4, p.18).

**Formalization Note.** Written as an infimum of reals; for laws with finite expectations and
`ϵ > 0` the set is nonempty (Lemma F.1), bounded below by `0` and closed, so the infimum is the
paper's minimum. -/
def kappa {ι : Type*} [Fintype ι] (D : ι → Measure ℝ) (ε : ℝ) : ℝ :=
  sInf {κ : ℝ | 0 ≤ κ ∧ ∑ i, ∫ x, max (x - κ) 0 ∂(D i) ≤ ε}

/-- **Transformation `T^ϵ`** (§4, p.18): `D^ϵ_i` is the distribution of
`V̄_i = ϵ · ⌊min(V_i, κ_ϵ) / ϵ⌋`, the push-forward of `D_i`; the cost function is unchanged
(`T^ϵ(D_1, …, D_n, c) = (D^ϵ_1, …, D^ϵ_n, c)`). -/
def discretize {ι : Type*} [Fintype ι] (D : ι → Measure ℝ) (ε : ℝ) (i : ι) : Measure ℝ :=
  (D i).map fun x => ε * (⌊min x (kappa D ε) / ε⌋ : ℝ)

end PandoraComb


