-- Prove2me | Definitions.Def_RandTreeUniv_InT2Prime
-- name    : RandTreeUniv_InT2Prime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:13:02.373193+00:00
-- url     : https://prove2.me/theorems/f8068548-d8d7-4b1b-87c1-ebacf9d33cf3
-- title:
--   The family $\mathcal T_2'$ (Algorithm 6.5 runs $\Gamma$ full steps on $T_1$ and $T_2$)
-- statement:
--   Fix $\Gamma=\Delta^3$, $\delta_1>0$ and $\alpha=n\ln\ln n/(K^3\ln n)$. For $T\in\mathcal T_2$, divide $T$ into four trees $T_1,\dots,T_4$ (§6) and run Algorithm 6.5 on $T_1$ (rooted at $r_{1,2}$) and on $T_2$ (roots $r_{1,2},r_{2,3}$) with threshold $(10+\delta_1)\alpha$; let $i_1,i_2$ be the returned step indices. The family $\mathcal T_2'\subseteq\mathcal T_2$ consists of the trees with $i_1=i_2=\Gamma+1$, which happens exactly when steps $1,\dots,\Gamma$ pass on both trees.
--
--   **Formalization Note** A tree belongs to the family when *some* four-tree decomposition has both runs passing steps $1,\dots,\Gamma$. The paper fixes one decomposition per tree; this family contains the paper's $\mathcal T_2'$ for every such choice.
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), §6, p.32 (PDF 33); Algorithm 6.5, pp.31–32 (PDF 32–33)

import Mathlib
import Definitions.Def_RandTreeUniv_InT2
import Definitions.Def_RandTreeUniv_IsFourTreeDecomp
import Definitions.Def_RandTreeUniv_StepPasses

set_option autoImplicit false

open scoped Classical

namespace RandTreeUniv

/-- `T ∈ T′₂` (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), §6, p.32 (PDF 33)): "The first case is when `i₁, i₂ = Γ + 1`, and the
subfamily of trees corresponding to this case is denoted by `T′₂ ⊆ T₂`." Algorithm 6.5 is run on `T₁` (rooted at `r_{1,2}`) and on `T₂` (roots `r_{1,2}, r_{2,3}`), with
`Γ = ∆³` and threshold `(10 + δ₁)α`, `α = n ln ln n/(K³ ln n)` (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), §6, pp.31–32 (PDF 32–33)).
The algorithm returns `i_j = Γ + 1` exactly when steps `1, …, Γ` are all passed.

**Formalization Note** `T ∈ T₂` and *some* four-tree decomposition `(W, r)` of `T` (as in
`IsFourTreeDecomp`) has both runs passing steps `1, …, Γ` (0-based `i < ∆³`). The paper fixes
one decomposition per tree; this family contains the paper's `T′₂` for every such choice. -/
def InT2Prime (n : ℕ) (K : ℝ) (Δ : ℕ) (δ₁ : ℝ) (T : SimpleGraph (Fin n)) : Prop :=
  InT2 n K Δ T ∧ ∃ (W : Fin 4 → Finset (Fin n)) (r : Fin 3 → Fin n), IsFourTreeDecomp T W r ∧
    (∀ i < Δ ^ 3, StepPasses T {r 0} (W 0) ((10 + δ₁) * alpha K 1 n) i) ∧
    (∀ i < Δ ^ 3, StepPasses T {r 0, r 1} (W 1) ((10 + δ₁) * alpha K 1 n) i)

end RandTreeUniv


