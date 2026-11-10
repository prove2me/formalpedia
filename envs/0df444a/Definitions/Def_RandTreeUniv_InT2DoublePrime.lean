-- Prove2me | Definitions.Def_RandTreeUniv_InT2DoublePrime
-- name    : RandTreeUniv_InT2DoublePrime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:13:00.958118+00:00
-- url     : https://prove2.me/theorems/e318cee3-408e-49ca-aa68-8d167cd257ad
-- title:
--   The family $\mathcal T_2''=\mathcal T_2\setminus\mathcal T_2'$
-- statement:
--   With the notation of $\mathcal T_2'$, the family $\mathcal T_2''=\mathcal T_2\setminus\mathcal T_2'$ consists of the trees of $\mathcal T_2$ for which Algorithm 6.5 applied to $T_1$ and $T_2$ yields $\min\{i_1,i_2\}<\Gamma+1$, i.e. some step among $1,\dots,\Gamma$ fails on $T_1$ or on $T_2$.
--
--   **Formalization Note** A tree belongs to the family when *some* four-tree decomposition has the run on $T_1$ or on $T_2$ failing one of the steps $1,\dots,\Gamma$. The paper fixes one decomposition per tree; this family contains the paper's $\mathcal T_2''$ for every such choice. Since every tree has a decomposition (Lemma 6.1), $\mathcal T_2'\cup\mathcal T_2''=\mathcal T_2$ for the same $\delta_1$.
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), §6, pp.32 and 44 (PDF 33, 45)

import Mathlib
import Definitions.Def_RandTreeUniv_InT2
import Definitions.Def_RandTreeUniv_IsFourTreeDecomp
import Definitions.Def_RandTreeUniv_StepPasses

set_option autoImplicit false

open scoped Classical

namespace RandTreeUniv

/-- `T ∈ T″₂ := T₂ \ T′₂` (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), §6, p.32 (PDF 33)): the trees of `T₂` for which `i₁ ≤ Γ` or
`i₂ ≤ Γ`. Algorithm 6.5 is run on `T₁` (rooted at `r_{1,2}`) and on `T₂` (roots `r_{1,2}, r_{2,3}`), with
`Γ = ∆³` and threshold `(10 + δ₁)α`, `α = n ln ln n/(K³ ln n)` (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), §6, pp.31–32 (PDF 32–33)).
The algorithm returns `i_j = Γ + 1` exactly when steps `1, …, Γ` are all passed.

**Formalization Note** `T ∈ T₂` and *some* four-tree decomposition `(W, r)` of `T` (as in
`IsFourTreeDecomp`) has the run on `T₁` or the run on `T₂` failing one of the steps `1, …, Γ`
(0-based `i < ∆³`). The paper fixes one decomposition per tree; this family contains the paper's
`T″₂` for every such choice. Every tree of `T₂` has a decomposition (Lemma 6.1), so `T″₂` and
`T′₂` (same `δ₁`) together cover `T₂`. -/
def InT2DoublePrime (n : ℕ) (K : ℝ) (Δ : ℕ) (δ₁ : ℝ) (T : SimpleGraph (Fin n)) : Prop :=
  InT2 n K Δ T ∧ ∃ (W : Fin 4 → Finset (Fin n)) (r : Fin 3 → Fin n), IsFourTreeDecomp T W r ∧
    ((∃ i < Δ ^ 3, ¬ StepPasses T {r 0} (W 0) ((10 + δ₁) * alpha K 1 n) i) ∨
      (∃ i < Δ ^ 3, ¬ StepPasses T {r 0, r 1} (W 1) ((10 + δ₁) * alpha K 1 n) i))

end RandTreeUniv


