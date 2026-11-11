-- Prove2me | Definitions.Def_MemoSDPI_Main_IsReplicableOn
-- name    : MemoSDPI_Main_IsReplicableOn
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:41:31.435904+00:00
-- url     : https://prove2.me/theorems/e6cd82a9-ceae-438c-9681-fa77be8a2f8d
-- title:
--   ρ-replicability of an algorithm on a family of distributions (Definition 6.3)
-- statement:
--   Let $A(S; R)$ be the output of an algorithm $A$ on a sample $S$ of $n$ records with seed $R$, where the seed carries all the internal randomness of $A$. The algorithm is **$\rho$-replicable on a family $\mathcal P$** of distributions if for every $D \in \mathcal P$,
--   $$
--   \Pr\big[A(S; R) = A(S'; R)\big] \;\ge\; 1 - \rho,
--   $$
--   where the samples $S, S' \sim D^n$ and the seed $R$ are independent. Requiring this only for the distributions in $\mathcal P$ weakens the notion and so strengthens lower bounds against it.
--
--   **Formalization Note** At one distribution this is the published `DPVerify.IsReplicableAt` (the measure of the agreement set under $D^n \otimes D^n \otimes P$, in $[0,\infty]$); on a family it is required for every member. The family is a set of `ProbabilityMeasure X`.
-- source:
--   Feldman, Lyu, Talwar, Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities, STOC 2027 submission (manuscript sha256 dbb300da…), pp. 25–26, Definition 6.3

import Mathlib
import Definitions.Def_DPVerify_RandAlg
import Definitions.Def_DPVerify_IsReplicableAt

set_option autoImplicit false

open MeasureTheory

namespace MemoSDPI.Main

/-- **`ρ`-replicability on a family of distributions** (Feldman, Lyu, Talwar, *Lower Bounds for
Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities*, STOC
2027 submission (manuscript sha256 dbb300da…), pp. 25–26, Definition 6.3): for every `D ∈ F`,
`Pr[A(S; R) = A(S′; R)] ≥ 1 − ρ`, where `S, S′ ∼ D^n` and the seed `R` are independent.

**Formalization Note.** At one distribution this is the published `DPVerify.IsReplicableAt`
(the product `D^n ⊗ D^n ⊗ A.P` of the agreement set, in `ℝ≥0∞`); on a family it is required for
every member. -/
def IsReplicableOn {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (A : DPVerify.RandAlg X Y n) (F : Set (ProbabilityMeasure X)) (ρ : ℝ) : Prop :=
  ∀ D ∈ F, DPVerify.IsReplicableAt A D ρ

end MemoSDPI.Main


