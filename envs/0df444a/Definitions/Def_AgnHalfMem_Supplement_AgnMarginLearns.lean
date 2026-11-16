-- Prove2me | Definitions.Def_AgnHalfMem_Supplement_AgnMarginLearns
-- name    : AgnHalfMem_Supplement_AgnMarginLearns
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:55:26.360962+00:00
-- url     : https://prove2.me/theorems/d9f86469-b3c9-410a-9196-7c67e365ca45
-- title:
--   Agnostic PAC learning of halfspaces with $\gamma$-margin to excess error $\varepsilon$, success probability $2/3$
-- statement:
--   Let $A$ be a randomized streaming algorithm (a seeded family of branching programs with seed law $P$) that reads $T$ samples in $\mathbb R^d\times\{-1,1\}$. It **agnostically PAC learns halfspaces with $\gamma$-margin to excess error $\varepsilon$ with success probability $2/3$** if for every probability distribution $D$ on $\mathbb R^d\times\{-1,1\}$ with $\Pr_D[x=0]=0$ (the distributions on which $\mathrm{err}_\gamma$ is defined), run on $T$ i.i.d. samples from $D$, it outputs a classifier $f:\mathbb R^d\to\{-1,1\}$ such that
--   $$
--   \Pr_{(x,y)\sim D}[f(x)\ne y]\ \le\ \mathrm{OPT}_\gamma(D)+\varepsilon
--   $$
--   with probability at least $2/3$ over its seed and the samples.
--
--   This is the learning task of Theorem 4.3. The learner is distribution-free and may be improper: its output need not be a halfspace.
--
--   **Formalization Note** The probability is the product measure (seed law times $D^{\otimes T}$) of the success set, as in the base mission's success probability; for jointly measurable algorithms this set is measurable. Distributions with mass at $x=0$, where the printed margin quotient is undefined, are not required.
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), §1, p.3 (agnostic margin learning goal); Theorem 4.3, p.10

import Mathlib
import Definitions.Def_AgnHalfMem_err
import Definitions.Def_AgnHalfMem_StreamAlg
import Definitions.Def_AgnHalfMem_Supplement_marginErr

open MeasureTheory

namespace AgnHalfMem

namespace Supplement

/-- **Agnostic PAC learning of halfspaces with γ-margin.** S. Garg, T. Jadhav, *Memory-Sample
Tradeoffs for Agnostically Learning Halfspaces*, STOC 2027 submission (manuscript, PDF sha256
386bc9b3…43f84d5), §1, p.3: "in the agnostic setting, given a stream of samples from a joint
distribution D, the goal is to output a function f : ℝ → {−1, 1} such that
Pr_{(x,y)∼D}[f(x) ≠ y] ≤ min_{w∈H}(errγ(w, D)) + ε"; Theorem 4.3, p.10: "agnostically PAC learns
halfspaces with γ-margin to excess error at most ε, with success probability at least 2/3".

`AgnMarginLearns γ ε A P`: for **every** probability measure `D` on `ℝ^d × {−1, 1}` that puts
no mass on `x = 0` (where the printed `y⟨w, x⟩/‖x‖₂` is undefined), the
randomized streaming algorithm `A` (seed law `P`), given `T` i.i.d. samples from `D`, outputs with
probability at least `2/3` a classifier `f` with `err(f, D) ≤ OPT_γ(D) + ε`.

**Formalization Note.** The learner is distribution-free (no fixed marginal) and may be improper
(any output classifier). The paper's `errγ(w, D)` is defined only when `x ≠ 0` `D`-almost
surely, so the learner is required to succeed exactly on those `D` (`D {x = 0} = 0`); on them
`optMargin` is the printed `OPT_γ`. The probability is the product measure `P ⊗ D^{⊗T}` of the success set,
as in the base mission's `succProb`; Lean's measure of a set is its outer measure, and for jointly
measurable algorithms (`IsMeasurableAlg`) the success set is measurable. Labels are `Bool`
(`true ↔ +1`). -/
def AgnMarginLearns {Ω S : Type*} [MeasurableSpace Ω] {d T : ℕ} (γ ε : ℝ)
    (A : StreamAlg Ω S (Fin d → ℝ) T) (P : Measure Ω) : Prop :=
  ∀ D : Measure ((Fin d → ℝ) × Bool), IsProbabilityMeasure D → D {p | p.1 = 0} = 0 →
    ENNReal.ofReal (2 / 3) ≤
      (P.prod (Measure.pi fun _ : Fin T => D))
        {q | err D ((A q.1).output q.2) ≤ optMargin D γ + ε}

end Supplement

end AgnHalfMem


