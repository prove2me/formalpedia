-- Prove2me | Definitions.Def_GaussPart_Supplement_PUILearner
-- name    : GaussPart_Supplement_PUILearner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:04:01.423983+00:00
-- url     : https://prove2.me/theorems/748fe517-6166-4a2c-bcbd-20976281a4f9
-- title:
--   PUI learners with Gaussian reference on the sampling RAM
-- statement:
--   Let $\mathcal F$ be a class of Boolean functions on $\mathbb R^d$ and let $N,T$ be real functions of $(\epsilon,\sigma,p_+,q)$. A program $A$ with evaluator $E_A$ is a **PUI learner** for $\mathcal F$ with reference $\mathcal N(0,I_d)$, sample complexity $N$, running time $T$ and failure probability at most $1/12$ if for every $\epsilon\in(0,1)$, $\sigma\in(0,1]$, $p_+\in(0,1]$, $q\ge1$:
--
--   1. started with $\epsilon,\sigma,p_+,q$ in memory, $A$ halts on every sample stream after at most $N(\epsilon,\sigma,p_+,q)$ samples and work $T(\epsilon,\sigma,p_+,q)$;
--   2. for every $f\in\mathcal F$ and every $D^*$ that is $(q,\sigma)$-smooth with respect to $\mathcal N(0,I_d)$ with $D^*(f=1)\ge p_+$, fed i.i.d. samples of $D^*_+=D^*\mid\{f=1\}$, with probability at least $11/12$ it outputs a hypothesis $h$ (evaluated within work $T$) with
--   $$
--   \Pr_{x\sim D^*}[h(x)\neq f(x)]\le\epsilon .
--   $$
--
--   This is the learner assumed by the reduction from reliable to PUI learning (Theorem 1.11, Lemma 6.3).
--
--   **Formalization Note** The learner sees only the positive conditional samples; the error is under $D^*$.
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Definition 1.7, p.4 (PDF p.6); Definition 5.1, p.44 (PDF p.46); Lemma 6.3, p.61 (PDF p.63)

import Mathlib
import Definitions.Def_GaussMixHH_Machine
import Definitions.Def_GaussPart_Cell
import Definitions.Def_GaussPart_IsSmooth
import Definitions.Def_GaussPart_Supplement_Learner

open MeasureTheory ProbabilityTheory

namespace GaussPart

namespace Supplement

/-- **A PUI learner on the sampling RAM** (Definitions 1.7 and 5.1, arXiv:2611.05264, sha256
7e0ca6d4…, p.4, PDF p.6 and p.44, PDF p.46; the learner `A` of Lemma 6.3, p.61, PDF p.63), with
reference `N(0, I_d)`, sample complexity `N(ϵ, σ, p₊, q)`, running time `T(ϵ, σ, p₊, q)` and failure
probability at most `1/12`: for every `ϵ ∈ (0, 1)`, `σ ∈ (0, 1]`, `p₊ ∈ (0, 1]`, `q ≥ 1`, the program `A`
started with `ϵ, σ, p₊, q` in memory halts on every sample stream after at most `N(ϵ, σ, p₊, q)`
samples and work `T(ϵ, σ, p₊, q)`; and for every target `f ∈ F` and every `D∗` that is
`(q, σ)`-smooth with respect to `N(0, I_d)` with `D∗(f = 1) ≥ p₊`, fed i.i.d. samples of
`D∗₊ := D∗ | {f = 1}`, with probability at least `11/12` it outputs a hypothesis `h` (computed by the
evaluator `EA` within work `T(ϵ, σ, p₊, q)`) with `Pr_{x∼D∗}[h(x) ≠ f(x)] ≤ ϵ`.

**Formalization Note.** The learner sees `D∗₊` only (the reference is known); its error is measured
under `D∗`. `D∗₊` is `ProbabilityTheory.cond`, a probability measure since `D∗(f = 1) ≥ p₊ > 0`. A lower bound on a
probability is at most `1` (Definition 5.1 takes `p₊ ∈ (0, 1)`); larger values admit no target. -/
def IsPUILearner {d : ℕ} (F : Set (Vec d → ℝ)) (N T : ℝ → ℝ → ℝ → ℝ → ℝ)
    (A EA : GaussMixHH.Program) : Prop :=
  ∀ ε σ pPos q : ℝ, 0 < ε → ε < 1 → 0 < σ → σ ≤ 1 → 0 < pPos → pPos ≤ 1 → 1 ≤ q →
    RunsWithin A d [ε, σ, pPos, q] (N ε σ pPos q) (T ε σ pPos q) ∧
    ∀ f ∈ F, ∀ Ds : Measure (Vec d), IsProbabilityMeasure Ds →
      IsSmooth (stdGaussian (Vec d)) Ds q σ → ENNReal.ofReal pPos ≤ Ds {x | f x = 1} →
      SucceedsWith A d [ε, σ, pPos, q] (Measure.infinitePi fun _ : ℕ => cond Ds {x | f x = 1})
        (11 / 12) (fun s => Ds {x | hyp EA d (T ε σ pPos q) s x ≠ f x} ≤ ENNReal.ofReal ε)

end Supplement

end GaussPart


