-- Prove2me | Definitions.Def_SumReLU_sampleLaw
-- name    : SumReLU_sampleLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:26:32.862365+00:00
-- url     : https://prove2.me/theorems/a8781301-3269-4b17-9540-be35df81fd0e
-- title:
--   The law of a labeled example $(x,f(x))$ and the run space of coins and examples
-- statement:
--   The learner has access to independent examples $(x,y)$ with $x\sim N(0,I_d)$ and $y=f(x)$, $f=\sum_i\beta_i\sigma(w_i\cdot x)$. The law of one example is the image of $N(0,I_d)$ under $x\mapsto(x,f(x))$, a probability measure on $\mathbb R^{d+1}$.
--
--   The randomness of a randomized learner is a tape of independent fair coins together with, independently, an infinite i.i.d. stream of examples with this law.
--
--   This is the only way the unknown target enters the main theorem: the learner sees $(\beta,w)$ only through examples.
--
--   **Formalization Note** One example is one vector of $\mathbb R^{d+1}$ with $x$ in coordinates $0,\dots,d-1$ and the label $y$ in coordinate $d$, so that one `sample` instruction of the `GaussMixHH` machine in dimension $d+1$ reads one example. The coin tape is the published `GaussMixHH.coinTape`.
-- source:
--   Diakonikolas, Diakonikolas, Wang, Zarifis, Learning Positive Linear Combinations of ReLUs in Fully Polynomial Time, arXiv:2610.32940 (PDF sha256 66803576…6c48), Definition 1.2 and Theorem 1.3, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_GaussMixHH_Machine
import Definitions.Def_SumReLU_reluSum

open MeasureTheory ProbabilityTheory

namespace SumReLU

/-- One labeled example `(x, y) ∈ ℝᵈ × ℝ` written as one vector of `ℝ^{d+1}`: coordinates
`0, …, d − 1` are `x`, coordinate `d` is the label `y`. -/
noncomputable def exampleVec {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) (y : ℝ) :
    EuclideanSpace ℝ (Fin (d + 1)) :=
  WithLp.toLp 2 fun m : Fin (d + 1) => if h : (m : ℕ) < d then x ⟨m, h⟩ else y

/-- **The law of one example** `(x, f(x))`, `x ∼ N(0, I_d)`, `f = reluSum β w`: the pushforward of
`N(0, I_d)` under `x ↦ (x, f(x))`.

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), Definition 1.2, p.2 (PDF p.4): "access to independent examples (x, y) ∼ D, where D is a
distribution supported on ℝᵈ × ℝ such that x ∼ N(0, I_d) and y = f(x)"; Theorem 1.3, p.2.

**Formalization Note.** One example is one vector of `ℝ^{d+1}` with the label last, so that one
`sample` instruction of the `GaussMixHH` machine in dimension `d + 1` reads one example. The
target `β`, `w` enters only through this law. -/
noncomputable def sampleLaw {d k : ℕ} (β : Fin k → ℝ) (w : Fin k → EuclideanSpace ℝ (Fin d)) :
    Measure (EuclideanSpace ℝ (Fin (d + 1))) :=
  (stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun x => exampleVec x (reluSum β w x))

/-- The randomness of a run: a fair-coin tape (`GaussMixHH.coinTape`) and, independent of it, an
i.i.d. stream of examples with law `sampleLaw β w` ("independent examples", Theorem 1.3, p.2,
PDF p.4). -/
noncomputable def sampleSpace {d k : ℕ} (β : Fin k → ℝ) (w : Fin k → EuclideanSpace ℝ (Fin d)) :
    Measure ((ℕ → Bool) × (ℕ → EuclideanSpace ℝ (Fin (d + 1)))) :=
  GaussMixHH.coinTape.prod (Measure.infinitePi fun _ : ℕ => sampleLaw β w)

end SumReLU


