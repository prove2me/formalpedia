-- Prove2me | Definitions.Def_SKWeakPoincare_IsAugOriginal
-- name    : SKWeakPoincare_IsAugOriginal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:54.985512+00:00
-- url     : https://prove2.me/theorems/10acdbe2-f235-4738-8ffb-da7b6e9dbe09
-- title:
--   The original augmented model $P^{\mathrm{aug}}_{0,n,\beta}$: $A\sim P_{0,n}$, $X\sim\mu_{\beta,A}$, $Y_t=tX+B_t$
-- statement:
--   Under $P^{\mathrm{aug}}_{0,n,\beta}$ one draws the interaction matrix $A\sim P_{0,n}$ (a symmetric zero-diagonal matrix with independent $N(0,1/n)$ entries above the diagonal), then $X\sim\mu_{\beta,A}$, and sets $Y_t=tX+B_t$ for an independent standard Brownian motion $(B_t)_{t\ge0}$ in $\mathbb R^n$. `IsAugOriginal β P Wr σ B` says that the random variables $A=$ `Wr`, $X=$ `σ` and $B$ on a probability space $(\Omega,P)$ have this joint law:
--
--   1. $P(A\in S,\ X=x)=\int_S\mu_{\beta,A}(x)\,dP_{0,n}(A)$ for every Borel $S$ and every $x$;
--   2. $B$ is a standard Brownian motion in $\mathbb R^n$;
--   3. $B$ is independent of $(A,X)$.
--
--   `augField σ B t` is $Y_t=tX+B_t$. This is the law of Lemma 2.1 (ii).
--
--   **Formalization Note** $P_{0,n}$ is `disorderLaw n` and $\mu_{\beta,A}$ is `gibbs (β • A)`. The independent diagonal $d\sim P^{\mathrm{diag}}_{n,\beta}$ of Definition 3.1 enters no event of Lemma 2.1 and is omitted. Brownian time is $\mathbb R_{\ge0}$, so a real time $t\ge0$ is read as `t.toNNReal`.
-- source:
--   Hou–Liu–Yu, Simulated annealing and Weak Poincaré inequalities with inverse-polynomial accuracy for the Sherrington–Kirkpatrick model, arXiv:2610.09882, Definition 3.1, p.15; Lemma 2.1, p.8 (P^aug_{0,n,β})

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_tilt
import Definitions.Def_SKAnnealing_Sampling_IsStdBrownian

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SKWeakPoincare

/-- **The original augmented model `P^aug_{0,n,β}`** realised on a probability space `(Ω, P)`:
`Wr` is the interaction matrix `A ∼ P_{0,n}`, `σ` is `X ∼ μ_{β,A}` given `A`, and `B` is a standard
Brownian motion in `ℝ^n` independent of `(A, X)`.
Hou–Liu–Yu, arXiv:2610.09882, Definition 3.1, p. 15, and Lemma 2.1, p. 8 ("one draws the matrix
`A ∼ P_{0,n}`, then draws `X ∼ μ_A`, then sets `Y_t = tX + B_t` for an independent Brownian motion").

**Formalization Note.** The law of `(A, X)` is given on rectangles: `P(A ∈ S, X = x) =
∫_S μ_{β,A}(x) dP_{0,n}(A)`, with `μ_{β,A} = gibbs (β • A)` and `P_{0,n} = disorderLaw n` (i.i.d.
`N(0, 1/n)` entries above the diagonal of the zero-diagonal symmetric `A`). The independent diagonal
`d ∼ P^diag_{n,β}` of Definition 3.1 enters no event of Lemma 2.1 and is omitted. The field is
`augField σ B` (`Y_t = tX + B_t`). -/
def IsAugOriginal {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (β : ℝ) (P : Measure Ω)
    (Wr : Ω → Disorder n) (σ : Ω → Spin n) (B : ℝ≥0 → Ω → (Fin n → ℝ)) : Prop :=
  IsProbabilityMeasure P ∧ Measurable Wr ∧ Measurable σ ∧
    (∀ S : Set (Disorder n), MeasurableSet S → ∀ x : Spin n,
      P (Wr ⁻¹' S ∩ σ ⁻¹' {x}) = ∫⁻ W in S, ENNReal.ofReal (gibbs (β • W) x) ∂(disorderLaw n)) ∧
    IsStdBrownian B P ∧
    IndepFun (fun ω => (Wr ω, σ ω)) (fun ω t => B t ω) P

/-- The observation field `Y_t = tX + B_t` of the augmented model, at a real time `t ≥ 0`
(`B` is indexed by `ℝ≥0`; `t` is read as `t.toNNReal`). -/
noncomputable def augField {Ω : Type*} {n : ℕ} (σ : Ω → Spin n) (B : ℝ≥0 → Ω → (Fin n → ℝ))
    (t : ℝ) (ω : Ω) : Fin n → ℝ :=
  t • spinVec (σ ω) + B t.toNNReal ω

end SKWeakPoincare


