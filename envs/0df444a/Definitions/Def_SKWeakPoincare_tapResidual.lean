-- Prove2me | Definitions.Def_SKWeakPoincare_tapResidual
-- name    : SKWeakPoincare_tapResidual
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:40:11.907145+00:00
-- url     : https://prove2.me/theorems/a0460e25-1bd1-4348-a910-b77992bab348
-- title:
--   Planted augmented law at a fixed time, the fixed point $q_\beta(t)$, and the TAP residual $R_{\mathrm{TAP}}$
-- statement:
--   **Planted augmented law (Definition 3.2).** Draw $X\sim\mathrm{Unif}(\{\pm1\}^n)$ and a GOE matrix $W$ ($W_{ij}=W_{ji}\sim N(0,1/n)$ for $i<j$, $W_{ii}\sim N(0,2/n)$), independently. Set $A_{\mathrm{full}}=W+\beta XX^\top/n$, let $A$ be its zero-diagonal part and $d$ its diagonal. The diagonal $d$ is independent of $(X,A)$ with i.i.d. $N(\beta/n,2/n)$ coordinates; its law is $P^{\mathrm{diag}}_{n,\beta}$ (`diagLaw`). At a fixed time $t$ the field is $Y_t=tX+B_t$, and $B_t$ has the law of $\sqrt t\,g$ with $g\sim N(0,I_n)$. `plantedAugLaw β n` is the joint law of $((W,X),(d,g))$.
--
--   **Scalar fixed point (eq. (10)).** $f(a)=E_{G\sim N(0,1)}[\tanh^2(a+\sqrt a\,G)]$, and $q_\beta(t)$ is the solution in $[0,1]$ of $q=f(\beta^2q+t)$ (`IsQFixed β t q`).
--
--   **TAP residual.** For $u\in(-1,1)^n$,
--   $$
--   R_{\mathrm{TAP}}(u;A_{\mathrm{full}},y,q)=\operatorname{arctanh}(u)-y-\beta A_{\mathrm{full}}u+\beta^2(1-q)u,
--   $$
--   with $\operatorname{arctanh}$ applied coordinatewise.
--
--   These are the objects of the TAP residual bound (Theorem 2.2).
--
--   **Formalization Note** The off-diagonal part is the published `plantedLaw` (edges $i<j$ and a uniform plant) and $g$ is `gaussVecLaw`; then $A=$ `plantedMatrix β W X` and $A_{\mathrm{full}}=A+\mathrm{diag}(d)$. $\operatorname{arctanh}$ is Mathlib's `Real.artanh`. By Lemma 3.8 the fixed point exists and is unique for $0\le\beta<1$, $t\ge0$.
-- source:
--   Hou–Liu–Yu, Simulated annealing and Weak Poincaré inequalities with inverse-polynomial accuracy for the Sherrington–Kirkpatrick model, arXiv:2610.09882, Section 2.5.1, p.11 (R_TAP); Definitions 3.1–3.2, p.15 (planted model, P^diag); eq. (10), p.17 (q_β(t)); Section 3.4, p.18 (R_TAP)

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_tapHessian
import Definitions.Def_SKAnnealing_Sampling_plantedTilted

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SKWeakPoincare

/-- The law `P^diag_{n,β}` of the diagonal `d` of `A_full`: i.i.d. `N(β/n, 2/n)` coordinates.
Hou–Liu–Yu, arXiv:2610.09882, Definitions 3.1–3.2, p. 15 (`d_i = W_ii + β X_i²/n = W_ii + β/n` with
`W_ii ∼ N(0, 2/n)`). -/
noncomputable def diagLaw (β : ℝ) (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ : Fin n => gaussianReal (β / n) (2 / (n : ℝ≥0))

/-- **The planted augmented law at a fixed time** (Definition 3.2, p. 15; Section 2.5.1, p. 11): the
joint law of `((W, X), (d, g))` with `W` the off-diagonal GOE entries (i.i.d. `N(0, 1/n)` for `i < j`),
`X ∼ Unif({±1}^n)`, `d ∼ P^diag_{n,β}` and `g ∼ N(0, I_n)`, all independent.

**Formalization Note.** From these, `A = plantedMatrix β W X` (the zero-diagonal part of
`W + βXXᵀ/n`), `A_full = A + diag(d)` and `Y_t = tX + √t g`, which has the law of `tX + B_t` at the
fixed time `t` (`B_t ∼ √t g`). Theorem 2.2 concerns one fixed `t` at a time, so only the time-`t`
marginal of the Brownian motion enters. -/
noncomputable def plantedAugLaw (β : ℝ) (n : ℕ) :
    Measure ((Disorder n × Spin n) × ((Fin n → ℝ) × (Fin n → ℝ))) :=
  (plantedLaw n).prod ((diagLaw β n).prod (gaussVecLaw n))

/-- The scalar-channel function `f(a) = E_{G∼N(0,1)}[tanh²(a + √a G)]` of eq. (10), p. 17. -/
noncomputable def scalarF (a : ℝ) : ℝ :=
  ∫ G, Real.tanh (a + Real.sqrt a * G) ^ 2 ∂(gaussianReal 0 1)

/-- `q` is a solution in `[0, 1]` of the fixed-point equation (10), `q = f(β²q + t)`, p. 17.

**Formalization Note.** By Lemma 3.8 (p. 17) the solution in `[0, 1]` exists and is unique for
`0 ≤ β < 1`, `t ≥ 0`; it is `q_β(t)`. Statements quantify over every `q` with `IsQFixed β t q`. -/
def IsQFixed (β t q : ℝ) : Prop :=
  q ∈ Set.Icc (0 : ℝ) 1 ∧ q = scalarF (β ^ 2 * q + t)

/-- **The prescribed-overlap TAP residual**
`R_TAP(u; A_full, y, q) = arctanh(u) − y − β A_full u + β²(1 − q) u` (coordinatewise arctanh),
for `u ∈ (−1, 1)^n`. Hou–Liu–Yu, arXiv:2610.09882, Section 2.5.1, p. 11, and Section 3.4, p. 18.

**Formalization Note.** `arctanh` is Mathlib's `Real.artanh`. -/
noncomputable def tapResidual {n : ℕ} (β : ℝ) (Afull : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ)
    (q : ℝ) (u : Fin n → ℝ) : Fin n → ℝ :=
  fun i => Real.artanh (u i) - y i - β * (Afull.mulVec u) i + β ^ 2 * (1 - q) * u i

end SKWeakPoincare


