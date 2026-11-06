-- Prove2me | Definitions.Def_SKAnnealing_Sampling_plantedTilted
-- name    : SKAnnealing_Sampling_plantedTilted
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:15:35.868195+00:00
-- url     : https://prove2.me/theorems/d3005a3e-2242-4ebf-ae27-43a33bf665b2
-- title:
--   The planted SK model, its laws, and the tilted measure $\mu_t$ of Theorem 1.4
-- statement:
--   Draw $W\sim\mathrm{GOE}(N)$ (entries $W_{ij}=W_{ji}\sim\mathcal N(0,1/N)$) and an independent **plant** $x\sim\mathrm{Unif}\{\pm1\}^N$. The **planted SK model** is the Gibbs measure with interaction $\beta M$, $M=W+\frac\beta N xx^\top$:
--   $$\pi(y)\propto\exp\Big(\frac\beta2\,y^\top\Big(W+\beta\frac{xx^\top}{N}\Big)y\Big)\propto\exp\Big(\frac\beta2\,y^\top Wy+\frac{\beta^2}{2N}\langle y,x\rangle^2\Big).$$
--   For $g\sim\mathcal N(0,\mathrm{Id}_N)$ independent of $(W,x)$ and $t\ge0$, the measure of **Theorem 1.4** is
--   $$\mu_t(y)\propto\exp\Big(\frac\beta2\,y^\top\Big(W+\beta\frac{xx^\top}{N}\Big)y+\big\langle tx+g\sqrt t,\,y\big\rangle\Big),$$
--   the tilt of $\pi$ by the field $tx+\sqrt t\,g$. It is stochastic localization of the planted model at time $t$, with the plant as the localized sample and $B_t=\sqrt t\,g$.
--
--   Defined here: the planted interaction (edge weights $\beta W_{ik}+\frac{\beta^2}N x_ix_k$, $i<k$), the joint law of $(W,x)$, the standard Gaussian law of $g$, the joint law of $((W,x),g)$, and $\mu_t$.
--
--   **Formalization Note** Diagonal terms of $W$ and of $xx^\top$ add constants on $\{\pm1\}^N$ and are dropped; the disorder law is the published `OAI.CriticalSK.disorderLaw` (iid $\mathcal N(0,1/N)$ edges).
-- source:
--   Du, Huang, Mohanty, Rajaraman, Sampling from the Sherrington–Kirkpatrick Model up to Criticality, arXiv:2610.17717 (PDF of October 29, 2026), p. 3 (planted model); Lemma 2.5, p. 12; Theorem 1.4, p. 4

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_tilt

open OAI.CriticalSK MeasureTheory ProbabilityTheory

namespace SKAnnealing.Sampling

/-- The **planted interaction** `β M = β (W + (β/N) x xᵀ)` on the edges `i < k`:
`J_{ik} = β W_{ik} + (β²/N) x_i x_k`, so `gibbs (plantedDisorder β W x) (y) ∝ exp((β/2) yᵀ(W + β xxᵀ/N) y)`
`∝ exp((β/2) yᵀWy + (β²/(2N))⟨y, x⟩²)`.

Du, Huang, Mohanty, Rajaraman, *Sampling from the Sherrington–Kirkpatrick Model up to Criticality*, arXiv:2610.17717 (PDF of October 29, 2026), p. 3 (planted model `π`), Lemma 2.5 (`H_pl`), p. 12, Theorem 1.4, p. 4.

**Formalization Note** Reading R8: diagonal terms are constant on `{±1}^N` and are dropped. -/
noncomputable def plantedDisorder {N : ℕ} (β : ℝ) (W : Disorder N) (x : Spin N) : Disorder N :=
  fun e => β * W e + β ^ 2 / N * spinValue (x e.val.1) * spinValue (x e.val.2)

/-- Joint law of `(W, x)`: `W ∼ GOE(N)` off the diagonal (`OAI.CriticalSK.disorderLaw`, iid `N(0, 1/N)`
edges) and an independent uniform plant `x ∼ Unif{±1}^N`. -/
noncomputable def plantedLaw (N : ℕ) : Measure (Disorder N × Spin N) :=
  (disorderLaw N).prod (PMF.uniformOfFintype (Spin N)).toMeasure

/-- Standard Gaussian vector `g ∼ N(0, Id_N)`. -/
noncomputable def gaussVecLaw (N : ℕ) : Measure (Fin N → ℝ) :=
  Measure.pi fun _ : Fin N => gaussianReal 0 1

/-- Joint law of `((W, x), g)`, all independent: the randomness of Theorem 1.4 and Section 4. -/
noncomputable def plantedFieldLaw (N : ℕ) : Measure ((Disorder N × Spin N) × (Fin N → ℝ)) :=
  (plantedLaw N).prod (gaussVecLaw N)

/-- The measure `µ_t` of **Theorem 1.4**:
`µ_t(y) ∝ exp((β/2) yᵀ(W + β xxᵀ/N) y + ⟨t x + g √t, y⟩)`.

Du, Huang, Mohanty, Rajaraman, *Sampling from the Sherrington–Kirkpatrick Model up to Criticality*, arXiv:2610.17717 (PDF of October 29, 2026), Theorem 1.4, p. 4 (restated pp. 12, 15).

**Formalization Note** Reading R11: stochastic localization on the planted model at time `t` with the plant
`x` as the localized sample and `B_t = √t g`. `Real.sqrt t` is the paper's `√t` (`t ≥ 0` in every use). -/
noncomputable def plantedTilted {N : ℕ} (β t : ℝ) (W : Disorder N) (x : Spin N) (g : Fin N → ℝ) :
    Spin N → ℝ :=
  tilt (gibbs (plantedDisorder β W x)) (t • spinVec x + Real.sqrt t • g)

end SKAnnealing.Sampling


