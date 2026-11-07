-- Prove2me | Definitions.Def_PrivLittlestone_endpointProb
-- name    : PrivLittlestone_endpointProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:31:15.64556+00:00
-- url     : https://prove2.me/theorems/27d700bd-eedf-4515-88ac-8bf058480de6
-- title:
--   Probability $p(e\mid H)$ of a phase endpoint
-- statement:
--   At a phase-start history $H$ (start round $t_0$, past classifiers and aggregate $g$), with threshold $U$ and parameter $s > 0$, let $x \sim \mathrm{Lap}(2/s)$ be the threshold noise (density $f$) and $Y_t \sim \mathrm{Lap}(4/s)$ independent query noises. The endpoint $e = (k, \mathrm{cross})$, a first crossing at round $k$, has conditional probability
--   $$
--   G(x) = \prod_{t_0 \le t < k} \mathbb P[Y_t < U + x - q_t]\cdot \mathbb P[Y_k \ge U + x - q_k],
--   $$
--   the endpoint $e = (T, \text{no-cross})$ has $\prod_{t_0 \le t \le T} \mathbb P[Y_t < U + x - q_t]$, and
--   $$
--   p(e \mid H) = \int G(x) f(x)\, dx ,
--   $$
--   with $q_t$ the reset counter of the continuation. In world $b$ the records are those of world $b$.
--
--   **Formalization Note** $0$-based rounds: a crossing endpoint is $(k, \mathrm{true})$ with $t_0 \le k < T$ and no crossing is $(T, \mathrm{false})$. Values in $[0, \infty]$.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Lemma B.2 and its proof, p.22

import Mathlib
import Definitions.Def_PrivLittlestone_phaseCount
import Definitions.Def_PrivLearn_Generic_Privacy

namespace PrivLittlestone

open MeasureTheory

/-- The **probability of a phase endpoint** `p(e | H)` (He–He, *Private Online Learning of
Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256
21480556…c562), Lemma B.2 and its proof, p.22), at the phase-start history `H` given by the
start round `t₀`, the past classifiers and the phase aggregate `g`, with threshold `U` (`Uth`) and
parameter `s`: with threshold noise `x ∼ Lap(2/s)` and independent query noises
`Y_t ∼ Lap(4/s)`, an endpoint `e = (k, cross)` (first crossing at round `k`) has conditional
probability `G(x) = ∏_{t₀ ≤ t < k} P[Y_t < U + x − q_t] · P[Y_k ≥ U + x − q_k]`, and `e = (T, no-cross)`
has `∏_{t₀ ≤ t < T} P[Y_t < U + x − q_t]`; `p(e | H) = ∫ G(x) f(x) dx`, with `q_t` the phase counter of
the continuation in which `g` is held fixed.

**Formalization Note** 0-based rounds: a crossing endpoint is `(k, true)` with `t₀ ≤ k < T`, and
no crossing through the horizon is `(T, false)`. The world `b` enters through the input
strategy (`worldInput adv b`). Probabilities are in `ℝ≥0∞`. -/
noncomputable def endpointProb {X : Type*} {T : ℕ} (inp : InputStrategy X T)
    (past : Fin T → X → Bool) (t₀ : ℕ) (g : X → Bool) (s Uth : ℝ) (e : ℕ × Bool) : ENNReal :=
  ∫⁻ x, (∏ t ∈ Finset.Ico t₀ (if e.2 then e.1 else T),
      PrivLearn.Generic.laplace (4 / s) (Set.Iio (Uth + x - (phaseCount inp past t₀ g t : ℝ)))) *
    (if e.2 then
      PrivLearn.Generic.laplace (4 / s) (Set.Ici (Uth + x - (phaseCount inp past t₀ g e.1 : ℝ)))
    else 1) ∂(PrivLearn.Generic.laplace (2 / s))

end PrivLittlestone


