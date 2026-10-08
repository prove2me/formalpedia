-- Prove2me | Definitions.Def_OnlineLearningOCO_OnlineToBatch_Setting
-- name    : OnlineLearningOCO_OnlineToBatch_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T14:23:08.913959+00:00
-- url     : https://prove2.me/theorems/715348d8-a79d-495b-9a5c-1f534e7cb313
-- title:
--   Vapnik's general setting of learning and the online-to-batch conversion (Definition 5.1, pp. 186–187)
-- statement:
--   This file fixes the model of §5: Vapnik's general setting of learning (Definition 5.1) and the online-to-batch conversion box on p. 187.
--
--   Hypotheses are vectors $w$ in $E = \mathbb R^d$, and the hypothesis class is a set $S \subseteq E$. Examples range over a measurable space $\Psi$ and are drawn from a probability distribution $Q$. A **cost** $c(w,\psi)$ is the cost of using hypothesis $w$ on example $\psi$, and the **risk** of $w$ is
--   $$C(w) = \mathbb E_{\psi\sim Q}\,[c(w,\psi)] = \int_\Psi c(w,\psi)\,dQ(\psi).$$
--   The cost is **admissible** (`IsCost`) when, on $S\times\Psi$, it is jointly measurable and nonnegative, and $c(w,\cdot)$ is $Q$-integrable for every $w\in S$, so that $C(w)$ is a real number.
--
--   An **online learner** (`IsOnlineLearner`) is a family of measurable maps $A_t : \Psi^t \to S$, $t = 0,1,2,\dots$: in round $t$ it has seen the examples $\psi_0,\dots,\psi_{t-1}$ (equivalently the losses $f_s(w) = c(w,\psi_s)$, $s<t$) and predicts $A_t(\psi_0,\dots,\psi_{t-1})$. Given a sample $\psi = (\psi_0,\dots,\psi_{T-1})$, the **iterates** are $w_t(\psi) = A_t(\psi_0,\dots,\psi_{t-1})$. The sample has law $Q^{\otimes T}$ (independent draws from $Q$), and $\mathrm{Unif}[T]$ is the uniform law on the round indices $\{0,\dots,T-1\}$.
--
--   The conversion outputs either
--   $$\bar w_{\mathrm{avg}}(\psi) = \frac1T\sum_{t} w_t(\psi) \qquad\text{or}\qquad \bar w_{\mathrm{rand}}(\psi,r) = w_r(\psi),\quad r\sim\mathrm{Unif}[T]\ \text{independent of }\psi.$$
--   Finally, the average online loss and the average regret against a comparator $u$ are
--   $$\frac1T\sum_t f_t(w_t) = \frac1T\sum_t c(w_t,\psi_t),\qquad \frac1T\sum_t \big(f_t(w_t)-f_t(u)\big).$$
--
--   Every statement of the mission is phrased with these objects.
--
--   **Formalization Note** Rounds are numbered $0,\dots,T-1$ instead of $1,\dots,T$. Hypotheses live in `EuclideanSpace ℝ (Fin d)` because averaging needs a vector space; the paper's $S$ is an abstract class. The type of $A_t$ (a function of the first $t$ examples only) encodes the paper's "$w_t$ only depends on $\psi_1,\dots,\psi_{t-1}$". The algorithm may read the examples themselves, not only the losses $c(\cdot,\psi_s)$: this is a larger class of algorithms than the paper's, so statements over it are at least as strong. Joint measurability of $c$ on $S\times\Psi$ and measurability of each $A_t$ are added (the paper requires measurability of each $c(w,\cdot)$, footnote 1); nonnegativity is footnote 1's "$c(w,\cdot):\Psi\to\mathbb R^+$". $c$ is a function on all of $E\times\Psi$, but only its values on $S\times\Psi$ are constrained.
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, pp. 186–187, Definition 5.1 and footnote 1, Online-To-Batch Conversion box

import Mathlib

open MeasureTheory

namespace OnlineLearningOCO.OnlineToBatch

/-- The risk `C(w) = 𝔼_{ψ∼Q}[c(w, ψ)]` of a hypothesis `w` in Vapnik's general setting of learning
(Shalev-Shwartz, *Online Learning and Online Convex Optimization*, Found. Trends Mach. Learn. 4(2)
(2011), Definition 5.1, p. 186). `c w` is the cost of `w` as a function of the example. -/
noncomputable def risk {E Ψ : Type*} [MeasurableSpace Ψ] (Q : Measure Ψ) (c : E → Ψ → ℝ) (w : E) : ℝ :=
  ∫ ψ, c w ψ ∂Q

/-- The standing assumptions on the cost in §5 (Definition 5.1 and its footnote 1, p. 186): on
`S × Ψ` the cost is jointly measurable, nonnegative (`c(w,·) : Ψ → ℝ₊`), and for every `w ∈ S`
the random variable `c(w,·)` has a finite expectation, so that `C(w)` is a real number.

Formalization Note: joint measurability on `S × Ψ` (the paper asks only for measurability of each
`c(w,·)`) is needed so that the cost of a data-dependent hypothesis `c(w_t, ψ_t)` is a random
variable. -/
structure IsCost {d : ℕ} {Ψ : Type*} [MeasurableSpace Ψ] (S : Set (EuclideanSpace ℝ (Fin d)))
    (Q : Measure Ψ) (c : EuclideanSpace ℝ (Fin d) → Ψ → ℝ) : Prop where
  measurable : Measurable (fun p : S × Ψ => c p.1 p.2)
  nonneg : ∀ w ∈ S, ∀ ψ, 0 ≤ c w ψ
  integrable : ∀ w ∈ S, Integrable (c w) Q

/-- An online learning algorithm in the online-to-batch conversion (p. 187), with predictions in
`S`. In round `t` (rounds counted from `0`) the algorithm has seen the examples
`ψ₀, …, ψ_{t-1}`, i.e. the loss functions `f_s = c(·, ψ_s)` for `s < t`, and predicts
`A t (ψ₀, …, ψ_{t-1}) ∈ S`. The type of `A` makes the algorithm non-anticipating: its prediction
in round `t` never depends on `ψ_t, ψ_{t+1}, …`. Each prediction map is measurable. -/
structure IsOnlineLearner {d : ℕ} {Ψ : Type*} [MeasurableSpace Ψ] (S : Set (EuclideanSpace ℝ (Fin d)))
    (A : (t : ℕ) → (Fin t → Ψ) → EuclideanSpace ℝ (Fin d)) : Prop where
  mem : ∀ t h, A t h ∈ S
  measurable : ∀ t, Measurable (A t)

/-- The prediction `w_t` of the online algorithm `A` in round `t` of the conversion, as a function
of the whole sample `ψ = (ψ₀, …, ψ_{T-1})`: it is `A` applied to the first `t` examples. -/
def iterate {E Ψ : Type*} (A : (t : ℕ) → (Fin t → Ψ) → E) {T : ℕ} (ψ : Fin T → Ψ) (t : Fin T) : E :=
  A t (fun i : Fin t => ψ (Fin.castLE t.isLt.le i))

/-- The law of the i.i.d. sample `ψ₀, …, ψ_{T-1}`: the product of `T` copies of `Q`. -/
noncomputable def sampleLaw {Ψ : Type*} [MeasurableSpace Ψ] (Q : Measure Ψ) (T : ℕ) :
    Measure (Fin T → Ψ) :=
  Measure.pi fun _ => Q

/-- The uniform distribution on the round indices `[T] = {0, …, T-1}` (a probability measure when
`0 < T`). -/
noncomputable def uniformIndex (T : ℕ) : Measure (Fin T) :=
  ((T : ENNReal)⁻¹) • Measure.count

/-- The output of the online-to-batch conversion with averaging (p. 187):
`w̄ = (1/T) ∑_{t} w_t`. -/
noncomputable def averageOutput {d : ℕ} {Ψ : Type*}
    (A : (t : ℕ) → (Fin t → Ψ) → EuclideanSpace ℝ (Fin d)) {T : ℕ} (ψ : Fin T → Ψ) :
    EuclideanSpace ℝ (Fin d) :=
  (1 / (T : ℝ)) • ∑ t : Fin T, iterate A ψ t

/-- The output of the online-to-batch conversion with randomization (p. 187): `w̄ = w_r`, where the
index `r` is drawn from `uniformIndex T`, independently of the sample. -/
def randomizedOutput {E Ψ : Type*} (A : (t : ℕ) → (Fin t → Ψ) → E) {T : ℕ} (ψ : Fin T → Ψ)
    (r : Fin T) : E :=
  iterate A ψ r

/-- The average online loss `(1/T) ∑_t f_t(w_t)`, with `f_t(w) = c(w, ψ_t)`. -/
noncomputable def avgOnlineLoss {E Ψ : Type*} (c : E → Ψ → ℝ) (A : (t : ℕ) → (Fin t → Ψ) → E)
    {T : ℕ} (ψ : Fin T → Ψ) : ℝ :=
  (1 / (T : ℝ)) * ∑ t : Fin T, c (iterate A ψ t) (ψ t)

/-- The average regret `(1/T) ∑_t (f_t(w_t) − f_t(u))` of the online algorithm against a
comparator `u`, with `f_t(w) = c(w, ψ_t)`. -/
noncomputable def avgRegret {E Ψ : Type*} (c : E → Ψ → ℝ) (A : (t : ℕ) → (Fin t → Ψ) → E)
    {T : ℕ} (ψ : Fin T → Ψ) (u : E) : ℝ :=
  (1 / (T : ℝ)) * ∑ t : Fin T, (c (iterate A ψ t) (ψ t) - c u (ψ t))

end OnlineLearningOCO.OnlineToBatch


