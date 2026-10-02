-- Prove2me | Definitions.Def_ProcessingNetworks_Stability_StabilityConditions
-- name    : ProcessingNetworks_Stability_StabilityConditions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T17:17:19.782206+00:00
-- url     : https://prove2.me/theorems/f9f4584d-67ad-4617-83aa-154a31d3c08d
-- title:
--   Positive recurrence, stationary distributions and convergence for the ambient chain
-- statement:
--   Proposition 3.5 states that three conditions on the Markov representation of an SPN are
--   equivalent. This item defines each of the three for the continuous-time chain $X$ of a Markov
--   representation, given through its jump matrix $G$ (`jump`) and exit rates $\lambda$ (`rate`), following
--   Appendix D:
--
--   **(a) Positive recurrence (Definition D.15).** `tabooProb jump x n y` is the probability that the
--   jump chain started at $x$ is at $y$ after $n$ steps without having returned to $x$ at steps
--   $1, \dots, n$ (defined by the recursion $g_x(0, y) = [y = x]$, $g_x(n+1, x) = 0$,
--   $g_x(n+1, y) = \sum_z g_x(n, z)\, G(z, y)$ for $y \ne x$); `firstReturnProb jump x n`
--   $= \sum_z g_x(n, z)\, G(z, x)$ is the probability of a first return at step $n+1$; `Recurrent jump x`
--   says the jump chain returns to $x$ with probability one (Definition D.7); and
--   `meanReturnTime jump rate x` is the expected first passage time $\mathbb{E}_x(T_x)$ of the CTMC back
--   to $x$ (Eq. (D.15)), computed through the construction (D.5)–(D.6): the chain holds for an
--   independent unit-mean exponential clock divided by $\lambda(y)$ at each state $y$ visited before
--   the first return, so
--   $$
--   \mathbb{E}_x(T_x) \;=\; \sum_{n \ge 0} \sum_{y} \frac{g_x(n, y)}{\lambda(y)} .
--   $$
--   `PositiveRecurrent jump rate` says every state is recurrent with $\mathbb{E}_x(T_x) < \infty$.
--
--   **(b) Unique stationary distribution (Definition D.16).** `IsStationaryDistribution jump rate π`
--   says the probability distribution $\pi$ satisfies $\pi \Lambda = 0$ for the generator $\Lambda$
--   (off-diagonal $\Lambda(x, y) = \lambda(x) G(x, y)$, diagonal $-\lambda(y)$), written out as
--   $$
--   \sum_x \pi(x)\, \lambda(x)\, G(x, y) \;=\; \pi(y)\, \lambda(y) \qquad \text{for every } y
--   $$
--   (Lemma D.9); `HasUniqueStationaryDistribution` says such a $\pi$ exists and is unique.
--
--   **(c) Convergence in distribution to a non-defective limit.** `ConvergesInDistribution Z` says there
--   is a genuine probability distribution $\pi$ on $\mathbb{Z}_+^I$ (automatically non-defective, being a
--   `PMF`) with $\Pr(Z(t) = z) \to \pi(z)$ for every $z$, as $t \to \infty$.
--
--   **Formalization note.** Both (a) and (b) are the continuous-time notions of the book (the mean
--   return time includes the exponential holding times, and stationarity is for the generator, not
--   for the jump matrix). Requiring recurrence separately in (a) is what makes a transient chain fail
--   positive recurrence even when the series $\sum_n \sum_y g_x(n, y)/\lambda(y)$ happens to converge.
--   "Non-defective" in (c) is captured by using Mathlib's `PMF` type as the limit object.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 47, Proposition 3.5 (supporting notions)

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation

namespace ProcessingNetworks.Stability

open MeasureTheory ProbabilityTheory
open scoped ENNReal

open Classical in
/-- Taboo transition probabilities of the jump chain: `tabooProb jump x n y` is the probability
that the chain driven by `jump`, started at `x`, is at `y` after `n` steps without having returned
to `x` at any of the steps `1, …, n` (so `tabooProb jump x 0 y = [y = x]`). -/
noncomputable def tabooProb {X : Type*} (jump : X → PMF X) (x : X) : ℕ → X → ℝ≥0∞
  | 0, y => if y = x then 1 else 0
  | n + 1, y => if y = x then 0 else ∑' z : X, tabooProb jump x n z * jump z y

/-- Probability that the jump chain started at `x` first returns to `x` at step `n + 1`
(`N_x = n + 1` in Eq. (D.16)). -/
noncomputable def firstReturnProb {X : Type*} (jump : X → PMF X) (x : X) (n : ℕ) : ℝ≥0∞ :=
  ∑' z : X, tabooProb jump x n z * jump z x

/-- The state `x` is recurrent (Definition D.7, through the jump chain, as the book does): the
chain started at `x` returns to `x` with probability one. -/
def Recurrent {X : Type*} (jump : X → PMF X) (x : X) : Prop :=
  ∑' n : ℕ, firstReturnProb jump x n = 1

/-- Expected first passage time `E_x(T_x)` of the continuous-time chain back to `x` (Eq. (D.15)),
computed through the sample-path construction (D.5)–(D.6): the chain holds for an independent
unit-mean exponential clock divided by `λ(y)` at every state `y` its jump chain visits before the
first return, so `E_x(T_x) = ∑ₙ ∑ᵧ P_x(Yₙ = y, n < N_x) / λ(y)`. -/
noncomputable def meanReturnTime {X : Type*} (jump : X → PMF X) (rate : X → ℝ) (x : X) : ℝ≥0∞ :=
  ∑' n : ℕ, ∑' y : X, tabooProb jump x n y * ENNReal.ofReal (rate y)⁻¹

/-- Positive recurrence of the continuous-time chain with jump matrix `jump` and exit rates `rate`
(Definition D.15): every state is recurrent with finite mean return time `E_x(T_x) < ∞`. -/
def PositiveRecurrent {X : Type*} (jump : X → PMF X) (rate : X → ℝ) : Prop :=
  ∀ x : X, Recurrent jump x ∧ meanReturnTime jump rate x < ⊤

/-- `π` is a stationary distribution for the continuous-time chain (Definition D.16): `π Λ = 0`
for the generator `Λ` with off-diagonal entries `Λ(x, y) = λ(x) G(x, y)` and diagonal
`Λ(y, y) = -λ(y)`; written out (Lemma D.9), `∑ₓ π(x) λ(x) G(x, y) = π(y) λ(y)` for every `y`. -/
def IsStationaryDistribution {X : Type*} (jump : X → PMF X) (rate : X → ℝ) (π : PMF X) : Prop :=
  ∀ y : X, ∑' x : X, π x * ENNReal.ofReal (rate x) * jump x y = π y * ENNReal.ofReal (rate y)

/-- The chain has a unique stationary distribution (Proposition 3.5(b)). -/
def HasUniqueStationaryDistribution {X : Type*} (jump : X → PMF X) (rate : X → ℝ) : Prop :=
  ∃! π : PMF X, IsStationaryDistribution jump rate π

/-- The buffer-contents process `Z` converges in distribution to a non-defective limit
(Proposition 3.5(c)): there is a genuine probability distribution `π` on `Z^I_+` (a `PMF`, hence
automatically non-defective) such that, for every `z`, `P(Z(t) = z) → π(z)` as `t → ∞`. -/
def ConvergesInDistribution {Ω : Type*} [MeasureSpace Ω] {I : ℕ} (Z : ℝ → Ω → Fin I → ℕ) : Prop :=
  ∃ π : PMF (Fin I → ℕ), ∀ z : Fin I → ℕ,
    Filter.Tendsto (fun t : ℝ => (ℙ {ω | Z t ω = z}).toReal) Filter.atTop (nhds (π z).toReal)

end ProcessingNetworks.Stability


