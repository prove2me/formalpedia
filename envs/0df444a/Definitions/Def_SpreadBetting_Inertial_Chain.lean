-- Prove2me | Definitions.Def_SpreadBetting_Inertial_Chain
-- name    : SpreadBetting_Inertial_Chain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:13.937602+00:00
-- url     : https://prove2.me/theorems/f29cf38c-389f-4e54-a76b-6dd272608160
-- title:
--   (4.1), (4.5)–(4.6), Definitions 1–3, pp. 10, 19, 27–28 — the market-state kernel on ℤ, O(·), slowly vanishing and regular residual probabilities
-- statement:
--   **Market-state kernel.** Under hypothesis $H_i$, the inertial policy with residual probabilities $\rho$ and a Markov strategy $\xi$ of the informed bettor, the market state $Z_t$ is a Markov chain on $\mathbb Z$ that moves from $z$ to $z+1$ with probability
--   $$
--   p(z) = \xi(z)(+1) + \xi(z)(0)\,\bar F_i(\tilde s(z))
--   $$
--   and to $z-1$ with probability $1 - p(z)$. For the threshold strategies of the paper, $p(z) = 1$ when the informed bettor bets $+1$, $p(z) = 0$ when he bets $-1$, and $p(z) = \bar F_i(\tilde s(z))$ when he waits.
--
--   **Definition 1 (p. 10).** For $f, g : \mathbb Z_+ \to \mathbb R$, $f(T) = O(g(T))$ if there are $M < \infty$ and $T_0$ with $|f(T)| \le M g(T)$ for all $T \ge T_0$.
--
--   **Definition 2 (p. 27).** A sequence $\rho = \{\rho(z) \in (0, \tfrac12 - \alpha), z \in \mathbb Z_+\}$ is **slowly vanishing** if
--   $$
--   \liminf_{z\to\infty} z\rho(z) > \tfrac14 \quad\text{and}\quad \lim_{z\to\infty}\rho(z) = 0.
--   $$
--
--   **Definition 3 (p. 28).** $\rho$ is **regular** if there is $A \in \mathbb R \cup \{\pm\infty\}$ with $\rho(z)/\rho(z+1) = 1 + A/z + o(1/z)$ as $z \to \infty$.
--
--   These are the notions in which the convergence and regret results of the paper are stated.
--
--   **Formalization Note** The up-probability is clamped to $[0,1]$ so that the kernel is a Markov kernel for every input; the clamp is the identity for admissible strategies. The chain's path law is taken from the published `GittinsIndex` definition (`BanditAlgorithm.markovChainMeasure`), whose coordinate $\omega_t$ is the paper's $Z_{t+1}$. The liminf of Definition 2 is taken in `EReal`; Definition 3 is encoded as $z(\rho(z)/\rho(z+1) - 1) \to A$ in `EReal`.
-- source:
--   Birge, Feng, Keskin & Schultz, SSRN 3283392 (version of April 14, 2020), pp. 10, 14, 19, 27–28, (4.1), (4.5)–(4.6), Definitions 1–3

import Mathlib
import Definitions.Def_SpreadBetting_Inertial_Model

/-!
Birge, Feng, Keskin & Schultz, SSRN 3283392 (version of April 14, 2020).

The transition kernel on `ℤ` of the market state `Z_t` (4.1) under the inertial policy and a
Markov strategy of the informed bettor ((4.5)–(4.6), p. 19), Definition 1 (`O(·)`, p. 10), and
Definitions 2–3 (slowly vanishing and regular residual probability sequences, pp. 27–28).
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace SpreadBetting.Inertial

/-- Probability that the state moves up, `z ↦ z + 1`, under `H_i` when the informed bettor uses
the Markov strategy `ξ [] ·`: `ξ(+1) + ξ(0) F̄_i(s̃(z))`, clamped to `[0,1]` (the clamp is the
identity for admissible strategies). -/
noncomputable def upProb (M : Market) (ρp : ℕ → ℝ) (i : Fin 2) (ξ : Strategy) (z : ℤ) : ℝ :=
  max 0 (min 1 (ξ [] z .pos + ξ [] z .wait * Fbar M i (sTilde M ρp z)))

/-- The transition kernel of `Z_t` on `ℤ`: up with probability `upProb`, down otherwise. -/
noncomputable def chainKernel (M : Market) (ρp : ℕ → ℝ) (i : Fin 2) (ξ : Strategy) :
    Kernel ℤ ℤ where
  toFun z := ENNReal.ofReal (upProb M ρp i ξ z) • Measure.dirac (z + 1)
    + ENNReal.ofReal (1 - upProb M ρp i ξ z) • Measure.dirac (z - 1)
  measurable' := measurable_of_countable _

instance chainKernel.instIsMarkovKernel (M : Market) (ρp : ℕ → ℝ) (i : Fin 2) (ξ : Strategy) :
    IsMarkovKernel (chainKernel M ρp i ξ) where
  isProbabilityMeasure z := by
    constructor
    have h0 : 0 ≤ upProb M ρp i ξ z := le_max_left _ _
    have h1 : upProb M ρp i ξ z ≤ 1 := max_le zero_le_one (min_le_left _ _)
    show (ENNReal.ofReal (upProb M ρp i ξ z) • Measure.dirac (z + 1)
      + ENNReal.ofReal (1 - upProb M ρp i ξ z) • Measure.dirac (z - 1)) Set.univ = 1
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add h0 (by linarith)]
    simp

/-- Definition 1 (p. 10): `f(T) = O(g(T))` iff `|f(T)| ≤ C g(T)` for all `T ≥ T_0`. -/
def IsBigOP (f g : ℕ → ℝ) : Prop := ∃ C : ℝ, ∃ T0 : ℕ, ∀ T ≥ T0, |f T| ≤ C * g T

/-- Definition 2 (p. 27): `ρ : ℤ₊ → (0, 1/2 - α)` is slowly vanishing if
`liminf_z z ρ(z) > 1/4` (in `EReal`) and `ρ(z) → 0`. -/
def SlowlyVanishing (M : Market) (ρp : ℕ → ℝ) : Prop :=
  (∀ z : ℕ, 1 ≤ z → ρp z ∈ Set.Ioo 0 (1 / 2 - alpha M)) ∧
  (1 / 4 : EReal) < Filter.liminf (fun z : ℕ => ((z * ρp z : ℝ) : EReal)) atTop ∧
  Tendsto ρp atTop (𝓝 0)

/-- Definition 3 (p. 28): `ρ` is regular if `ρ(z)/ρ(z+1) = 1 + A/z + o(1/z)` for some
`A ∈ ℝ ∪ {±∞}`, i.e. `z (ρ(z)/ρ(z+1) - 1) → A` in `EReal`. -/
def Regular (ρp : ℕ → ℝ) : Prop :=
  ∃ A : EReal, Tendsto (fun z : ℕ => ((z * (ρp z / ρp (z + 1) - 1) : ℝ) : EReal)) atTop (𝓝 A)

end SpreadBetting.Inertial


