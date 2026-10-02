-- Prove2me | Definitions.Def_MDPFinance_POMDPFinance_TerminalWealth
-- name    : MDPFinance_POMDPFinance_TerminalWealth
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:33:21.648522+00:00
-- url     : https://prove2.me/theorems/b0836138-cf3d-4231-89a1-532823ad9f22
-- title:
--   The stationary terminal-wealth market under partial observation (Section 6.1 model data)
-- statement:
--   This definition fixes the terminal-wealth maximization problem of Section 6.1: an investor with
--   utility function $U : \mathrm{dom}\,U \to \mathbb R$ (strictly increasing, strictly concave,
--   continuous) and constant one-period rate $i$ chooses a portfolio strategy to maximize the
--   expected utility of terminal wealth $X_N$, observing only the stock prices (returns) and not the
--   driving unobservable factor $Y_n$.
--
--   The feasible set of actions at wealth $x$ is
--   $$
--   D(x) := \Big\{a \in \mathbb R^d \;\Big|\; (1+i)(x+a\cdot z) \in \mathrm{dom}\,U \text{ for }
--   q_R(y,\cdot)\text{-a.e. } z, \text{ for every } y \in E_Y\Big\},
--   $$
--   quantified over every $y$ because Assumption (FM)(ii) — the support of the return distribution
--   does not depend on $y$ — makes this well-defined and independent of the (unobserved) $y$, exactly
--   as the book remarks immediately after stating the model.
--
--   **Formalization Note.** The wealth transition $T_X(x,a,z) := (1+i)(x+a\cdot z)$, the zero stage
--   reward and the terminal reward $g(x,y) := U(x)$ are not bundled into a separate field here: they
--   are used directly, unbundled, by the shared value-function scaffold
--   (`MDPFinance.POMDPFinance.HistPolicy`) that this market's data feeds into.
--
--   **Moderation note.** The market now carries $\operatorname{dom}U\in\{[0,\infty),(0,\infty)\}$, $1+i>0$ and the section's standing **Assumption (FM)** (p. 176): (i) no arbitrage for every $y$, (ii) the support of $R(y)$ independent of $y$ (made precise as the laws $Q^R(\cdot\mid y)$ having the same null sets, which is what makes $D(x)$ and $\tilde A$ independent of the unobserved $y$), (iii) $\sup_y\mathbb E\|R(y)\|<\infty$. Without (FM) Theorem 6.1.1's existence of maximizers and finiteness of the values fail.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 177, model data preceding Theorem 6.1.1

import Mathlib
import Definitions.Def_MDPFinance_POMDPFinance_Filter

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MDPFinance.POMDPFinance

variable {EY : Type*} [MeasurableSpace EY] {d : ℕ}

/-- The (stationary) terminal-wealth market of §6.1 (Bäuerle–Rieder, p. 177-178, PDF 190-191):
utility `U : \text{dom } U → ℝ` (strictly increasing, strictly concave, continuous), constant rate
`i`, feasible set `D(x) := \{a \mid (1+i)(x+a\cdot z) \in \text{dom } U \text{ for } q_R(y,\cdot)
\text{-a.e. } z, \text{ every } y\}` (`FM`(ii): the support of `R(y)` is independent of `y`, so
quantifying `∀ y` is faithful and well-defined, matching the book's own remark just after the
model's bullet list). `dom U = [0,∞)` or `(0,∞)`, `1+i > 0`, and the section's standing
Assumption (FM) (p. 176) are fields. -/
structure TerminalWealthMarket (M : FilterMarket EY d) where
  domU : Set ℝ
  hdomU : domU = Set.Ici 0 ∨ domU = Set.Ioi 0
  U : ℝ → ℝ
  hU_mono : StrictMonoOn U domU
  hU_concave : StrictConcaveOn ℝ domU U
  hU_cont : ContinuousOn U domU
  i : ℝ
  hi_pos : 0 < 1 + i
  /-- Assumption (FM)(i): no arbitrage, for every hidden state `y`. -/
  hNA : ∀ y (φ : Fin d → ℝ), (∀ᵐ z ∂(M.law y), 0 ≤ ∑ j, φ j * z j) →
    ∀ᵐ z ∂(M.law y), ∑ j, φ j * z j = 0
  /-- Assumption (FM)(ii): the support of `R(y)` is independent of `y` — made precise as the
  laws having the same null sets, which is what makes the a.s. conditions in `D(x)` and `Ã`
  independent of the unobserved `y`. -/
  hsupp : ∀ y y', M.law y ≪ M.law y'
  /-- Assumption (FM)(iii): `sup_y 𝔼‖R(y)‖ < ∞`. -/
  hmom : ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ y, ∫⁻ z, ‖z‖ₑ ∂(M.law y) ≤ K

variable {M : FilterMarket EY d}

/-- `D(x) := \{a \in ℝ^d \mid (1+i)(x+a\cdot z) \in \text{dom } U\}` for `q_R(y,\cdot)`-a.e. `z`,
for every `y \in E_Y` (Bäuerle–Rieder, p. 177). -/
def TerminalWealthMarket.D (Mk : TerminalWealthMarket M) (x : ℝ) : Set (Fin d → ℝ) :=
  {a | ∀ y : EY, ∀ᵐ z ∂(M.lam.withDensity fun z => ENNReal.ofReal (M.qR y z)),
    (1 + Mk.i) * (x + ∑ j, a j * z j) ∈ Mk.domU}

end MDPFinance.POMDPFinance


