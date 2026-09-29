-- Prove2me | Definitions.Def_KarlinDP_Deterministic_Model
-- name    : KarlinDP_Deterministic_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:15:10.976582+00:00
-- url     : https://prove2.me/theorems/7ab59983-7169-4519-a29f-e492e493f11e
-- title:
--   Karlin's deterministic dynamic programming model: trajectory ωₙ, weights Pₙ(s), yield Φ(ω, s), optimal return K(ω)
-- statement:
--   This file sets up the deterministic dynamic programming model of Karlin (1955). Let $\Omega$ be a state space and $D$ a decision space. A **strategy** is a sequence $s = (\delta_1, \delta_2, \dots)$ of decisions, one per stage. The data of the model are a return function $L : \Omega \times D \to \mathbb{R}$, a transition $T : D \times \Omega \to \Omega$, $(\delta, \omega) \mapsto T_\delta\,\omega$, and a normalization factor $P : D \to \mathbb{R}$.
--
--   1. **Trajectory.** Starting from $\omega_1 = \omega$, the states visited under $s$ are $\omega_n = T_{\delta_{n-1}}\,\omega_{n-1}$.
--   2. **Weights.** The normalization constants have the product form $P_n(s) = \prod_{i=1}^{n-1} P(\delta_i)$, with $P_1(s) = 1$.
--   3. **Partial yields.** The $k$-th partial sum of the yield is $\sum_{n=1}^{k} L(\omega_n, \delta_n)\, P_n(s)$ (display (1) of the paper).
--   4. **Total yield.** The payoff of $s$ from $\omega$ is
--   $$\Phi(\omega, s) = \sum_{n=1}^{\infty} L(\omega_n, \delta_n)\, P_n(s).$$
--   5. **Optimal return.** $K(\omega) = \sup_{s} \Phi(\omega, s)$, the paper's $\max_S \Phi(\omega, s)$.
--
--   These objects are shared by every statement of the mission: existence of optimal strategies, the principle of optimality, and uniqueness of solutions of the functional equation.
--
--   **Formalization Note** A strategy is a function `s : ℕ → D`, and Lean's 0-based index `k` is the paper's stage $k+1$: `s 0` is $\delta_1$, `trajectory T ω s 0 = ω` is $\omega_1$, and `weight P s k` is $P_{k+1}(s)$, so `weight P s 0 = 1`. The paper allows stage-dependent returns $L_n$; the model uses a single $L$, as the paper does from display (1) on and as the functional equation (2) requires. The total yield is a `tsum`, which Lean sets to $0$ for a non-summable series; every statement using it assumes the uniform convergence (1), which excludes that case. The optimal return is a supremum, which Lean sets to $0$ for an unbounded family; it is used only under hypotheses that make $\Phi(\omega,\cdot)$ bounded and its supremum attained.
-- source:
--   Karlin, The Structure of Dynamic Programing Models, Naval Res. Logist. Quart. 2(4), 1955, pp. 286–287, §Formal Structure (the spaces Ω, D, S, L_n, T_δ, P_n(s) = Π_{i=1}^{n-1} P(δ_i), Φ(ω, s), display (1)); p. 290, K(ω) = max_S Φ(ω, s)

import Mathlib

namespace KarlinDP.Deterministic

/-- The state trajectory generated from the initial state `ω` by the strategy `s = (δ₁, δ₂, …)`
(Karlin 1955, p. 287): `ω₁ = ω` and `ω_n = T_{δ_{n-1}} ω_{n-1}`. Lean index `k` is the paper's
stage `k + 1`: `trajectory T ω s 0 = ω` is `ω₁`, and `s k` is the paper's `δ_{k+1}`. -/
def trajectory {Ω D : Type*} (T : D → Ω → Ω) (ω : Ω) (s : ℕ → D) : ℕ → Ω
  | 0 => ω
  | k + 1 => T (s k) (trajectory T ω s k)

/-- The normalization constant in product form (p. 287): `weight P s k = ∏_{i<k} P (s i)`, the
paper's `P_{k+1}(s) = ∏_{i=1}^{k} P(δ_i)`; in particular `weight P s 0 = 1` is `P₁(s) ≡ 1`. -/
def weight {D : Type*} (P : D → ℝ) (s : ℕ → D) (k : ℕ) : ℝ :=
  ∏ i ∈ Finset.range k, P (s i)

/-- The `k`-th partial sum of the total yield, display (1) of p. 287:
`∑_{n=1}^{k} L(ω_n, δ_n) P_n(s)`, written with Lean's 0-based index. -/
def partialYield {Ω D : Type*} (L : Ω → D → ℝ) (T : D → Ω → Ω) (P : D → ℝ) (ω : Ω)
    (s : ℕ → D) (k : ℕ) : ℝ :=
  ∑ n ∈ Finset.range k, L (trajectory T ω s n) (s n) * weight P s n

/-- The total yield `Φ(ω, s) = ∑_{n=1}^{∞} L(ω_n, δ_n) P_n(s)` (p. 287), as a `tsum`
(which is `0` if the series is not summable). -/
noncomputable def totalYield {Ω D : Type*} (L : Ω → D → ℝ) (T : D → Ω → Ω) (P : D → ℝ)
    (ω : Ω) (s : ℕ → D) : ℝ :=
  ∑' n, L (trajectory T ω s n) (s n) * weight P s n

/-- The optimal return `K(ω) = max_S Φ(ω, s)` (p. 290), written as the supremum over all
strategies `s : ℕ → D`. It is the maximum only when the family is bounded above and the supremum
is attained; statements using it supply hypotheses that guarantee this. -/
noncomputable def optimalReturn {Ω D : Type*} (L : Ω → D → ℝ) (T : D → Ω → Ω) (P : D → ℝ)
    (ω : Ω) : ℝ :=
  ⨆ s : ℕ → D, totalYield L T P ω s

end KarlinDP.Deterministic


