-- Prove2me | Definitions.Def_MirrorBP_JEA_MBP
-- name    : MirrorBP_JEA_MBP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-23T03:57:45.595986+00:00
-- url     : https://prove2.me/theorems/0ebf0051-dafa-44e5-8b93-2811d6e478fc
-- title:
--   §3.1, pp. 12–13 — normalized queue lengths (9), congestion function (8), the MBP score (10), Algorithm 1, and the potential F
-- statement:
--   The Mirror Backpressure (MBP) policy (§3.1, pp. 12–13).
--
--   1. **Normalized queue lengths** (9). With $\delta_K = \sqrt K$ and $\tilde K = K + m\delta_K$,
--   $$\bar q_i = \frac{q_i + \delta_K}{\tilde K}, \qquad i \in V,$$
--   so that $\mathbf 1^\top \bar{\mathbf q} = 1$ and every $\bar q_i > 0$.
--   2. **Congestion function** (8). $f(\bar q_j) = -\sqrt m\, \bar q_j^{-1/2}$.
--   3. **Score** (10). For a congestion function $f$ and a type-$\tau$ customer, the score of $(j,k) \in \mathcal P(\tau)\times\mathcal D(\tau)$ is $w_{j\tau k} + f(\bar q_j) - f(\bar q_k)$.
--   4. **Algorithm 1.** Let $(j^*, k^*)$ maximize the score over $\mathcal P(\tau) \times \mathcal D(\tau)$ (pairs with $j = k$ allowed). If the score of $(j^*, k^*)$ is nonnegative and $q_{j^*} > 0$, serve the customer from $j^*$ to $k^*$; otherwise drop her. The policy is deterministic, stationary and blind: it never uses the rates $\boldsymbol\phi^t$.
--   5. **Potential.** For an antiderivative $F_1$ of $f$, $F(\bar{\mathbf q}) = \sum_j F_1(\bar q_j)$; for (8) this is (16), $F(\bar{\mathbf q}) = -2\sqrt m \sum_j \sqrt{\bar q_j}$.
--
--   The score is defined for a general congestion function, as Lemmas 1 and 2 use it; Theorem 1 instantiates (8).
--
--   **Formalization Note** The argmax is a tie-breaking rule `sel` with the property `IsArgmaxSel` (membership in $\mathcal P(\tau)\times\mathcal D(\tau)$ and maximality); theorems quantify over every such rule. `mbpPolicy` puts probability one on the MBP decision and takes the membership half of `IsArgmaxSel` to certify feasibility. Algorithm 1's last line prints $1/K$ for $1/\tilde K$; $\bar{\mathbf q}$ is computed from $\mathbf q$ by (9) in every period, which is what the definition does.
-- source:
--   Kanoria, Qian, Blind Dynamic Resource Allocation in Closed Networks via Mirror Backpressure, arXiv:1903.02764v4, pp. 12–13, (8), (9), (10), Algorithm 1; p. 18, (16); Appendix B.1, appendix p. 5 (PDF 38)

import Mathlib
import Definitions.Def_MirrorBP_JEA_Model

namespace MirrorBP.JEA

open Finset

variable {V Ty : Type} [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]

/-- `K̃ = K + m δ_K` with `δ_K = √K` (display (9), p. 12), for `m` nodes and `K` supply units. -/
noncomputable def Kt (m K : ℕ) : ℝ :=
  (K : ℝ) + (m : ℝ) * Real.sqrt K

/-- The normalized queue lengths `q̄_i = (q_i + δ_K)/K̃`, `δ_K = √K`, `K̃ = K + m√K` with `m = |V|`
(display (9), p. 12). For `q ∈ Ω_K` and `K ≥ 1` every `q̄_i` is positive and `∑_i q̄_i = 1`. -/
noncomputable def qbar (K : ℕ) (q : V → ℕ) (i : V) : ℝ :=
  ((q i : ℝ) + Real.sqrt K) / Kt (Fintype.card V) K

/-- The congestion function (8), p. 12: `f(x) = −√m · x^{−1/2}` (used at positive arguments only). -/
noncomputable def fMBP (m : ℕ) (x : ℝ) : ℝ :=
  -Real.sqrt m * x ^ (-(1 / 2 : ℝ))

/-- The MBP score of the pair `(j, k)` for a type-`τ` customer at state `q`, for a congestion function
`f`: `w_{jτk} + f(q̄_j) − f(q̄_k)` (display (10), p. 13). -/
noncomputable def score (w : V → Ty → V → ℝ) (f : ℝ → ℝ) (K : ℕ) (q : V → ℕ) (τ : Ty) (j k : V) : ℝ :=
  w j τ k + f (qbar K q j) - f (qbar K q k)

/-- A tie-breaking rule `sel` for the argmax of (10)/Algorithm 1: for every state `q` and type `τ`,
`sel q τ = (j*, k*)` is a pair in `P(τ) × D(τ)` (pairs with `j = k` allowed) maximizing the score over
`P(τ) × D(τ)`. -/
structure IsArgmaxSel (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (f : ℝ → ℝ) (K : ℕ)
    (sel : (V → ℕ) → Ty → V × V) : Prop where
  mem : ∀ q τ, (sel q τ).1 ∈ P τ ∧ (sel q τ).2 ∈ D τ
  max : ∀ q τ, ∀ j ∈ P τ, ∀ k ∈ D τ, score w f K q τ j k ≤ score w f K q τ (sel q τ).1 (sel q τ).2

/-- The MBP decision, Algorithm 1, p. 13: with `(j*, k*) = sel q τ` the argmax pair, serve the customer
with `(j*, k*)` if its score `w_{j*τk*} + f(q̄_{j*}) − f(q̄_{k*})` is nonnegative and the origin queue
`q_{j*}` is non-empty; otherwise drop the customer. -/
noncomputable def mbpDecision (w : V → Ty → V → ℝ) (f : ℝ → ℝ) (K : ℕ)
    (sel : (V → ℕ) → Ty → V × V) (q : V → ℕ) (τ : Ty) : Decision V :=
  if 0 ≤ score w f K q τ (sel q τ).1 (sel q τ).2 ∧ 0 < q (sel q τ).1 then some (sel q τ) else none

/-- The Mirror Backpressure policy (Algorithm 1, p. 13) as a deterministic, stationary, Markov member of
the policy class: it puts probability one on `mbpDecision`. `hmem` says the tie-break returns pairs in
`P(τ) × D(τ)` (field `mem` of `IsArgmaxSel`), which makes the decision feasible. -/
noncomputable def mbpPolicy (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (f : ℝ → ℝ) (K : ℕ)
    (sel : (V → ℕ) → Ty → V × V) (hmem : ∀ q τ, (sel q τ).1 ∈ P τ ∧ (sel q τ).2 ∈ D τ) :
    Policy P D where
  act _ _ q τ d := if d = mbpDecision w f K sel q τ then 1 else 0
  nonneg _ _ q τ d := by split_ifs <;> norm_num
  sum_one _ _ q τ := by simp
  feasible _ _ q τ d hd := by
    rw [if_neg]
    rintro rfl
    apply hd
    unfold mbpDecision
    split_ifs with h
    · exact ⟨(hmem q τ).1, (hmem q τ).2, h.2⟩
    · trivial

/-- The Lyapunov potential `F(q̄) = ∑_j F₁(q̄_j)`, where `F₁` is an antiderivative of the congestion
function (proof of Lemma 1, Appendix B.1; for (8), `F₁(x) = −2√m √x` gives (16), p. 18). -/
noncomputable def Fpot (F₁ : ℝ → ℝ) (x : V → ℝ) : ℝ :=
  ∑ j, F₁ (x j)

end MirrorBP.JEA


