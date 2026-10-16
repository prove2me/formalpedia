-- Prove2me | Definitions.Def_InfFisher_Linear_Setting
-- name    : InfFisher_Linear_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T08:04:49.494102+00:00
-- url     : https://prove2.me/theorems/22aac337-617b-46e2-8f30-c737ffbc09d5
-- title:
--   §4.1 — Pareto optimality, linear valuations, Assumption 1, and Theorem 4 conic data
-- statement:
--   For normalized linear valuations $v_i(\theta)=c_i\theta+d_i$ on $[0,1]$, the setting defines Assumption 1, the parabolic cone, the adjacent buyer matrix, and the auxiliary constraints of Theorem 4:
--
--   $$\mathcal C=\{(s,t)\in\mathbb R^2:s^2\le t\},\qquad G_i(s,t)=(d_is+\tfrac{c_i}{2}t,-d_{i+1}s-\tfrac{c_{i+1}}{2}t).$$
--
--   It also defines Pareto optimality for a general continuum item space. The conic representation is the existence of real auxiliary variables satisfying the displayed constraints of Theorem 4, including nonnegative utilities and all bounds on $z_i,w_i$.
--
--   These definitions separate the market model from the geometry of sorted linear valuations.
--
--   **Formalization Note** Lean numbers buyers from zero. Coefficients and auxiliary variables use natural number indices, so Lean pair $k$ corresponds to the paper's adjacent pair $k+1$.
-- source:
--   Gao & Kroer, Infinite-Dimensional Fisher Markets and Tractable Fair Division, arXiv:2010.03025v5, Assumption 1, p. 14; Theorem 4, pp. 15–16

import Definitions.Def_InfFisher_Linear_Market
import Definitions.Def_InfFisher_EG_Setting

namespace InfFisher.Linear

open MeasureTheory
variable {α : Type*} [MeasurableSpace α]

/-- The linear valuations of §4, indexed by buyer numbers starting at zero. -/
def linVal (c d : ℕ → ℝ) (n : ℕ) : Fin n → ℝ → ℝ :=
  fun i θ => c i.val * θ + d i.val

/-- Assumption 1: normalized, nonnegative linear valuations with strictly decreasing intercepts. -/
noncomputable def Assumption1 (n : ℕ) (c d : ℕ → ℝ) : Prop :=
  (∀ i < n, ∀ θ ∈ Set.Icc (0 : ℝ) 1, 0 ≤ c i * θ + d i) ∧
  (∀ i < n, c i / 2 + d i = 1) ∧
  (∀ i < n, d i ≤ 2 ∧ 0 ≤ d i) ∧
  (∀ i j, i < j → j < n → d j < d i)

/-- The epigraph of the square, denoted `𝒞` in Theorem 4. -/
def paraCone : Set (ℝ × ℝ) := {q | q.1 ^ 2 ≤ q.2}

/-- The matrix `Gᵢ` of Theorem 4 applied to `(sᵢ,tᵢ)`. -/
noncomputable def Gmap (c d : ℕ → ℝ) (k : ℕ) (s t : ℝ) : ℝ × ℝ :=
  (d k * s + c k / 2 * t, -(d (k + 1)) * s - c (k + 1) / 2 * t)

/-- All auxiliary constraints of Theorem 4, for a fixed utility vector. -/
def conicConstraints (n : ℕ) (c d : ℕ → ℝ)
    (u : Fin n → ℝ) (z w s t : ℕ → ℝ) : Prop :=
  (∀ i : Fin n, i.val = 0 → u i ≤ z 0) ∧
  (∀ i : Fin n, 1 ≤ i.val → i.val ≤ n - 2 →
    u i ≤ z i.val + w (i.val - 1)) ∧
  (∀ i : Fin n, i.val = n - 1 → u i ≤ 1 + w (n - 2)) ∧
  (∀ k < n - 1,
    Gmap c d k (s k) (t k) = (z k, w k) ∧
    (s k, t k) ∈ paraCone ∧
    z k ∈ Set.Icc (0 : ℝ) 1 ∧
    w k ∈ Set.Icc (-1 : ℝ) 0 ∧
    0 ≤ z k + w k)

/-- The projected conic representation of the feasible utility set. -/
def conicRep (n : ℕ) (c d : ℕ → ℝ) (u : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ u i) ∧ ∃ z w s t : ℕ → ℝ, conicConstraints n c d u z w s t

end InfFisher.Linear


