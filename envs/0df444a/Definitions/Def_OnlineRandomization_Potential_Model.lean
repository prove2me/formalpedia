-- Prove2me | Definitions.Def_OnlineRandomization_Potential_Model
-- name    : OnlineRandomization_Potential_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T07:24:16.530391+00:00
-- url     : https://prove2.me/theorems/7054be6e-a7bb-4f07-ad73-33183f4b4c01
-- title:
--   Request-answer games, online algorithms, adaptive adversaries and competitiveness
-- statement:
--   This file sets up the general framework of request-answer games of Ben-David, Borodin, Karp, Tardos and Wigderson.
--
--   A **request-answer game** consists of a request set $R$, a finite answer set $A$, and cost functions $f_n : R^n \times A^n \to \mathbb R$ for $n = 0, 1, 2, \dots$. The **off-line optimum** of a request sequence $r = (r_1, \dots, r_n)$ is
--   $$
--   c(r) = \min \{ f_n(r, a) \mid a \in A^n \}.
--   $$
--
--   1. A **deterministic online algorithm** $G$ is a sequence of maps $g_i : R^i \to A$. On $r = (r_1, \dots, r_n)$ it answers $G(r) = (a_1, \dots, a_n)$ with $a_i = g_i(r_1, \dots, r_i)$, at cost $c_G(r) = f_n(r, G(r))$.
--   2. A function $\alpha : \mathbb R \to \mathbb R$ is **linear** in the paper's sense if $\alpha(x) = c x + d$ for constants $c, d$.
--   3. $G$ is **$\alpha$-competitive** if $c_G(r) \le \alpha(c(r))$ for every request sequence $r$.
--   4. A **randomized online algorithm** $H$ is a probability distribution over deterministic online algorithms $H_y$, where $y$ ranges over a probability space of coin tosses. It is **$\beta$-competitive against any oblivious adversary** if $\mathbb E_y[c_{H_y}(r)] \le \beta(c(r))$ for every $r$.
--   5. An **adaptive off-line adversary** $Q$ is a sequence of maps $q_n : A^n \to R \cup \{\mathrm{stop}\}$, $n = 0, 1, \dots, d_Q$, with $q_{d_Q}$ always equal to $\mathrm{stop}$: it chooses the next request from the algorithm's answers so far. An **adaptive on-line adversary** $S = (Q, P)$ adds maps $p_n : A^n \to A$; it answers its own request $r_{n+1}$ with $b_{n+1} = p_n(a_1, \dots, a_n)$ before the algorithm does.
--
--   These are the objects all results of the paper are stated about; the mission's later items build on them.
--
--   **Formalization Note** Request and answer sequences are Lean lists, oldest first; `cost r a` is $f_n(r, a)$ for lists of common length $n$, and its value on lists of different lengths is never used. Costs are real numbers, whereas the paper allows the value $+\infty$ ("not all answer sequences are allowed"); every theorem quantifying over games is therefore stated for the real-valued games only. The minimum $c(r)$ is taken over the finite nonempty set $A^n$, so $A$ is assumed nonempty. A deterministic algorithm is one function on request lists; its value on the empty list is unused. "Stop" is `none`, and the depth bound $d_Q$ is a field with the property that the adversary stops once $d_Q$ answers have been given. A randomized algorithm carries a probability measure on its coin space and the requirement that each answer is a measurable function of the coins; the expectations of the paper are Bochner integrals over the coins (each integrand used in the mission takes finitely many values, so it is integrable).
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript pp. 7-9, §2

import Mathlib

namespace OnlineRandomization.Potential

open MeasureTheory

/-- Manuscript p. 7: a request-answer game with request set `R` and answer set `A`.
For lists of equal length `n`, `cost r a` is the paper's `f_n(r, a)`; its value on lists of
different lengths is never used. Costs are real (the paper allows the value `∞`). -/
structure Game (R A : Type*) where
  cost : List R → List A → ℝ

/-- Manuscript p. 7: the off-line optimum `c(r) = min { f_n(r, a) | a ∈ A^n }`, a minimum over
the finite nonempty set `A^n`. -/
noncomputable def Game.opt {R A : Type*} [Fintype A] [Nonempty A]
    (F : Game R A) (r : List R) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun a : Fin r.length → A => F.cost r (List.ofFn a))

/-- Manuscript p. 7: the paper's "linear" functions `α, β : ℝ → ℝ` are affine,
`α(x) = c·x + d`. -/
def IsLinear (α : ℝ → ℝ) : Prop :=
  ∃ c d : ℝ, ∀ x : ℝ, α x = c * x + d

/-- Manuscript p. 7: a deterministic online algorithm `(g_i)_{i ≥ 1}`, `g_i : R^i → A`,
represented as one function on request lists; `G (r_1, …, r_i)` is `g_i(r_1, …, r_i)`.
Its value on the empty list is never used. -/
abbrev DetAlg (R A : Type*) := List R → A

/-- Manuscript p. 7: `G(r) = (a_1, …, a_n)` with `a_i = g_i(r_1, …, r_i)`; list index `i`
(0-based) holds the paper's `a_{i+1}`. -/
def DetAlg.answers {R A : Type*} (G : DetAlg R A) (r : List R) : List A :=
  (List.range r.length).map fun i => G (r.take (i + 1))

/-- Manuscript p. 7: the cost `c_G(r) = f_n(r, G(r))`. -/
def DetAlg.costOn {R A : Type*} (F : Game R A) (G : DetAlg R A) (r : List R) : ℝ :=
  F.cost r (G.answers r)

/-- Manuscript p. 8: an adaptive off-line adversary `Q = (q_n)`, `q_n : A^n → R ∪ {stop}`,
with `none` for "stop" and a depth bound `d_Q` from which on it always stops. -/
structure OfflineAdv (R A : Type*) where
  next : List A → Option R
  depth : ℕ
  stop_of_le : ∀ a : List A, depth ≤ a.length → next a = none

/-- Manuscript p. 8: an adaptive on-line adversary `S = (Q, P)`; `ans (a_1, …, a_i)` is
`p_i(a_1, …, a_i)`, the adversary's own answer `b_{i+1}` to its request `r_{i+1}`. -/
structure OnlineAdv (R A : Type*) extends OfflineAdv R A where
  ans : List A → A

/-- Manuscript p. 7: a randomized online algorithm in mixed form, a probability distribution
over deterministic online algorithms `G_x`, `x` the coins. Each answer is a measurable function
of the coins. -/
structure RandAlg (R A Ω : Type*) [MeasurableSpace Ω] where
  μ : Measure Ω
  isProb : IsProbabilityMeasure μ
  alg : Ω → DetAlg R A
  meas : ∀ (r : List R) (x : A), MeasurableSet {ω | alg ω r = x}

/-- Manuscript p. 7: a deterministic algorithm `G` is `α`-competitive if
`c_G(r) ≤ α(c(r))` for every request sequence `r`. For a deterministic algorithm this is also
competitiveness against adaptive adversaries (p. 8). -/
def IsCompetitive {R A : Type*} [Fintype A] [Nonempty A]
    (F : Game R A) (α : ℝ → ℝ) (G : DetAlg R A) : Prop :=
  ∀ r : List R, G.costOn F r ≤ α (F.opt r)

/-- Manuscript p. 7: a randomized algorithm `H` is `β`-competitive against any oblivious
adversary if `E_y[c_{H_y}(r)] ≤ β(c(r))` for every request sequence `r`. -/
def IsCompetitiveObl {R A Ω : Type*} [Fintype A] [Nonempty A] [MeasurableSpace Ω]
    (F : Game R A) (β : ℝ → ℝ) (H : RandAlg R A Ω) : Prop :=
  ∀ r : List R, (∫ y, (H.alg y).costOn F r ∂H.μ) ≤ β (F.opt r)

end OnlineRandomization.Potential


