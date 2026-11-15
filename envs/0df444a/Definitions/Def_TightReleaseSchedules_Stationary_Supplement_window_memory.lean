-- Prove2me | Definitions.Def_TightReleaseSchedules_Stationary_Supplement_window_memory
-- name    : TightReleaseSchedules_Stationary_Supplement_window_memory
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:19:58.337819+00:00
-- url     : https://prove2.me/theorems/79b381c2-7a01-4a3a-8772-530776733364
-- title:
--   Sliding-window gain queries and one-pass streaming algorithms with persistent state
-- statement:
--   Let $W,k\ge1$. A stream consists of transformed rows $(z_i,r_i)\in\mathbb R^k\times\mathbb R$, arriving one at a time. After $t\ge W$ arrivals the window holds the last $W$ rows, and the window objective and the numerical update gain are
--
--   $$
--   L_t(\omega)=\frac1{2W}\sum_{i=t-W+1}^{t}(r_i-z_i^\top\omega)^2,\qquad G_t(\omega,\omega')=L_t(\omega)-L_t(\omega')\qquad(\omega,\omega'\in\mathbb R^k).
--   $$
--
--   A **deterministic one-pass algorithm** has a persistent state between arrivals, an initial state, an update reading each arriving row once, and an unrestricted query map that returns a real number from the current state and $(\omega,\omega')$. It uses $M$ persistent bits in the worst case when the set of states it can occupy between arrivals, over all admissible streams, has at most $2^M$ elements.
--
--   A **randomized algorithm with $M$ persistent bits** keeps an $M$-bit string between arrivals. It reads a public random seed drawn once from an arbitrary probability space; the seed is shared and not charged. Every transition, the initial state and every query each use a fresh, independent private draw from an arbitrary probability space. The answer to a fixed query on a fixed stream is then a random variable.
--
--   Given public alphabets $A_1,\dots,A_{k+1}\subset\mathbb R$, one for each of the $k$ coordinates of $z$ and one for the residual $r$, a row is admissible when each of its coordinates lies in its own alphabet. A row belongs to the **restricted subclass** when $r_i=0$ and every coordinate of $z_i$ is an unsigned $b$-bit integer in $\{0,1,\dots,2^b-1\}$. This is the setting $w_0=0$, coordinate projection, $Q=2^b$ of the lower-bound proof. The vector $e_j$ is the $j$-th coordinate vector.
--
--   **Formalization Note** Streams are infinite sequences; the state after $t$ arrivals depends only on the first $t$ rows. Persistent-state counts are `Set.encard`. The private draws are indexed by $\mathbb N$ and combined into a product probability measure. All maps are measurable, so answer probabilities are actual probabilities.
-- source:
--   Jing Wang, When to Update a Pretrained Model: Tight Release Schedules under Distribution Shift, STOC 2027 submission #1096 (October 2026), Appendix B.1 and proof of Theorem B.1, printed pp.28–29, PDF pp.29–30

import Mathlib

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
noncomputable section

namespace TightReleaseSchedules.Stationary.Supplement

/-- A transformed row `(z, r) ∈ ℝ^k × ℝ`, with `z = Uᵀx` and `r = y − w₀ᵀx`. -/
abbrev StreamRow (k : ℕ) := (Fin k → ℝ) × ℝ

/-- The window objective after `t` arrivals `x 0, …, x (t−1)`:
`L_t(ω) = (1/(2W)) ∑_{i=t−W+1}^{t} (r_i − z_iᵀω)²` over the last `W` arrivals. -/
def windowLoss {k : ℕ} (W : ℕ) (x : ℕ → StreamRow k) (t : ℕ) (ω : Fin k → ℝ) : ℝ :=
  (1 / (2 * (W : ℝ))) * ∑ i ∈ Finset.Ico (t - W) t, ((x i).2 - ∑ c, (x i).1 c * ω c) ^ 2

/-- The numerical update gain `G_t(ω, ω′) = L_t(ω) − L_t(ω′)`. -/
def windowGain {k : ℕ} (W : ℕ) (x : ℕ → StreamRow k) (t : ℕ) (ω ω' : Fin k → ℝ) : ℝ :=
  windowLoss W x t ω - windowLoss W x t ω'

/-- Every coordinate of the row lies in its own public alphabet of encodable reals:
coordinate `c` of `z` in `A c.castSucc`, the residual `r` in `A (Fin.last k)`. -/
def RowInAlphabet {k : ℕ} (A : Fin (k + 1) → Set ℝ) (row : StreamRow k) : Prop :=
  (∀ c : Fin k, row.1 c ∈ A c.castSucc) ∧ row.2 ∈ A (Fin.last k)

/-- The lower-bound subclass: `w₀ = 0` and coordinate projection, so `r_i = 0`, and each
coordinate of `z_i` is an unsigned `b`-bit integer in `{0, 1, …, 2^b − 1}`. -/
def RestrictedRow {k : ℕ} (b : ℕ) (row : StreamRow k) : Prop :=
  (∀ c, ∃ n : ℕ, n < 2 ^ b ∧ row.1 c = n) ∧ row.2 = 0

/-- A deterministic one-pass streaming algorithm: its persistent state between arrivals,
the update on each arriving row, and an unrestricted query computation. -/
structure StreamAlgorithm (k : ℕ) where
  State : Type
  init : State
  update : State → StreamRow k → State
  query : State → (Fin k → ℝ) → (Fin k → ℝ) → ℝ

/-- The state after the first `t` arrivals. -/
def StreamAlgorithm.stateAfter {k : ℕ} (A : StreamAlgorithm k) (x : ℕ → StreamRow k) :
    ℕ → A.State
  | 0 => A.init
  | n + 1 => A.update (A.stateAfter x n) (x n)

/-- The persistent states the algorithm can occupy between arrivals on admissible streams.
An algorithm uses `M` persistent bits in the worst case iff this set has at most `2^M`
elements. -/
def StreamAlgorithm.reachable {k : ℕ} (A : StreamAlgorithm k) (valid : StreamRow k → Prop) :
    Set A.State :=
  {σ | ∃ x : ℕ → StreamRow k, (∀ n, valid (x n)) ∧ ∃ t, σ = A.stateAfter x t}

/-- `e_j`, the `j`-th coordinate vector of `ℝ^k`. -/
def coordVec {k : ℕ} (j : Fin k) : Fin k → ℝ := Pi.single j 1

/-- A randomized one-pass streaming algorithm with `M` persistent bits: public randomness
(read-only, shared, uncharged) and fresh private randomness in every transition and in the
query. The state between arrivals is an `M`-bit string. -/
structure RandomizedStreamAlgorithm (k M : ℕ) where
  Public : Type
  publicMeasurable : MeasurableSpace Public
  publicLaw : @Measure Public publicMeasurable
  publicProbability : @IsProbabilityMeasure Public publicMeasurable publicLaw
  Private : Type
  privateMeasurable : MeasurableSpace Private
  privateLaw : @Measure Private privateMeasurable
  privateProbability : @IsProbabilityMeasure Private privateMeasurable privateLaw
  init : Public → Private → (Fin M → Bool)
  update : Public → Private → (Fin M → Bool) → StreamRow k → (Fin M → Bool)
  query : Public → Private → (Fin M → Bool) → (Fin k → ℝ) → (Fin k → ℝ) → ℝ
  measurable_init : Measurable (fun p : Public × Private => init p.1 p.2)
  measurable_update : ∀ σ row, Measurable (fun p : Public × Private => update p.1 p.2 σ row)
  measurable_query : ∀ σ ω ω',
    Measurable (fun p : Public × Private => query p.1 p.2 σ ω ω')

attribute [instance] RandomizedStreamAlgorithm.publicMeasurable
  RandomizedStreamAlgorithm.publicProbability RandomizedStreamAlgorithm.privateMeasurable
  RandomizedStreamAlgorithm.privateProbability

/-- The state after `t` arrivals, with public seed `p` and private draws `ξ 0` (initial
state), `ξ (n+1)` (transition on arrival `n`). -/
def RandomizedStreamAlgorithm.stateAfter {k M : ℕ} (A : RandomizedStreamAlgorithm k M)
    (p : A.Public) (ξ : ℕ → A.Private) (x : ℕ → StreamRow k) : ℕ → (Fin M → Bool)
  | 0 => A.init p (ξ 0)
  | n + 1 => A.update p (ξ (n + 1)) (A.stateAfter p ξ x n) (x n)

/-- The joint law of the public seed, the independent private transition draws, and an
independent private draw for the query. -/
def RandomizedStreamAlgorithm.law {k M : ℕ} (A : RandomizedStreamAlgorithm k M) :
    Measure (A.Public × ((ℕ → A.Private) × A.Private)) :=
  A.publicLaw.prod ((Measure.infinitePi (fun _ : ℕ => A.privateLaw)).prod A.privateLaw)

/-- The probability that the query `(ω, ω′)` asked after `t` arrivals of the fixed stream
`x` is answered with exactly the value `g`. -/
def RandomizedStreamAlgorithm.probAnswer {k M : ℕ} (A : RandomizedStreamAlgorithm k M)
    (x : ℕ → StreamRow k) (t : ℕ) (ω ω' : Fin k → ℝ) (g : ℝ) : ℝ≥0∞ :=
  A.law {r | A.query r.1 r.2.2 (A.stateAfter r.1 r.2.1 x t) ω ω' = g}

end TightReleaseSchedules.Stationary.Supplement


