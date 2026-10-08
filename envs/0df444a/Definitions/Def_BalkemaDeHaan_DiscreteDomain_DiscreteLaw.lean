-- Prove2me | Definitions.Def_BalkemaDeHaan_DiscreteDomain_DiscreteLaw
-- name    : BalkemaDeHaan_DiscreteDomain_DiscreteLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:05:35.863073+00:00
-- url     : https://prove2.me/theorems/99151390-31cb-4d08-9512-c724d66251c8
-- title:
--   Discrete laws with an unbounded jump sequence, conditions (12a)–(12b), and tail equivalence
-- statement:
--   1. A law $\nu$ on $\mathbb R$ is **discrete with jump sequence** $t_0 < t_1 < t_2 < \cdots$ if the $t_n$ are strictly increasing and unbounded, every $t_n$ carries positive mass, and $\nu$ puts no mass outside $\{t_0, t_1, \dots\}$. Its distribution function $F_0 = 1 - R_0$ is then right-continuous and jumps exactly at the $t_n$.
--   2. Condition **(12a)** on the jumps:
--   $$\frac{t_{n+1} - t_n}{t_n - t_{n-1}} \to e^{pc} \quad (n \to \infty).$$
--   3. Condition **(12b)** on the tail:
--   $$\frac{R_0(t_{n+1})}{R_0(t_n)} \to e^{-p} \quad (n \to \infty).$$
--   4. Two laws whose distribution functions satisfy $F_i(x) < 1$ for all $x$ are **tail equivalent** if $1 - F_1(x) \sim 1 - F_2(x)$ as $x \to \infty$, i.e. the ratio of the tails tends to $1$.
--
--   These are the ingredients of the characterization of the domains of attraction of the discrete limit laws $\Pi_{p,c}$ (Theorem 5).
--
--   **Formalization Note** (12a) is indexed from $n = 1$: the Lean sequence is $(t_{n+2} - t_{n+1})/(t_{n+1} - t_n)$. Tail equivalence includes the condition $F_i(x) < 1$ for both laws, as the page requires; without it the ratio of tails would divide by zero.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), pp. 799–800 (PDF 8–9), §3, (12a), (12b) and the definition of tail equivalence

import Mathlib

open MeasureTheory Filter Topology

namespace BalkemaDeHaan.DiscreteDomain

/-- `ν` is a discrete law whose discontinuity points form the unbounded increasing sequence
`t₀ < t₁ < t₂ < ⋯` (§3, pp. 799–800, PDF 8–9): `t` is strictly increasing and tends to `∞`,
every `t n` carries positive mass, and `ν` puts no mass off `{t₀, t₁, …}`. Its distribution
function `cdf ν` is then a right-continuous step function jumping exactly at the `t n`. -/
def IsDiscreteWithJumps (ν : Measure ℝ) (t : ℕ → ℝ) : Prop :=
  StrictMono t ∧ Tendsto t atTop atTop ∧ ν (Set.range t)ᶜ = 0 ∧ ∀ n, 0 < ν {t n}

/-- Condition (12a), p. 800 (PDF 9): `(t_{n+1} - t_n)/(t_n - t_{n-1}) → e^{pc}` as `n → ∞`
(indexed from `n = 1`). -/
def GapRatio (t : ℕ → ℝ) (p c : ℝ) : Prop :=
  Tendsto (fun n : ℕ => (t (n + 2) - t (n + 1)) / (t (n + 1) - t n)) atTop
    (𝓝 (Real.exp (p * c)))

/-- Condition (12b), p. 800 (PDF 9): `R(t_{n+1})/R(t_n) → e^{-p}` as `n → ∞`, where
`R(x) = ν((x, ∞))` is the BalkemaDeHaan.LimitTypes.tail of `ν`. -/
def TailRatio (ν : Measure ℝ) (t : ℕ → ℝ) (p : ℝ) : Prop :=
  Tendsto (fun n : ℕ => (ν (Set.Ioi (t (n + 1)))).toReal / (ν (Set.Ioi (t n))).toReal) atTop
    (𝓝 (Real.exp (-p)))

/-- Tail equivalence (p. 800, PDF 9): two laws whose distribution functions satisfy
`F_i(x) < 1` for all `x` are BalkemaDeHaan.LimitTypes.tail equivalent if `1 - F₁(x) ~ 1 - F₂(x)` as `x → ∞`. -/
def TailEquiv (μ₁ μ₂ : Measure ℝ) : Prop :=
  (∀ x, 0 < μ₁ (Set.Ioi x)) ∧ (∀ x, 0 < μ₂ (Set.Ioi x)) ∧
  Tendsto (fun x => (μ₁ (Set.Ioi x)).toReal / (μ₂ (Set.Ioi x)).toReal) atTop (𝓝 1)

end BalkemaDeHaan.DiscreteDomain


