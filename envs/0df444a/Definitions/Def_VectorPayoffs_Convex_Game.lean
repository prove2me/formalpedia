-- Prove2me | Definitions.Def_VectorPayoffs_Convex_Game
-- name    : VectorPayoffs_Convex_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:06:21.401229+00:00
-- url     : https://prove2.me/theorems/e83f4f67-e88e-4ed5-8f14-92feff3b0613
-- title:
--   Vector-payoff game: an r × s matrix of distributions on a closed bounded convex X ⊆ ℝ^N, strategies, plays, approachability and excludability (§1–§3)
-- statement:
--   This file fixes the model of Blackwell's repeated game with vector payoffs and every object the paper's statements refer to.
--
--   1. **The game.** An $r\times s$ matrix $M=\|m(i,j)\|$, $1\le i\le r$, $1\le j\le s$, each element of which is a probability distribution on Euclidean $N$-space $\mathbb R^N$ concentrated on a fixed closed, bounded, convex set $X\subseteq\mathbb R^N$.
--   2. **Mean matrix and transpose.** $\bar m(i,j)=\int x\,m(i,j)(dx)$ is the mean of $m(i,j)$, and $\bar M=\|\bar m(i,j)\|$. The transpose $M'$ is the $s\times r$ matrix with $m'(j,i)=m(i,j)$ on the same $X$: the two players exchange roles.
--   3. **The sets $R(p)$ and $T(q)$.** Let $P$ ($Q$) be the simplex of probability vectors in $\mathbb R^r$ ($\mathbb R^s$). For $p\in P$ and $q\in Q$,
--   $$R(p)=\operatorname{conv}\Big\{\sum_{i}p_i\,\bar m(i,j)\;:\;1\le j\le s\Big\},\qquad T(q)=\operatorname{conv}\Big\{\sum_{j}q_j\,\bar m(i,j)\;:\;1\le i\le r\Big\}.$$
--   4. **Strategies.** A strategy of a player with $k$ pure actions is a sequence $f=\{f_n\}_{n\ge0}$ of measurable maps $f_n$ from $n$-tuples $(x_1,\dots,x_n)$ of past outcomes to the simplex of probability vectors in $\mathbb R^k$; $f_0$ is a single point of the simplex. The stationary strategy $f_n\equiv q$ ignores the history.
--   5. **Averages.** For a history $(x_1,\dots,x_n)$, $\bar x_n=\frac1n\sum_{i=1}^n x_i$ ($\bar x_0=0$).
--   6. **Plays.** A sequence of random vectors $x_1,x_2,\dots$ on a probability space $(\Omega,\mathcal F,\mu)$ is a play of $(f,g)$ in $M$ if each $x_n$ is measurable and, for every $n\ge0$ and every Borel set $B$,
--   $$\mu\big(x_{n+1}\in B\;\big|\;x_1,\dots,x_n\big)=\sum_{i=1}^r\sum_{j=1}^s p_i\,q_j\,m(i,j)(B)\quad\text{a.s.},\qquad p=f_n(x_1,\dots,x_n),\ q=g_n(x_1,\dots,x_n).$$
--   That is: given the past outcomes, I and II draw $i$ and $j$ independently from $p$ and $q$, and the next outcome is drawn from $m(i,j)$.
--   7. **Approachability.** With $\delta_n$ the distance from $\bar x_n$ to $S$, the set $S\subseteq\mathbb R^N$ is *approachable with $f^*$* if for every $\varepsilon>0$ there is $N_0$ such that for every strategy $g$ of II and every play of $(f^*,g)$,
--   $$\mathrm{Prob}\{\delta_n\ge\varepsilon\text{ for some }n\ge N_0\}<\varepsilon .$$
--   It is *excludable with $g^*$* if there is $d>0$ such that for every $\varepsilon>0$ there is $N_0$ such that for every strategy $f$ of I and every play of $(f,g^*)$,
--   $$\mathrm{Prob}\{\delta_n\ge d\text{ for all }n\ge N_0\}>1-\varepsilon .$$
--   $S$ is *approachable (excludable) in $M$* if it is approachable with some $f^*$ (excludable with some $g^*$).
--   8. **Theorem 1's condition.** At a point $x\notin S$ with mixed action $p$: some point $y\in S$ closest to $x$ is such that the hyperplane through $y$ perpendicular to the segment $xy$ separates $x$ from $R(p)$, i.e. $\langle x-y,\,w-y\rangle\le0$ for all $w\in R(p)$.
--
--   These are the objects of every statement of the mission: Theorems 1 and 3, the transpose fact, and the proof steps of Theorem 3.
--
--   **Formalization Note** Points live in `EuclideanSpace ℝ (Fin N)`; pure actions are `Fin r` and `Fin s`; mixed actions are elements of `stdSimplex`. Outcomes are indexed from $1$ (`x 0` is unused). A play is described by the conditional law of each next outcome given the past, via conditional expectations of indicators, and approachability/excludability quantify over every probability space in `Type` carrying such a play, so they do not depend on a particular construction of the process. Distances are `Metric.infEDist` (extended), which is $+\infty$ to the empty set, as in the paper; the empty set is therefore not approachable. Strategies are required to be measurable in the history (implicit in the paper, needed for the process to exist). Separation is weak (closed half-space).
-- source:
--   Blackwell, An analog of the minimax theorem for vector payoffs, Pacific J. Math. 6(1), 1956, pp. 1–2 (§1: M, X, strategies, plays, approachable, excludable, transpose M′), p. 3 (§2: M̄, R(p), THEOREM 1's hypothesis), p. 6 (§3: T(q) in THEOREM 3)

import Mathlib

open MeasureTheory

namespace VectorPayoffs.Convex

/-- Euclidean `N`-space, where the vector payoffs live. -/
abbrev E (N : ℕ) : Type := EuclideanSpace ℝ (Fin N)

/-- Blackwell (1956), §1, p. 1: an `r × s` matrix `M = ‖m(i, j)‖` each element of which is a
probability distribution over a closed bounded convex set `X` in Euclidean `N`-space. -/
structure Game (N r s : ℕ) where
  /-- The closed bounded convex set carrying every payoff distribution. -/
  X : Set (E N)
  isClosed_X : IsClosed X
  isBounded_X : Bornology.IsBounded X
  convex_X : Convex ℝ X
  /-- `m i j` is the payoff distribution when I plays row `i` and II plays column `j`. -/
  m : Fin r → Fin s → Measure (E N)
  isProb : ∀ i j, IsProbabilityMeasure (m i j)
  m_compl_X : ∀ i j, m i j Xᶜ = 0

namespace Game

variable {N r s : ℕ}

/-- §2, p. 3: `m̄(i, j)`, the mean value of the distribution `m(i, j)` (the matrix `M̄`). -/
noncomputable def mbar (G : Game N r s) (i : Fin r) (j : Fin s) : E N :=
  ∫ x, x ∂(G.m i j)

/-- §1, p. 2: the `s × r` matrix `M'`, the transpose of `M` (roles of the players swapped). -/
def transpose (G : Game N r s) : Game N s r where
  X := G.X
  isClosed_X := G.isClosed_X
  isBounded_X := G.isBounded_X
  convex_X := G.convex_X
  m := fun j i => G.m i j
  isProb := fun j i => G.isProb i j
  m_compl_X := fun j i => G.m_compl_X i j

/-- §2, p. 3: for `p ∈ P`, `R(p)` is the convex hull of the `s` points `∑ᵢ pᵢ m̄(i, j)`. -/
noncomputable def R (G : Game N r s) (p : Fin r → ℝ) : Set (E N) :=
  convexHull ℝ (Set.range fun j : Fin s => ∑ i, p i • G.mbar i j)

/-- §3, p. 6 (THEOREM 3): for `q ∈ Q`, `T(q)` is the convex hull of the `r` points
`∑ⱼ qⱼ m̄(i, j)`. -/
noncomputable def T (G : Game N r s) (q : Fin s → ℝ) : Set (E N) :=
  convexHull ℝ (Set.range fun i : Fin r => ∑ j, q j • G.mbar i j)

end Game

/-- §1, pp. 1–2: a strategy for a player with `k` pure actions: for every `n = 0, 1, 2, …` a
function of the `n`-tuple of past outcomes `(x₁, …, xₙ)` with values in the simplex of mixed
actions. Measurability in the history is required so that the play is a well-defined process. -/
structure Strategy (N k : ℕ) where
  toFun : (n : ℕ) → (Fin n → E N) → (Fin k → ℝ)
  mem : ∀ n h, toFun n h ∈ stdSimplex ℝ (Fin k)
  meas : ∀ n, Measurable (toFun n)

/-- The stationary strategy `fₙ ≡ q`. -/
def Strategy.const {N k : ℕ} (q : Fin k → ℝ) (hq : q ∈ stdSimplex ℝ (Fin k)) :
    Strategy N k where
  toFun := fun _ _ => q
  mem := fun _ _ => hq
  meas := fun _ => measurable_const

/-- The average `(1/n) ∑_{k=1}^n x_k` of a history of length `n` (it is `0` for `n = 0`). -/
noncomputable def avgHist {N n : ℕ} (h : Fin n → E N) : E N :=
  (n : ℝ)⁻¹ • ∑ k, h k

/-- The history `(x₁, …, xₙ)` of an outcome process `x`, indexed from `1` (`x 0` is unused). -/
def hist {N : ℕ} {Ω : Type} (x : ℕ → Ω → E N) (n : ℕ) (ω : Ω) : Fin n → E N :=
  fun k => x (k.val + 1) ω

/-- `x̄ₙ = (1/n) ∑_{i=1}^n xᵢ`. -/
noncomputable def avg {N : ℕ} {Ω : Type} (x : ℕ → Ω → E N) (n : ℕ) (ω : Ω) : E N :=
  avgHist (hist x n ω)

namespace Game

variable {N r s : ℕ}

/-- §1, p. 2: `x₁, x₂, …` is the sequence of random outcomes determined by the pair of
strategies `(f, g)` together with `M`: each `xₙ` is measurable, and given `x₁, …, xₙ` the next
outcome `xₙ₊₁` has law `∑ᵢ ∑ⱼ pᵢ qⱼ m(i, j)` with `p = fₙ(x₁, …, xₙ)`, `q = gₙ(x₁, …, xₙ)`
(I and II draw `i` and `j` independently from `p` and `q`, then the outcome is drawn from
`m(i, j)`). -/
def IsPlay (G : Game N r s) (f : Strategy N r) (g : Strategy N s) {Ω : Type}
    [MeasurableSpace Ω] (μ : Measure Ω) (x : ℕ → Ω → E N) : Prop :=
  (∀ n, Measurable (x (n + 1))) ∧
  ∀ (n : ℕ) (B : Set (E N)), MeasurableSet B →
    μ[(x (n + 1) ⁻¹' B).indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap (hist x n) inferInstance]
      =ᵐ[μ] fun ω => ∑ i, ∑ j,
        f.toFun n (hist x n ω) i * g.toFun n (hist x n ω) j * (G.m i j B).toReal

/-- §1, p. 2: `S` is approachable with `f` in `M`: for every `ε > 0` there is an `N₀` such
that, for every strategy `g` of II and every play of `(f, g)`,
`Prob {δₙ ≥ ε for some n ≥ N₀} < ε`, where `δₙ` is the distance from `x̄ₙ` to `S`. -/
def ApproachableWith (G : Game N r s) (S : Set (E N)) (f : Strategy N r) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ (g : Strategy N s) (Ω : Type) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (x : ℕ → Ω → E N), G.IsPlay f g μ x →
      (μ {ω | ∃ n, N₀ ≤ n ∧ 1 ≤ n ∧
        ENNReal.ofReal ε ≤ Metric.infEDist (avg x n ω) S}).toReal < ε

/-- §1, p. 2: `S` is excludable with `g` in `M`: there is `d > 0` such that for every `ε > 0`
there is an `N₀` such that, for every strategy `f` of I and every play of `(f, g)`,
`Prob {δₙ ≥ d for all n ≥ N₀} > 1 - ε`. -/
def ExcludableWith (G : Game N r s) (S : Set (E N)) (g : Strategy N s) : Prop :=
  ∃ d : ℝ, 0 < d ∧ ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ (f : Strategy N r) (Ω : Type)
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (x : ℕ → Ω → E N),
      G.IsPlay f g μ x →
        1 - ε < (μ {ω | ∀ n, N₀ ≤ n → 1 ≤ n →
          ENNReal.ofReal d ≤ Metric.infEDist (avg x n ω) S}).toReal

/-- `S` is approachable in `M`: approachable with some strategy of I. -/
def ApproachableIn (G : Game N r s) (S : Set (E N)) : Prop :=
  ∃ f : Strategy N r, G.ApproachableWith S f

/-- `S` is excludable in `M`: excludable with some strategy of II. -/
def ExcludableIn (G : Game N r s) (S : Set (E N)) : Prop :=
  ∃ g : Strategy N s, G.ExcludableWith S g

/-- THEOREM 1's condition at a point `x ∉ S` with mixed action `p`: some point `y` of `S`
closest to `x` is such that the hyperplane through `y` perpendicular to `xy` (weakly)
separates `x` from `R(p)`, i.e. `⟪x - y, w - y⟫ ≤ 0` for every `w ∈ R(p)`. -/
def BlackwellCondition (G : Game N r s) (S : Set (E N)) (p : Fin r → ℝ) (x : E N) : Prop :=
  ∃ y ∈ S, (∀ z ∈ S, dist x y ≤ dist x z) ∧ ∀ w ∈ G.R p, inner ℝ (x - y) (w - y) ≤ 0

end Game

end VectorPayoffs.Convex


