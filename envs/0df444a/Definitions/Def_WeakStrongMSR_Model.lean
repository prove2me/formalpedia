-- Prove2me | Definitions.Def_WeakStrongMSR_Model
-- name    : WeakStrongMSR_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:25:39.577124+00:00
-- url     : https://prove2.me/theorems/4514b900-91b1-483c-a396-022c9074ca74
-- title:
--   The weak–strong oracle model: corruption law, adversary, weak distances, aspect ratio, solutions
-- statement:
--   An instance of the **weak–strong oracle model** is a metric $(X,d)$ on $n$ points, which are identified with $\{0,\dots,n-1\}$, and a corruption probability $\delta\in(0,\tfrac12)$. Distinct points have positive distance.
--
--   1. Every unordered pair $\{x,y\}$ of distinct points is **corrupted** independently with probability exactly $\delta$. A corruption set $C$ therefore has probability
--   $$\Pr[C]=\delta^{|C|}(1-\delta)^{\binom n2-|C|}.$$
--   2. An **adversary** knows $d$ and $C$ and assigns a value $\mathrm{adv}(C,\{x,y\})$ to every pair. The **weak distance** is
--   $$\tilde d(x,y)=\begin{cases}\mathrm{adv}(C,\{x,y\}) & \{x,y\}\in C,\\ d(x,y) & \{x,y\}\notin C,\ x\neq y,\\ 0 & x=y.\end{cases}$$
--   It is symmetric and fixed once $C$ is drawn, so a repeated weak query returns the same answer.
--   3. Joint probabilities over $C$ and the randomness of an algorithm are $\sum_{C}\Pr[C]\cdot\Pr[\text{event}\mid C]$.
--   4. The **aspect ratio** is the largest distance between distinct points divided by the smallest one.
--   5. A **solution** has $k$ slots. Slot $j$ has a centre $\mathrm{ctr}_j$ and a radius $\mathrm{rad}_j$, and every point $v$ has a slot label $\sigma(v)$. It is **valid** if every radius is nonnegative and $d(\mathrm{ctr}_{\sigma(v)},v)\le \mathrm{rad}_{\sigma(v)}$ for every $v$. Its cost is $\sum_j\mathrm{rad}_j$.
--
--   These are the objects in which every statement of the mission is phrased.
--
--   **Formalization Note** The adversary is a deterministic function of the corruption set, quantified after the metric. A randomized adversary is a mixture of such functions. Empty slots are allowed, so $k$ slots means "at most $k$ balls", the convention of the published `msrOpt`.
-- source:
--   Friggstad–Jamshidian–Vakilian, Minimum Sum-of-Radii Clustering with Strong and Weak Oracles (manuscript, STOC 2027 submission, sha256 5f8fbaf3…67e8f92a0), Definition 1.1, p.1 (PDF 2); §2.1–§2.3, p.5 (PDF 6); §4, p.29 (PDF 30)

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumRadiiPTAS_Main_Basic

open scoped Classical

set_option autoImplicit false

namespace WeakStrongMSR

/-!
# The weak–strong oracle model: corruption, adversary, weak table, aspect ratio, solutions

Z. Friggstad, M. Jamshidian, A. Vakilian, *Minimum Sum-of-Radii Clustering with Strong and Weak
Oracles*, manuscript (STOC 2027 submission, sha256 5f8fbaf3…67e8f92a0): Definition 1.1, p.1;
§2.1–§2.3, p.5; §4, p.29 ("each edge is corrupted independently with probability exactly δ").

This module bundles the tightly coupled objects of the model (one definition per source concept).

**Formalization Note.**
* The points are `Fin n`; the metric is `d : Fin n → Fin n → ℝ`, a metric in the sense of the
  published `MinSumClust.IsMetric` (distinct points at positive distance, §2.1).
* An unordered pair `{x, y}` is a `Sym2 (Fin n)`; `pairs n` are the pairs of distinct points.
  A corruption set `C` is a subset of `pairs n`; every pair is corrupted independently with
  probability exactly `δ`, so `C` has probability `corrWeight δ C`.
* The adversary sees `d` and `Corrupt` (§2.2): it is a function of the corruption set returning a
  value for each pair; it is quantified after `d`. A randomized adversary is a mixture of such
  functions.
* The weak table is `weakDist d C adv`: `adv C {x, y}` on a corrupted pair, `d x y` otherwise,
  `0` on the diagonal. It is symmetric and fixed once `C` is drawn ("repeating a weak query gives
  the same value").
* A solution is written with `k` slots (R6): slot `j` has a centre `ctr j` and a radius `rad j`,
  and each point carries a slot label `σ v`; empty slots are allowed, so this is "at most `k`
  balls". -/

/-- The unordered pairs `{x, y}` of distinct points of `Fin n`. -/
noncomputable def pairs (n : ℕ) : Finset (Sym2 (Fin n)) :=
  Finset.univ.filter (fun e => ¬ e.IsDiag)

/-- The probability of the corruption set `C ⊆ pairs n` when every pair is corrupted
independently with probability `δ` (Definition 1.1): `δ^{|C|} (1 − δ)^{|pairs n| − |C|}`. -/
noncomputable def corrWeight {n : ℕ} (δ : ℝ) (C : Finset (Sym2 (Fin n))) : ℝ :=
  δ ^ C.card * (1 - δ) ^ ((pairs n).card - C.card)

/-- The probability, over the corruption set, of an event `E` of the corruption set. -/
noncomputable def corrProb {n : ℕ} (δ : ℝ) (E : Finset (Sym2 (Fin n)) → Prop) : ℝ :=
  ∑ C ∈ (pairs n).powerset, if E C then corrWeight δ C else 0

/-- The joint probability, over the corruption set `C` and a randomized procedure whose law given
`C` is `μ C`, of an event `E C o` of `C` and the outcome `o`. -/
noncomputable def jointProb {n : ℕ} {α : Type*} (δ : ℝ) (μ : Finset (Sym2 (Fin n)) → PMF α)
    (E : Finset (Sym2 (Fin n)) → α → Prop) : ENNReal :=
  ∑ C ∈ (pairs n).powerset, ENNReal.ofReal (corrWeight δ C) * (μ C).toOuterMeasure {o | E C o}

/-- An adversary: given the corruption set, a value for every pair (used on corrupted pairs). -/
abbrev Adversary (n : ℕ) : Type := Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ

/-- The weak distance `d̃(x, y)`: the adversary's value on a corrupted pair, the true distance on
an honest pair, and `0` for `x = y`. -/
noncomputable def weakDist {n : ℕ} (d : Fin n → Fin n → ℝ) (C : Finset (Sym2 (Fin n)))
    (adv : Adversary n) (x y : Fin n) : ℝ :=
  if x = y then 0 else if s(x, y) ∈ C then adv C s(x, y) else d x y

/-- The ordered pairs of distinct points. -/
noncomputable def offDiag (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 ≠ p.2)

/-- The aspect ratio (§2.3): the largest distance between distinct points divided by the smallest
one; `1` when there are fewer than two points. -/
noncomputable def aspectRatio {n : ℕ} (d : Fin n → Fin n → ℝ) : ℝ :=
  if h : (offDiag n).Nonempty then
    (offDiag n).sup' h (fun p => d p.1 p.2) / (offDiag n).inf' h (fun p => d p.1 p.2)
  else 1

/-- A valid solution (§2.1): every radius is nonnegative and every point lies in the ball of its
slot, `d(ctr (σ v), v) ≤ rad (σ v)`. -/
def ValidSolution {n k : ℕ} (d : Fin n → Fin n → ℝ) (σ : Fin n → Fin k) (ctr : Fin k → Fin n)
    (rad : Fin k → ℝ) : Prop :=
  (∀ j, 0 ≤ rad j) ∧ ∀ v, d (ctr (σ v)) v ≤ rad (σ v)

/-- The cost of a solution: the total radius `∑_j rad j`. -/
noncomputable def solCost {k : ℕ} (rad : Fin k → ℝ) : ℝ := ∑ j, rad j

end WeakStrongMSR


