-- Prove2me | Definitions.Def_MinSumRadiiPTAS_Main_Basic
-- name    : MinSumRadiiPTAS_Main_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:59:53.04253+00:00
-- url     : https://prove2.me/theorems/89f7f46b-5040-4090-9de1-cfe329fd9003
-- title:
--   Balls, covers, $\mathrm{cost}$, $\mathrm{cost}_\lambda$, the MSR objective $\mathrm{rad}$, $\mathrm{opt}$ and the normalised instances of Lemma 2.1
-- statement:
--   The point set is $P = \{0, \dots, n-1\}$ (`Fin n`) with distances $d$ (a metric, the published `MinSumClust.IsMetric`, where statements need it).
--
--   1. **Ball** `Ball n` (§2, p. 6): a pair (center $c_B \in P$, radius $r_B \in \mathbb R$); its point set is `B.pts d` $= \mathrm{Ball}(c_B, r_B) = \{p \in P : d(c_B, p) \le r_B\}$. Radii of balls are nonnegative (p. 1); statements about arbitrary balls say $0 \le r_B$ explicitly. `B.withRadius r` is the ball with the same center and radius $r$.
--   2. **Minimal balls** `minimalBalls d` $= \mathfrak B = \{\mathrm{Ball}(p, d(p,q)) : p, q \in P\}$ (p. 6).
--   3. **Costs** (p. 6): $\mathrm{cost}(S) = \sum_{B \in S} r_B$ and $\mathrm{cost}_\lambda(S) = \mathrm{cost}(S) + \lambda |S|$ for a finite set of balls (`cost`, `costL`), and the same for a list of balls with every occurrence counted (`lcost`, `lcostL`).
--   4. **Covering** (p. 6): `Covers d S X` (a set of balls) and `CoversL d l X` (a list) say every point of $X$ lies in some ball.
--   5. **MSR objective** (p. 1): $\mathrm{rad}(C) = \min_{p \in P} \max_{q \in C} d(p, q)$ (the center may lie outside $C$), with $\mathrm{rad}(\emptyset) = 0$; a clustering into at most $k$ clusters is a labelling $\sigma : P \to \{0, \dots, k-1\}$ (empty classes allowed), `msrCost d σ` $= \sum_{j} \mathrm{rad}(\sigma^{-1}(j))$, and `msrOpt d k` $= \mathrm{opt}$ is its minimum over all labellings ($0$ if there is none, i.e. $k = 0 < n$).
--   6. **Normalised instance** `StandingInstance d k ε` (Lemma 2.1, p. 7): $d$ is a metric, $1 \le k \le n$, every distance between distinct points is an integer in $[1, \lceil 10k/\varepsilon\rceil]$, and $\mathrm{opt} \le 8k/\varepsilon$.
--   7. `logPlus z` $= \log_+(z) = \max(0, \log z)$, natural logarithm; $\log_+(0) = 0$ (p. 29).
--
--   **Formalization Note** Clusterings as labellings with empty classes of radius $0$ are exactly the partitions into at most $k$ clusters, so `msrOpt` is the paper's $\mathrm{opt}$ (equivalently, the least sum of radii of at most $k$ balls covering $P$, p. 6).
-- source:
--   Fabrizio Grandoni, Anupam Gupta, Jatin Yadav, A PTAS for the Minimum Sum of Radii Problem, manuscript dated November 3, 2026 (STOC 2027 submission), SHA-256 99b43d49…, §1 p. 1, §2 p. 6, Lemma 2.1 p. 7, Lemma 7.4 p. 29

import Mathlib
import Definitions.Def_MinSumClust_IsMetric

open scoped Classical

namespace MinSumRadiiPTAS.Main

/-!
# Balls, covers, costs and the minimum sum of radii objective

Grandoni, Gupta, Yadav, *A PTAS for the Minimum Sum of Radii Problem*, manuscript dated
November 3, 2026 (STOC 2027 submission), SHA-256 99b43d49…: §1, p. 1 (MSR, `rad`, balls with
radii in `ℝ≥0`), §2, p. 6 (`Ball(x, r)`, minimal balls `𝔅`, `cost`, `cost_λ`, covering), p. 7
(Lemma 2.1: the normalised instances of §§3–7).

**Formalization Note.** The point set `P` is `Fin n` and the metric is a function
`d : Fin n → Fin n → ℝ` satisfying the published `MinSumClust.IsMetric`. A ball is the pair
(center, radius); its point set is `Ball.pts d B = {p : d(c_B, p) ≤ r_B}`. Sets of balls are
`Finset (Ball n)` (mathematical sets of balls) or `List (Ball n)` (machine outputs, where a repeated
ball is counted every time it occurs). A clustering into at most `k` clusters is a labelling
`σ : Fin n → Fin k`; empty label classes are allowed and have radius `0`. -/

/-- A ball: a center `c_B ∈ P` and a radius `r_B` (§2, p. 6). Radii of balls are nonnegative
(p. 1, `r_i ∈ ℝ≥0`); where a statement quantifies over arbitrary balls it says `0 ≤ radius`. -/
structure Ball (n : ℕ) where
  /-- The center `c_B`. -/
  center : Fin n
  /-- The radius `r_B`. -/
  radius : ℝ

/-- The point set of a ball: `Ball(c, r) = {p ∈ P : d(c, p) ≤ r}` (§2, p. 6). -/
noncomputable def Ball.pts {n : ℕ} (d : Fin n → Fin n → ℝ) (B : Ball n) : Finset (Fin n) :=
  Finset.univ.filter (fun p => d B.center p ≤ B.radius)

/-- The ball with the same center and the radius changed to `r`. -/
def Ball.withRadius {n : ℕ} (B : Ball n) (r : ℝ) : Ball n := ⟨B.center, r⟩

/-- The set `𝔅 = {Ball(p, d(p, q)) : p, q ∈ P}` of minimal balls (§2, p. 6). -/
noncomputable def minimalBalls {n : ℕ} (d : Fin n → Fin n → ℝ) : Finset (Ball n) :=
  Finset.univ.image (fun pq : Fin n × Fin n => (⟨pq.1, d pq.1 pq.2⟩ : Ball n))

/-- `cost(S) = ∑_{B ∈ S} r_B` (§2, p. 6). -/
noncomputable def cost {n : ℕ} (S : Finset (Ball n)) : ℝ := ∑ B ∈ S, B.radius

/-- `cost_λ(S) = cost(S) + λ |S|` (§2, p. 6). -/
noncomputable def costL {n : ℕ} (lam : ℝ) (S : Finset (Ball n)) : ℝ := cost S + lam * S.card

/-- `cost` of a list of balls, every occurrence counted. -/
noncomputable def lcost {n : ℕ} (l : List (Ball n)) : ℝ := (l.map Ball.radius).sum

/-- `cost_λ` of a list of balls, every occurrence counted: `lcost l + λ · length l`. -/
noncomputable def lcostL {n : ℕ} (lam : ℝ) (l : List (Ball n)) : ℝ := lcost l + lam * l.length

/-- A set of balls covers `X` if every point of `X` lies in one of its balls (§2, p. 6). -/
def Covers {n : ℕ} (d : Fin n → Fin n → ℝ) (S : Finset (Ball n)) (X : Finset (Fin n)) : Prop :=
  ∀ x ∈ X, ∃ B ∈ S, x ∈ B.pts d

/-- A list of balls covers `X`. -/
def CoversL {n : ℕ} (d : Fin n → Fin n → ℝ) (l : List (Ball n)) (X : Finset (Fin n)) : Prop :=
  ∀ x ∈ X, ∃ B ∈ l, x ∈ B.pts d

/-- The radius of a cluster `C ⊆ P`: `rad(C) = min_{p ∈ P} max_{q ∈ C} d(p, q)` (p. 1; footnote 1:
the center may lie outside `C`), and `0` for the empty cluster. -/
noncomputable def rad {n : ℕ} (d : Fin n → Fin n → ℝ) (C : Finset (Fin n)) : ℝ :=
  if h : C.Nonempty then
    (Finset.univ : Finset (Fin n)).inf' ⟨h.choose, Finset.mem_univ _⟩
      (fun p => C.sup' h (fun q => d p q))
  else 0

/-- The MSR cost of a clustering given as a labelling `σ : Fin n → Fin k`: the sum over the `k`
label classes of their radii (empty classes cost `0`). -/
noncomputable def msrCost {n k : ℕ} (d : Fin n → Fin n → ℝ) (σ : Fin n → Fin k) : ℝ :=
  ∑ j : Fin k, rad d (Finset.univ.filter (fun v => σ v = j))

/-- `opt`: the least MSR cost of a partition of `P` into at most `k` clusters, the minimum over all
labellings `σ : Fin n → Fin k` (a finite nonempty set when `k ≥ 1`; `0` when there is none). -/
noncomputable def msrOpt {n : ℕ} (d : Fin n → Fin n → ℝ) (k : ℕ) : ℝ :=
  if h : (Finset.univ : Finset (Fin n → Fin k)).Nonempty then
    (Finset.univ : Finset (Fin n → Fin k)).inf' h (fun σ => msrCost d σ)
  else 0

/-- The normalised instances of §§3–7, the output of Lemma 2.1 (p. 7): `d` is a metric,
`1 ≤ k ≤ n`, every distance between distinct points is a positive integer in `[1, ⌈10k/ε⌉]`,
and the optimum MSR cost is at most `8k/ε`. -/
def StandingInstance {n : ℕ} (d : Fin n → Fin n → ℝ) (k : ℕ) (ε : ℝ) : Prop :=
  MinSumClust.IsMetric d ∧ 1 ≤ k ∧ k ≤ n ∧
    (∀ p q : Fin n, p ≠ q →
      ∃ m : ℕ, d p q = (m : ℝ) ∧ 1 ≤ m ∧ (m : ℝ) ≤ (⌈10 * (k : ℝ) / ε⌉₊ : ℝ)) ∧
    msrOpt d k ≤ 8 * (k : ℝ) / ε

/-- `log₊(z) = max(0, log z)`, natural logarithm, with `log₊(0) = 0` (Lemma 7.4, p. 29). -/
noncomputable def logPlus (z : ℝ) : ℝ := max 0 (Real.log z)

end MinSumRadiiPTAS.Main


