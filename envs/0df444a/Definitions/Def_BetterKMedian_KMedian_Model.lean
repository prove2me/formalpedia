-- Prove2me | Definitions.Def_BetterKMedian_KMedian_Model
-- name    : BetterKMedian_KMedian_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-13T15:07:34.293558+00:00
-- url     : https://prove2.me/theorems/1cda4b56-b1a1-415b-b7ac-9e7259568ced
-- title:
--   Metric $k$-median with rational data: cost, $\mathrm{opt}_\ell$, $\beta$-stability, the binary code, and randomized algorithms with coin flips
-- statement:
--   This file fixes the objects needed to state the $k$-median results of the paper (Theorems 1.1, 1.2 and 1.4): instances, costs, optima, stability, and what a deterministic or randomized algorithm receives and returns.
--
--   **Instances.** A metric $k$-median instance consists of finitely many points, a distance $d$ on them with rational values, a set $D$ of clients, a nonempty set $F$ of facilities, and an integer $k \ge 1$. The distance is a pseudometric: nonnegative, symmetric, zero on the diagonal, and satisfying the triangle inequality; distinct points may be at distance $0$, and a point may be both a client and a facility.
--
--   **Costs and optima.** For a nonempty $S \subseteq F$,
--   $$d(j, S) = \min_{i \in S} d(i, j), \qquad \mathrm{cost}(S) = \sum_{j \in D} d(j, S).$$
--   A solution with at most $\ell$ centers is a nonempty $S \subseteq F$ with $|S| \le \ell$, and
--   $$\mathrm{opt}_\ell = \min\{\mathrm{cost}(S) : \emptyset \ne S \subseteq F,\ |S| \le \ell\}, \qquad \mathrm{opt} = \mathrm{opt}_k .$$
--
--   **Stability.** An instance is $\beta$-stable if $\mathrm{opt}_{k-1} \ge (1+\beta)\,\mathrm{opt}_k$. Every instance with $k = 1$ is $\beta$-stable.
--
--   **Algorithms.** An algorithm reads the instance written in binary: the number of points, $k$, one bit per point for membership in $D$, one bit per point for membership in $F$, and all pairwise distances as fractions. It writes one bit per point, the indicator of the set of facilities it opens. A randomized algorithm reads, after the instance, a string of coin flips; for a number $m$ of coins and an event $E$ on coin strings,
--   $$\Pr_m[E] = \frac{|\{r \in \{0,1\}^m : E(r)\}|}{2^m}.$$
--
--   The file also names the time bound of Theorem 1.4: for natural numbers $a, b$, reals $\beta, \varepsilon > 0$ and an input length $N$,
--   $$T_{a,b}(\beta, \varepsilon, N) = \exp\!\bigl(a\,\beta^{-1}(1/\varepsilon)^b\bigr)\,(N+2)^{a(1/\varepsilon)^b}.$$
--
--   **Formalization Note** The paper's convention $d(j, \emptyset) = +\infty$ is encoded by requiring solutions to be nonempty; `distToSet` returns $0$ on the empty set and `optAt 0 = 0`, values that no statement uses. The paper's $\mathrm{opt}_0 = +\infty$ is encoded by making every instance with $k=1$ stable. The binary code reuses `encodeNat` and `encodeRat` of the published `OAI.MetricKMedian` definitions, and has the same layout as `OAI.MetricKMedian.encodeInstance`; that file's instance structure is not reused because it requires $d(x,y)=0 \iff x=y$ and $k \le |F|$. These conventions match the facility-location definitions already published for this paper (`BetterKMedian.LMPGreedy`).
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (2026), STOC 2027 submission, SHA-256 5c2605b2…f461, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/693.pdf, §1 (printed pp. 1–3, PDF 3–5), §2 Preliminaries (printed pp. 5–6, PDF 7–8)

import Mathlib
import Definitions.Def_MetricKMedian

set_option autoImplicit false

/-!
# Metric k-median with rational data, its binary code, randomized algorithms, stability

Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl,
*A Better-than-2 Approximation for k-Median* (2026), STOC 2027 submission,
SHA-256 5c2605b2…f461, §1 (printed pp. 1–3, PDF 3–5), §2 "Preliminaries" (printed pp. 5–6,
PDF 7–8). These are the definitions used by Theorems 1.1, 1.2 and 1.4.

Conventions (the same as `Definitions.Def_BetterKMedian_LMPGreedy_UFL` and
`Definitions.Def_BetterKMedian_LMPGreedy_Encoding` for facility location).
* The points are `Fin n`; the clients `D` and the facilities `F` are finite sets of points (they
  may overlap). Distances are rational and form a **pseudometric** on the points; distinct
  points at distance `0` are allowed. There is at least one facility, and `k ≥ 1`. The number
  `k` may exceed `|F|`.
* `d(j, S) = min_{i ∈ S} d(i, j)`, `cost(S) = Σ_{j ∈ D} d(j, S)`. The paper's convention
  `d(j, ∅) = +∞` is encoded by feasibility: a solution is a **nonempty** `S ⊆ F`.
* `opt_ℓ` (`optAt ℓ`) is the minimum of `cost` over the solutions with at most `ℓ` facilities
  (§2, p. 6: "a set `S ⊆ F` of at most `k` facilities"); `opt = opt_k`. For `ℓ = 0` there is no
  solution and `optAt 0 = 0`, a value that is never used.
* An instance is `β`-stable if `opt_{k−1} ≥ (1 + β) opt_k` (§2, p. 6). For `k = 1` the paper's
  `opt_0` is `+∞` when there is a client, so every instance with `k = 1` is stable.
* An algorithm reads the binary code `encode` of the instance, written as the published
  `OAI.MetricKMedian.encodeInstance` writes its instances (`encodeNat`/`encodeRat` are reused):
  `n`, `k`, the client and facility indicator bits, and the `n²` distances row-major. It outputs
  the indicator bit-list `code S` of its facility set.
* A randomized algorithm reads the code of the instance followed by a string of coin flips
  (`encodeWithCoins`). `coinProb m E` is the probability of `E` over `m` independent fair coins.
-/

namespace BetterKMedian.KMedian

/-- A metric k-median instance with rational data: points `Fin n`, a rational pseudometric
`dist`, clients, a nonempty set of facilities, and the number `k ≥ 1` of centers. -/
structure RatInstance where
  /-- number of points -/
  n : ℕ
  /-- rational distances -/
  dist : Fin n → Fin n → ℚ
  /-- the clients `D` -/
  clients : Finset (Fin n)
  /-- the facilities `F` -/
  facilities : Finset (Fin n)
  /-- the number `k` of centers -/
  k : ℕ
  dist_nonneg : ∀ x y, 0 ≤ dist x y
  dist_self : ∀ x, dist x x = 0
  dist_symm : ∀ x y, dist x y = dist y x
  dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z
  k_pos : 1 ≤ k
  facilities_nonempty : facilities.Nonempty

namespace RatInstance

variable (I : RatInstance)

/-- `d(j, S) = min_{i ∈ S} d(i, j)` for a nonempty set `S`; `0` for `S = ∅`, a value no
solution uses (solutions are nonempty). -/
noncomputable def distToSet (S : Finset (Fin I.n)) (j : Fin I.n) : ℝ :=
  if h : S.Nonempty then S.inf' h (fun i => (I.dist i j : ℝ)) else 0

/-- Connection cost `cost(S) = Σ_{j ∈ D} d(j, S)`. -/
noncomputable def cost (S : Finset (Fin I.n)) : ℝ :=
  ∑ j ∈ I.clients, I.distToSet S j

/-- A solution with at most `ℓ` centers: a nonempty `S ⊆ F` with `|S| ≤ ℓ`. -/
def IsSolution (ℓ : ℕ) (S : Finset (Fin I.n)) : Prop :=
  S ⊆ I.facilities ∧ S.Nonempty ∧ S.card ≤ ℓ

/-- The finite family of solutions with at most `ℓ` centers. -/
noncomputable def solutions (ℓ : ℕ) : Finset (Finset (Fin I.n)) := by
  classical
  exact I.facilities.powerset.filter (fun S => S.Nonempty ∧ S.card ≤ ℓ)

/-- `opt_ℓ`: the minimum of `cost` over the solutions with at most `ℓ` centers. For `ℓ = 0`
there is no solution and the value is `0` (never used). -/
noncomputable def optAt (ℓ : ℕ) : ℝ :=
  if h : (I.solutions ℓ).Nonempty then (I.solutions ℓ).inf' h I.cost else 0

/-- `opt = opt_k`, the optimum value of the k-median instance. -/
noncomputable def opt : ℝ := I.optAt I.k

/-- `β`-stability (§2, p. 6): `opt_{k−1} ≥ (1 + β) opt_k`. Every instance with `k = 1` is
stable (`opt_0 = +∞` in the paper). -/
def IsStable (β : ℝ) : Prop :=
  I.k = 1 ∨ (1 + β) * I.optAt I.k ≤ I.optAt (I.k - 1)

/-- The binary code of an instance: `encodeNat n`, `encodeNat k`, the client indicator bits, the
facility indicator bits, then the `n²` distances row-major, each as `encodeRat`. -/
def encode (I : RatInstance) : List Bool :=
  OAI.MetricKMedian.encodeNat I.n ++ OAI.MetricKMedian.encodeNat I.k ++
    List.ofFn (fun i : Fin I.n => decide (i ∈ I.clients)) ++
    List.ofFn (fun i : Fin I.n => decide (i ∈ I.facilities)) ++
    (List.ofFn (fun i : Fin I.n =>
      (List.ofFn (fun j : Fin I.n => OAI.MetricKMedian.encodeRat (I.dist i j))).flatten)).flatten

/-- The input of a randomized algorithm: the code of the instance followed by the coin flips. -/
def encodeWithCoins (x : RatInstance × List Bool) : List Bool :=
  x.1.encode ++ x.2

/-- The output code of a set of points: its indicator bit-list, of length `n`. -/
def code (S : Finset (Fin I.n)) : List Bool :=
  List.ofFn (fun i : Fin I.n => decide (i ∈ S))

/-- `output` is the code of a solution with at most `ℓ` centers. -/
def IsSolutionCode (ℓ : ℕ) (output : List Bool) : Prop :=
  ∃ S : Finset (Fin I.n), output = I.code S ∧ I.IsSolution ℓ S

/-- `output` is the code of a solution with at most `ℓ` centers and cost at most `ρ · opt_k`. -/
def IsApproxCode (ℓ : ℕ) (ρ : ℝ) (output : List Bool) : Prop :=
  ∃ S : Finset (Fin I.n), output = I.code S ∧ I.IsSolution ℓ S ∧ I.cost S ≤ ρ * I.opt

end RatInstance

/-- The probability of the event `E` over `m` independent fair coin flips: the fraction of the
`2^m` coin strings `r` of length `m` with `E r`. -/
noncomputable def coinProb (m : ℕ) (E : List Bool → Prop) : ℝ :=
  (Set.ncard {r : Fin m → Bool | E (List.ofFn r)} : ℝ) / 2 ^ m

/-- The time bound `exp(a · β⁻¹ · (1/ε)^b) · (N + 2)^(a · (1/ε)^b)` of Theorem 1.4, in the
input length `N`: of the form `exp(O(β⁻¹ poly(1/ε))) · N^{poly(1/ε)}` for absolute constants
`a`, `b`. -/
noncomputable def stableTimeBound (a b : ℕ) (β ε : ℝ) (N : ℕ) : ℝ :=
  Real.exp ((a : ℝ) * β⁻¹ * (1 / ε) ^ b) * ((N : ℝ) + 2) ^ ((a : ℝ) * (1 / ε) ^ b)

end BetterKMedian.KMedian


