-- Prove2me | Definitions.Def_SingleSampleCombPI_XOS_Model
-- name    : SingleSampleCombPI_XOS_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T09:08:01.597073+00:00
-- url     : https://prove2.me/theorems/00acd1c2-3b7f-4fc5-8601-033460778a42
-- title:
--   §§2.1–2.4 — buyers with supporting prices, XOS, hindsight optimum, free-disposal value, single-item problem
-- statement:
--   This file fixes the combinatorial allocation model. There are $n$ buyers and $m$ items with one unit of each. The per-item allocation set is $A=\{0,1\}$ (indivisible items) or $A=[0,1]$ (divisible items); buyer $i$ receives $x_i\in A^m$, and an allocation profile is **feasible** when every $x_i\in A^m$ and $\sum_i x_{i,j}\le1$ for every item $j$.
--
--   1. **Buyer types.** A buyer type consists of a valuation $v$, a supporting-price oracle $q$ and a demand oracle $d$. The valuation is **valid** when $v(0)=0$, $v\ge0$ on $A^m$ and $v$ is monotone on $A^m$. The oracle $q$ gives **supporting prices** (Definition 1) when for every $x\in A^m$, $q(x)\in\mathbb R^m_{\ge0}$, $\langle q(x),x\rangle=v(x)$ and $\langle q(x),x'\rangle\le v(x')$ for every $x'\in A^m$ with $x'\le x$. The demand oracle is valid when, at every nonnegative price vector $p$, the bundle $d(p)$ maximizes $v(S)-\sum_{j\in S}p_j$ over all bundles $S$. The zero buyer has $v=0$, $q=0$ and $d=\emptyset$.
--   2. **XOS** (Definition 2). On bundles, $v(S)=\max_k\sum_{j\in S}a_{j,k}$ for a finite nonempty family of nonnegative additive clauses (the published XOS expression); the paper's empty family, value $0$, is the single zero clause. An XOS buyer has an XOS valuation and valid supporting-price and demand oracles.
--   3. **Hindsight optimum** (§2.1). $\mathrm{Opt}(v)=\sup\{\sum_i v_i(x_i): x\text{ feasible}\}$.
--   4. **Free-disposal value** (Definition 7). For provisional allocations $x_1,\dots,x_n\in A^m$,
--   $$\mathrm{FD}(x_1,\dots,x_n)=\sup\Big\{\sum_i\langle q_i(x_i),y_i\rangle:\ y_i\in A^m,\ y_i\le x_i,\ \sum_i y_i\le\mathbf 1\Big\},$$
--   with the supporting prices frozen at the $x_i$.
--   5. **Single-item problem** (§2.4). A single-item buyer is a pair $(q_i,x_i)$ with $q_i\ge0$, $x_i\in A$ ($x_i=0$ means an absent buyer for indivisible items). An allocation $y$ is feasible when $y_i\in A$, $y_i\le x_i$ and $\sum_iy_i\le1$; $\mathrm{Opt}(\{(q_i,x_i)\})$ is the supremum of $\sum_iq_iy_i$ over feasible $y$, and $\mathrm{FracKnap}$ is the optimum fractional knapsack of size $1$ with densities $q_i$ and weights $x_i$. The maximum of an empty family is $0$.
--   6. **Expectations and costs.** Uniform averages over finite sets, independent Bernoulli$(q)$ coins, and nonnegative lower integrals over arbitrary probability spaces of internal seeds, all of nonnegative quantities in $[0,\infty]$; a cost record counts primitive operations, demand queries and supporting-price queries.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** Allocations are vectors `Fin m → ℝ` and bundles are indicator vectors; values of $v$ off $A^m$ are never used. The suprema are attained (maxima of finite sets for indivisible items) except for the divisible hindsight optimum, where the supremum is the corrected benchmark.
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), SHA-256 d6ed330221fdb64a0d8f70c7d0abbd3346ee1cb8f9e101a745f7e1e57d35230e, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/30.pdf, §§2.1–2.4, PDF pp. 7–12 (printed pp. 5–10), Definitions 1, 2, 7

import Mathlib
import Definitions.Def_ComplementFreeCA_XOSGreedy_Model

open scoped ENNReal

namespace SingleSampleCombPI.XOS

/-! # Combinatorial allocation model (Chawla–Dang, STOC 2027 submission #30, §§2.1–2.4)

Buyers are `Fin n`, items are `Fin m`, each item has one unit of supply. -/

/-- The two resource regimes of §2.2: indivisible items (`A = {0,1}`) and divisible
items (`A = [0,1]`). -/
inductive Regime
  | indivisible
  | divisible
  deriving DecidableEq

/-- The per-item allocation set `A ⊆ [0,1]`. -/
def Regime.dom : Regime → Set ℝ
  | .indivisible => {0, 1}
  | .divisible => Set.Icc 0 1

/-- Allocation (and price) vectors in `ℝ^m`. -/
abbrev Vec (m : ℕ) := Fin m → ℝ

/-- Buyer-feasibility (the demand constraint): `x ∈ A^m`. -/
def InDom (A : Regime) {m : ℕ} (x : Vec m) : Prop := ∀ j, x j ∈ A.dom

/-- Vectors of `A^m`. -/
abbrev AVec (A : Regime) (m : ℕ) := {x : Vec m // InDom A x}

/-- Inner product `⟨p, x⟩ = ∑_j p_j x_j`. -/
def dot {m : ℕ} (p x : Vec m) : ℝ := ∑ j, p j * x j

/-- The indicator vector `1_S ∈ {0,1}^m` of a bundle `S ⊆ [m]`. -/
def ind {m : ℕ} (S : Finset (Fin m)) : Vec m := fun j => if j ∈ S then 1 else 0

/-- Indicator vectors are indivisible allocations (a structural lemma). -/
theorem ind_inDom {m : ℕ} (S : Finset (Fin m)) : InDom .indivisible (ind S) := by
  intro j
  by_cases h : j ∈ S <;> simp [ind, h, Regime.dom]

/-- A buyer type as seen by the platform: the valuation `v : A^m → ℝ≥0` (values off
`A^m` are never used), the supporting-price oracle `q` (`x ↦ q_v(x)`, Definition 1) and a
demand oracle `d` (`p ↦` a bundle maximizing `v(S) - p(S)`).  Algorithms only call `q`
and `d`; welfare and the benchmark use `v`. -/
structure Buyer (m : ℕ) where
  /-- the valuation function -/
  v : Vec m → ℝ
  /-- the supporting-price oracle -/
  q : Vec m → Vec m
  /-- the demand oracle -/
  d : Vec m → Finset (Fin m)

/-- §2.2: `v` is finite, nonnegative, normalized (`v(0) = 0`) and monotone on `A^m`. -/
def IsValuation (A : Regime) {m : ℕ} (v : Vec m → ℝ) : Prop :=
  v 0 = 0 ∧ (∀ x, InDom A x → 0 ≤ v x) ∧
    ∀ x y, InDom A x → InDom A y → x ≤ y → v x ≤ v y

/-- Definition 1 (one-sided supporting prices): for every `x ∈ A^m`, `q(x) ∈ ℝ^m_{≥0}`,
`⟨q(x), x⟩ = v(x)`, and `⟨q(x), x'⟩ ≤ v(x')` for every `x' ∈ A^m` with `x' ≤ x`. -/
def IsSupporting (A : Regime) {m : ℕ} (v : Vec m → ℝ) (q : Vec m → Vec m) : Prop :=
  ∀ x, InDom A x → (∀ j, 0 ≤ q x j) ∧ dot (q x) x = v x ∧
    ∀ x', InDom A x' → x' ≤ x → dot (q x) x' ≤ v x'

/-- A buyer type whose valuation satisfies §2.2 and whose supporting-price oracle is valid. -/
def Buyer.Valid (A : Regime) {m : ℕ} (b : Buyer m) : Prop :=
  IsValuation A b.v ∧ IsSupporting A b.v b.q

/-- The demand oracle returns a genuine maximizer of `v(S) - p(S)` at every nonnegative
price vector (the only prices any algorithm here queries). -/
def Buyer.DemandValid {m : ℕ} (b : Buyer m) : Prop :=
  ∀ p : Vec m, 0 ≤ p → ∀ T : Finset (Fin m),
    b.v (ind T) - ∑ j ∈ T, p j ≤ b.v (ind (b.d p)) - ∑ j ∈ b.d p, p j

/-- The zero valuation, with zero supporting prices and the empty demand answer. -/
def Buyer.zero (m : ℕ) : Buyer m := ⟨fun _ => 0, fun _ => 0, fun _ => ∅⟩

/-- Definition 2 (XOS): on bundles, `v(S) = max_k ∑_{j∈S} a_{j,k}` for finitely many
nonnegative additive clauses.  The published `XOSExpr` requires a nonempty clause family;
the paper's empty-family value `0` is the single zero clause. -/
def IsXOS {m : ℕ} (v : Vec m → ℝ) : Prop :=
  ∃ E : ComplementFreeCA.XOSGreedy.XOSExpr m, ∀ S : Finset (Fin m), v (ind S) = E.val S

/-- An admissible XOS buyer for the indivisible regime: XOS valuation, valid supporting-price
oracle (Definition 1) and valid demand oracle. -/
def XOSBuyer {m : ℕ} (b : Buyer m) : Prop :=
  IsXOS b.v ∧ b.Valid .indivisible ∧ b.DemandValid

/-- Supply- and buyer-feasibility of an allocation profile: `x_i ∈ A^m`, `∑_i x_i ≤ 1`. -/
def Feasible (A : Regime) {n m : ℕ} (x : Fin n → Vec m) : Prop :=
  (∀ i, InDom A (x i)) ∧ ∀ j, ∑ i, x i j ≤ 1

/-- The hindsight optimum `Opt(v)` (§2.1), taken as the supremum of the welfare of all
feasible allocations.  For indivisible items the set is finite and this is its maximum; for
divisible items the supremum need not be attained (see the source-correction notes). -/
noncomputable def Opt (A : Regime) {n m : ℕ} (b : Fin n → Buyer m) : ℝ :=
  sSup {w | ∃ x : Fin n → Vec m, Feasible A x ∧ w = ∑ i, (b i).v (x i)}

/-- Definition 7 (free-disposal value): the best trimming `y_i ≤ x_i`, `y_i ∈ A^m`,
`∑ y_i ≤ 1`, evaluated at the supporting prices `q_i(x_i)` frozen at the provisional
allocations. -/
noncomputable def FD (A : Regime) {n m : ℕ} (b : Fin n → Buyer m) (x : Fin n → Vec m) : ℝ :=
  sSup {w | ∃ y : Fin n → Vec m, Feasible A y ∧ y ≤ x ∧ w = ∑ i, dot ((b i).q (x i)) (y i)}

/-! ## Single-item problem (§2.4) -/

/-- A single-item buyer `(q_i, x_i)`: unit reward and demand. -/
abbrev Item := ℝ × ℝ

/-- `q_i ≥ 0` and `x_i ∈ A`; in the indivisible regime `x_i = 0` means the buyer is absent. -/
def ItemValid (A : Regime) (it : Item) : Prop := 0 ≤ it.1 ∧ it.2 ∈ A.dom

/-- Feasibility of a single-item allocation: `y_i ∈ A`, `y_i ≤ x_i`, `∑_i y_i ≤ 1`. -/
def ItemFeasible (A : Regime) {n : ℕ} (it : Fin n → Item) (y : Fin n → ℝ) : Prop :=
  (∀ i, y i ∈ A.dom ∧ y i ≤ (it i).2) ∧ ∑ i, y i ≤ 1

/-- The single-item hindsight optimum `Opt({(q_i, x_i)})`. -/
noncomputable def itemOpt (A : Regime) {n : ℕ} (it : Fin n → Item) : ℝ :=
  sSup {w | ∃ y : Fin n → ℝ, ItemFeasible A it y ∧ w = ∑ i, (it i).1 * y i}

/-- The optimum fractional knapsack of size 1: item `i` has density `q_i` and weight `x_i`,
and a fraction `θ_i ∈ [0,1]` of it is packed. -/
noncomputable def fracKnap {n : ℕ} (it : Fin n → Item) : ℝ :=
  sSup {w | ∃ θ : Fin n → ℝ, (∀ i, 0 ≤ θ i ∧ θ i ≤ 1) ∧ ∑ i, θ i * (it i).2 ≤ 1 ∧
    w = ∑ i, θ i * ((it i).1 * (it i).2)}

/-- Maximum of a finite family, with the paper's convention (footnote 4) that the maximum
of an empty family is `0`. -/
noncomputable def maxOrZero {ι : Type*} (s : Finset ι) (f : ι → ℝ) : ℝ :=
  if h : s.Nonempty then s.sup' h f else 0

/-- The per-item instance `{(q_{i,j}(x_i), x_{i,j})}_{i∈[n]}` of item `j`. -/
def itemsAt {n m : ℕ} (b : Fin n → Buyer m) (x : Fin n → Vec m) (j : Fin m) : Fin n → Item :=
  fun i => ((b i).q (x i) j, x i j)

/-! ## Expectations over the explicit randomness -/

/-- Uniform average over a finite set (uniform permutations, fair swap coins). -/
noncomputable def avg {X : Type*} [Fintype X] (f : X → ℝ≥0∞) : ℝ≥0∞ :=
  (Fintype.card X : ℝ≥0∞)⁻¹ * ∑ x, f x

/-- Real-valued uniform average over a finite set. -/
noncomputable def avgR {X : Type*} [Fintype X] (f : X → ℝ) : ℝ :=
  (Fintype.card X : ℝ)⁻¹ * ∑ x, f x

/-- Bernoulli(`q`) weight of an outcome. -/
noncomputable def bernW (q : ℝ) (h : Bool) : ℝ := if h then q else 1 - q

/-- Expectation over independent Bernoulli(`q`) coins `H_1, …, H_n`. -/
noncomputable def bernExp {n : ℕ} (q : ℝ) (f : (Fin n → Bool) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ H, ENNReal.ofReal (∏ i, bernW q (H i)) * f H

/-- Real-valued expectation over independent Bernoulli(`q`) coins. -/
noncomputable def bernExpR {n : ℕ} (q : ℝ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  ∑ H, (∏ i, bernW q (H i)) * f H

/-- An arbitrary probability space of internal random seeds. No countability, atomicity,
or finite-support restriction is imposed. -/
structure RandomSource (Ω : Type) where
  /-- measurable events of the seed space -/
  space : MeasurableSpace Ω
  /-- probability law of the seed -/
  law : @MeasureTheory.Measure Ω space
  /-- total probability is one -/
  isProbability : @MeasureTheory.IsProbabilityMeasure Ω space law

/-- Discrete random choices as a special case of an arbitrary random source. The full
sigma algebra makes every function of a discrete seed measurable. -/
noncomputable def RandomSource.ofPMF {Ω : Type} (p : PMF Ω) : RandomSource Ω := by
  letI : MeasurableSpace Ω := ⊤
  exact ⟨⊤, p.toMeasure, inferInstance⟩

/-- Two independent random sources, used for the replay order and the FD algorithm seed. -/
noncomputable def RandomSource.prod {Ω Ξ : Type} (p : RandomSource Ω) (q : RandomSource Ξ) :
    RandomSource (Ω × Ξ) := by
  letI := p.space
  letI := q.space
  letI := p.isProbability
  letI := q.isProbability
  exact ⟨inferInstance, p.law.prod q.law, inferInstance⟩

/-- Nonnegative expectation over arbitrary internal randomness. On measurable payoffs this
is the ordinary expectation. On arbitrary maps it is the lower integral, so the definition
requires no extra regularity assumption on source valuations or oracles. Finite external
random choices are placed inside this integral in the performance predicates below. -/
noncomputable def pexp {Ω : Type} (p : RandomSource Ω) (f : Ω → ℝ≥0∞) : ℝ≥0∞ := by
  letI := p.space
  exact ∫⁻ ω, f ω ∂p.law

/-- Independent copies of an internal random source, interpreted by iterated nonnegative
expectations. For measurable payoffs this is expectation under the product probability law. -/
noncomputable def pexpPi {Ω : Type} (p : RandomSource Ω) :
    {m : ℕ} → ((Fin m → Ω) → ℝ≥0∞) → ℝ≥0∞
  | 0, f => f Fin.elim0
  | _m + 1, f => pexp p (fun ω => pexpPi p (fun rest => f (Fin.cons ω rest)))

/-! ## Cost accounting (unit-cost oracle model of §3.4) -/

/-- A cost record `(primitive operations, demand queries, supporting-price queries)`;
primitive operations are unit-cost real arithmetic, comparisons and random draws. -/
abbrev Cost := ℕ × ℕ × ℕ

/-- All three counters are at most `K (N+1)^K`. -/
def Cost.PolyBounded (c : Cost) (K N : ℕ) : Prop :=
  c.1 ≤ K * (N + 1) ^ K ∧ c.2.1 ≤ K * (N + 1) ^ K ∧ c.2.2 ≤ K * (N + 1) ^ K

end SingleSampleCombPI.XOS


