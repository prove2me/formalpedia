-- Prove2me | Definitions.Def_DeepQOperator_Family
-- name    : DeepQOperator_Family
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:00:02.455085+00:00
-- url     : https://prove2.me/theorems/a6450777-63c5-4fdd-96b3-f0d1c1d6591e
-- title:
--   The three-row Bellman family (6) on the full convex box $P_{cb}$
-- statement:
--   Let $m\ge2$, $r=\lceil\log_2 m\rceil$ and $n=2^r$. For $i\in\{0,\dots,m-1\}$ and $v\in\{0,1\}^r$ the **Walsh word** is $c_i(v)=(-1)^{i\cdot v}$, where $i\cdot v$ is the dot product modulo two of the binary expansion of $i$ with $v$. The parameter is $\theta=(a,z)$ with an address $a\in\mathbb R^n$ and payloads $z\in\mathbb R^m$, and the input domain is the **full convex box**
--   $$P_{cb}=[-1,1]^n\times[0,1]^m.$$
--   The **Walsh scores** are $b_i(a)=c_i^{\mathsf T}a/(2n)$, and the three rows of the family (6) are
--   $$A=\max\Big\{\tfrac14,\ \max_i\big(b_i(a)+\tfrac{z_i}{16}\big)\Big\},\qquad B=\max\Big\{\tfrac14,\ \max_i b_i(a)\Big\},\qquad C=\max\big(\{a_v\}_v\cup\{z_i\}_i\big).$$
--   For $J\subseteq\{0,\dots,m-1\}$, $A_J$ and $B_J$ denote the same maxima with $i$ restricted to $J$ and the floor $1/4$ kept (so $A_\emptyset=B_\emptyset=1/4$).
--
--   The two actions have the Bellman scores (1), $t_a=r_a+\gamma\sum_i w_{ai}M_i$ with row values $M=(A,B,C)$: action $+$ has response $(1,0,0)$ and reward $-\gamma/32$, action $-$ has response $(0,1,0)$ and reward $0$. The **decision loss** (3) is $\ell(a,\theta)=\max_{b\in\{+,-\}}t_b(\theta)-t_a(\theta)$, and the **contrast** is $g=t_+-t_-=\gamma(A-B-1/32)$.
--
--   An **affine scalar query** is a map $\theta\mapsto\alpha^{\mathsf T}\theta+\alpha_0$. The **raw dictionary** is the set of displayed affine features of (6): the constant $1/4$, $b_i(a)+z_i/16$, $b_i(a)$, and every coordinate $a_v$ and $z_i$.
--
--   This is the hard family on which Theorem 2 separates fixed from adaptive finite-reply acquisition.
--
--   **Formalization Note** $r$ is `Nat.clog 2 m`; an address $v\in\{0,1\}^r$ is encoded as `v : Fin (2^r)` through its binary expansion. The parameter is one function on `Fin n ⊕ Fin m`. Restricted maxima are folds of `max` starting from $1/4$. Decision `true` is $+$. The constant site is listed once although the paper lists it in row A and in row B.
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), §1 eq. (1) p.1, §2 eq. (3) p.3, §3 eq. (6) p.4, Appendix D.1 p.20 (PDF pp.4, 6, 7, 23)

import Mathlib

open Finset

namespace DeepQOperator

/-!
# The three-row Bellman family (6) on the full convex box

Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions*,
STOC 2027 submission (manuscript sha256 9f8f3285…), §1 eq. (1) p.1, §2 eq. (3) p.3, §3 eq. (6)
p.4 (PDF pp.4, 6, 7), Appendix D.1 p.20 (PDF p.23).

For `m ≥ 2` put `r = ⌈log₂ m⌉`, `n = 2^r`. The parameter is `θ = (a, z)` with an address
`a ∈ [-1,1]^n` and payloads `z ∈ [0,1]^m`. The Walsh word `c_i(v) = (-1)^{i·v}` uses the dot
product modulo two of the binary expansions of `i` and `v`. The Walsh scores are
`b_i(a) = c_iᵀa/(2n)`, and the three rows of (6) are
`A = max{1/4, max_i (b_i + z_i/16)}`, `B = max{1/4, max_i b_i}`, `C = max({a_v} ∪ {z_i})`.
The two actions have responses `(1,0,0)`, `(0,1,0)` and rewards `-γ/32`, `0` in the Bellman
score (1), and the loss is (3).

**Formalization Note.**
* `r = Nat.clog 2 m`, which is `⌈log₂ m⌉` for `m ≥ 1`. An address `v ∈ {0,1}^r` is encoded as
  `v : Fin (2^r)` through its binary expansion; `i·v` is the number of bit positions `k < r` at
  which both `i` and `v` have a one, taken modulo two through the power of `-1`.
* The parameter is one function `θ : Fin n ⊕ Fin m → ℝ`; `Sum.inl v` is the address coordinate
  `a_v` and `Sum.inr i` the payload `z_i`. The domain is the set `Pcb m`.
* `rowAOn m J θ`, `rowBOn m J θ` are the row maxima restricted to the index set `J`, with the
  floor `1/4` kept; over the empty set the maximum is the floor ("maxima over the empty set are
  omitted", p.25). `rowA = rowAOn univ`, `rowB = rowBOn univ`.
* The decision `true` is the action `+` (response `(1,0,0)`, reward `-γ/32`) and `false` the
  action `-` (response `(0,1,0)`, reward `0`). `loss` is (3) with `D = {+, -}`.
* An affine scalar query is a pair `(α, α₀)` with value `αᵀθ + α₀`. The raw dictionary is the set
  of its sites: the constant `1/4` (shared by rows A and B, which list it once each), `b_i + z_i/16`,
  `b_i` and every coordinate `a_v`, `z_i`.
-/

/-- `r = ⌈log₂ m⌉`. -/
abbrev rr (m : ℕ) : ℕ := Nat.clog 2 m

/-- `n = 2^r`, the number of address coordinates. -/
abbrev nn (m : ℕ) : ℕ := 2 ^ rr m

/-- Address positions `v ∈ {0,1}^r`, encoded by their binary expansion. -/
abbrev Addr (m : ℕ) : Type := Fin (nn m)

/-- Coordinates of the parameter `θ = (a, z)`: addresses then payloads. -/
abbrev Coord (m : ℕ) : Type := Addr m ⊕ Fin m

/-- The Walsh word `c_i(v) = (-1)^{i·v}` on `{0,1}^r`. -/
noncomputable def walsh (r i : ℕ) (v : Fin (2 ^ r)) : ℝ :=
  (-1 : ℝ) ^ ((Finset.range r).filter (fun k => (i.testBit k && (v : ℕ).testBit k) = true)).card

/-- The full convex box `P_cb = [-1,1]^n × [0,1]^m`. -/
def Pcb (m : ℕ) : Set (Coord m → ℝ) :=
  {θ | (∀ v : Addr m, θ (Sum.inl v) ∈ Set.Icc (-1 : ℝ) 1) ∧ ∀ i : Fin m, θ (Sum.inr i) ∈ Set.Icc (0 : ℝ) 1}

/-- The Walsh score `b_i(a) = c_iᵀa/(2n)`. -/
noncomputable def bScore (m : ℕ) (i : Fin m) (θ : Coord m → ℝ) : ℝ :=
  (∑ v : Addr m, walsh (rr m) i v * θ (Sum.inl v)) / (2 * (nn m : ℝ))

/-- Row A restricted to `J`, floor kept: `max{1/4, max_{i∈J} (b_i + z_i/16)}`. -/
noncomputable def rowAOn (m : ℕ) (J : Finset (Fin m)) (θ : Coord m → ℝ) : ℝ :=
  J.fold max (1 / 4 : ℝ) (fun i => bScore m i θ + θ (Sum.inr i) / 16)

/-- Row B restricted to `J`, floor kept: `max{1/4, max_{i∈J} b_i}`. -/
noncomputable def rowBOn (m : ℕ) (J : Finset (Fin m)) (θ : Coord m → ℝ) : ℝ :=
  J.fold max (1 / 4 : ℝ) (fun i => bScore m i θ)

/-- Row A of (6). -/
noncomputable def rowA (m : ℕ) (θ : Coord m → ℝ) : ℝ := rowAOn m Finset.univ θ

/-- Row B of (6). -/
noncomputable def rowB (m : ℕ) (θ : Coord m → ℝ) : ℝ := rowBOn m Finset.univ θ

/-- Row C of (6): `max({a_v}_v ∪ {z_i}_i)`. -/
noncomputable def rowC (m : ℕ) (θ : Coord m → ℝ) : ℝ :=
  Finset.univ.sup' ⟨Sum.inl ⟨0, Nat.two_pow_pos _⟩, Finset.mem_univ _⟩ θ

/-- The three row values `(A, B, C)`. -/
noncomputable def rows (m : ℕ) (θ : Coord m → ℝ) : Fin 3 → ℝ := ![rowA m θ, rowB m θ, rowC m θ]

/-- The Bellman score (1) of an action with reward `rew` and response weights `w` on the row
values `M`: `rew + γ Σ_i w_i M_i`. -/
def bellmanScore (γ rew : ℝ) (w M : Fin 3 → ℝ) : ℝ := rew + γ * ∑ i, w i * M i

/-- `t₊`: response `(1,0,0)`, reward `-γ/32`. -/
noncomputable def tPlus (m : ℕ) (γ : ℝ) (θ : Coord m → ℝ) : ℝ :=
  bellmanScore γ (-γ / 32) ![1, 0, 0] (rows m θ)

/-- `t₋`: response `(0,1,0)`, reward `0`. -/
noncomputable def tMinus (m : ℕ) (γ : ℝ) (θ : Coord m → ℝ) : ℝ :=
  bellmanScore γ 0 ![0, 1, 0] (rows m θ)

/-- The score of decision `a` (`true` is `+`, `false` is `-`). -/
noncomputable def actScore (m : ℕ) (γ : ℝ) (a : Bool) (θ : Coord m → ℝ) : ℝ :=
  if a then tPlus m γ θ else tMinus m γ θ

/-- The decision loss (3): `ℓ(a, θ) = max_{b ∈ D} t_b(θ) - t_a(θ)`. -/
noncomputable def loss (m : ℕ) (γ : ℝ) (a : Bool) (θ : Coord m → ℝ) : ℝ :=
  max (tPlus m γ θ) (tMinus m γ θ) - actScore m γ a θ

/-- The contrast `g = t₊ - t₋`. -/
noncomputable def contrast (m : ℕ) (γ : ℝ) (θ : Coord m → ℝ) : ℝ := tPlus m γ θ - tMinus m γ θ

/-- An affine scalar query `θ ↦ αᵀθ + α₀`, stored as `(α, α₀)`. -/
abbrev AffQuery (ι : Type) : Type := (ι → ℝ) × ℝ

/-- The value `αᵀθ + α₀` of an affine query. -/
def affEval {ι : Type} [Fintype ι] (q : AffQuery ι) (θ : ι → ℝ) : ℝ := ∑ c, q.1 c * θ c + q.2

/-- The constant raw site `1/4` (the floor of rows A and B). -/
noncomputable def constSite (m : ℕ) : AffQuery (Coord m) := (0, 1 / 4)

/-- The raw row-A site `b_i(a) + z_i/16`. -/
noncomputable def siteA (m : ℕ) (i : Fin m) : AffQuery (Coord m) :=
  (Sum.elim (fun v => walsh (rr m) i v / (2 * (nn m : ℝ))) (fun j => if j = i then 1 / 16 else 0), 0)

/-- The raw row-B site `b_i(a)`. -/
noncomputable def siteB (m : ℕ) (i : Fin m) : AffQuery (Coord m) :=
  (Sum.elim (fun v => walsh (rr m) i v / (2 * (nn m : ℝ))) (fun _ => 0), 0)

/-- The raw row-C coordinate site `a_v` or `z_i`. -/
noncomputable def siteC (m : ℕ) (c : Coord m) : AffQuery (Coord m) := (fun c' => if c' = c then 1 else 0, 0)

/-- The raw dictionary of (6): the displayed affine features of the three rows, including the
constant. -/
noncomputable def rawDictionary (m : ℕ) : Set (AffQuery (Coord m)) :=
  {constSite m} ∪ Set.range (siteA m) ∪ Set.range (siteB m) ∪ Set.range (siteC m)

end DeepQOperator


