-- Prove2me | Definitions.Def_PerishablePricing_Backlog_LNatConvex
-- name    : PerishablePricing_Backlog_LNatConvex
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T20:24:39.814413+00:00
-- url     : https://prove2.me/theorems/624350b7-c18c-4bdc-9c3b-4e765e7afc06
-- title:
--   Definition 1, p. 287 — L♮-convex sets, L♮-convex and L♮-concave functions on a set, and the ordered sets 𝒱ₙ,ₖ
-- statement:
--   Let $\iota$ be an index set and write vectors as $u \in \mathbb{R}^{\iota}$. The operations $u \wedge v$ and $u \vee v$ are the componentwise minimum and maximum, and $e$ is the vector whose components are all ones.
--
--   A set $\mathcal{V} \subseteq \mathbb{R}^{\iota}$ is **L♮-convex** if for all $u, v \in \mathcal{V}$ and all $\alpha \ge 0$,
--
--   $$(u + \alpha e) \wedge v \in \mathcal{V} \quad\text{and}\quad u \vee (v - \alpha e) \in \mathcal{V}.$$
--
--   A real function $f$ is **L♮-convex on** $\mathcal{V}$ if $\mathcal{V}$ is an L♮-convex set and for all $u, v \in \mathcal{V}$ and all $\alpha \ge 0$,
--
--   $$f(u) + f(v) \ge f\big((u + \alpha e) \wedge v\big) + f\big(u \vee (v - \alpha e)\big).$$
--
--   A function $f$ is **L♮-concave on** $\mathcal{V}$ if $-f$ is L♮-convex on $\mathcal{V}$.
--
--   For $n, k \in \mathbb{N}$ the ordered sets are
--
--   $$\mathcal{V}_{n,k} = \{(s_1, \dots, s_n) \in \mathbb{R}^n : s_1 \le \dots \le s_k\}, \qquad \mathcal{V}^+_{n,k} = \{(s_1, \dots, s_n) \in \mathbb{R}^n : 0 \le s_1 \le \dots \le s_k\}.$$
--
--   These notions are the language of the whole mission: the state space of the backlogging model is $\mathcal{V}_{l-1,l-1}$, and Theorem 1 asserts L♮-concavity of the value functions on ordered sets.
--
--   **Formalization Note** The paper treats $\mathbb{F} \in \{\mathbb{R}, \mathbb{Z}\}$ at once; this mission formalizes the real case $\mathbb{F} = \mathbb{R}$ only. Functions are real-valued on an explicit domain, which is the paper's convention "f is L♮-convex on a set 𝒱" (the extension of $f$ by $+\infty$ off $\mathcal{V}$ is L♮-convex); values off the domain are never used. Vectors are `ι → ℝ`, the lattice operations are Mathlib's pointwise `⊓`/`⊔`, and $e$ is the constant function `1`. The ordered sets are indexed from $0$: `V n k` requires `s i ≤ s j` whenever `i ≤ j < k`, and `Vplus n k` additionally requires the first $k$ coordinates to be nonnegative, which together with the ordering is $0 \le s_1$ when $k \ge 1$.
-- source:
--   Chen, Pang, Pan, Coordinating Inventory Control and Pricing Strategies for Perishable Products, Oper. Res. 62(2), 2014, Definition 1 and the following paragraph, and the sets 𝒱_{n,k}, 𝒱⁺_{n,k}, p. 287 (PDF p. 5)

import Mathlib

namespace PerishablePricing.Backlog

/-!
# L♮-convex sets and functions on a domain (Chen, Pang, Pan 2014, Definition 1, p. 287)

Vectors are real functions `ι → ℝ` on an index type `ι` (the paper's `𝔽ⁿ` with `𝔽 = ℝ`).
The lattice operations `⊓`, `⊔` are Mathlib's pointwise minimum and maximum (the paper's `∧`, `∨`),
and the all-ones vector `e` is `(1 : ι → ℝ)`, so `α • 1` is `αe`.

A function is real-valued on an explicit domain `S`; this is the paper's convention "f is
L♮-convex on a set 𝒱" (the extension by `+∞` off `𝒱` is L♮-convex), which avoids extended reals.
-/

/-- An **L♮-convex set** (p. 287): for all `u, v ∈ S` and `α ≥ 0`,
`(u + αe) ∧ v ∈ S` and `u ∨ (v − αe) ∈ S`. -/
def LNatConvexSet {ι : Type*} (S : Set (ι → ℝ)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ∀ α : ℝ, 0 ≤ α →
    (u + α • (1 : ι → ℝ)) ⊓ v ∈ S ∧ u ⊔ (v - α • (1 : ι → ℝ)) ∈ S

/-- `f` is **L♮-convex on the set `S`** (Definition 1 and the paragraph after it, p. 287): `S` is
an L♮-convex set and for all `u, v ∈ S` and `α ≥ 0`,
`f(u) + f(v) ≥ f((u + αe) ∧ v) + f(u ∨ (v − αe))`. Values of `f` off `S` are never used. -/
def LNatConvexOn {ι : Type*} (S : Set (ι → ℝ)) (f : (ι → ℝ) → ℝ) : Prop :=
  LNatConvexSet S ∧
    ∀ u ∈ S, ∀ v ∈ S, ∀ α : ℝ, 0 ≤ α →
      f ((u + α • (1 : ι → ℝ)) ⊓ v) + f (u ⊔ (v - α • (1 : ι → ℝ))) ≤ f u + f v

/-- `f` is **L♮-concave on `S`** if `−f` is L♮-convex on `S` (p. 287). -/
def LNatConcaveOn {ι : Type*} (S : Set (ι → ℝ)) (f : (ι → ℝ) → ℝ) : Prop :=
  LNatConvexOn S (-f)

/-- The ordered set `𝒱_{n,k} = {(s_1, …, s_n) : s_1 ≤ ⋯ ≤ s_k}` (p. 287), 0-based:
`s i ≤ s j` whenever `i ≤ j` and `j < k`. -/
def V (n k : ℕ) : Set (Fin n → ℝ) :=
  {s | ∀ i j : Fin n, i ≤ j → (j : ℕ) < k → s i ≤ s j}

/-- The ordered set `𝒱⁺_{n,k} = {(s_1, …, s_n) : 0 ≤ s_1 ≤ ⋯ ≤ s_k}` (p. 287), 0-based: an
element of `𝒱_{n,k}` whose first `k` coordinates are nonnegative. -/
def Vplus (n k : ℕ) : Set (Fin n → ℝ) :=
  {s | s ∈ V n k ∧ ∀ i : Fin n, (i : ℕ) < k → 0 ≤ s i}

end PerishablePricing.Backlog


