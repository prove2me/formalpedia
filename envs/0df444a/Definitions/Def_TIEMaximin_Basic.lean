-- Prove2me | Definitions.Def_TIEMaximin_Basic
-- name    : TIEMaximin_Basic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:38:12.256207+00:00
-- url     : https://prove2.me/theorems/7da3c1f6-6c62-46df-880a-fd87a5406a40
-- title:
--   Allocations, integral suballocations, additive values, lotteries and their marginals
-- statement:
--   There are $m$ goods and $n$ agents. An **allocation** $A$ is a partition of the goods into $n$ possibly empty bundles $A_1,\dots,A_n$, and an **integral suballocation** is a tuple of pairwise disjoint bundles that need not cover all goods. A valuation profile assigns a nonnegative value $v_i(g)$ to every agent $i$ and good $g$, and bundles are valued additively, $v_i(S)=\sum_{g\in S}v_i(g)$.
--
--   A **lottery** is a probability distribution over allocations (or integral suballocations). It **implements** the fractional allocation $x$ if $\Pr_{A\sim L}[g\in A_i]=x_{ig}$ for every agent $i$ and good $g$.
--
--   These objects are the common language of every statement of the mission.
--
--   **Formalization Note** Allocations are maps `Fin m → Fin n`, suballocations are maps `Fin m → Option (Fin n)`, and lotteries are `PMF`s on these finite types, so they are automatically finite and expectations are finite sums. Nonnegativity is the separate predicate `Nonneg`.
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), §2, pp.6–7; Definition 2.1, p.7

import Mathlib

namespace TIEMaximin

open Finset

/-- **Allocations** (§2, p.6). An allocation of the goods `Fin m` to the agents `Fin n` is a map
sending every good to the agent who receives it; `A g = i` means `g ∈ A_i`.

Ma, Tao, Wang, *Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee*,
arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), §2, p.6: "An allocation
A ≜ (A_1, . . . , A_n) is a partition of M into n (possibly empty) bundles".

**Formalization Note.** Agents and goods are `Fin n` and `Fin m`, 0-based. A map `Fin m → Fin n`
is exactly a partition of the goods into `n` labelled, possibly empty bundles. -/
abbrev Alloc (n m : ℕ) : Type := Fin m → Fin n

/-- **Integral suballocations** (§2, p.6): every good goes to at most one agent (`none` = the good
is unassigned). This is the paper's "tuple of pairwise disjoint bundles (A_i) with ⋃ A_i ⊆ M"
(arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…, §2, p.6). -/
abbrev SubAlloc (n m : ℕ) : Type := Fin m → Option (Fin n)

/-- **Nonnegative valuation profile** (§2, p.6): `v i g = v_i(g) ≥ 0` for every agent `i` and good
`g`. The additive valuation of a bundle is the sum of its goods' values (`valOf`).

arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), §2, p.6: "nonnegative additive
valuation v_i : 2^M → ℝ≥0, that is, v_i(S) = Σ_{g∈S} v_i(g)".

**Formalization Note.** Valuations are real matrices `Fin n → Fin m → ℝ`; nonnegativity is this
separate predicate, assumed for every profile and every report a statement quantifies over. -/
def Nonneg {n m : ℕ} (v : Fin n → Fin m → ℝ) : Prop :=
  ∀ i g, 0 ≤ v i g

/-- The additive value `u(A_j) = Σ_{g ∈ A_j} u(g)` of agent `j`'s bundle in the allocation `A`,
for item values `u` (§2, p.6 of arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…).
Agent `i`'s own value is `valOf (v i) i A = v_i(A_i)`; `valOf (v i) j A = v_i(A_j)`. -/
def valOf {n m : ℕ} (u : Fin m → ℝ) (j : Fin n) (A : Alloc n m) : ℝ :=
  ∑ g with A g = j, u g

/-- The additive value `u(A_j)` of agent `j`'s bundle in an integral suballocation `A`
(arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…, §2, p.6). -/
def subValOf {n m : ℕ} (u : Fin m → ℝ) (j : Fin n) (A : SubAlloc n m) : ℝ :=
  ∑ g with A g = some j, u g

/-- **Expectation** `E_{a∼μ}[F(a)] = Σ_a μ(a)·F(a)` under a lottery `μ` on a finite type
(Definitions 2.1, 2.2, p.7 of arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…).

**Formalization Note.** A lottery is a `PMF` on a finite type, so it is automatically a finite
lottery and the expectation is a finite sum (no integrability side condition). -/
noncomputable def expect {α : Type*} [Fintype α] (μ : PMF α) (F : α → ℝ) : ℝ :=
  ∑ a, (μ a).toReal * F a

/-- The **marginal** `Pr_{A∼μ}[g ∈ A_i]` of a lottery over allocations (Definition 2.1, p.7 of
arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…). -/
noncomputable def marginal {n m : ℕ} (μ : PMF (Alloc n m)) (i : Fin n) (g : Fin m) : ℝ :=
  expect μ (fun A => if A g = i then 1 else 0)

/-- **A lottery implements a fractional allocation** (Definition 2.1, p.7): agent `i` receives good
`g` with probability `x i g`, `Pr_{A∼L}[g ∈ A_i] = x_ig`.

arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Definition 2.1, p.7. -/
def Implements {n m : ℕ} (μ : PMF (Alloc n m)) (x : Fin n → Fin m → ℝ) : Prop :=
  ∀ i g, marginal μ i g = x i g

/-- The marginal `Pr_{A∼μ}[g ∈ A_i]` of a lottery over integral suballocations (§2, p.6–7 of
arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…: "Lotteries over integral
suballocations, their supports, and the fractional suballocations they implement are defined in
the same way"). -/
noncomputable def subMarginal {n m : ℕ} (μ : PMF (SubAlloc n m)) (i : Fin n) (g : Fin m) : ℝ :=
  expect μ (fun A => if A g = some i then 1 else 0)

/-- A lottery over integral suballocations **implements** the fractional suballocation `b` if
`Pr_{A∼μ}[g ∈ A_i] = b_ig` for all `i, g` (§2, pp.6–7 of arXiv:2609.35670, version of 2026-11-03,
sha256 4e68de70…). -/
def SubImplements {n m : ℕ} (μ : PMF (SubAlloc n m)) (b : Fin n → Fin m → ℝ) : Prop :=
  ∀ i g, subMarginal μ i g = b i g

end TIEMaximin


