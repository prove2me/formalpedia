-- Prove2me | Definitions.Def_SubnormalCover_uniformCover
-- name    : SubnormalCover_uniformCover
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-14T12:43:16.10775+00:00
-- url     : https://prove2.me/theorems/fab962e8-24a1-4922-96ae-4b5eee23724f
-- title:
--   Uniform covers of a group by cosets
-- statement:
--   A finite system of left cosets $a_1G_1,\dots,a_kG_k$ of a group $G$ is a **uniform cover** of weight $w$ when the covering function $w_{\mathcal A}(x)=|\{i : x\in a_iG_i\}|$ of Sun's equation (1.2) is constant, equal to $w$. The case $w=1$ is a coset partition, the setting of the Herzog-Schönheim conjecture; a uniform cover need not have any disjoint subcover at all.
--
--   `IsUniformCover K a w` says that for every $x$ the number of indices $i$ with $(a_i)^{-1}x\in K_i$ is exactly `w`. The count is `Nat.card` of a subtype, so no decidability hypothesis is needed, and the family is indexed by `Fin k` so that multiplicities stay visible — every conclusion in this mission counts indices, not distinct subgroups. A cover is **trivial** when every $K_i$ is the whole group; nontriviality is deliberately *not* folded into the definition and appears as the explicit hypothesis `∃ i, K i ≠ ⊤` wherever it is needed, since without it the results are false.
--
--   Also defined here: `coverLcm K`, the modulus $N=[n_1,\dots,n_k]$, the least common multiple of the indices $n_i=[G:K_i]$, whose prime divisors are exactly those of the product $n_1\cdots n_k$; and `indexMultiplicity K m`, the number of indices $i$ with $[G:K_i]=m$, of which the paper's $M$ is a uniform bound.
-- source:
--   Z.-W. Sun, On the Herzog-Schönheim conjecture for uniform covers of groups, J. Algebra 273 (2004) 153-175, https://doi.org/10.1016/S0021-8693(03)00526-X, §1, eqs. (1.1) and (1.2)

import Mathlib

namespace SubnormalCover

/-- A finite system of left cosets `a i • K i`, `i : Fin k`, is a **uniform cover** of `G` with
weight `w` if the covering function `w_A(x) = |{i : x ∈ a i K i}|` of Z.-W. Sun's equation (1.2)
is constant, equal to `w`.

The membership `x ∈ a i • K i` is spelled `(a i)⁻¹ * x ∈ K i`, and the count is `Nat.card` of the
subtype of such indices, so that no decidability assumption is needed.

The case `w = 1` is a **disjoint cover**, i.e. a partition of `G` into cosets; this is the setting
of the Herzog-Schönheim conjecture. A uniform cover is called **trivial** when `K i = ⊤` for every
`i`; nontriviality is expressed in the statements below as `∃ i, K i ≠ ⊤`, and is never folded
into this definition. -/
def IsUniformCover {G : Type*} [Group G] {k : ℕ} (K : Fin k → Subgroup G) (a : Fin k → G)
    (w : ℕ) : Prop :=
  ∀ x : G, Nat.card {i : Fin k // (a i)⁻¹ * x ∈ K i} = w

/-- The **modulus** `N = [n₁, …, n_k]` of a system of cosets: the least common multiple of the
indices `n i = [G : K i]`. Its prime divisors are exactly those of the product `n₁ ⋯ n_k`, which
is the quantity named in the abstract of the source. -/
noncomputable def coverLcm {G : Type*} [Group G] {k : ℕ} (K : Fin k → Subgroup G) : ℕ :=
  Finset.univ.lcm fun i => (K i).index

/-- The **multiplicity** of the value `m` among the indices, i.e. `|{i : [G : K i] = m}|`. The
quantity `M` of the source is a bound for this, uniform in `m`. -/
noncomputable def indexMultiplicity {G : Type*} [Group G] {k : ℕ} (K : Fin k → Subgroup G) (m : ℕ) : ℕ :=
  (Finset.univ.filter fun i => (K i).index = m).card

end SubnormalCover


