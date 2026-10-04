-- Prove2me | Definitions.Def_MilnorWolf_Growth
-- name    : MilnorWolf_Growth
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-09-19T22:29:29.273991+00:00
-- url     : https://prove2.me/theorems/5ee8b429-fcf5-4315-9ea9-a225c12d72b8
-- title:
--   Wolf's growth function, polynomial growth, polycyclic groups and the growth exponents
-- statement:
--   Wolf's definitions, which Milnor's addendum also uses, on top of the published `Chou.wordBall`.
--
--   - `growthFunction S m`, Wolf's $g_S(m)$. pp. 425–426: “Let $S$ be a finite subset of a group
--     $\Gamma$. As usual an expression $s_1^{a_1} \cdots s_r^{a_r}$, $s_i \in S$, $a_i \in \boldsymbol{Z}$
--     is called a *word of length $|a_1| + \cdots + |a_r|$ based on $S$*. Following Milnor [9] we define
--     the *growth function* $g_S$ to be the function on positive integers given by (3.1) $g_S(m)$ is
--     the number of distinct elements of $\Gamma$ expressible as words of length $\le m$ based on $S$.”
--     Here $g_S(m)$ is taken as the size of the ball of radius $m$ (products of at most $m$ factors
--     from $S \cup S^{-1}$).
--   - `HasPolynomialGrowthOfDegreeLE G E`. p. 431: “Let $\Gamma$ be a finitely generated group, $S$ a
--     finite generating set, and $E \ge 0$ an integer. If there is a constant $c > 0$ such that
--     $g_S(m) \le cm^E$ for every integer $m \ge 1$, then we say that $\Gamma$ has *polynomial growth of
--     degree $\le E$*. Lemma 3.5 says that this condition is independent of choice of $S$.” Here: for
--     some finite generating set $S$ there is such a $c$.
--   - `IsPolycyclic G`. p. 432: “A solvable group is called *polycyclic* if it satisfies the
--     (equivalent) conditions of the following proposition.” The first condition of Proposition 4.1,
--     p. 433: “(1) There is a normal series $\Gamma = A_0 \supset A_1 \supset \cdots \supset A_t = \{1\}$
--     with every quotient $A_i/A_{i+1}$ finite or infinite cyclic.” Here: there is a chain
--     $G = A_0 \supseteq A_1 \supseteq \cdots \supseteq A_t = 1$ of subgroups, each $A_{i+1}$ normal in
--     $A_i$, with every quotient $A_i/A_{i+1}$ cyclic (finite or infinite). No solvability hypothesis is
--     needed: such a series already makes $G$ solvable.
--   - `lcs G k`, `lcsFactor G k`, `lcsRank G k`. p. 426, Theorem 3.2: “Let $\Gamma$ be a finitely
--     generated nilpotent group with lower central series
--     $\Gamma = \Gamma_0 \supsetneqq \Gamma_1 \supsetneqq \cdots \supsetneqq \Gamma_s \supsetneqq \Gamma_{s+1} = \{1\}$,
--     $\Gamma_{k+1} = [\Gamma, \Gamma_k]$. Then each $\Gamma_k/\Gamma_{k+1}$ is a finitely generated
--     abelian group, say $\Gamma_k/\Gamma_{k+1} = A_k \times B_k$ with $A_k$ finite abelian and $B_k$
--     free abelian of finite rank $n_k$, and we define ‘growth exponents’ by (3.3)
--     $E_1(\Gamma) = \sum_{k=0}^{s} (k + 1)n_k$, $E_2(\Gamma) = \sum_{k=0}^{s} 2^k n_k$.” These are the
--     lower central series $\Gamma_k$, the abelian group $\Gamma_k/\Gamma_{k+1}$ (presented as a
--     quotient of the abelianization of $\Gamma_k$), and its $\mathbb Z$-rank $n_k$, the rank of its
--     free abelian part.
--   - `growthExponentOne G`, `growthExponentTwo G`: Wolf's $E_1$ and $E_2$, defined by (3.3) at the
--     end of the second sentence quoted in full in the previous item, whose $\Gamma$ is “a finitely
--     generated nilpotent group” (p. 426): “$E_1(\Gamma) = \sum_{k=0}^{s} (k + 1)n_k$,
--     $E_2(\Gamma) = \sum_{k=0}^{s} 2^k n_k$.” The sum runs over $k < s + 1$ where $s + 1$ is the
--     nilpotency class (so both are $0$ for a group that is not nilpotent).
--
--   No theorem is stated here.
-- source:
--   Wolf, J. A., Growth of finitely generated solvable groups and curvature of Riemannian manifolds, Journal of Differential Geometry 2 (1968) 421–446, https://doi.org/10.4310/jdg/1214428658, p. 426 (growth function), p. 431 (polynomial growth of degree ≤ E), Proposition 4.1 (1) p. 433 (polycyclic), (3.3) p. 426 (growth exponents); Milnor refers to Wolf for definitions (p. 447)

import Definitions.Def_Chou_Growth
import Mathlib

/-!
# Growth of finitely generated groups: Wolf's definitions (J. Differential Geometry 2 (1968))

J. A. Wolf, *Growth of finitely generated solvable groups and curvature of Riemannian manifolds*,
J. Differential Geometry 2 (1968) 421–446; J. Milnor, *Growth of finitely generated solvable
groups*, ibid. 447–449, refers to Wolf for these definitions.

For a finite subset `S` of a group `Γ`, Wolf's growth function `g_S(m)` (p. 426) counts the
elements expressible as words of length `≤ m` based on `S`, a word `s₁^{a₁} ⋯ s_r^{a_r}` having
length `|a₁| + ⋯ + |a_r|`; `g_S(m)` is taken here as the size of the ball `Chou.wordBall S m` of the
published growth bundle, the set of products of at most `m` factors from `S ∪ S⁻¹`.  `Γ` has *polynomial
growth of degree `≤ E`* (p. 431) if `g_S(m) ≤ c m^E` for some finite generating set `S`, some
`c > 0` and every `m ≥ 1`; exponential growth is `Chou.HasExponentialGrowth`.  A solvable group is
*polycyclic* (Proposition 4.1 (1), p. 433) if it has a normal series with every quotient finite or
infinite cyclic; here, as in Kurosh, a normal series is a chain in which each term is normal in the
preceding one.  For a finitely generated nilpotent group with lower central series
`Γ = Γ₀ ⊇ Γ₁ ⊇ ⋯ ⊇ Γ_s ⊇ Γ_{s+1} = 1`, each `Γ_k/Γ_{k+1}` is a finitely generated abelian group
`A_k × B_k` with `A_k` finite and `B_k` free abelian of rank `n_k`, and Wolf's growth exponents
(3.3) are `E₁ = ∑ (k+1) n_k` and `E₂ = ∑ 2^k n_k`.  The rank `n_k` is taken as the `ℤ`-rank of
the abelian group `Γ_k/Γ_{k+1}`, presented as a quotient of the abelianization of `Γ_k` so that
its commutativity is available by construction; the sum runs over `k < s + 1`, Mathlib's
`Group.nilpotencyClass` (which is `0`, giving an empty sum, when the group is not nilpotent).
-/

namespace MilnorWolf

open Chou

/-- Wolf's growth function `g_S(m)` (p. 426), “the number of distinct elements of `Γ` expressible as
words of length `≤ m` based on `S`”, taken here as the size of the ball `Chou.wordBall S m`. -/
noncomputable def growthFunction {G : Type*} [Group G] (S : Finset G) (m : ℕ) : ℕ :=
  Nat.card (wordBall (S : Set G) m)

/-- Wolf, p. 431: `Γ` has polynomial growth of degree `≤ E` if for some finite generating set `S`
there is a constant `c > 0` with `g_S(m) ≤ c m^E` for every integer `m ≥ 1`. -/
def HasPolynomialGrowthOfDegreeLE (G : Type*) [Group G] (E : ℕ) : Prop :=
  ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 1 ≤ m → (growthFunction S m : ℝ) ≤ c * (m : ℝ) ^ E

/-- Wolf, Proposition 4.1 (1) (p. 433): a group is polycyclic if it has a normal series
`Γ = A₀ ⊇ A₁ ⊇ ⋯ ⊇ A_t = 1`, each `A_{i+1}` normal in `A_i`, with every quotient `A_i/A_{i+1}`
cyclic (finite or infinite). -/
def IsPolycyclic (G : Type*) [Group G] : Prop :=
  ∃ (t : ℕ) (A : Fin (t + 1) → Subgroup G), A 0 = ⊤ ∧ A (Fin.last t) = ⊥ ∧
    ∀ i : Fin t, A i.succ ≤ A i.castSucc ∧
      ∃ _ : ((A i.succ).subgroupOf (A i.castSucc)).Normal,
        IsCyclic (A i.castSucc ⧸ (A i.succ).subgroupOf (A i.castSucc))

/-- The `k`-th term `Γ_k` of the lower central series of `G`: `Γ₀ = G` and `Γ_{k+1} = ⁅Γ_k, G⁆` in
Mathlib's bracket order; Wolf writes `Γ_{k+1} = [Γ, Γ_k]`, the same subgroup by
`Subgroup.commutator_comm`. -/
abbrev lcs (G : Type*) [Group G] (k : ℕ) : Subgroup G :=
  (⊤ : Subgroup G).lowerCentralSeries k

/-- The abelian group `Γ_k/Γ_{k+1}` of the lower central series, realised as the quotient of the
abelianization of `Γ_k` by the image of `Γ_{k+1}`, so that it is a `CommGroup` by construction. -/
abbrev lcsFactor (G : Type*) [Group G] (k : ℕ) : Type _ :=
  Abelianization (lcs G k) ⧸
    Subgroup.map (Abelianization.of (G := lcs G k)) ((lcs G (k + 1)).subgroupOf (lcs G k))

/-- `n_k` of Wolf (3.3): the rank of the free abelian part of `Γ_k/Γ_{k+1}`, the `ℤ`-rank of that
abelian group. -/
noncomputable def lcsRank (G : Type*) [Group G] (k : ℕ) : ℕ :=
  Module.finrank ℤ (Additive (lcsFactor G k))

/-- Wolf's growth exponent `E₁(Γ) = ∑_{k=0}^{s} (k+1) n_k` of (3.3), for a nilpotent group with
`Γ_{s+1} = 1`; `s + 1` is Mathlib's `Group.nilpotencyClass`, which is `0` for a non-nilpotent
group, so that the sum is then empty. -/
noncomputable def growthExponentOne (G : Type*) [Group G] : ℕ :=
  ∑ k ∈ Finset.range (Group.nilpotencyClass G), (k + 1) * lcsRank G k

/-- Wolf's growth exponent `E₂(Γ) = ∑_{k=0}^{s} 2^k n_k` of (3.3). -/
noncomputable def growthExponentTwo (G : Type*) [Group G] : ℕ :=
  ∑ k ∈ Finset.range (Group.nilpotencyClass G), 2 ^ k * lcsRank G k

end MilnorWolf


