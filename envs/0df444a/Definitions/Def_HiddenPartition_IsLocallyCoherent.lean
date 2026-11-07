-- Prove2me | Definitions.Def_HiddenPartition_IsLocallyCoherent
-- name    : HiddenPartition_IsLocallyCoherent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:30.215824+00:00
-- url     : https://prove2.me/theorems/0c38a43b-21b2-491d-b25e-7456ec2a2441
-- title:
--   $t$-locally coherent family of bijections
-- statement:
--   Throughout, $G$ is a finite simple graph whose vertex set is partitioned into $k$ non-empty independent domains $V(G)=V_1\sqcup\cdots\sqcup V_k$, $A$ and $B$ are finite non-empty sets with $|A|=|B|=M$, and $\mathcal F=\{f_v:A\to B\}_{v\in V(G)}$ is a family of maps with copy maps $\phi_a(v)=(\mathrm{dom}(v),f_v(a))$, images $W_a=\phi_a(V(G))$ (Section 3.1). A seed $a$ **generates** a target pair $\{x,y\}$ when $\{x,y\}=\{\phi_a(u),\phi_a(v)\}$ for an edge $\{u,v\}$ of $G$.
--
--   For an integer $t\ge1$, $\mathcal F$ is a **$t$-locally coherent family of bijections** if
--
--   1. (bijectivity) every $f_v:A\to B$ is a bijection;
--   2. (copy injectivity) every $\phi_a:V(G)\to V(Z)$ is injective;
--   3. (single-vertex overlap, for $t\ge2$) $|W_a\cap W_{a'}|\le1$ for all seeds $a\ne a'$;
--   4. (unique seed for short cycles, for $t\ge3$) for every $3\le\ell\le t$, every simple cycle of length $\ell$ in the target graph $Z$ has a unique seed that generates all of its edges.
--
--   For $t=1$ only properties 1–2 are required and for $t=2$ only properties 1–3. These are the properties of the family that yield the partition guarantee and the clique and density control of the construction.
--
--   **Formalization Note** Properties 3 and 4 are implications with antecedents $t\ge2$ and $t\ge3$. A simple cycle of length $\ell$ is a closed walk of $Z$ that is a cycle (Mathlib `Walk.IsCycle`) of length $\ell$.
-- source:
--   H. Agrawal, P. Eua-anant, B. Haeupler, B. Laekhanukit, P. Mihov, L. Milenković, R. Santos, Z. Zhang, From One Hidden Subgraph to Dense Graph Partitions with Applications to Hardness of Clustering, STOC 2027 submission (manuscript sha256 17239d0bf911912040cb82c45ae979b179c419fb0b9e69d6d1413bf70068b601), §3.1, p.13 (pdf p.15)

import Mathlib
import Definitions.Def_HiddenPartition_target

set_option autoImplicit false

namespace HiddenPartition

/-- The seed `a` **generates** the unordered target pair `e` when `e = {ϕ_a(u), ϕ_a(v)}` for an
edge `(u, v)` of `G` (Agrawal et al., STOC 2027 submission, manuscript sha256 17239d0b…, §3.1,
p.13 (pdf p.15)). -/
def Generates {V A B : Type*} {k : ℕ} (G : SimpleGraph V) (dom : V → Fin k) (f : V → A → B)
    (a : A) (e : Sym2 (Fin k × B)) : Prop :=
  ∃ u v, G.Adj u v ∧ e = s(phi dom f a u, phi dom f a v)

/-- **`t`-locally coherent family of bijections** (Agrawal et al., STOC 2027 submission,
manuscript sha256 17239d0b…, §3.1, p.13 (pdf p.15)).

For an integer `t ≥ 1`, the family `F = {f_v : A → B}_{v ∈ V(G)}` is `t`-locally coherent when
1. (bijectivity) every `f_v : A → B` is a bijection;
2. (copy injectivity) every `ϕ_a : V(G) → V(Z)` is injective;
3. (single-vertex overlap, for `t ≥ 2`) `|W_a ∩ W_{a'}| ≤ 1` whenever `a ≠ a'`;
4. (unique seed for short cycles, for `t ≥ 3`) for every `3 ≤ ℓ ≤ t`, every simple cycle of
   length `ℓ` in the target graph `Z` has a unique seed that generates all of its edges.

**Formalization Note.** Clauses 3 and 4 are implications with antecedents `2 ≤ t` and `3 ≤ t`,
as printed ("`t = 1` requires only the first two properties, and `t = 2` requires the first
three"). A simple cycle of length `ℓ` is a closed walk `c` of `Z` with `c.IsCycle` and
`c.length = ℓ`; "generates all its edges" is `Generates … a e` for every `e ∈ c.edges`. -/
def IsLocallyCoherent {V A B : Type*} [Fintype V] [DecidableEq B] {k : ℕ} (t : ℕ)
    (G : SimpleGraph V) (dom : V → Fin k) (f : V → A → B) : Prop :=
  (∀ v, Function.Bijective (f v)) ∧
  (∀ a, Function.Injective (phi dom f a)) ∧
  (2 ≤ t → ∀ a a', a ≠ a' → (W dom f a ∩ W dom f a').card ≤ 1) ∧
  (3 ≤ t → ∀ ℓ : ℕ, 3 ≤ ℓ → ℓ ≤ t → ∀ (x : Fin k × B) (c : (target G dom f).Walk x x),
    c.IsCycle → c.length = ℓ → ∃! a, ∀ e ∈ c.edges, Generates G dom f a e)

end HiddenPartition


