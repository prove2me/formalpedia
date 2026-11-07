-- Prove2me | Definitions.Def_AKSZigZag_IsExpander
-- name    : AKSZigZag_IsExpander
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:17:56.513196+00:00
-- url     : https://prove2.me/theorems/c2838134-1132-4794-9442-bc9afb57f801
-- title:
--   Expander graph with parameters $(\lambda,\alpha,c)$
-- statement:
--   Let $G$ be a bipartite graph with vertex classes $V_1$ and $V_2$, and edge set $E\subseteq V_1\times V_2$. For $X\subseteq V_1$, write $\Gamma(X)\subseteq V_2$ for the set of neighbours of $X$; neighbours of a set $Y\subseteq V_2$ are defined in the same way.
--
--   When $|V_1|=|V_2|=n$, the graph is an **expander with parameters $(\lambda,\alpha,c)$** if:
--   1. every $X\subseteq V_1$ with $|X|\le\alpha n$ satisfies $|\Gamma(X)|\ge\lambda|X|$;
--   2. the same holds for every $Y\subseteq V_2$;
--   3. every vertex has at most $c$ incident edges.
--
--   Bounded valency makes the number of edges linear in $n$, while small sets have many neighbours. In §3 such a graph between the lower and upper halves of the registers yields a bounded-depth $\varepsilon$-halver.
--
--   The module also defines matchings (no two edges share an endpoint), the valency bound, and the comparator $(a,\lfloor m/2\rfloor+b)$ of an edge between $A=\{1,\dots,\lfloor m/2\rfloor\}$ and $B=\{\lfloor m/2\rfloor+1,\dots,m\}$.
--
--   **Formalization Note** $V_1=$ `Fin p` and $V_2=$ `Fin q`, and the graph is a `Finset` of pairs. The paper also uses expanders whose sides differ by one (Remark, p.4). For sides of different sizes, the bound on $|X|$ is $\alpha$ times the size of the side in which $\Gamma(X)$ lies; for $p=q=n$ both bounds are the paper's $\alpha n$. The valency bound $c$ is a natural number.
-- source:
--   Ajtai, Komlós, Szemerédi, An O(n log n) Sorting Network, STOC 1983, doi:10.1145/800061.808726, §2, pp.3–4 (definition of expander graphs, Γ(A)), §3, p.4 (one-factors; A, B)

import Mathlib

namespace AKSZigZag

/-- The neighbourhood `Γ(X) ⊆ V₂` of a set `X ⊆ V₁` in the bipartite graph with edge set
`E ⊆ V₁ × V₂`, `V₁ = Fin p`, `V₂ = Fin q` (AKS, STOC 1983, §2, p.3:
"Γ(A) = {v ∈ V | (v,a) ∈ E for some a ∈ A}"). -/
def nbhd {p q : ℕ} (E : Finset (Fin p × Fin q)) (X : Finset (Fin p)) : Finset (Fin q) :=
  (E.filter fun e => e.1 ∈ X).image Prod.snd

/-- The neighbourhood `Γ(Y) ⊆ V₁` of a set `Y ⊆ V₂` (same graph, other side). -/
def nbhdInv {p q : ℕ} (E : Finset (Fin p × Fin q)) (Y : Finset (Fin q)) : Finset (Fin p) :=
  (E.filter fun e => e.2 ∈ Y).image Prod.fst

/-- Every vertex of either side has at most `c` incident edges ("the maximum valency in G does
not exceed c", AKS, STOC 1983, §2, p.4). -/
def MaxValencyLE {p q : ℕ} (E : Finset (Fin p × Fin q)) (c : ℕ) : Prop :=
  (∀ a : Fin p, (E.filter fun e => e.1 = a).card ≤ c) ∧
    (∀ b : Fin q, (E.filter fun e => e.2 = b).card ≤ c)

/-- A matching ("one-factor", AKS, STOC 1983, §3, p.4): no two distinct edges share an
endpoint. -/
def IsMatching {p q : ℕ} (F : Finset (Fin p × Fin q)) : Prop :=
  (∀ e ∈ F, ∀ e' ∈ F, e.1 = e'.1 → e = e') ∧ (∀ e ∈ F, ∀ e' ∈ F, e.2 = e'.2 → e = e')

/-- **Expander graphs with parameters (λ, α, c)** (AKS, STOC 1983, §2, pp.3–4): "Given two sets
V1, V2, |V1| = |V2| = n, a bipartite graph G with vertex-sets V1, V2 is called an expander graph
with parameters (λ,α,c) if for any set A ⊂ V1, |A| ≤ αn we have |Γ(A)| ≥ λA and the same holds
for subsets of V2, and yet the maximum valency in G does not exceed c."

Here `V₁ = Fin p`, `V₂ = Fin q` and the edge set is `E ⊆ V₁ × V₂`.

**Formalization Note.** The paper's "λA" means `λ|A|`. The paper takes `|V₁| = |V₂| = n`; its
Remark (p.4) also uses sides of sizes differing by one. For sides of unequal size the bound on
`|X|` is `α` times the size of the *other* side (the side `Γ(X)` lives in); for `p = q = n` both
bounds are the paper's `αn`. The valency bound `c` is a natural number (a valency is an integer,
so "valency ≤ c" for real `c` is "valency ≤ ⌊c⌋"). -/
def IsExpander {p q : ℕ} (E : Finset (Fin p × Fin q)) (lam α : ℝ) (c : ℕ) : Prop :=
  (∀ X : Finset (Fin p), (X.card : ℝ) ≤ α * q → lam * X.card ≤ (nbhd E X).card) ∧
    (∀ Y : Finset (Fin q), (Y.card : ℝ) ≤ α * p → lam * Y.card ≤ (nbhdInv E Y).card) ∧
    MaxValencyLE E c

/-- The comparator of a bipartite edge between the register sets `A = (1, …, ⌊m/2⌋)` and
`B = (⌊m/2⌋+1, …, m)` (AKS, STOC 1983, §3, p.4). In 0-based registers `Fin m`, the vertex `a` of
`A = Fin (m/2)` is register `a` and the vertex `b` of `B = Fin (m - m/2)` is register
`m/2 + b`; the comparator is `(a, m/2 + b)`, which puts the smaller element into `A`. -/
def edgeComp {m : ℕ} (e : Fin (m / 2) × Fin (m - m / 2)) : Fin m × Fin m :=
  (⟨e.1.val, by have := e.1.isLt; omega⟩, ⟨m / 2 + e.2.val, by have := e.2.isLt; omega⟩)

end AKSZigZag


