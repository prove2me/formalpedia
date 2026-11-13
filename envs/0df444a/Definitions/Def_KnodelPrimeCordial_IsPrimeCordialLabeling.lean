-- Prove2me | Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
-- name    : KnodelPrimeCordial_IsPrimeCordialLabeling
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T05:59:05.094169+00:00
-- url     : https://prove2.me/theorems/f7442430-571c-4573-a557-d686eb1cbe2d
-- title:
--   Prime cordial labeling of a finite simple graph
-- statement:
--   Let $G=(V,E)$ be a finite simple graph and let $f:V\to\mathbb N$ be a vertex labeling. Each edge $uv\in E$ receives the label
--
--   $$
--   f(uv)=\begin{cases}1,&\gcd(f(u),f(v))=1,\\ 0,&\gcd(f(u),f(v))>1.\end{cases}
--   $$
--
--   Write $e_1(f)$ and $e_0(f)$ for the numbers of edges labeled $1$ and $0$. The labeling $f$ is a **prime cordial labeling** of $G$ when
--
--   1. $f$ is a bijection from $V$ onto $\{1,2,\dots,|V|\}$, and
--   2. $|e_0(f)-e_1(f)|\le 1$.
--
--   Since every label is at least $1$, every gcd is at least $1$, so each edge carries exactly one of the two labels. This is the central notion of the paper; the predicate "prime cordial" asks for the existence of such a labeling.
--
--   **Formalization Note** The two edge sets are filters of the undirected edge set `edgeFinset` (each edge counted once), using the symmetric function $\gcd(f(u),f(v))$ on unordered pairs. The bijection is `Set.BijOn f univ (Icc 1 |V|)`, so the labels are $1,\dots,|V|$, never $0$. The difference $e_0-e_1$ is computed in $\mathbb Z$.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), §1, p.2 (PDF p.2), definition of prime cordial labeling; same text in the abstract, p.1

import Mathlib

namespace KnodelPrimeCordial

/-- The gcd of the labels at the two ends of an (unordered) edge `e = uv` under a vertex
labeling `f`: `edgeGcd f s(u, v) = gcd(f(u), f(v))`. Well defined on `Sym2 V` because `gcd`
is symmetric. -/
def edgeGcd {V : Type*} (f : V → ℕ) (e : Sym2 V) : ℕ :=
  Sym2.lift ⟨fun u v => Nat.gcd (f u) (f v), fun u v => Nat.gcd_comm (f u) (f v)⟩ e

/-- The edges labeled `1`: the edges `uv` of `G` with `gcd(f(u), f(v)) = 1`. -/
def edgesLabelOne {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (f : V → ℕ) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => edgeGcd f e = 1)

/-- The edges labeled `0`: the edges `uv` of `G` with `gcd(f(u), f(v)) > 1`. -/
def edgesLabelZero {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (f : V → ℕ) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => 1 < edgeGcd f e)

/-- **Prime cordial labeling** (Haque, Khanam, Shahriar, *Prime cordial labeling of Knödel
graph*, manuscript (2026), §1, p.2; same text in the abstract, p.1): "A graph with vertex set V
is said to have a prime cordial labeling if there is a bijection f from V to {1, 2, . . . , |V|}
such that if each edge uv is assigned the label 1 for gcd(f(u), f(v)) = 1 and 0 for
gcd(f(u), f(v)) > 1 then the number of edges labeled with 0 and the number of edges labeled
with 1 differ by at most 1."

`IsPrimeCordialLabeling G f` says: `f` maps `V` bijectively onto `{1, …, |V|}`, and the
numbers `e₀`, `e₁` of edges labeled `0` and `1` satisfy `|e₀ − e₁| ≤ 1`.

**Formalization Note** Labels are natural numbers and the bijection is `Set.BijOn f univ
(Icc 1 |V|)`, so the labels are `1, …, |V|` (never `0`). Edges are the undirected edges of the
simple graph (`edgeFinset`), each counted once. The difference `e₀ − e₁` is taken in `ℤ`. -/
def IsPrimeCordialLabeling {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (f : V → ℕ) : Prop :=
  Set.BijOn f Set.univ (Set.Icc 1 (Fintype.card V)) ∧
    |((edgesLabelZero G f).card : ℤ) - ((edgesLabelOne G f).card : ℤ)| ≤ 1

end KnodelPrimeCordial


