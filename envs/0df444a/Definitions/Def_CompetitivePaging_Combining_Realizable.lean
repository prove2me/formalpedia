-- Prove2me | Definitions.Def_CompetitivePaging_Combining_Realizable
-- name    : CompetitivePaging_Combining_Realizable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:22:03.127212+00:00
-- url     : https://prove2.me/theorems/c1e15bbe-2349-4f59-a3ab-26d45fd2557b
-- title:
--   Competitiveness against another on-line algorithm, and realizable sequences of ratios
-- statement:
--   Fix a finite set $M$ of $n$ vertices with the **uniform metric** ($d(x,y)=1$ for $x\ne y$), so that serving requests with $k$ servers on $M$ is the paging problem with a fast memory of $k$ pages. A deterministic on-line algorithm of **type** $(k,n)$ holds $k$ servers on $M$ and, after each request $r$, moves servers so that some server sits on $r$; its configuration after a request sequence depends only on that sequence. Its cost $C_A(\sigma)$ on a request sequence $\sigma$ is the total distance travelled by its servers, i.e. the number of server moves.
--
--   Let $A$ and $B$ be deterministic on-line algorithms of the same type and let $c$ be a real number. Then $A$ is **$c$-competitive against $B$** if there is a constant $a$ such that for every request sequence $\sigma$
--   $$C_A(\sigma)\le c\cdot C_B(\sigma)+a .$$
--
--   A finite sequence $c^*=(c(1),\dots,c(m))$ of reals is **realizable** if for every type $(k,n)$ and every $m$-tuple $B(1),\dots,B(m)$ of deterministic on-line algorithms of type $(k,n)$ there is a deterministic on-line algorithm $A$ of type $(k,n)$ that is $c(i)$-competitive against $B(i)$ for every $i=1,\dots,m$.
--
--   These two notions are the objects of Theorem 6: they formalize the question whether one on-line paging algorithm can combine the guarantees of several given ones.
--
--   **Formalization Note** A type $(k,n)$ is a natural number $k$ together with an arbitrary finite type `M : Type` carrying a metric in which distinct points are at distance $1$; $n$ is the cardinality of $M$. Algorithms are the `KServer.OnlineAlgorithm k M` of the published `KServer_model` definition; each algorithm carries its own initial configuration. The additive constant $a$ is chosen before the request sequence. The definition of realizability does not itself require $c(i)>0$; Theorem 6 assumes it.
-- source:
--   Fiat, Karp, Luby, McGeoch, Sleator, Young, Competitive Paging Algorithms, arXiv:cs/0205038v1, pp. 8–9 (PDF pp. 9–10), §6, definitions of the type of an algorithm, of c-competitive against, and of realizable

import Mathlib
import Definitions.Def_KServer_model

namespace CompetitivePaging.Combining

/-- **`c`-competitive against another on-line algorithm** (Fiat et al. 1991, §6, p. 8).
For two deterministic on-line algorithms `A` and `B` of the same type (the same number `k` of
servers and the same vertex set `M`), `A` is `c`-competitive against `B` if there is a constant
`a`, chosen before the request sequence, such that on every request sequence `σ`
`C_A(σ) ≤ c · C_B(σ) + a`. -/
def CompetitiveAgainst {k : ℕ} {M : Type} [MetricSpace M]
    (A B : KServer.OnlineAlgorithm k M) (c : ℝ) : Prop :=
  ∃ a : ℝ, ∀ σ : List M, A.cost σ ≤ c * B.cost σ + a

/-- **Realizable sequence of ratios** (Fiat et al. 1991, §6, pp. 8–9). A finite sequence
`c = (c(1), …, c(m))` is realizable if for every type `(k, n)` — `k` servers on a finite set `M`
of `n` vertices with the uniform metric (every two distinct vertices at distance `1`, so that the
cost of an algorithm is its number of page faults, §2) — and for every `m`-tuple
`B(1), …, B(m)` of deterministic on-line algorithms of that type, there is a deterministic
on-line algorithm `A` of the same type that is `c(i)`-competitive against `B(i)` for every `i`. -/
def Realizable {m : ℕ} (c : Fin m → ℝ) : Prop :=
  ∀ (k : ℕ) (M : Type) [MetricSpace M] [Fintype M],
    (∀ x y : M, x ≠ y → dist x y = 1) →
    ∀ B : Fin m → KServer.OnlineAlgorithm k M,
      ∃ A : KServer.OnlineAlgorithm k M, ∀ i, CompetitiveAgainst A (B i) (c i)

end CompetitivePaging.Combining


