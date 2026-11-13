-- Prove2me | Definitions.Def_KnodelPrimeCordial_PrimeCordial
-- name    : KnodelPrimeCordial_PrimeCordial
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:01:21.78569+00:00
-- url     : https://prove2.me/theorems/a8452fe9-27ce-43a0-8a72-9d7f73b639b1
-- title:
--   Prime cordial graph
-- statement:
--   A finite simple graph $G$ is **prime cordial** if it has a prime cordial labeling: a bijection $f:V\to\{1,\dots,|V|\}$ such that the number of edges $uv$ with $\gcd(f(u),f(v))>1$ and the number of edges with $\gcd(f(u),f(v))=1$ differ by at most one.
--
--   For example (Sundaram, Ponraj, Somasundaram), the path $P_n$ is prime cordial if and only if $n\ne 3,5$, and the cycle $C_n$ if and only if $n\ge 6$. The paper's main theorem decides this property for the Knödel graphs $W_{3,n}$.
--
--   **Formalization Note** Graphs are finite simple graphs (`SimpleGraph V` with `Fintype V`), as the paper assumes throughout ("finite undirected graphs without loops or multiple edges", p.1).
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), §1, p.2 (PDF p.2), "A graph is called prime cordial if it has a prime cordial labeling."

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling

namespace KnodelPrimeCordial

/-- **Prime cordial graph** (Haque, Khanam, Shahriar, *Prime cordial labeling of Knödel
graph*, manuscript (2026), §1, p.2): "A graph is called prime cordial if it has a prime cordial
labeling."

`PrimeCordial G` holds when some `f : V → ℕ` is a prime cordial labeling of `G`
(`IsPrimeCordialLabeling`: a bijection onto `{1, …, |V|}` whose numbers of `0`-edges and
`1`-edges differ by at most one).

**Formalization Note** Graphs are finite simple graphs (`SimpleGraph V`, `Fintype V`), as the
paper assumes on p.1 ("finite undirected graphs without loops or multiple edges"). -/
def PrimeCordial {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop :=
  ∃ f : V → ℕ, IsPrimeCordialLabeling G f

end KnodelPrimeCordial


