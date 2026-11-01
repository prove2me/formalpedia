-- Prove2me | Definitions.Def_XOSMax_IsKXOS
-- name    : XOSMax_IsKXOS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:24:20.522021+00:00
-- url     : https://prove2.me/theorems/4fe42e84-c087-4d36-b70a-157c4c798996
-- title:
--   $k$-XOS set functions
-- statement:
--   A set function $f$ is **$k$-XOS** if it admits a representation of width exactly $k$ as a maximum of additive functions:
--   $$
--   \exists\,w_1,\dots,w_k:E\to\mathbb R,\quad f(X)=\max_{i\in[k]}\sum_{v\in X}w_i(v)\quad\text{for all finite }X\subseteq E .
--   $$
--   There is no sign, monotonicity or normalization assumption. The values of $f$ and of the clauses may be negative, $f$ need not be monotone, and $f(\emptyset)=0$ follows from the representation.
--
--   This is the input class of the mission. The width is an analysis parameter only: the algorithms never receive it.
--
--   **Formalization Note** Clauses may repeat, so a $k$-XOS function is also $(k+1)$-XOS, and a statement about $k$-XOS functions covers every width that admits a representation, not only the least one.
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, §1, p.1, "An XOS function admitting a representation of width k is called k-XOS"

import Mathlib
import Definitions.Def_XOSMax_Represents

namespace XOSMax

/-- `IsKXOS k f`: the set function `f` is **`k`-XOS**, i.e. it admits a representation of width
exactly `k` as a maximum of additive functions (Filmus, Kawase, Kobayashi & Yamaguchi,
arXiv:1811.09045v3, §1, p.1, "An XOS function admitting a representation of width k is called
k-XOS").

**Formalization Note** There is no sign, monotonicity or normalization condition: clauses may be
negative, `f` need not be monotone, and `f ∅ = 0` is a consequence of the representation. The
clauses need not be distinct, so a `k`-XOS function is also `(k + 1)`-XOS. -/
def IsKXOS {E : Type} (k : ℕ) (f : Finset E → ℝ) : Prop :=
  ∃ w : Fin k → E → ℝ, Represents w f

end XOSMax


