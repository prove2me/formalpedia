-- Prove2me | Definitions.Def_XOSMax_Represents
-- name    : XOSMax_Represents
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:41.602517+00:00
-- url     : https://prove2.me/theorems/d56665ef-99f9-4898-989b-2a46be1b54a8
-- title:
--   Representation of a set function as a maximum of additive clauses
-- statement:
--   Let $E$ be a ground type and let $f$ assign a real number to every finite subset of $E$. A family of real weights $w_1,\dots,w_k$ on $E$ **represents** $f$ if
--   $$
--   f(X)=\max_{i\in[k]}\ \sum_{v\in X}w_i(v)\qquad\text{for every finite }X\subseteq E .
--   $$
--   Each $w_i$ is an additive function $f_i(X)=\sum_{v\in X}f_i(v)$ given by its values on singletons, and $k$ is the **width** of the representation.
--
--   Every statement of the mission about cliques and index sets is relative to such a representation.
--
--   **Formalization Note** The maximum is stated with `IsGreatest`, so it is attained and width $0$ admits no representation. The weights are signed, as the paper remarks that "each fi as well as f can take negative values".
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, §1, p.1, "f(X) = max"

import Mathlib

namespace XOSMax

/-- `Represents w f`: the family `w₁, …, w_k` of additive clauses is a representation of width `k`
of the set function `f`, that is, `f(X) = max_{i∈[k]} ∑_{v∈X} wᵢ(v)` for every `X`
(Filmus, Kawase, Kobayashi & Yamaguchi, *Tight Approximation for Unconstrained XOS Maximization*,
arXiv:1811.09045v3, §1, p.1, "f(X) = max").

**Formalization Note** The ground set is a type `E`, subsets are `Finset E`. The clause `fᵢ` is
given by its values `w i v = fᵢ({v})` on singletons, and `fᵢ(X)` is the sum `∑ v ∈ X, w i v`. The
values are signed: the paper remarks that "each fi as well as f can take negative values". The
maximum is a genuine one, `IsGreatest`, so `k = 0` admits no representation (`[0]` is empty and the
maximum does not exist). -/
def Represents {E : Type} {k : ℕ} (w : Fin k → E → ℝ) (f : Finset E → ℝ) : Prop :=
  ∀ X : Finset E, IsGreatest (Set.range fun i : Fin k => ∑ v ∈ X, w i v) (f X)

end XOSMax


