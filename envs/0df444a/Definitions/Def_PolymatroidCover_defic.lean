-- Prove2me | Definitions.Def_PolymatroidCover_defic
-- name    : PolymatroidCover_defic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:26.178191+00:00
-- url     : https://prove2.me/theorems/98eba3a6-3122-4741-9194-75d1f83f4eba
-- title:
--   Deficiency $\tilde f(X) = f(X) - \sum_{e\in X} f(e)$ and $\tilde f(X \mid S)$
-- statement:
--   For a set function $f$ on $E$ the **deficiency function** is
--
--   $$
--   \tilde f(X) := f(X) - \sum_{e \in X} f(e) \qquad (X \subseteq E),
--   $$
--
--   and the **conditional deficiency** is $\tilde f(X \mid S) := \tilde f(X \cup S) - \tilde f(S)$, the marginal of $\tilde f$. A set $X$ is independent exactly when $\tilde f(X) \ge 0$, and $\tilde f$ is submodular when $f$ is a polymatroid. For disjoint $X$ and $S$, $\tilde f(X \mid S) = f(X \mid S) - \sum_{e \in X} f(e)$, so $X$ is independent from $S$ exactly when $\tilde f(X \mid S) \ge 0$. The algorithm uses $\tilde f$ to measure violations of independence.
--
--   **Formalization Note** Both functions take values in `ℤ`.
-- source:
--   Bérczi, Chandrasekaran, Chekuri, Liu, Ravi, Approximate Covering and Packing in Polymatroids, STOC 2027 submission (manuscript sha256 47f38a6f…), §2, p.10 (PDF p.12), eq. (5); conditional form by the convention of §1.1, p.2

import Mathlib

namespace PolymatroidCover

/-- The deficiency function of eq. (5) (Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), §2, printed p.10 = PDF p.12):
`f̃(X) := f(X) − ∑_{e ∈ X} f(e)`, computed in `ℤ`. -/
def defic {n : ℕ} (f : Finset (Fin n) → ℕ) (X : Finset (Fin n)) : ℤ :=
  (f X : ℤ) - ∑ e ∈ X, (f {e} : ℤ)

/-- The conditional deficiency `f̃(X | S) := f̃(X ∪ S) − f̃(S)` (Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), the convention
`g(A | T) := g(A ∪ T) − g(T)` of §1.1, printed p.2, applied to `g = f̃`; used in (8),
printed p.12 = PDF p.14).

**Formalization Note** For disjoint `X` and `S` this equals `f(X | S) − ∑_{e∈X} f(e)`, the
formula of printed p.10; in every use in the paper `X` is disjoint from `S`. -/
def deficCond {n : ℕ} (f : Finset (Fin n) → ℕ) (X S : Finset (Fin n)) : ℤ :=
  defic f (X ∪ S) - defic f S

end PolymatroidCover


