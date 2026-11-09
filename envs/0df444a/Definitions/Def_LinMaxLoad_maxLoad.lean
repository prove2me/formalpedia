-- Prove2me | Definitions.Def_LinMaxLoad_maxLoad
-- name    : LinMaxLoad_maxLoad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:09.176352+00:00
-- url     : https://prove2.me/theorems/86583aac-9642-4cbd-966b-1fb57d1079ba
-- title:
--   Max load $M(S,f)$
-- statement:
--   Let $f : A \to B$ be a function and $S \subseteq A$ a finite set. The **max load** of $S$ with respect to $f$ is the largest number of points of $S$ that $f$ sends to a single value:
--
--   $$
--   M(S, f) := \max_{b \in B} \, |S \cap f^{-1}(b)| .
--   $$
--
--   Thinking of $f$ as a hash function placing the elements of $S$ into bins indexed by $B$, $M(S,f)$ is the size of the fullest bin. It is the basic quantity of the mission: the expected linear max load $m(S)$ is its average over random linear maps.
--
--   **Formalization Note** The maximum is taken over the image $f(S)$ rather than over all of $B$. Bins outside the image are empty, so the value is the same for nonempty $S$, and the empty set has max load $0$. This form needs no finiteness of $B$, which matters for quotient targets. The page writes $h^{-1}(b)$, a slip for $f^{-1}(b)$.
-- source:
--   Kumar–Zuckerman, Linear Max Load and Additive Structure, STOC 2027 submission (manuscript sha256 9dfdbfff…163b056d), Definition 1, p.3 (restated in Section 2.1, p.8)

import Mathlib

namespace LinMaxLoad

/-- **Max load** (Definition 1, p.3; restated in Section 2.1, p.8, of
Kumar–Zuckerman, *Linear Max Load and Additive Structure*, STOC 2027 submission manuscript
(sha256 9dfdbfffae232e07951f18360ca77987748ff477822893e9f447422f163b056d)).
For a function `f : A → B` and a finite set `S ⊆ A`,
`M(S, f) := max_{b ∈ B} |S ∩ f⁻¹(b)|`.

**Formalization Note** The maximum is taken over the image `f(S)` instead of all of `B`:
bins outside the image have load 0, so the value is the same whenever `S` is nonempty, and
the empty set has max load 0 (the maximum of an empty family of natural numbers). Taking the
maximum over the image needs no finiteness of `B`. The page's `h⁻¹(b)` is a slip for
`f⁻¹(b)`. -/
def maxLoad {A B : Type*} [DecidableEq B] (f : A → B) (S : Finset A) : ℕ :=
  (S.image f).sup fun b => (S.filter fun a => f a = b).card

end LinMaxLoad


