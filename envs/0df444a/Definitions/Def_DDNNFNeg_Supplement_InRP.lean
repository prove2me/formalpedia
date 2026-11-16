-- Prove2me | Definitions.Def_DDNNFNeg_Supplement_InRP
-- name    : DDNNFNeg_Supplement_InRP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:47:19.867776+00:00
-- url     : https://prove2.me/theorems/2a1e0efa-c7c3-4d20-82e0-4e866ba107fd
-- title:
--   The class RP
-- statement:
--   A language $L \subseteq \{0,1\}^*$ is in **RP** if there are a polynomial $p$ and a deterministic polynomial-time $V$ such that, for $r$ uniform in $\{0,1\}^{p(|x|)}$:
--
--   1. if $x \in L$, then $\Pr_r[V \text{ accepts } (x, r)] \ge 1/2$;
--   2. if $x \notin L$, then $V$ accepts $(x, r)$ for no $r$.
--
--   **Formalization Note** The probability is a counting ratio, $2^{p(|x|)} \le 2 \cdot \#\{r : V \text{ accepts } (x,r)\}$; $V$ accepts when it outputs the string $1$.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §4, pp.10–11

import Mathlib
import Definitions.Def_DDNNFNeg_Supplement_PolyTimeFun
import Definitions.Def_DDNNFNeg_Supplement_pairEnc

namespace DDNNFNeg.Supplement

/-- The language `L ⊆ {0,1}*` is in **RP** (randomized polynomial time with one-sided error)
(Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §4, p.10–11): there are a polynomial `p` and a deterministic polynomial-time `V` such
that, with `r` uniform over `{0,1}^{p(|x|)}`, `P[V(x, r) accepts] ≥ 1/2` if `x ∈ L`, and
`V(x, r)` accepts for no `r` if `x ∉ L`.

**Formalization Note** `V` accepts when its output is `[true]`. The probability is a counting
ratio: `2^{p(|x|)} ≤ 2 · #{r : V(x, r) accepts}`. -/
def InRP (L : Set (List Bool)) : Prop :=
  ∃ (p : Polynomial ℕ) (V : List Bool → List Bool), PolyTimeFun V ∧
    ∀ x : List Bool,
      (x ∈ L → 2 ^ (p.eval x.length) ≤ 2 * (Finset.univ.filter fun r : Fin (p.eval x.length) → Bool =>
        V (pairEnc x (List.ofFn r)) = [true]).card) ∧
      (x ∉ L → ∀ r : Fin (p.eval x.length) → Bool, V (pairEnc x (List.ofFn r)) ≠ [true])

end DDNNFNeg.Supplement


