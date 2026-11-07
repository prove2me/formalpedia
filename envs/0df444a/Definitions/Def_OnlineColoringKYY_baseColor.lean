-- Prove2me | Definitions.Def_OnlineColoringKYY_baseColor
-- name    : OnlineColoringKYY_baseColor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:27:45.581031+00:00
-- url     : https://prove2.me/theorems/79faa065-15df-4f3a-8d20-0de1d54260e0
-- title:
--   Base color $\varphi(u)$ fixed when $u$ is paired with $w$
-- statement:
--   In the adversary of Section 4.2, the base color of a vertex is fixed only when a second vertex with the same online color arrives. When $u$ is paired with $w$ (and $x_u \ne x_w$), let $s$ be the least index with $x_u(s) \ne x_w(s)$. The base color of $u$ is
--   $$
--   \varphi(u) = 2s + x_u(s).
--   $$
--   Then $\varphi(u) \in X_u$, $\varphi(w) \in X_w$ and $\{\varphi(u), \varphi(w)\} = \{2s, 2s+1\}$: this is the paper's rule of choosing $s$ such that one base color of the pair $s$ is in exactly one of $X_u, X_w$ and the other is in the other, and assigning each vertex the one in its own set.
--
--   **Formalization Note** The paper allows any such $s$; taking the least fixes one strategy of the adversary. Base colors are 0-indexed. If $x_u = x_w$ (excluded by the distinctness of the codes) the value is $0$.
-- source:
--   Kawarabayashi–Yoneda–Yoneda, Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms, STOC 2027 submission (manuscript sha256 3d1eeea6…), Section 4.2, "Adversary algorithm", printed p.13 (PDF p.15)

import Mathlib

set_option autoImplicit false

namespace OnlineColoringKYY

/-- The **base color** `φ(u)` that the adversary assigns to vertex `u` once `u` is paired with a
vertex `w` (the second vertex of `u`'s online color) (Kawarabayashi–Yoneda–Yoneda, *Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms*, STOC 2027 submission (manuscript sha256 3d1eeea6…), Section 4.2, "Adversary algorithm",
printed p.13 = PDF p.15): with `s` the least index at which the codes of `u` and `w` differ,
`φ(u) = 2s + code u s`.

Then `φ(u) ∈ X_u`, `φ(w) ∈ X_w` and `{φ(u), φ(w)} = {2s, 2s + 1}`: this is the paper's rule
"choose `s` such that `2s − 1` is in exactly one of `{X_v1, X_v2}`, and `2s` is in the other",
with the least such `s`.

**Formalization Note** Base colors are 0-indexed (see `admits`). The paper allows any such `s`;
choosing the least one fixes one adversary strategy. If the codes of `u` and `w` agree everywhere
(which never happens for distinct vertices under an injective code) the value is the junk `0`. -/
def baseColor {ℓ : ℕ} (code : ℕ → Fin ℓ → Bool) (u w : ℕ) : ℕ :=
  if h : (Finset.univ.filter (fun i : Fin ℓ => code u i ≠ code w i)).Nonempty then
    2 * ((Finset.univ.filter (fun i : Fin ℓ => code u i ≠ code w i)).min' h).val +
      (code u ((Finset.univ.filter (fun i : Fin ℓ => code u i ≠ code w i)).min' h)).toNat
  else 0

end OnlineColoringKYY


