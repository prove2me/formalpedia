-- Prove2me | Definitions.Def_ReplParity_tokens
-- name    : ReplParity_tokens
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:39:55.052791+00:00
-- url     : https://prove2.me/theorems/90aba573-73cd-421f-916b-76cb81d847d5
-- title:
--   Tokens $\mathcal T(S)$, the token order and the truncation $\mathcal B(S)$
-- statement:
--   For a sample $S$ in $\mathbb F_2^n$ and each subspace $V$, let $w_S(V)=\dim(V)\,n_S(V)$ be the number of vectors in the parts that span $V$. The token set is
--   $$\mathcal T(S)=\{(V,j):1\le j\le w_S(V)\}.$$
--   Tokens are ordered by decreasing $\dim V$, then by the canonical code of $V$, then by $j$; the key of $(V,j)$ is $(n-\dim V,\ \mathrm{code}(V),\ j)$, compared lexicographically. For a finite set $T$ and a key, the **first $\kappa$ elements** are those with fewer than $\kappa$ elements of $T$ before them; for $T=\mathcal T(S)$ and $\kappa=K/4$ this is $\mathcal B(S)$.
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), proof of Lemma 3.2, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_ReplParity_mult

namespace ReplParity

/-- `w_S(V) = dim(V) · n_S(V)`, the number of vectors in the parts that span `V`. -/
noncomputable def tokWeight {n : ℕ} (S : List (Vec n)) (V : Subsp n) : ℕ :=
  Module.finrank (ZMod 2) V * mult S V

open Classical in
/-- **Token sets.** Shen, Zhong, *Replicable Parity Learning: Cubic Sample Complexity and a
Geometric Characterization*, STOC 2027 submission (manuscript sha256 40424491…), proof of
Lemma 3.2, p.16 (PDF p.18): "for each span V of a part, let w_S(V) = dim(V) n_S(V) be the number of
vectors in the parts that span V. Each part is linearly independent, so Σ_V w_S(V) = K, and the
token set is T(S) = {(V, j) : 1 ≤ j ≤ w_S(V)}." -/
noncomputable def tokens {n : ℕ} (S : List (Vec n)) : Finset (Subsp n × ℕ) :=
  Finset.univ.biUnion (fun V => (Finset.Icc 1 (tokWeight S V)).image (fun j => (V, j)))

/-- The token order of p.16: "by decreasing dim V, then by the canonical encoding of V, and then by
j". The key of `(V, j)` is `(n − dim V, rk V, j)`, compared lexicographically; smaller keys come
first. -/
noncomputable def tokKey {n : ℕ} (rk : Subsp n → ℕ) (t : Subsp n × ℕ) : Lex (ℕ × Lex (ℕ × ℕ)) :=
  toLex (n - Module.finrank (ZMod 2) t.1, toLex (rk t.1, t.2))

/-- The first `κ` elements of a finite set `T` in the order given by `key`: the elements with fewer
than `κ` elements of `T` before them. With `key` injective on `T`, this is the set of the first `κ`
elements, `B(S)` of p.16 for `T = T(S)`. -/
def firstK {τ τ' : Type*} [LinearOrder τ'] (key : τ → τ') (κ : ℕ) (T : Finset τ) : Finset τ :=
  T.filter (fun t => (T.filter (fun t' => key t' < key t)).card < κ)

end ReplParity


