-- Prove2me | Definitions.Def_ReplParity_tokenMinHash
-- name    : ReplParity_tokenMinHash
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:41:02.200272+00:00
-- url     : https://prove2.me/theorems/58856dad-6c86-4b9b-9fb1-d55bd28299cd
-- title:
--   The token min-hash construction (proof of Lemma 3.2)
-- statement:
--   Fix $K$, $\eta$ and an admissible implementation (field $F$, integer reading, token encoding, subspace code), and let $K=4\lceil128n^3/\eta^2\rceil$ in the lemma. On a sample $S$ of $K$ vectors and a seed $c=(c_0,\dots,c_{2\kappa-1})\in F^{2\kappa}$, $\kappa=K/4$:
--
--   1. compute the stable partition of $S$, the tokens $\mathcal T(S)$ and the first $\kappa$ tokens $\mathcal B(S)$;
--   2. hash each token $z$ by $h(z)=\sum_{\ell<2\kappa}c_\ell\,z^\ell$ (with $z$ encoded in $F$), read as a $b$-bit integer;
--   3. output the span $W$ named by the token of $\mathcal B(S)$ with the least hash, ties broken by the token order.
--
--   The seed is uniform, i.e. the coefficients are independent and uniform in $F$.
--
--   **Formalization Note** The selected token is unique because the subspace code is injective. If $\mathcal B(S)$ is empty (every sample point is zero, an event of probability $0$ when $Q$ lives on nonzero vectors) the output is $\{0\}$.
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), proof of Lemma 3.2, p.16 (PDF p.18); Lemma 3.2, p.15

import Mathlib
import Definitions.Def_ReplParity_TokenHashImpl
import Definitions.Def_ReplParity_tokens

namespace ReplParity

/-- `K = 4⌈128n³/η²⌉`, the sample size of Lemma 3.2 (p.15). -/
noncomputable def tokK (n : ℕ) (η : ℝ) : ℕ := 4 * ⌈128 * (n : ℝ) ^ 3 / η ^ 2⌉₊

/-- The polynomial hash `h(x) = Σ_{ℓ<k} c_ℓ x^ℓ` with coefficients `c`. -/
def polyHash {F : Type*} [Field F] {k : ℕ} (c : Fin k → F) (x : F) : F :=
  ∑ ℓ : Fin k, c ℓ * x ^ (ℓ : ℕ)

open Classical in
/-- **The token min-hash construction (proof of Lemma 3.2).** Shen, Zhong, *Replicable Parity
Learning: Cubic Sample Complexity and a Geometric Characterization*, STOC 2027 submission (manuscript
sha256 40424491…), proof of Lemma 3.2, p.16 (PDF p.18): "We compute the stable partition of S and,
for each span V of a part, let w_S(V) = dim(V) n_S(V) … the token set is T(S) = {(V, j) : 1 ≤ j ≤
w_S(V)}. We order the tokens by decreasing dim V, then by the canonical encoding of V, and then by
j, and we let B(S) be the set of the first κ = K/4 tokens. … The seed consists of independent
uniform coefficients c_0, . . . , c_{2κ−1} in the field 𝔽_{2^b}, and the hash of a token z is
h(z) = Σ_{ℓ<2κ} c_ℓ z^ℓ, read as a b-bit integer. The output W is the span named by the token of
B(S) with the least hash, where ties are broken by the token order."

Input: `K` samples `S` and the seed `c` (`2κ = K/2` field coefficients). The selected token
minimizes (hash read as an integer, token key) lexicographically; the output is the subspace it
names.

**Formalization Note.** `H` fixes the field, the integer reading, the token encoding and the
subspace order (`TokenHashImpl`). Since `rk` is injective, the selected token is unique. If
`B(S)` is empty (all samples zero, which has probability `0` under a distribution on nonzero
vectors) the output is `{0}`. -/
noncomputable def tokenMinHash {n K : ℕ} {η : ℝ} (H : TokenHashImpl n K η) (S : Fin K → Vec n)
    (c : Fin (K / 2) → H.F) : Subsp n :=
  let B := firstK (tokKey H.rk) (K / 4) (tokens (List.ofFn S))
  let score : Subsp n × ℕ → Lex (ℕ × Lex (ℕ × Lex (ℕ × ℕ))) :=
    fun t => toLex (((H.toInt (polyHash c (H.enc t)) : Fin (2 ^ H.b)) : ℕ), tokKey H.rk t)
  if h : ∃ t ∈ B, ∀ t' ∈ B, score t ≤ score t' then (Classical.choose h).1 else ⊥

end ReplParity


