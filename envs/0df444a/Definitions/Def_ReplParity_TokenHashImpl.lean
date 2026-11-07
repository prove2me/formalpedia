-- Prove2me | Definitions.Def_ReplParity_TokenHashImpl
-- name    : ReplParity_TokenHashImpl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:30.103599+00:00
-- url     : https://prove2.me/theorems/a988c159-3571-445d-99e3-05aa01515fea
-- title:
--   Admissible implementations of the token min-hash
-- statement:
--   The token min-hash of Lemma 3.2 depends on four implementation choices, fixed by a value of this structure for sample size $K$ and parameter $\eta$:
--
--   1. a finite field $F$ together with a bijection $F\to\{0,\dots,2^b-1\}$ (reading a field element as a $b$-bit integer), where $2^b\ge 8K^2/\eta$;
--   2. an encoding of tokens $(V,j)$ (a subspace $V$ and an index $j$) into $F$, injective on all tokens with $j\le K$;
--   3. an injective code of subspaces, the "canonical encoding of $V$" that orders tokens of equal dimension.
--
--   The paper takes $b$ the least power of two with $b\ge\max\{B_0,\lceil\log_2(8K^2/\eta)\rceil\}$, $B_0=n^2+\lceil\log_2(K+1)\rceil$, the field $\mathbb F_{2^b}$ built by quadratic extensions, and reduced row echelon bases to encode subspaces; that is one admissible choice.
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), proof of Lemma 3.2, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_ReplParity_Vec

namespace ReplParity

/-- **Admissible implementation choices of the token min-hash.** Shen, Zhong, *Replicable Parity
Learning: Cubic Sample Complexity and a Geometric Characterization*, STOC 2027 submission (manuscript
sha256 40424491…), proof of Lemma 3.2, p.16 (PDF p.18): "We order the tokens by decreasing dim V,
then by the canonical encoding of V, and then by j" and "each token has an injective encoding with
B_0 = n² + ⌈log₂(K + 1)⌉ bits, and we let b be the least power of two with
b ≥ max{B_0, ⌈log₂(8K²/η)⌉}. The seed consists of independent uniform coefficients
c_0, . . . , c_{2κ−1} in the field 𝔽_{2^b}, and the hash of a token z is h(z) = Σ_{ℓ<2κ} c_ℓ z^ℓ,
read as a b-bit integer."

A value of `TokenHashImpl n K η` fixes:
1. a finite field `F` and a bijection `toInt : F ≃ Fin (2^b)` (the reading as a `b`-bit integer),
   with `2^b ≥ 8K²/η`;
2. an encoding `enc` of tokens `(V, j)` into `F`, injective on all tokens with `j ≤ K`;
3. an injective code `rk` of subspaces (the canonical encoding used to order tokens).

**Formalization Note.** The paper's choices (the least admissible power of two `b`, `𝔽_{2^b}` built by
quadratic extensions, the encoding of `V` by its reduced row echelon basis) are one instance; the
statements about the construction hold for every value of this structure. -/
structure TokenHashImpl (n K : ℕ) (η : ℝ) where
  /-- The hash field. -/
  F : Type
  [instField : Field F]
  [instFintype : Fintype F]
  [instDecEq : DecidableEq F]
  /-- The bit length of a field element. -/
  b : ℕ
  /-- Reading a field element as a `b`-bit integer. -/
  toInt : F ≃ Fin (2 ^ b)
  /-- The field is large enough for the collision bound. -/
  big : 8 * (K : ℝ) ^ 2 / η ≤ 2 ^ b
  /-- The encoding of tokens into the field. -/
  enc : Subsp n × ℕ → F
  enc_injOn : Set.InjOn enc {t | t.2 ≤ K}
  /-- The canonical code of a subspace, used to order tokens. -/
  rk : Subsp n → ℕ
  rk_inj : Function.Injective rk

attribute [instance] TokenHashImpl.instField TokenHashImpl.instFintype TokenHashImpl.instDecEq

end ReplParity


