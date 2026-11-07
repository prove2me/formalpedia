-- Prove2me | Definitions.Def_SubexpPrimes_digitPoly
-- name    : SubexpPrimes_digitPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:58:39.999487+00:00
-- url     : https://prove2.me/theorems/ec9f2f61-e188-4f01-8c24-ad7f019dc778
-- title:
--   Digit polynomials, the ring $R_{P,\ell}$ and decoding
-- statement:
--   For $|\gamma|<1$ with $|\gamma|=\sum_{j=1}^p\gamma_j2^{-j}$, the **digit polynomial** of $\gamma$ is $\operatorname{sgn}(\gamma)\sum_j\gamma_jV^j$, and for $\gamma=\pm1$ it is $\pm1$. It gives back $\gamma$ at $V=1/2$. The ring is $R_{P,\ell}=(\mathbb Z/2^P\mathbb Z)[V]/(V^\ell)$. The **decoded value** of an element with coefficients $h_j$ is
--
--   $$
--   \widehat Z=\sum_{j\le J}h_j2^{-j},
--   $$
--
--   with $h_j$ the representative in $(-2^{P-1},2^{P-1}]$.
--
--   **Formalization Note** An element of $R_{P,\ell}$ is a polynomial over `ZMod (2^P)` read through its $\ell$ low coefficients. Truncation is a ring homomorphism, so a contraction may be computed untruncated.
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Lemma A.24, pp.75, 92; p.74

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_SubexpPrimes_NetDesc

set_option autoImplicit false

namespace SubexpPrimes

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **The digit polynomial** — Gajulapalli, *Deterministic Construction of Primes in Subexponential
Time* (manuscript, sha256 6ad4d3de…), proof of Lemma A.24, p.92: for `|γ| < 1` with
`|γ| = ∑_{j=1}^p γ_j 2^{-j}`, it is `sgn(γ) ∑_j γ_j V^j`; for `γ = ±1` it is `±1`. It gives back `γ`
at `V = 1/2`. The digit `γ_j` is the parity of `⌊|γ| 2^j⌋`. -/
noncomputable def digitPoly (p : ℕ) (γ : ℚ) : Polynomial ℤ :=
  if γ = 1 then 1 else if γ = -1 then -1 else
    Polynomial.C (if γ < 0 then -1 else 1) *
      ∑ j ∈ Finset.Icc 1 p, Polynomial.C (⌊|γ| * 2 ^ j⌋ % 2) * Polynomial.X ^ j

/-- **The truncated polynomial ring `R_{P,ℓ} = (ℤ/2^Pℤ)[V]/(V^ℓ)`** (p.74). An element is
represented by any polynomial in `(ZMod (2^P))[V]` and stands for its residue modulo `V^ℓ`, that
is, for its coefficients of degree `< ℓ`. Truncation is a ring homomorphism, so a contraction may be
computed here and truncated afterwards. -/
abbrev TruncPoly (P : ℕ) := Polynomial (ZMod (2 ^ P))

/-- The word of an element of `R_{P,ℓ}`: its `ℓ` coefficients, each an integer in `[0, 2^P)`
in binary. -/
def truncWord {P : ℕ} (ℓ : ℕ) (r : TruncPoly P) : List Bool :=
  Encoding.encodeList countWord (List.ofFn fun k : Fin ℓ => (r.coeff k).val)

/-- The tables of the conversion in Lemma A.24: every entry `γ` replaced by its digit polynomial,
over `R_{P,ℓ}`. Reading through `ℓ` low coefficients is the truncation of the tables. -/
noncomputable def digitTable (D : NetDesc) (T : D.Tables ℚ) (P : ℕ) : D.Tables (TruncPoly P) :=
  fun v z => (digitPoly D.prec (T v z)).map (Int.castRingHom (ZMod (2 ^ P)))

/-- The representative in `(-2^{P-1}, 2^{P-1}]` of a residue modulo `2^P` (p.92). -/
def centeredRep {P : ℕ} (r : ZMod (2 ^ P)) : ℤ :=
  if 2 * r.val ≤ 2 ^ P then (r.val : ℤ) else (r.val : ℤ) - 2 ^ P

/-- **The decoded value** (p.92): `Ẑ = ∑_{j ≤ J} h_j 2^{-j}`, where `h_j` is the centered
representative of the `j`-th coefficient of the contraction over `R_{P,J+1}`. -/
noncomputable def digitDecode {P : ℕ} (J : ℕ) (H : TruncPoly P) : ℚ :=
  ∑ j ∈ Finset.range (J + 1), (centeredRep (H.coeff j) : ℚ) / 2 ^ j

end SubexpPrimes


